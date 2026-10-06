use crate::env::{ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecursorData, ReducibilityHint};
use crate::expr::{BinderStyle, Expr};
use crate::hash64;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_hash_set, new_fx_index_map, BigUintPtr, Config, DagMarker, ExportFile, ExprPtr, FxHashMap,
    FxIndexMap, LeanDag, LevelPtr, LevelsPtr, NameCache, NamePtr, StringPtr,
};
use num_bigint::BigUint;
use serde::de::{Error as DeError, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::Cow;
use std::collections::HashMap;
use std::error::Error;
use std::io::BufRead;
use std::sync::Arc;
use std::{assert_matches, fmt};

fn check_semver<'a>(meta: &FileMeta<'a>) -> Result<(), Box<dyn Error>> {
    const MIN_SEMVER: semver::Version = semver::Version::new(3, 1, 0);
    const MAX_SEMVER: semver::Version = semver::Version::new(3, 2, 0);
    let export_file_semver = semver::Version::parse(&meta.format.version)?;
    if export_file_semver < MIN_SEMVER {
        return Err(Box::from(format!(
            "export format version is less than the minimum supported version. Found {}, but min supported is {}",
            export_file_semver, MIN_SEMVER
        )))
    } else if export_file_semver >= MAX_SEMVER {
        return Err(Box::from(format!(
            "export format version is greater than the maximum supported version. Found {}, but max (exclusive) supported is {}",
            export_file_semver, MAX_SEMVER
        )))
    } else {
        Ok(())
    }
}

pub struct Parser<'a, R: BufRead> {
    buf_reader: R,
    line_num: usize,
    dag: LeanDag<'a>,
    declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    notations: FxHashMap<NamePtr<'a>, Notation<'a>>,
    config: Config,
    /// Tracks axiom names that were found in the export file, but not white-listed,
    /// for use when `unpermitted_axiom_hard_error: false`
    skipped: Vec<(u32, Declar<'a>)>,
    mutual_block_sizes: FxHashMap<NamePtr<'a>, (usize, usize)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
struct FormatMeta<'a> {
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>,
    format: FormatMeta<'a>,
}

#[derive(Hash, Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum BackRef {
    #[serde(alias = "in")]
    In(u32),
    #[serde(alias = "il")]
    Il(u32),
    #[serde(alias = "ie")]
    Ie(u32),
}

impl BackRef {
    pub fn id(&self) -> u32 {
        match *self {
            BackRef::In(id) | BackRef::Il(id) | BackRef::Ie(id) => id,
        }
    }

    fn assert(self, (idx, inserted): (BackRef, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Name");
        }
        if self != idx {
            eprintln!(
                "Declined: Name back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                idx, self
            );
            std::process::exit(2);
        }
    }

    fn assert_in(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Name");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::In(lhs) {
            eprintln!(
                "Declined: Name back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::In(lhs),
                self
            );
            std::process::exit(2);
        }
    }

    fn assert_il(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Level");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Il(lhs) {
            eprintln!(
                "Declined: Level back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::Il(lhs),
                self
            );
            std::process::exit(2);
        }
    }

    fn assert_ie(self, (idx, inserted): (usize, bool)) {
        if !inserted {
            panic!("Attempted to insert duplicate Expr");
        }
        let lhs = u32::try_from(idx).unwrap();
        if self != BackRef::Ie(lhs) {
            eprintln!(
                "Declined: Expr back-reference mismatch, expected {:?}, found {:?}. Back-refs must be continuous.",
                BackRef::Ie(lhs),
                self
            );
            std::process::exit(2);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct ExportJsonObject<'a> {
    #[serde(flatten)]
    pub val: ExportJsonVal<'a>,
    #[serde(flatten)]
    pub i: Option<BackRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct RecursorRule {
    pub ctor: u32,
    pub nfields: u16,
    pub rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct IndInfo {
    pub name: u32,
    #[serde(rename = "levelParams")]
    pub uparams: Vec<u32>,
    #[serde(rename = "type")]
    pub ty: u32,
    pub all: Vec<u32>,
    pub ctors: Vec<u32>,
    #[serde(rename = "isRec")]
    pub is_rec: bool,
    #[serde(rename = "isReflexive")]
    pub is_reflexive: bool,
    #[serde(rename = "numIndices")]
    pub num_indices: u16,
    #[serde(rename = "numNested")]
    pub num_nested: u16,
    #[serde(rename = "numParams")]
    pub num_params: u16,
    #[serde(rename = "isUnsafe")]
    pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct Constructor {
    pub name: u32,
    #[serde(rename = "levelParams")]
    pub uparams: Vec<u32>,
    #[serde(rename = "type")]
    pub ty: u32,
    #[serde(rename = "isUnsafe")]
    pub is_unsafe: bool,
    pub cidx: u16,
    #[serde(rename = "numParams")]
    pub num_params: u16,
    #[serde(rename = "numFields")]
    pub num_fields: u16,
    pub induct: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct Recursor {
    pub name: u32,
    #[serde(rename = "levelParams")]
    pub uparams: Vec<u32>,
    #[serde(rename = "type")]
    pub ty: u32,
    #[serde(rename = "isUnsafe")]
    pub is_unsafe: bool,
    #[serde(rename = "numParams")]
    pub num_params: u16,
    #[serde(rename = "numIndices")]
    pub num_indices: u16,
    #[serde(rename = "numMotives")]
    pub num_motives: u16,
    #[serde(rename = "numMinors")]
    pub num_minors: u16,
    pub rules: Vec<RecursorRule>,
    pub all: Vec<u32>,
    pub k: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub enum ExportJsonVal<'a> {
    // The exporter metadata, incl. info about the lean, exporter, and format versions used
    // to create the export file.
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr { pre: u32, str: Cow<'a, str> },
    #[serde(rename = "num")]
    NameNum { pre: u32, i: u32 },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(
        rename = "natVal",
        deserialize_with = "deserialize_biguint_from_string",
        serialize_with = "serialize_biguint_to_string"
    )]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData { expr: u32, data: serde_json::Value },
    #[serde(rename = "letE")]
    ExprLet {
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    #[serde(rename = "const")]
    ExprConst {
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>,
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32,
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle,
    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "name")]
        binder_name: u32,
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
        #[serde(rename = "binderInfo")]
        binder_info: BinderStyle,
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: usize,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort(u32),
    #[serde(rename = "bvar")]
    ExprBVar(u16),
    #[serde(rename = "axiom")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "thm")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "def")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety,
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "quot")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind,
    },
    #[serde(rename = "inductive")]
    Inductive {
        #[serde(rename = "types")]
        ind_vals: Vec<IndInfo>,
        #[serde(rename = "ctors")]
        ctor_vals: Vec<Constructor>,
        #[serde(rename = "recs")]
        rec_vals: Vec<Recursor>,
    },
}

pub fn parse_export_file<'p, 'a, R: BufRead>(
    buf_reader: &mut R,
    config: Config,
) -> Result<(crate::util::ExportFile<'p>, Vec<(u32, Declar<'a>)>, Vec<ExportJsonObject<'a>>), Box<dyn Error>> {
    let mut parser = Parser::new(buf_reader, config);
    let mut line_buffer = String::new();
    let mut export_objects: Vec<ExportJsonObject<'a>> = vec![];
    loop {
        let amt = parser.buf_reader.read_line(&mut line_buffer)?;
        if amt == 0 {
            break
        }
        let ret = parser.go1(line_buffer.as_str())?;
        if matches!(ret, ExportJsonObject {val : ExportJsonVal::Metadata(..), ..}) && parser.line_num != 0 {
            export_objects.push(ret);   
            break;
        }
        export_objects.push(ret);
        parser.line_num += 1;
        line_buffer.clear();
    }
    let name_cache = parser.dag.mk_name_cache();
    let mut export_file = crate::util::ExportFile {
        dag: parser.dag,
        declars: parser.declars,
        notations: parser.notations,
        name_cache, // todo!("avoid duplicated generations")
        config: parser.config,
        mutual_block_sizes: parser.mutual_block_sizes,
        ind_name_to_recursor_names: HashMap::default(), // todo!("avoid empty value here")
    };
    export_file.post_process();
    Ok((export_file, parser.skipped, export_objects))
}

impl<'p> ExportFile<'p> {
    pub fn post_process(&mut self) {
        // If the execution config has `unknown_pp_declar_hard_error: true`, and a `pp_declars`
        // that includes `foo`, then we return early with an error if no `foo` declaration is present
        // in the export file.
        if self.config.unknown_pp_declar_hard_error {
            if let Some(pp_declars) = self.config.pp_declars.as_ref() {
                let mut pp_declar_names =
                    pp_declars.iter().map(|s| s.as_str()).collect::<crate::util::FxHashSet<&str>>();
                for declar_name in self.declars.keys() {
                    let n = self.dag.name_to_string(*declar_name);
                    pp_declar_names.remove(n.as_str());
                }
                if pp_declar_names.len() > 0 {
                    let list = pp_declar_names.into_iter().collect::<Vec<&str>>();
                    panic!("these pp_declars were not found in the exported environment: {:#?}", list)
                }
            }
        }

        self.name_cache = self.dag.mk_name_cache();
        // Maps inductive names to exported recursor names. This is later reused in the inductive
        // module to require that the set of derived recursors matches the set of exported recursors,
        // so that additional "unassociated" recursors cannot be added to the environment.
        self.ind_name_to_recursor_names = new_fx_hash_map();
        for declar in self.declars.values() {
            match declar {
                Declar::Constructor(ConstructorData { inductive_name, info, .. }) => {
                    match self.declars.get(inductive_name).unwrap() {
                        Declar::Inductive(InductiveData { all_ctor_names, .. }) => {
                            assert!(all_ctor_names.contains(&info.name))
                        }
                        _ => panic!("failed to find inductive {:?}", self.dag.name_to_string(*inductive_name)),
                    }
                }
                Declar::Recursor(RecursorData { all_inductives, info, .. }) => {
                    for ind_name in all_inductives.iter().copied() {
                        self.ind_name_to_recursor_names.entry(ind_name).or_insert(new_fx_hash_set()).insert(info.name);
                    }
                }
                _ => continue,
            }
        }
    }
}

#[derive(Debug)]
pub enum LeanDagInsertResult<'a> {
    Id((BackRef, bool)),
    Declars(Vec<(NamePtr<'a>, Declar<'a>, Option<usize>)>),
    Skip(Declar<'a>),
    Metadata,
}

impl<'a, R: BufRead> Parser<'a, R> {
    pub fn new(buf_reader: R, config: Config) -> Self {
        Self {
            buf_reader,
            line_num: 0usize,
            dag: LeanDag::new(&config),
            declars: new_fx_index_map(),
            notations: new_fx_hash_map(),
            config,
            skipped: Vec::new(),
            mutual_block_sizes: new_fx_hash_map(),
        }
    }

    fn go1<'b>(&mut self, line: &str) -> Result<ExportJsonObject<'b>, Box<dyn Error>> {
        let line = serde_json::from_str::<ExportJsonObject>(line)?;
        let ExportJsonObject { val, i: assigned_idx } = line.clone();
        match self.dag.go1(val, Some(&self.config))? {
            LeanDagInsertResult::Id(idx_) => assigned_idx.unwrap().assert(idx_),
            LeanDagInsertResult::Declars(declars) => {
                let declar_size = self.declars.len();
                for (name, declar, mutual_block_size) in declars {
                    assert!(self.declars.insert(name, declar).is_none());
                    if let Some(mutual_block_size) = mutual_block_size {
                        self.mutual_block_sizes.insert(name, (declar_size, mutual_block_size));
                    }
                }
            }
            LeanDagInsertResult::Skip(d) => self.skipped.push((self.declars.len().try_into().unwrap(), d)),
            LeanDagInsertResult::Metadata => assert!(assigned_idx.is_none()),
        }
        Ok(line)
    }
}

impl Config {
    fn axiom_permitted(&self, n: &String) -> bool {
        self.unsafe_permit_all_axioms || self.permitted_axioms.as_ref().map(|v| v.contains(n)).unwrap_or(false)
    }
}

impl<'a> LeanDag<'a> {
    // Used for the axiom whitelist feature.
    fn name_to_string(&self, n: NamePtr<'a>) -> String {
        match self.names.get_index(n.idx()).copied().unwrap() {
            Name::Anon => String::new(),
            Name::Str(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + self.strings.get_index(sfx.idx()).unwrap()
            }
            Name::Num(pfx, sfx, _) => {
                let mut s = self.name_to_string(pfx);
                if !s.is_empty() {
                    s.push('.');
                }
                s + format!("{}", sfx).as_str()
            }
        }
    }

    fn num_loose_bvars(&self, e: ExprPtr<'a>) -> u16 { self.exprs.get_index(e.idx()).unwrap().num_loose_bvars() }

    fn has_fvars(&self, e: ExprPtr<'a>) -> bool { self.exprs.get_index(e.idx()).unwrap().has_fvars() }

    pub fn get_name_ptr(&self, idx: u32) -> NamePtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.names.len(), "{} !< {}", idx, self.names.len());
        out
    }

    fn get_level_ptr(&self, idx: u32) -> LevelPtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        if !((idx as usize) < self.levels.len()) {
            eprintln!("! ({} < {})", idx, self.levels.len());
            panic!()
        }
        out
    }
    fn get_names(&self, idxs: &[u32]) -> Vec<NamePtr<'a>> {
        let mut names = Vec::new();
        for idx in idxs.iter().copied() {
            assert!(self.names.get_index(idx as usize).is_some());
            names.push(NamePtr::from(DagMarker::ExportFile, idx as usize));
        }
        names
    }

    pub fn get_uparams_ptr(&mut self, name_idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for name_idx in name_idxs.iter().copied() {
            let name_ptr = self.get_name_ptr(name_idx);
            let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
            // Has to already exist
            let idx = self.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap();
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.uparams.insert_full(Arc::from(levels)).0)
    }

    pub fn get_uparams_ptr_with_default_zero(&mut self, name_idxs: &[Option<u32>]) -> LevelsPtr<'a> {
        let levels : Vec<_> = name_idxs.iter().map(|name_idx| {
            LevelPtr::from(
                DagMarker::ExportFile,
                if let Some(name_idx) = *name_idx {
                    let name_ptr = self.get_name_ptr(name_idx);
                    let hash = hash64!(crate::level::PARAM_HASH, name_ptr);
                    self.levels.get_index_of(&Level::Param(name_ptr, hash)).unwrap()
                } else {
                    self.levels.get_index_of(&Level::Zero).unwrap()
                },
            )
        }).collect();
        // );
        // }
        LevelsPtr::from(DagMarker::ExportFile, self.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_levels_ptr(&mut self, idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::new();
        for idx in idxs.iter().copied() {
            levels.push(LevelPtr::from(DagMarker::ExportFile, idx as usize));
        }
        LevelsPtr::from(DagMarker::ExportFile, self.uparams.insert_full(Arc::from(levels)).0)
    }

    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        let out = crate::util::Ptr::from(DagMarker::ExportFile, idx as usize);
        assert!((idx as usize) < self.exprs.len());
        out
    }

    pub fn go1<'b>(
        self: &mut LeanDag<'a>,
        val: ExportJsonVal,
        cfg: Option<&Config>,
    ) -> Result<LeanDagInsertResult<'a>, Box<dyn Error>> {
        use ExportJsonVal::*;
        let insert_name = move |self_: &mut Self, v| {
            let (i, b) =
                if let Some(i) = self_.names.get_index_of(&v) { (i, false) } else { self_.names.insert_full(v) };
            Ok(LeanDagInsertResult::Id((BackRef::In(i.try_into().unwrap()), b)))
        };
        let insert_level = |self_: &mut Self, v| {
            let (i, b) =
                if let Some(i) = self_.levels.get_index_of(&v) { (i, false) } else { self_.levels.insert_full(v) };
            Ok(LeanDagInsertResult::Id((BackRef::Il(i.try_into().unwrap()), b)))
        };
        let insert_expr = |self_: &mut Self, v| {
            let (i, b) =
                if let Some(i) = self_.exprs.get_index_of(&v) { (i, false) } else { self_.exprs.insert_full(v) };
            Ok(LeanDagInsertResult::Id((BackRef::Ie(i.try_into().unwrap()), b)))
        };
        let insert_declar = |name, declar| Ok(LeanDagInsertResult::Declars(vec![(name, declar, None)]));
        match val {
            Metadata(json_val) => {
                let _ = check_semver(&json_val)?;
                Ok(LeanDagInsertResult::Metadata)
            }
            NameStr { pre, str } => {
                let pfx = self.get_name_ptr(pre);
                let sfx = StringPtr::from(
                    DagMarker::ExportFile,
                    self.strings.insert_full(std::borrow::Cow::Owned(str.to_string())).0,
                );

                // let insert_result = {
                let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                insert_name(self, Name::Str(pfx, sfx, hash))
                // };
                // assigned_idx.unwrap().assert_in(insert_result);
            }
            NameNum { pre, i } => {
                let pfx = self.get_name_ptr(pre);
                let sfx = i as u64;
                // let insert_result = {
                let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
                insert_name(self, Name::Num(pfx, sfx, hash))
                // };
                // assigned_idx.unwrap().assert_in(insert_result);
            }
            NatLit(big_uint) => {
                if matches!(cfg, Some(Config { nat_extension: false, .. })) {
                    return Err(Box::<dyn Error>::from(
                        format!("Nat lit extension disallowed by checker execution config, but export file contains a nat literal")
                    ))
                }
                let num_ptr =
                    BigUintPtr::from(DagMarker::ExportFile, self.bignums.as_mut().unwrap().insert_full(big_uint).0);
                // let insert_result = {
                //     let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
                //     self.dag.exprs.insert_full(Expr::NatLit { ptr: num_ptr, hash })
                // };
                //todo: deprecated code?
                // if !self.config.nat_extension {
                //     return Err(Box::<dyn Error>::from(format!(
                //         "Nat lit extension disallowed by checker execution config" /* found {:?}",
                //                                                                    line */
                //     )))
                // }
                let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
                insert_expr(self, Expr::NatLit { ptr: num_ptr, hash })
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            StrLit(cow_str) => {
                if matches!(cfg, Some(Config { string_extension: false, .. })) {
                    return Err(Box::<dyn Error>::from(
                        format!("String lit extension disallowed by checker execution config, but export file contains a string literal")
                    ))
                }
                let s = cow_str.to_string();
                let string_ptr =
                    StringPtr::from(DagMarker::ExportFile, self.strings.insert_full(crate::util::CowStr::Owned(s)).0);
                // let insert_result = {
                let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
                insert_expr(self, Expr::StringLit { ptr: string_ptr, hash })
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            LevelSucc(l) => {
                let l = self.get_level_ptr(l);
                // let insert_result = {
                let hash = hash64!(crate::level::SUCC_HASH, l);
                insert_level(self, Level::Succ(l, hash))
                // };
                // assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                // let insert_result = {
                let hash = hash64!(crate::level::MAX_HASH, l, r);
                insert_level(self, Level::Max(l, r, hash))
                // };
                // assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelIMax([l, r]) => {
                let l = self.get_level_ptr(l);
                let r = self.get_level_ptr(r);
                // let insert_result = {
                let hash = hash64!(crate::level::IMAX_HASH, l, r);
                insert_level(self, Level::IMax(l, r, hash))
                // };
                // assigned_idx.unwrap().assert_il(insert_result);
            }
            LevelParam(var_idx) => {
                let n = self.get_name_ptr(var_idx);
                // let insert_result = {
                let hash = hash64!(crate::level::PARAM_HASH, n);
                insert_level(self, Level::Param(n, hash))
                // };
                // assigned_idx.unwrap().assert_il(insert_result);
            }
            ExprSort(level) => {
                let level = self.get_level_ptr(level);
                // let insert_result = {
                let hash = hash64!(crate::expr::SORT_HASH, level);
                insert_expr(self, Expr::Sort { level, hash })
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprMData { .. } => {
                panic!("Expr.mdata not supported");
            }
            ExprConst { name, levels } => {
                let name = self.get_name_ptr(name);
                let levels = self.get_levels_ptr(&levels);
                // let insert_result = {
                let hash = hash64!(crate::expr::CONST_HASH, name, levels);
                insert_expr(self, Expr::Const { name, levels, hash })
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprApp { fun, arg } => {
                let fun = self.get_expr_ptr(fun);
                let arg = self.get_expr_ptr(arg);
                // let insert_result = {
                let hash = hash64!(crate::expr::APP_HASH, fun, arg);
                let num_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
                let locals = self.has_fvars(fun) || self.has_fvars(arg);
                insert_expr(self, Expr::App { fun, arg, num_loose_bvars: num_bvars, has_fvars: locals, hash })
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprBVar(dbj_idx) => {
                // let insert_result = {
                let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
                insert_expr(self, Expr::Var { dbj_idx, hash })
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprLambda { binder_name, binder_type, binder_info, body } => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                // let insert_result = {
                let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_info, binder_type, body);
                let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                insert_expr(
                    self,
                    Expr::Lambda {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    },
                )
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprPi { binder_name, binder_type, binder_info, body } => {
                let binder_name = self.get_name_ptr(binder_name);
                let binder_type = self.get_expr_ptr(binder_type);
                let body = self.get_expr_ptr(body);
                // let insert_result = {
                let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_info, binder_type, body);
                let num_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
                let locals = self.has_fvars(binder_type) || self.has_fvars(body);
                insert_expr(
                    self,
                    Expr::Pi {
                        binder_name,
                        binder_style: binder_info,
                        binder_type,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                    },
                )
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprLet { name, ty, value, body, nondep } => {
                let binder_name = self.get_name_ptr(name);
                let binder_type = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let body = self.get_expr_ptr(body);
                // let insert_result = {
                let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
                let num_bvars = self
                    .num_loose_bvars(binder_type)
                    .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
                let locals = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
                insert_expr(
                    self,
                    Expr::Let {
                        binder_name,
                        binder_type,
                        val,
                        body,
                        num_loose_bvars: num_bvars,
                        has_fvars: locals,
                        hash,
                        nondep,
                    },
                )
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            ExprProj { type_name, idx, structure: struct_ } => {
                let ty_name = self.get_name_ptr(type_name);
                let structure = self.get_expr_ptr(struct_);
                // let insert_result = {
                let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
                let num_bvars = self.num_loose_bvars(structure);
                let locals = self.has_fvars(structure);
                insert_expr(
                    self,
                    Expr::Proj { ty_name, idx, structure, num_loose_bvars: num_bvars, has_fvars: locals, hash },
                )
                // };
                // assigned_idx.unwrap().assert_ie(insert_result);
            }
            Axiom { name, ty, uparams, is_unsafe } => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let info = DeclarInfo { name, ty, uparams };
                let axiom = Declar::Axiom { info };
                if let Some(config) = cfg {
                    let name_string = self.name_to_string(name);
                    if config.axiom_permitted(&name_string) {
                        // assert!(self.declars.insert(name, axiom).is_none());
                        insert_declar(name, axiom)
                    } else {
                        // let name_string = self.name_to_string(name);
                        if config.unpermitted_axiom_hard_error {
                            return Err(Box::from(format!("export file declares unpermitted axiom {:?}", name_string)))
                        } else {
                            Ok(LeanDagInsertResult::Skip(axiom))
                        }
                    }
                } else {
                    insert_declar(name, axiom)
                }
            }
            Defn { name, ty, uparams, value, hint, safety } => {
                assert!(!matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial));
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Definition { info, val, hint };
                insert_declar(name, definition)
            }
            Thm { name, ty, uparams, value } => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let theorem = Declar::Theorem { info, val };
                insert_declar(name, theorem)
            }
            Opaque { name, ty, uparams, value, is_unsafe } => {
                assert!(!is_unsafe);
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let definition = Declar::Opaque { info, val };
                insert_declar(name, definition)
            }
            Quot { name, ty, uparams, .. } => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, ty, uparams };
                let quot = Declar::Quot { info };
                insert_declar(name, quot)
            }
            Inductive { ind_vals, ctor_vals, rec_vals } => {
                let block_size = ind_vals.len() + ctor_vals.len() + rec_vals.len();
                let mut declars: Vec<_> = vec![];
                let mut ind_to_recs: FxHashMap<NamePtr, Vec<NamePtr>> =
                    ind_vals.iter().map(|x| (self.get_name_ptr(x.name), vec![])).collect();
                let mut recs: Vec<(NamePtr, Declar, Option<usize>)> = Default::default();
                for Recursor {
                    name,
                    uparams,
                    ty,
                    rules,
                    is_unsafe,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    k,
                    all,
                    ..
                } in rec_vals
                {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let rules = rules
                        .into_iter()
                        .map(|RecursorRule { rhs, ctor, nfields }| crate::env::RecRule {
                            val: self.get_expr_ptr(rhs),
                            ctor_name: self.get_name_ptr(ctor),
                            ctor_telescope_size_wo_params: nfields,
                        })
                        .collect::<Vec<_>>();
                    let all_inductives = self.get_names(&all);
                    for ind in &all_inductives {
                        ind_to_recs.get_mut(ind).unwrap().push(name);
                    }
                    let recursor = Declar::Recursor(RecursorData {
                        info,
                        all_inductives: Arc::from(all_inductives),
                        num_params,
                        num_indices,
                        num_motives,
                        num_minors,
                        rec_rules: Arc::from(rules),
                        is_k: k,
                    });
                    recs.push((name, recursor, None));
                }
                for IndInfo {
                    name,
                    ty,
                    uparams,
                    all,
                    ctors,
                    is_rec,
                    num_nested,
                    num_params,
                    num_indices,
                    is_unsafe,
                    ..
                } in ind_vals
                {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    // self.mutual_block_sizes.insert(name, (block_start, block_size));
                    let uparams = self.get_uparams_ptr(&uparams);
                    let ty = self.get_expr_ptr(ty);
                    let all_ind_names = Arc::from(self.get_names(&all));
                    let all_ctor_names = Arc::from(self.get_names(&ctors));
                    let inductive = Declar::Inductive(InductiveData {
                        info: DeclarInfo { name, uparams, ty },
                        is_recursive: is_rec,
                        is_nested: num_nested > 0,
                        num_params,
                        num_indices,
                        all_ind_names,
                        all_ctor_names,
                        all_recs_name: ind_to_recs.get(&name).unwrap().clone().into(), // todo: optimize
                    });
                    declars.push((name, inductive, Some(block_size)))
                }
                for Constructor { name, uparams, ty, is_unsafe, induct, cidx, num_params, num_fields, .. } in ctor_vals
                {
                    assert!(!is_unsafe);
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, ty, uparams };
                    let parent_inductive = self.get_name_ptr(induct);
                    let ctor_idx = cidx;
                    let ctor = Declar::Constructor(ConstructorData {
                        info,
                        inductive_name: parent_inductive,
                        ctor_idx,
                        num_params,
                        num_fields,
                    });
                    declars.push((name, ctor, None));
                }
                declars.append(&mut recs);
                Ok(LeanDagInsertResult::Declars(declars))
            }
        }
    }
}

/// Decimal string -> BigUint in sub-quadratic time. `BigUint::from_str` is quadratic in the digit count,
/// which makes nat literals with millions of digits (as in large `decide`/`norm_num` proofs) take days.
/// This splits the digit string by 10^(BASE_DIGITS * 2^j) and combines with big multiplications
/// (Karatsuba/Toom-3), so cost is that of multiplication times a log factor. Same value as `from_str`.
pub(crate) fn parse_decimal_fast(s: &str) -> Result<BigUint, String> {
    use std::str::FromStr;
    const BASE_DIGITS: usize = 2048;
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err("expected a non-empty string of ASCII digits".to_string());
    }
    let s = s.trim_start_matches('0');
    if s.is_empty() {
        return Ok(BigUint::ZERO);
    }
    fn go(s: &str, pows: &mut Vec<BigUint>) -> BigUint {
        if s.len() <= 2 * BASE_DIGITS {
            return BigUint::from_str(s).expect("validated nonempty ASCII digits");
        }
        // largest j with BASE_DIGITS * 2^j < s.len()
        let mut j = 0usize;
        while BASE_DIGITS << (j + 1) < s.len() {
            j += 1;
        }
        while pows.len() <= j {
            let next = match pows.last() {
                None => num_traits::pow::pow(BigUint::from(10u8), BASE_DIGITS),
                Some(last) => last * last,
            };
            pows.push(next);
        }
        let m = BASE_DIGITS << j;
        let (hi, lo) = s.split_at(s.len() - m);
        let hi_v = go(hi, pows);
        let lo_v = go(lo, pows);
        hi_v * &pows[j] + lo_v
    }
    let mut pows: Vec<BigUint> = Vec::new();
    Ok(go(s, &mut pows))
}

#[cfg(test)]
mod parse_decimal_fast_tests {
    use super::*;
    use std::str::FromStr;
    #[test]
    fn matches_from_str() {
        let mut x: u64 = 88172645463325252;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let lens = [1usize, 2, 9, 4095, 4096, 4097, 4098, 6144, 8191, 8192, 8193, 12345, 40000, 100_000, 300_001];
        for &l in &lens {
            for trial in 0..3 {
                let mut st = String::with_capacity(l);
                for i in 0..l {
                    let d = if trial == 1 && i < l / 2 { 0 } else { (next() % 10) as u8 }; // leading zeros too
                    st.push((b'0' + d) as char);
                }
                assert_eq!(parse_decimal_fast(&st).unwrap(), BigUint::from_str(&st).unwrap(), "len {l} trial {trial}");
            }
        }
        assert_eq!(parse_decimal_fast("0").unwrap(), BigUint::from(0u8));
        let nines = "9".repeat(20000);
        assert_eq!(parse_decimal_fast(&nines).unwrap(), BigUint::from_str(&nines).unwrap());
        assert!(parse_decimal_fast("").is_err());
        assert!(parse_decimal_fast("12a").is_err());
    }
}

/// Needed because the lean4export format serializes nat literals as strings:
/// https://github.com/leanprover/lean4export/blob/ddeb0869b0b5679b0104e16291ffd929fbaa6a48/format_ndjson.md?plain=1#L186
fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where
    D: Deserializer<'de>, {
    struct BigUintStringVisitor;

    impl<'de> Visitor<'de> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E>
        where
            E: DeError, {
            parse_decimal_fast(v).map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E>
        where
            E: DeError, {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}

fn serialize_biguint_to_string<S>(i: &BigUint, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer, {
    serializer.serialize_str(i.to_string().as_str())
}

mod semver_tests {
    use super::*;
    #[allow(dead_code)]
    fn mk_meta(s: &'static str) -> FileMeta<'static> {
        FileMeta {
            lean: LeanMeta { version: Cow::Borrowed(""), githash: Cow::Borrowed("") },
            exporter: ExporterMeta { version: Cow::Borrowed(""), name: Cow::Borrowed("") },
            format: FormatMeta { version: Cow::Borrowed(s) },
        }
    }

    #[test]
    fn test_ng() {
        let too_small = ["2.9.9", "2.9.99"];
        let too_big = ["4.0.0", "4.1.0", "3.2.0", "3.2.1"];

        for v in too_small {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
        for v in too_big {
            assert!(check_semver(&mk_meta(v)).is_err())
        }
    }

    #[test]
    fn test_ok() {
        let ok = ["3.1.0", "3.1.9"];
        for v in ok {
            assert!(check_semver(&mk_meta(v)).is_ok())
        }
    }
}
