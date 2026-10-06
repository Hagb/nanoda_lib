use std::{
    collections::{hash_map::OccupiedError, HashMap, HashSet},
    hash::BuildHasherDefault,
};

use crate::{
    env::Declar::{self, *},
    name::Name,
    pair::Key::{Const, LevelParam, Primitive},
    parser::BackRef,
    tc::*,
    util::{DagMarker, ExprPtr, FxHashMap, FxHashSet, LeanDag, LevelPtr, LevelsPtr, NamePtr, TcCtx, UniqueHashMap},
};
use rustc_hash::FxHasher;
use serde;

// #[derive(Hash, PartialEq, Eq)]
// enum NameType {
//     Declar,
//     Level,
// }

pub enum Key<'t> {
    Declar(NamePtr<'t>),
    LevelParam(NamePtr<'t>),
    Primitive(NamePtr<'t>),
    // BackRef,
    Const(NamePtr<'t>),
    // End,
}

pub const PRIMITIVES: [&str; 31] = [
    "eagerReduce",
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    "String",
    "String.ofList",
    // "String.rec", //
    "Nat",
    "Nat.zero",
    "Nat.succ",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.mod",
    "Nat.div",
    "Nat.beq",
    "Nat.ble",
    "Nat.gcd",
    "Nat.xor",
    "Nat.land",
    "Nat.lor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    // "Nat.rec", //
    // "Bool",    //
    "Bool.true",
    "Bool.false",
    // "Bool.rec", //
    "Char",
    "Char.ofNat",
    // "Char.rec", //
    // "UInt32",   //
    "List",
    "List.nil",
    "List.cons",
    // "List.rec",         //
    // "sorryAx",          //
    // "propext",          //
    // "Iff",              //
    // "Iff.intro",        //
    // "Classical.choice", //
    // "Nonempty",         //
    // "Nonempty.intro",   //
    // "Eq",               //
    // "Eq.refl",//
];

// enum NameNode<'t> {
//     Str(&'t str),
//     Num(u64),
// }

// #[derive(Default)]
pub struct PrimitiveEnv<'x, 't, 'p> {
    pub primitives: Vec<Key<'t>>,
    pub declars: HashSet<NamePtr<'t>, BuildHasherDefault<FxHasher>>,
    pub tc: TypeChecker<'x, 't, 'p>,
}

impl<'x, 't, 'p> PrimitiveEnv<'x, 't, 'p> {
    fn get_primitives_from_level(&mut self, level: LevelPtr<'t>) {
        // eprintln!("get_primitives",);
        match self.tc.ctx.read_level(level) {
            crate::level::Level::Zero => (),
            crate::level::Level::Succ(ptr, _) => self.get_primitives_from_level(ptr),
            crate::level::Level::Max(ptr, ptr1, _) => {
                self.get_primitives_from_level(ptr);
                self.get_primitives_from_level(ptr1);
            }
            crate::level::Level::IMax(ptr, ptr1, _) => {
                self.get_primitives_from_level(ptr);
                self.get_primitives_from_level(ptr1);
            }
            crate::level::Level::Param(ptr, _) => self.primitives.push(Key::LevelParam(ptr)),
        }
    }

    fn get_primitives_aux(&mut self, e: ExprPtr<'t>, consts: &mut Vec<NamePtr<'t>>) {
        // eprintln!("get_primitives_aux {}", self.tc.ctx.with_pp(|x| x.pp_expr(e)));
        if let (true, type_) = self.tc.is_proof(e) {
            return self.get_primitives_aux(type_, consts);
        }
        // let e = self.tc.whnf(e);
        let (e_fun, args) = self.tc.ctx.unfold_apps(e);
        match self.tc.ctx.read_expr(e_fun) {
            crate::expr::Expr::StringLit { .. } => (),
            crate::expr::Expr::NatLit { .. } => (),
            crate::expr::Expr::Proj { ty_name, structure, .. } => {
                self.primitives.push(Key::Const(ty_name));
                // consts.push(ty_name);
                // todo!("inductive");
                consts.push(ty_name);
                self.get_primitives_aux(structure, consts);
            }
            crate::expr::Expr::Var { .. } => (),
            crate::expr::Expr::Sort { level, .. } => {
                let simplified = self.tc.ctx.simplify(level);
                self.get_primitives_from_level(simplified);
            }
            crate::expr::Expr::Const { name, .. } => {
                self.primitives.push(Key::Const(name));
                // todo!("inductive");
                consts.push(name);
                // self.get_primitives(name, false);
            }
            crate::expr::Expr::App { .. } => unreachable!(),
            crate::expr::Expr::Pi { binder_name, binder_style, binder_type, body, .. }
            | crate::expr::Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                self.get_primitives_aux(binder_type, consts);
                let fvar = self.tc.ctx.mk_dbj_level(binder_name, binder_style, binder_type);
                let insted = self.tc.ctx.inst(body, &vec![fvar]);
                self.get_primitives_aux(insted, consts)
                // todo: optimization
            }
            crate::expr::Expr::Let { binder_type, val, body, .. } => {
                // self.get_primitives_aux(binder_type, consts);
                // self.get_primitives_aux(val, consts);
                let insted = self.tc.ctx.inst(body, &vec![val]);
                self.get_primitives_aux(insted, consts);
            }
            crate::expr::Expr::Local { .. } => (),
        }
        for arg in args {
            self.get_primitives_aux(arg, consts);
        }
    }

    pub fn get_primitives(&mut self, n: NamePtr<'t>, ty_only: bool /*, levels: Option<LevelsPtr<'t>>*/) {
        if self.declars.contains(&n) {
            return ()
        }
        self.declars.insert(n);
        // eprintln!("get_primitives {}", self.tc.ctx.name_to_string(n));
        let Some(declar) = self.tc.env.get_declar(&n) else {
            panic!("no declaration of `{}`", self.tc.ctx.name_to_string(n));
            // return
        };
        self.primitives.push(if matches!(
            declar,
            Inductive { .. } | Opaque { .. } | Axiom { .. } | Constructor(..) | Recursor(..)
        ) || PRIMITIVES.contains(&self.tc.ctx.name_to_string(declar.info().name).as_str())
        {
            Key::Primitive
        } else {
            Key::Declar
        }(n));
        let mut consts: Vec<NamePtr<'t>> = vec![];
        self.get_primitives_aux(declar.info().ty, &mut consts);
        if !ty_only {
            match declar {
                Theorem { val, .. } | Definition { val, .. } => self.get_primitives_aux(*val, &mut consts),
                Inductive(inductive_data) => {
                    consts.extend(inductive_data.all_ind_names.as_ref());
                    consts.extend(inductive_data.all_ctor_names.as_ref());
                    consts.extend(inductive_data.all_recs_name.as_ref());
                    // consts.extend(inductive_data.as_ref());
                }
                Constructor(..) | Recursor(..) => (),
                _ => (),
            }
        };
        for c in consts {
            self.get_primitives(c, false);
        }
    }

    pub fn print_primitives(&self) {
        for (i, k) in self.primitives.iter().enumerate() {
            match k {
                Key::Declar(ptr) => eprintln!("{}: declar {}", i, self.tc.ctx.name_to_string(*ptr)),
                Key::LevelParam(ptr) => eprintln!("{}: level {}", i, self.tc.ctx.name_to_string(*ptr)),
                Primitive(ptr) => eprintln!("{}: primitive {}", i, self.tc.ctx.name_to_string(*ptr)),
                Key::Const(name) => eprintln!("{}: const {}", i, self.tc.ctx.name_to_string(*name)),
            }
        }
    }

    pub fn pair_primitives<'x2, 't2, 'p2>(
        &self,
        env2: &PrimitiveEnv<'x2, 't2, 'p2>,
        // n1: NamePtr<'t1>,
        // n2: NamePtr<'t2>,
    ) -> (FxHashMap<NamePtr<'t2>, NamePtr<'t>>, FxHashMap<NamePtr<'t2>, NamePtr<'t>>) {
        let mut primitives: FxHashMap<NamePtr<'t2>, NamePtr<'t>> = Default::default();
        let mut levels: FxHashMap<NamePtr<'t2>, NamePtr<'t>> = Default::default();
        let mut end = 0;
        for prim in PRIMITIVES
            .iter()
            .map(|x| *x)
            .chain(self.tc.ctx.export_file.config.permitted_axioms.clone().unwrap_or(vec![]).iter().map(|x| x.as_str()))
        {
            // todo: use cache
            // env1.dag.
            if let Some(n1) = self.tc.ctx.export_file.dag.find_name(prim) {
                if let Some(n2) = env2.tc.ctx.export_file.dag.find_name(prim) {
                    eprintln!(
                        "force axiom/declar pairing: {} -> {}",
                        env2.tc.ctx.name_to_string(n2),
                        self.tc.ctx.name_to_string(n1)
                    );
                    primitives.insert(n2, n1);
                }
            }
        }
        for u in ["u", "v", "q"] {
            if let Some(n1) = self.tc.ctx.export_file.dag.find_name(u) {
                if let Some(n2) = env2.tc.ctx.export_file.dag.find_name(u) {
                    eprintln!(
                        "early level pairing: {} -> {}",
                        env2.tc.ctx.name_to_string(n2),
                        self.tc.ctx.name_to_string(n1)
                    );
                    levels.insert(n2, n1);
                }
            }
        }
        for (i, (e1, e2)) in self.primitives.iter().zip(&env2.primitives).enumerate() {
            end = i;
            match (e1, e2) {
                (Key::Declar { .. }, Key::Declar { .. }) => (),
                (Primitive(p1), Primitive(p2)) => {
                    let Err(OccupiedError { value, .. }) = primitives.try_insert(*p2, *p1) else {
                        eprintln!("declar: {} -> {}", env2.tc.ctx.name_to_string(*p2), self.tc.ctx.name_to_string(*p1));
                        continue
                    };
                    if value != *p1 {
                        eprintln!(
                            "different paired declar names: original {} != new {}",
                            self.tc.ctx.name_to_string(value),
                            self.tc.ctx.name_to_string(*p1)
                        );
                        break;
                    }
                }
                (Const(p1), Const(p2)) => {
                    ()
                    // let Err(OccupiedError { value, .. }) = primitives.try_insert(*p2, *p1) else {
                    //     eprintln!("const: {} -> {}", env2.tc.ctx.name_to_string(*p2), self.tc.ctx.name_to_string(*p1));
                    //     continue
                    // };
                    // if value != *p1 {
                    //     eprintln!(
                    //         "different paired const names: original {} != new {}",
                    //         self.tc.ctx.name_to_string(value),
                    //         self.tc.ctx.name_to_string(*p1)
                    //     );
                    //     break;
                    // }
                }
                (LevelParam(l1), LevelParam(l2)) => {
                    let Err(OccupiedError { value, .. }) = levels.try_insert(*l2, *l1) else {
                        eprintln!("level: {} -> {}", env2.tc.ctx.name_to_string(*l2), self.tc.ctx.name_to_string(*l1));
                        continue
                    };
                    if value != *l1 {
                        eprintln!(
                            "different paired level names: original {} != new {}, while continue",
                            self.tc.ctx.name_to_string(value),
                            self.tc.ctx.name_to_string(*l1)
                        );
                        // break;
                    };
                }
                _ => {
                    eprintln!("different key");
                    break;
                }
            }
        }
        eprintln!("length 1: {}; length 2: {}; end: {}", self.primitives.len(), env2.primitives.len(), end);
        assert_eq!(FxHashSet::from_iter(primitives.iter().map(|x| *x.1)).len(), primitives.len());
        // assert_eq!(FxHashSet::from_iter(levels.iter().map(|x| *x.1)).len(), levels.len());
        (primitives, levels)
    }

    pub fn pair_with<'x2, 't2, 'p2>(
        &mut self,
        env2: &mut PrimitiveEnv<'x2, 't2, 'p2>,
        n1: NamePtr<'t>,
        n2: NamePtr<'t2>,
    ) -> (FxHashMap<u32, u32>, FxHashMap<u32, u32>) {
        for prim in PRIMITIVES
            .iter()
            .map(|x| *x)
            .chain(self.tc.ctx.export_file.config.permitted_axioms.clone().unwrap_or(vec![]).iter().map(|x| x.as_str()))
        {
            // todo: use cache
            if let Some(n1) = self.tc.ctx.export_file.dag.find_name(prim) {
                if let Some(n2) = env2.tc.ctx.export_file.dag.find_name(prim) {
                    if self.tc.env.get_declar(&n1).is_some() && env2.tc.env.get_declar(&n2).is_some() {
                        eprintln!(
                            "early get axiom/primitive declar: {} -> {}",
                            env2.tc.ctx.name_to_string(n2),
                            self.tc.ctx.name_to_string(n1)
                        );
                        self.get_primitives(n1, false);
                        env2.get_primitives(n2, false);
                    }
                }
            }
        }
        self.get_primitives(n1, true);
        env2.get_primitives(n2, true);
        let (primitives, levels) = self.pair_primitives(env2);
        fn name_to_id<'x_, 't_, 'p_>(name: NamePtr<'t_>) -> u32 {
            // let name_ = env.tc.ctx.read_name(name);
            // match name.dag_marker() {
            //     DagMarker::ExportFile => &env.tc.ctx.export_file.dag.names,
            //     DagMarker::TcCtx => &env.tc.ctx.dag.names,
            // }.
            // env.tc.ctx.export_file.dag.names.get_index_of(&name_).unwrap().try_into().unwrap()
            assert_eq!(name.dag_marker(), DagMarker::ExportFile);
            name.idx().try_into().unwrap()
        }
        (
            primitives.into_iter().map(|(x, y)| (name_to_id(x), name_to_id(y))).collect(),
            levels.into_iter().map(|(x, y)| (name_to_id(x), name_to_id(y))).collect(),
        )

        // let n1 = self.tc.ctx.read_name(self.tc.ctx.dag.find_name(n).unwrap());
        // let n2 = env2.tc.ctx.read_name(env2.tc.ctx.dag.find_name(n).unwrap());
        // let n1_index = self.tc.ctx.dag.names.get_index_of(&n1);
        // let n2_index = env2.tc.ctx.dag.names.get_index_of(&n2);
    }
}

// impl<'t, 'p> TcCtx<'t, 'p> {
//     pub fn name_to_vec(self, name: NamePtr<'t>) -> Vec<NameNode> {
//         let mut name = self.read_name(name);
//         let mut name_: Vec<NameNode> = vec![];
//         while name != Name::Anon {
//             name_.push(match name {
//                 crate::name::Name::Anon => unreachable!(),
//                 crate::name::Name::Str(ptr, ptr1, _) => {
//                     name = self.read_name(ptr);
//                     NameNode::Str(self.read_string(ptr1))
//                 }
//                 crate::name::Name::Num(ptr, num, _) => {
//                     name = self.read_name(ptr);
//                     NameNode::Num(num)
//                 }
//             })
//         }
//         name_.reverse();
//         name_
//     }
// }
