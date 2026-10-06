#![feature(map_try_insert)]

use nanoda_lib::env::EnvLimit;
use nanoda_lib::expr::Expr;
use nanoda_lib::pair::Key::Const;
use nanoda_lib::pair::PrimitiveEnv;
use nanoda_lib::parser::{
    BackRef, Constructor, ExportJsonObject, ExportJsonVal, IndInfo, LeanDagInsertResult, Recursor, RecursorRule,
};
use nanoda_lib::tc::TypeChecker;
use nanoda_lib::util::{Config, ExportFile, LeanDag, TcCtx};
use rand::RngExt;
use rustc_hash::FxHashMap;
use std::assert_matches;
use std::borrow::Cow;
use std::collections::HashSet;
use std::error::Error;
use std::fs::OpenOptions;
use std::path::Path;

fn main() -> Result<(), MainError> {
    let mut args = std::env::args();
    let _ = args.next();
    let out = match args.next().as_ref() {
        None => Err(Box::from("This program expects a path to a configuration file.".to_string())),
        Some(p) if p == "-h" || p == "--help" => return Ok(println!("{}", HELP_LONG)),
        Some(p) => use_config(&Path::new(p)),
    }
    .map_err(|e| MainError(e))?;

    if let Some(msg) = out {
        println!("{}", msg);
    }
    Ok(())
}

// Returns an optional success message.
fn use_config<'c>(config_path: &'c Path) -> Result<Option<String>, Box<dyn Error>> {
    let cfg = Config::try_from(config_path)?;
    // Make sure the target pretty printer destination is accessible before doing any real work.
    let mut pp_destination = cfg.get_pp_destination()?;
    let (mut export_file, skipped_axioms, mut objs) = cfg.clone().to_export_file()?;
    // Check the environment
    export_file.check_all_declars();

    if let Ok((mut paired_export_file, _, mut pair_objs)) = cfg.clone().to_paired_export_file() {
        paired_export_file.check_all_declars();

        let mut insert_obj = |export_file: &mut ExportFile, objs: &mut Vec<_>, obj: ExportJsonVal<'c>| {
            let ret = match export_file.dag.go1(obj.clone(), Some(&cfg)).unwrap() {
                LeanDagInsertResult::Id((idx_, inserted)) => (Some(idx_), inserted),
                LeanDagInsertResult::Declars(declars) => {
                    let declar_size = export_file.declars.len();
                    for (name, declar, mutual_block_size) in declars {
                        assert!(export_file.declars.insert(name, declar).is_none(), "duplicated {}", export_file.with_ctx(|x| x.name_to_string(name)));
                        if let Some(mutual_block_size) = mutual_block_size {
                            export_file.mutual_block_sizes.insert(name, (declar_size, mutual_block_size));
                        }
                    }
                    (None, true)
                }
                LeanDagInsertResult::Skip(..) => (None, false), /*self.skipped.push(name)*/
                LeanDagInsertResult::None => (None, false),
            };
            if ret.1 {
                objs.push(ExportJsonObject { val: obj, i: ret.0.clone() })
            }
            ret
        };
        // let ((Some(BackRef::In(u_id)), _), (Some(BackRef::In(v_id)), _)) = (
        let mut l_map: FxHashMap<u32, u32> = ["u", "v", "q"]
            .map(|u| {
                let (Some(BackRef::In(n1)), _) =
                    insert_obj(&mut export_file, &mut objs, ExportJsonVal::NameStr { pre: 0, str: u.into() })
                else {
                    panic!()
                };
                let (Some(BackRef::In(n2)), _) = insert_obj(
                    &mut paired_export_file,
                    &mut pair_objs,
                    ExportJsonVal::NameStr { pre: 0, str: u.into() },
                ) else {
                    panic!()
                };
                (n2, n1)
            })
            .into_iter()
            .collect();

        // ) else {
        //     panic!()
        // };
        let mut dag1 = LeanDag::new(&cfg);
        let mut ctx1 = TcCtx::new(&export_file, &mut dag1);
        let declar1 = export_file.declars.last().unwrap();
        let env1 = export_file.new_env(EnvLimit::PpUnlimited);
        let tc1 = TypeChecker::new(&mut ctx1, &env1, Some(*declar1.1.info()));

        let mut dag2 = LeanDag::new(&cfg);
        let mut ctx2 = TcCtx::new(&paired_export_file, &mut dag2);
        let declar2 = paired_export_file.declars.last().unwrap();
        let env2 = paired_export_file.new_env(EnvLimit::PpUnlimited);
        let tc2 = TypeChecker::new(&mut ctx2, &env2, Some(*declar2.1.info()));

        let mut env1_ = PrimitiveEnv { primitives: vec![], declars: HashSet::from_iter([]), tc: tc1 };
        let mut env2_ = PrimitiveEnv { primitives: vec![], declars: HashSet::from_iter([]), tc: tc2 };
        eprintln!("pair {} {}", env1_.tc.ctx.name_to_string(*declar1.0), env2_.tc.ctx.name_to_string(*declar2.0));
        let (p_pairs, _) = env1_.pair_with(&mut env2_, *declar1.0, *declar2.0);
        use nanoda_lib::util::TcCtx;
        // let level_base: u32 = export_file.dag.levels.len().try_into().unwrap();
        let mut ids_map: FxHashMap<BackRef, u32> = FxHashMap::default();

        let prefix = loop {
            let rng: u32 = rand::rng().random();
            let prefix = format!("transformed_{}", rng);
            if export_file.dag.find_name(prefix.as_str()).is_none() {
                break prefix
            }
            // todo!("add to Dag");
        };
        if (true) {
            // todo!("add axioms and level params if needed");
        }
        let name_base: u32 = export_file.dag.names.len().try_into().unwrap();
        assert_eq!(
            insert_obj(&mut export_file, &mut objs, ExportJsonVal::NameStr { pre: 0, str: prefix.clone().into() }),
            (Some(BackRef::In(name_base)), true),
        );
        // objs.insert_full(todo!());
        // let mut declars_map: FxHashMap<usize, usize> = FxHashMap::default();
        // let mut exprs_map: FxHashMap<u32, u32> = FxHashMap::default();
        // let mut levels_map: FxHashMap<u32, u32> = FxHashMap::default();
        let map_name_when_defining_name = |ids_map: &FxHashMap<BackRef, u32>, old_id: u32| {
            if old_id == 0 {
                name_base
            } else {
                // todo!("map primitives' names");
                // *ids_map.get(&BackRef::In(old_id)).unwrap()
                old_id.strict_add(name_base)
            }
        };
        let map_declar_name = |ids_map: &FxHashMap<BackRef, u32>, old_id: u32| {
            if old_id == 0 {
                name_base
            } else {
                // todo!("map primitives' names");
                p_pairs.get(&old_id).map(|x| *x).unwrap_or_else(
                    // || *ids_map.get(&BackRef::In(old_id)).unwrap()
                    || old_id.strict_add(name_base),
                )
            }
        };
        let map_level_name = |ids_map: &FxHashMap<BackRef, u32>, old_id: u32| {
            // todo!("map level params used by primitives");
            if old_id == 0 {
                name_base
            } else {
                // l_pairs.get(&old_id).map(|x| *x).unwrap_or_else(||
                l_map.get(&old_id).map(|x| *x).unwrap_or_else(|| old_id.strict_add(name_base))
                // )
            }
        };
        let map_level = |ids_map: &FxHashMap<BackRef, u32>, old_id: u32| {
            if old_id == 0 {
                0
            } else {
                // *l_pairs.get(&old_id).or_else(|| ids_map.get(&BackRef::Il(old_id))).unwrap()
                *ids_map.get(&BackRef::Il(old_id)).unwrap()
            }
        };
        let map_expr = |ids_map: &FxHashMap<BackRef, u32>, old_id: u32| *ids_map.get(&BackRef::Ie(old_id)).unwrap();

        // let name_base: u32 = name_base.strict_add(1).try_into().unwrap();

        // let insert_with_idx
        // let insert_name =
        //     |name: ExportJsonVal, i: BackRef, env1_: &mut PrimitiveEnv, ids_map: &mut FxHashMap<BackRef, u32>| {
        //         assert_matches!(i, BackRef::In(..));
        //         let Ok(LeanDagInsertResult::Id((BackRef::In(idx), true))) = env1_.tc.ctx.dag.go1(name, Some(&cfg))
        //         else {
        //             panic!()
        //         };
        //         assert!(ids_map.insert(i, idx).is_none());
        //     };

        // let insert_expr =
        //     |name: ExportJsonVal, i: BackRef, env1_: &mut PrimitiveEnv, ids_map: &mut FxHashMap<BackRef, u32>| {
        //         assert_matches!(i, BackRef::Ie(..));
        //         let Ok(LeanDagInsertResult::Id((BackRef::Ie(idx), _))) = env1_.tc.ctx.dag.go1(name, Some(&cfg)) else {
        //             panic!()
        //         };
        //         assert!(ids_map.insert(i, idx).is_none());
        //     };

        // let insert_level =
        //     |name: ExportJsonVal, i: BackRef, env1_: &mut PrimitiveEnv, ids_map: &mut FxHashMap<BackRef, u32>| {
        //         assert_matches!(i, BackRef::Il(..));
        //         let Ok(LeanDagInsertResult::Id((BackRef::Il(idx), _))) = env1_.tc.ctx.dag.go1(name, Some(&cfg)) else {
        //             panic!()
        //         };
        //         assert!(ids_map.insert(i, idx).is_none());
        //     };
        // let insert_expr = |name: ExportJsonVal, i:BackRef, ids_map: &mut
        // let add_level = |v : ExportJsonVal| env1_.tc.ctx.dag.levels.cont;
        for ExportJsonObject { val, i: idx } in pair_objs.into_iter() {
            use nanoda_lib::parser::ExportJsonVal::*;
            let new_obj: Option<ExportJsonVal> = match val.clone() {
                Metadata(..) => None,
                NameStr { pre, str } => Some(NameStr { pre: map_name_when_defining_name(&ids_map, pre), str }),
                NameNum { pre, i } => Some(NameNum { pre: map_name_when_defining_name(&ids_map, pre), i }),
                LevelSucc(n) => Some(LevelSucc(map_level(&ids_map, n))),
                LevelMax(n) => Some(LevelMax(n.map(|x| map_level(&ids_map, x)))),
                LevelIMax(n) => Some(LevelIMax(n.map(|x| map_level(&ids_map, x)))),
                LevelParam(v) => Some(LevelParam(map_level_name(&ids_map, v))),
                e @ (NatLit(..) | StrLit(..) | ExprBVar(..)) => Some(e),
                ExprMData { .. } => panic!("MData is not supported"),
                ExprLet { name, ty, value, body, nondep } => Some(ExprLet {
                    name: map_declar_name(&ids_map, name),
                    ty: map_expr(&ids_map, ty),
                    value: map_expr(&ids_map, value),
                    body: map_expr(&ids_map, body),
                    nondep,
                }),
                ExprConst { name, levels } => Some(ExprConst {
                    name: map_declar_name(&ids_map, name),
                    levels: levels.iter().map(|x| map_level(&ids_map, *x)).collect(),
                }),
                ExprApp { fun, arg } => Some(ExprApp { fun: map_expr(&ids_map, fun), arg: map_expr(&ids_map, arg) }),
                ExprPi { binder_name, binder_type, body, binder_info } => Some(ExprPi {
                    binder_name: map_declar_name(&ids_map, binder_name),
                    binder_type: map_expr(&ids_map, binder_type),
                    body: map_expr(&ids_map, body),
                    binder_info,
                }),
                ExprLambda { binder_name, binder_type, body, binder_info } => Some(ExprLambda {
                    binder_name: map_declar_name(&ids_map, binder_name),
                    binder_type: map_expr(&ids_map, binder_type),
                    body: map_expr(&ids_map, body),
                    binder_info,
                }),
                ExprProj { type_name, idx, structure } => Some(ExprProj {
                    type_name: map_declar_name(&ids_map, type_name),
                    idx,
                    structure: map_expr(&ids_map, structure),
                }),
                ExprSort(l) => Some(ExprSort(map_level(&ids_map, l))),
                Axiom { name, uparams, ty, is_unsafe } =>
                    if p_pairs.contains_key(&name) {
                        None
                    } else {
                        Some(Axiom {
                            name: map_declar_name(&ids_map, name),
                            uparams: uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                            ty: map_expr(&ids_map, ty),
                            is_unsafe,
                        })
                    },
                Thm { name, uparams, ty, value } =>
                    if p_pairs.contains_key(&name) {
                        // panic!()
                        None
                    } else {
                        Some(Thm {
                            name: map_declar_name(&ids_map, name),
                            uparams: uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                            ty: map_expr(&ids_map, ty),
                            value: map_expr(&ids_map, value),
                        })
                    },
                Defn { name, uparams, ty, value, hint, safety } =>
                    if p_pairs.contains_key(&name) {
                        // panic!()
                        None
                    } else {
                        Some(Defn {
                            name: map_declar_name(&ids_map, name),
                            uparams: uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                            ty: map_expr(&ids_map, ty),
                            value: map_expr(&ids_map, value),
                            hint,
                            safety,
                        })
                    },
                Opaque { name, uparams, ty, value, is_unsafe } =>
                    if p_pairs.contains_key(&name) {
                        None
                    } else {
                        Some(Opaque {
                            name: map_declar_name(&ids_map, name),
                            uparams: uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                            ty: map_expr(&ids_map, ty),
                            value: map_expr(&ids_map, value),
                            is_unsafe,
                        })
                    },
                Quot { name, uparams, ty, kind } =>
                    if p_pairs.contains_key(&name) {
                        None
                    } else {
                        Some(Quot {
                            name: map_declar_name(&ids_map, name),
                            uparams: uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                            ty: map_expr(&ids_map, ty),
                            kind,
                        })
                    },
                Inductive { ind_vals, ctor_vals, rec_vals } =>
                    if p_pairs.contains_key(&ind_vals[0].name) {
                        None
                    } else {
                        Some(Inductive {
                            ind_vals: ind_vals
                                .iter()
                                .map(|x| IndInfo {
                                    name: map_declar_name(&ids_map, x.name),
                                    uparams: x.uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                                    ty: map_expr(&ids_map, x.ty),
                                    all: x.all.iter().map(|x| map_declar_name(&ids_map, *x)).collect(),
                                    ctors: x.ctors.iter().map(|x| map_declar_name(&ids_map, *x)).collect(),
                                    is_rec: x.is_rec,
                                    is_reflexive: x.is_reflexive,
                                    num_indices: x.num_indices,
                                    num_nested: x.num_nested,
                                    num_params: x.num_params,
                                    is_unsafe: x.is_unsafe,
                                })
                                .collect(),
                            ctor_vals: ctor_vals
                                .iter()
                                .map(|x| Constructor {
                                    name: map_declar_name(&ids_map, x.name),
                                    uparams: x.uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                                    ty: map_expr(&ids_map, x.ty),
                                    is_unsafe: x.is_unsafe,
                                    cidx: x.cidx,
                                    num_params: x.num_params,
                                    num_fields: x.num_fields,
                                    induct: map_declar_name(&ids_map, x.induct),
                                })
                                .collect(),
                            rec_vals: rec_vals
                                .iter()
                                .map(|x| Recursor {
                                    name: map_declar_name(&ids_map, x.name),
                                    uparams: x.uparams.iter().map(|x| map_level_name(&ids_map, *x)).collect(),
                                    ty: map_expr(&ids_map, x.ty),
                                    is_unsafe: x.is_unsafe,
                                    num_params: x.num_params,
                                    num_indices: x.num_indices,
                                    num_motives: x.num_motives,
                                    num_minors: x.num_minors,
                                    rules: x
                                        .rules
                                        .iter()
                                        .map(|x| RecursorRule {
                                            ctor: map_declar_name(&ids_map, x.ctor),
                                            nfields: x.nfields,
                                            rhs: map_expr(&ids_map, x.rhs),
                                        })
                                        .collect(),
                                    all: x.all.iter().map(|x| map_declar_name(&ids_map, *x)).collect(),
                                    k: x.k,
                                })
                                .collect(),
                        })
                    },
            };
            if let Some(new_obj) = new_obj {
                match insert_obj(&mut export_file, &mut objs, new_obj.clone()) {
                    (None, _) => (),
                    (Some(BackRef::In(new_idx)), inserted) => {
                        // paired_export_file.with_ctx(|x| x.dag.find_name());
                        assert!(
                            inserted,
                            "{}, {}",
                            serde_json::to_string(&val).unwrap(),
                            serde_json::to_string(&new_obj).unwrap()
                        );
                        assert_eq!(new_idx, idx.unwrap().id() + name_base);
                    }
                    (Some(new_idx), _) => {
                        ids_map.insert(idx.unwrap(), new_idx.id());
                    }
                }
            }
        }
        export_file.post_process();
        export_file.check_all_declars();
        for obj in objs {
            println!("{}", serde_json::to_string(&obj).unwrap());
        }
        // for declar in export_file.declars.values() {
        //     let name = export_file.with_ctx(|c| c.name_to_string(declar.info().name));
        //     if name.starts_with(&prefix) {
        //         eprintln!("check {}", name);
        //         eprintln!(
        //             "{}",
        //             export_file
        //                 .with_ctx(|c| c.with_pp(|pp| pp.pp_declar(declar.info().name)).unwrap_or("".to_string()))
        //         );
        //     }
        //     export_file.check_declar(declar);
        // }
    }

    // Pretty print as necessary
    let pp_errs = export_file.pp_selected_declars(pp_destination.as_mut());
    if export_file.config.print_success_message {
        if pp_errs.is_empty() {
            if skipped_axioms.is_empty() {
                Ok(Some(format!("Checked {} declarations with no errors", export_file.declars.len())))
            } else {
                Ok(Some(format!(
                    "Checked {} declarations with no errors, skipping exported but unpermitted axioms {:?}",
                    export_file.declars.len(),
                    skipped_axioms
                )))
            }
        } else {
            Ok(Some(format!(
                "Checked {} declarations with no typechecker errors, {} pretty printer errors: {:#?}",
                export_file.declars.len(),
                pp_errs.len(),
                pp_errs
            )))
        }
    } else if skipped_axioms.is_empty() {
        Ok(None)
    } else {
        Ok(Some(format!("Skipped exported but unpermitted axioms {:?}", skipped_axioms)))
    }
}

struct MainError(Box<dyn Error>);

impl std::fmt::Debug for MainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}\n\n{}", self.0, HELP_SHORT) }
}

const HELP_SHORT: &str = "run with `-h` or `--help` for help";
const HELP_LONG: &str = concat!(
    "nanoda_bin",
    " ",
    env!("CARGO_PKG_VERSION"),
    "\n\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n\n",
    "get more help at ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n\n",
    include_str!("../README.md")
);
