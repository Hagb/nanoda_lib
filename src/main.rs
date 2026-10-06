#![feature(map_try_insert)]

use nanoda_lib::env::{EnvLimit, ReducibilityHint};
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::pair::Key::Const;
use nanoda_lib::pair::{PrimitiveEnv, PRIMITIVES};
use nanoda_lib::parser::{
    parse_export_file, BackRef, Constructor, DefinitionSafety, ExportJsonObject, ExportJsonVal, IndInfo,
    LeanDagInsertResult, Recursor, RecursorRule,
};
use nanoda_lib::tc::TypeChecker;
use nanoda_lib::util::{Config, ExportFile, LeanDag, TcCtx};
use rand::RngExt;
use rustc_hash::{FxHashMap, FxHashSet};
use std::borrow::Cow;
use std::collections::HashSet;
use std::error::Error;
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::{assert_matches, cmp};

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
    let mut buf: Box<dyn BufRead> = if cfg.use_stdin {
        Box::new(BufReader::new(std::io::stdin()))
    } else if let Some(pathbuf) = cfg.export_file_path.as_ref() {
        Box::new(BufReader::new(OpenOptions::new().read(true).truncate(false).open(pathbuf).unwrap()))
    } else {
        panic!("Configuration file must specify en export file path or \"use_stdin\": true")
    };
    let (mut export_file, skipped_axioms, mut objs) = parse_export_file(&mut buf, cfg.clone())?;
    // Check the environment
    export_file.check_all_declars();

    'paired: {
        let buf: Option<Box<dyn BufRead>> = if cfg.use_stdin {
            Some(buf)
        } else if let Some(pathbuf) = cfg.paired_export_file_path.as_ref() {
            Some(Box::new(BufReader::new(OpenOptions::new().read(true).truncate(false).open(pathbuf).unwrap())))
        } else {
            None
        };
        let Some(mut buf) = buf else { break 'paired };
        let (mut paired_export_file, _, mut pair_objs) = parse_export_file(&mut buf, cfg.clone())?;
        if (cfg.use_stdin && pair_objs.len() == 0) {
            break 'paired;
        }
        paired_export_file.check_all_declars();
        fn name_from_str(s: &str) -> Vec<String> { s.split(".").map(|x| x.to_string()).collect() }

        let mut insert_obj = |export_file: &mut ExportFile, objs: &mut Vec<_>, obj: ExportJsonVal<'c>| {
            let ret = match export_file.dag.go1(obj.clone(), Some(&cfg)).unwrap() {
                LeanDagInsertResult::Id((idx_, inserted)) => (Some(idx_), inserted),
                LeanDagInsertResult::Declars(declars) => {
                    let declar_size = export_file.declars.len();
                    for (name, declar, mutual_block_size) in declars {
                        assert!(
                            export_file.declars.insert(name, declar).is_none(),
                            "duplicated {}",
                            export_file.with_ctx(|x| x.name_to_string(name))
                        );
                        if let Some(mutual_block_size) = mutual_block_size {
                            export_file.mutual_block_sizes.insert(name, (declar_size, mutual_block_size));
                        }
                    }
                    (None, true)
                }
                LeanDagInsertResult::Skip(..) => (None, false), /*self.skipped.push(name)*/
                LeanDagInsertResult::Metadata => (None, false),
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
        for prim in PRIMITIVES // todo: clean up
            .iter()
            .map(|x| *x)
            .chain(export_file.config.permitted_axioms.clone().unwrap_or(vec![]).iter().map(|x| x.as_str()))
        {
            for d in [(&mut export_file, &mut objs), (&mut paired_export_file, &mut pair_objs)] {
                let mut pre = 0;
                for s in name_from_str(prim) {
                    let (Some(BackRef::In(idx)), _) =
                        insert_obj(d.0, d.1, ExportJsonVal::NameStr { pre, str: s.into() })
                    else {
                        panic!()
                    };
                    pre = idx;
                    // eprintln!("{}", d.0.with_ctx(|x| x.name_to_string(x.export_file.dag.get_name_ptr(idx))))
                }
            }
        }

        // ) else {
        //     panic!()
        // };
        let mut dag1 = LeanDag::new(&cfg);
        let mut ctx1 = TcCtx::new(&export_file, &mut dag1);
        let last1_declar = export_file.declars.last().unwrap().1;
        let declar1 = if let Some((i, last1_skipped)) = skipped_axioms.last() {
            // eprintln!("skip {}", export_file.with_ctx(|c| c.name_to_string(last1_skipped.info().name)));
            if TryInto::<usize>::try_into(*i).unwrap() < export_file.declars.len() {
                last1_declar
            } else {
                last1_skipped
            }
        } else {
            last1_declar
        };
        let env1 = export_file.new_env(EnvLimit::PpUnlimited);
        let tc1 = TypeChecker::new(&mut ctx1, &env1, None);

        let mut dag2 = LeanDag::new(&cfg);
        let mut ctx2 = TcCtx::new(&paired_export_file, &mut dag2);
        let declar2 = paired_export_file.declars.last().unwrap();
        let env2 = paired_export_file.new_env(EnvLimit::PpUnlimited);
        let tc2 = TypeChecker::new(&mut ctx2, &env2, None);

        let mut env1_ = PrimitiveEnv { primitives: vec![], declars: HashSet::from_iter([]), tc: tc1 };
        let mut env2_ = PrimitiveEnv { primitives: vec![], declars: HashSet::from_iter([]), tc: tc2 };
        eprintln!(
            "pair {} {}",
            env1_.tc.ctx.name_to_string(declar1.info().name),
            env2_.tc.ctx.name_to_string(*declar2.0)
        );
        let (last1, last2) = (declar1.clone(), (declar2.0.clone(), declar2.1.clone()));
        let (p_pairs, l_pair) = env1_.pair_with(&mut env2_, declar1.info().ty, declar2.1.info().ty);
        use nanoda_lib::util::TcCtx;
        // let level_base: u32 = export_file.dag.levels.len().try_into().unwrap();
        let mut ids_map: FxHashMap<BackRef, u32> = FxHashMap::default();

        let (prefix, verify_prefix) = loop {
            let rng: u32 = rand::rng().random();
            let prefix = format!("transformed_{}", rng);
            let verify_prefix = format!("verify_{}", rng);
            if export_file.dag.find_name(prefix.as_str()).is_none()
                && export_file.dag.find_name(verify_prefix.as_str()).is_none()
            {
                break (prefix, verify_prefix)
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
                    if p_pairs
                        .get(&name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                    if p_pairs
                        .get(&name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                    if p_pairs
                        .get(&name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                    if p_pairs
                        .get(&name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                    if p_pairs
                        .get(&name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                    if p_pairs
                        .get(&ind_vals[0].name)
                        .map_or(false, |x| export_file.declars.contains_key(&export_file.dag.get_name_ptr(*x)))
                    {
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
                        ids_map.insert(idx.unwrap(), new_idx.id()).map(|x| assert_eq!(x, new_idx.id()));
                    }
                }
            }
        }
        // let a = last1.0;
        // let aa = paired_export_file.declars.last().unwrap();
        let (Some(BackRef::In(verify_nidx)), true) = insert_obj(
            &mut export_file,
            &mut objs,
            ExportJsonVal::NameStr { pre: 0, str: verify_prefix.clone().into() },
        ) else {
            panic!()
        };
        fn level_to_param(l: &Level) -> u32 {
            match l {
                Level::Param(i, _) => i.idx().try_into().unwrap(),
                _ => panic!(),
            }
        }
        let uparams1: Vec<u32> = export_file
            .dag
            .uparams
            .get_index(last1.info().uparams.idx())
            .unwrap()
            .iter()
            .map(|x| level_to_param(export_file.dag.levels.get_index(x.idx()).unwrap()).try_into().unwrap())
            .collect();
        let uparams2: Vec<Option<u32>> = paired_export_file
            .dag
            .uparams
            .get_index((last2.1.info().uparams.idx()))
            .unwrap()
            .iter()
            .map(|x| level_to_param(paired_export_file.dag.levels.get_index(x.idx()).unwrap()).try_into().unwrap())
            .map(|x: u32| l_pair.get(&x).map_or(None, |x| if uparams1.contains(x) { Some(*x) } else { None }))
            .collect();
        // eprintln!(
        // "param1 {:?} of {}, param2 {:?} of {}",
        //     uparams1,
        //     export_file.with_ctx(|x| x.name_to_string(last1.info().name)),
        //     uparams2,
        //     paired_export_file.with_ctx(|x| x.name_to_string(last2.1.info().name))
        // );
        let uparams_idx = export_file.dag.get_uparams_ptr_with_default_zero(uparams2.as_slice()).idx();
        let uparams2: Vec<u32> = export_file
            .dag
            .uparams
            .get_index(uparams_idx)
            .unwrap()
            .iter()
            .map(|x| x.idx().try_into().unwrap())
            .collect();
        let (Some(BackRef::Ie(const_idx)), _) = insert_obj(
            &mut export_file,
            &mut objs,
            ExportJsonVal::ExprConst {
                name: map_declar_name(&ids_map, last2.0.idx().try_into().unwrap()),
                levels: uparams2,
            },
        ) else {
            panic!()
        };
        let (None, _) = insert_obj(
            &mut export_file,
            &mut objs,
            ExportJsonVal::Defn {
                name: verify_nidx,
                uparams: uparams1,
                ty: last1.info().ty.idx().try_into().unwrap(),
                value: const_idx,
                hint: ReducibilityHint::Abbrev,
                safety: DefinitionSafety::Safe,
            },
        ) else {
            panic!()
        };
        export_file.post_process();
        export_file.check_all_declars();
        // for declar in export_file.declars.values() {
        //     let name = export_file.with_ctx(|c| c.name_to_string(declar.info().name));
        // if name.starts_with(&prefix) || name.starts_with(&verify_prefix) {
        //     // eprintln!("check {}", name);
        //     // eprintln!(
        //     //     "{}",
        //     //     export_file
        //     //         .with_ctx(|c| c.with_pp(|pp| pp.pp_declar(declar.info().name)).unwrap_or("".to_string()))
        //     // );
        // }
        //     export_file.check_declar(declar);
        // }
        for obj in objs {
            println!("{}", serde_json::to_string(&obj).unwrap());
        }
        eprintln!(
            "`{}` is adapted to prove `{}` in `{}`",
            paired_export_file.with_ctx(|x| x.name_to_string(last2.1.info().name)),
            export_file.with_ctx(|x| x.name_to_string(last1.info().name)),
            export_file.with_ctx(|x| x.name_to_string(x.export_file.dag.get_name_ptr(verify_nidx)))
        );
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
