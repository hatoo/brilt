use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use bril_rs::{Code, EffectOps, Instruction, Literal, ValueOps};

use crate::{annotation::Annotation, restructure::StructureAnalysis};

#[derive(Debug, Clone)]
pub enum Expr {
    // RVSDG
    Arg(usize),
    State,
    // EffectOps
    Print(Box<Expr>, Box<Expr>),
    Ret(Option<Box<Expr>>, Box<Expr>),
    Call(String, Vec<Expr>, Box<Expr>),
    // ConstOps
    ConstInt(i64),
    ConstBool(bool),
    // ValueOps
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum Rvsdg {
    Simple {
        outputs: Vec<Expr>,
        state: Expr,
    },
    Linear(Vec<Rvsdg>),
    // Gamma node
    Branch {
        cond_index: usize,
        branches: Vec<Rvsdg>,
    },
    // Theta node
    Loop {
        body: Box<Rvsdg>,
        cond_index: usize,
        outputs: Vec<usize>,
    },
}

fn to_rvsdg_block(codes: Vec<Code>, args: HashMap<String, usize>, outputs: &[String]) -> Rvsdg {
    let mut vars = args
        .into_iter()
        .map(|(k, v)| (k, Expr::Arg(v)))
        .collect::<HashMap<_, _>>();
    let mut state = Expr::State;

    for code in codes {
        match code {
            Code::Instruction(instr) => match instr {
                Instruction::Constant { dest, value, .. } => match value {
                    Literal::Int(i) => {
                        vars.insert(dest, Expr::ConstInt(i));
                    }
                    Literal::Bool(b) => {
                        vars.insert(dest, Expr::ConstBool(b));
                    }
                },
                Instruction::Value { args, dest, op, .. } => {
                    let args = args
                        .into_iter()
                        .map(|arg| vars.get(&arg).unwrap())
                        .collect::<Vec<_>>();

                    let expr = match op {
                        ValueOps::Add => {
                            Expr::Add(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Sub => {
                            Expr::Sub(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Mul => {
                            Expr::Mul(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Div => {
                            Expr::Div(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Eq => {
                            Expr::Eq(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Lt => {
                            Expr::Lt(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Gt => {
                            Expr::Gt(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Le => {
                            Expr::Le(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Ge => {
                            Expr::Ge(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Not => Expr::Not(Box::new(args[0].clone())),
                        ValueOps::And => {
                            Expr::And(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Or => {
                            Expr::Or(Box::new(args[0].clone()), Box::new(args[1].clone()))
                        }
                        ValueOps::Id => args[0].clone(),
                        ValueOps::Call => todo!(),
                    };

                    vars.insert(dest, expr);
                }
                Instruction::Effect {
                    args, op, funcs, ..
                } => {
                    let args = args
                        .into_iter()
                        .map(|arg| vars.get(&arg).unwrap())
                        .collect::<Vec<_>>();
                    match op {
                        EffectOps::Nop => {}
                        EffectOps::Print => {
                            state = Expr::Print(Box::new(args[0].clone()), Box::new(state));
                        }
                        EffectOps::Return => {
                            state = Expr::Ret(
                                args.get(0).map(|&e| e.clone()).map(Box::new),
                                Box::new(state),
                            );
                        }
                        EffectOps::Call => {
                            state = Expr::Call(
                                funcs[0].clone(),
                                args.into_iter().cloned().collect(),
                                Box::new(state),
                            );
                        }
                        _ => unreachable!(),
                    }
                }
            },
            _ => unreachable!(),
        }
    }

    Rvsdg::Simple {
        outputs: outputs
            .iter()
            .map(|var| vars.remove(var).unwrap())
            .collect(),
        state,
    }
}

pub fn to_rvsdg(
    demand: Annotation<HashSet<String>>,
    args: HashMap<String, usize>,
    outputs: &[String],
) -> Rvsdg {
    match demand {
        Annotation::Block(codes, _) => to_rvsdg_block(codes, args, outputs),
        Annotation::Branch(cond_var, branches, _) => {
            let branches = branches
                .into_iter()
                .map(|a| to_rvsdg(a, args.clone(), outputs))
                .collect::<Vec<_>>();

            Rvsdg::Branch {
                cond_index: args.get(&cond_var).copied().unwrap(),
                branches,
            }
        }
        Annotation::Loop(body, _) => {
            // ARGS: loop-var, loop-cond-var, outputs

            let mut v = args.iter().collect::<Vec<_>>();
            v.sort_by_key(|(_, i)| *i);

            let mut new_outputs = v.into_iter().map(|(v, _)| v).cloned().collect::<Vec<_>>();
            let mut output_indices = Vec::new();

            let cond_index = output_indices.len();
            new_outputs.push(StructureAnalysis::VAR_R.to_string());
            output_indices.push(cond_index);

            for v in outputs {
                if let Some(i) = args.get(v) {
                    output_indices.push(*i);
                } else {
                    output_indices.push(new_outputs.len());
                    new_outputs.push(v.clone());
                }
            }

            Rvsdg::Loop {
                body: Box::new(to_rvsdg(*body, args, outputs)),
                cond_index,
                outputs: output_indices,
            }
        }

        Annotation::Linear(v, _) => {
            let mut args = args;
            let mut out = Vec::new();
            for i in 0..v.len() {
                let outputs = v
                    .get(i + 1)
                    .map(|a| Cow::Owned(a.annotation().iter().cloned().collect::<Vec<_>>()))
                    .unwrap_or(Cow::Borrowed(outputs));

                out.push(to_rvsdg(v[i].clone(), args, &outputs));

                args = outputs
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (v.clone(), i))
                    .collect::<HashMap<_, _>>();
            }

            Rvsdg::Linear(out)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        annotation::{demand_set_annotation, read_write_annotation},
        cfg::Cfg,
        test::*,
    };
    use glob::glob;
    use std::io::Cursor;

    #[test]
    fn test_rvsdg() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("bril/examples/test/dom/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            for function in &mut program.functions {
                println!("checking {} ... ", path.to_str().unwrap());
                eprintln!("{}", function);
                let cfg = Cfg::new(&function.instrs);

                let sa = StructureAnalysis::new(cfg);
                let rw = read_write_annotation(sa);
                let ds = demand_set_annotation(rw);
                let rvsdg = to_rvsdg(
                    ds,
                    function
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, v)| (v.name.clone(), i))
                        .collect(),
                    &[],
                );

                dbg!(rvsdg);
            }
        }
    }
}
