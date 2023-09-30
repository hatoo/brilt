use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use bril_rs::{Code, ConstOps, EffectOps, Instruction, Literal, Type, ValueOps};

use crate::{
    annotation::{demand_set_annotation, read_write_annotation, Annotation},
    cfg::Cfg,
    restructure::StructureAnalysis,
};

#[derive(Debug, Clone)]
pub enum StateExpr {
    Arg(usize),
    Print(usize),
    Return(Option<usize>),
    Call(String, Vec<usize>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    // RVSDG
    Arg(usize),
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
    },
    // Original RVSDG has state edges but I've chosen to introduce a new node type that has single stateful operation
    // and its order is preserved by the linear node to (hopefully) make the representation egglog friendly.
    StateFul {
        outputs: Vec<StateExpr>,
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

struct BrilBuilder {
    codes: Vec<Code>,
    var_counter: usize,
    label_counter: usize,
}

impl BrilBuilder {
    fn add_code(&mut self, code: Code) {
        self.codes.push(code);
    }
}

impl BrilBuilder {
    fn new_var(&mut self) -> String {
        let var = format!("v{}", self.var_counter);
        self.var_counter += 1;
        var
    }

    fn add_expr(
        &mut self,
        args: &[String],
        expr: &Expr,
        cache: &mut HashMap<Expr, String>,
    ) -> String {
        if let Some(var) = cache.get(expr) {
            var.clone()
        } else {
            // FIXME: use macro
            let var: String = match expr {
                Expr::Arg(n) => args[*n].clone(),
                Expr::ConstInt(i) => {
                    let dest = self.new_var();
                    self.add_code(Code::Instruction(Instruction::Constant {
                        dest: dest.clone(),
                        op: ConstOps::Const,
                        value: Literal::Int(*i),
                        const_type: Type::Int,
                    }));
                    dest
                }
                Expr::ConstBool(b) => {
                    let dest = self.new_var();
                    self.add_code(Code::Instruction(Instruction::Constant {
                        dest: dest.clone(),
                        op: ConstOps::Const,
                        value: Literal::Bool(*b),
                        const_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Add(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Add,
                        op_type: Type::Int,
                    }));
                    dest
                }
                Expr::Sub(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Sub,
                        op_type: Type::Int,
                    }));
                    dest
                }
                Expr::Mul(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Mul,
                        op_type: Type::Int,
                    }));
                    dest
                }
                Expr::Div(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Div,
                        op_type: Type::Int,
                    }));
                    dest
                }
                Expr::Eq(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Eq,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Lt(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Lt,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Gt(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Gt,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Le(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Le,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Ge(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Ge,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Not(arg) => {
                    let dest = self.new_var();
                    let arg = self.add_expr(args, &arg, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![arg],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Not,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::And(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::And,
                        op_type: Type::Bool,
                    }));
                    dest
                }
                Expr::Or(lhs, rhs) => {
                    let dest = self.new_var();
                    let lhs = self.add_expr(args, &lhs, cache);
                    let rhs = self.add_expr(args, &rhs, cache);

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs, rhs],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Or,
                        op_type: Type::Bool,
                    }));
                    dest
                }
            };

            cache.insert(expr.clone(), var.clone());
            var
        }
    }
}

impl Rvsdg {
    pub fn new(args: &[String], mut structure: StructureAnalysis) -> Self {
        let args = args
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i))
            .collect::<HashMap<_, _>>();

        structure.split_effect();
        let rw = read_write_annotation(structure);
        let demand = demand_set_annotation(rw);

        to_rvsdg(demand, &args, &[])
    }
}

fn to_rvsdg_state(code: &Code, args: &HashMap<String, usize>, outputs: &[String]) -> Option<Rvsdg> {
    match code {
        Code::Instruction(instr) => match instr {
            Instruction::Effect {
                args: arguments,
                funcs,
                op,
                ..
            } => match op {
                EffectOps::Print => {
                    let arg = args[&arguments[0]];
                    let expr = StateExpr::Print(arg);

                    Some(Rvsdg::StateFul {
                        outputs: outputs
                            .iter()
                            .map(|s| StateExpr::Arg(args[s]))
                            .chain(std::iter::once(expr))
                            .collect(),
                    })
                }
                EffectOps::Return => {
                    let arg = arguments.get(0).map(|v| args[v]);
                    let expr = StateExpr::Return(arg);

                    Some(Rvsdg::StateFul {
                        outputs: outputs
                            .iter()
                            .map(|s| StateExpr::Arg(args[s]))
                            .chain(std::iter::once(expr))
                            .collect(),
                    })
                }
                EffectOps::Call => {
                    let expr = StateExpr::Call(
                        funcs[0].clone(),
                        arguments.iter().map(|v| args[v]).collect(),
                    );

                    Some(Rvsdg::StateFul {
                        outputs: outputs
                            .iter()
                            .map(|s| StateExpr::Arg(args[s]))
                            .chain(std::iter::once(expr))
                            .collect(),
                    })
                }
                _ => None,
            },
            Instruction::Value {
                args: arguments,
                dest,
                funcs,
                op,
                ..
            } if op == &ValueOps::Call => {
                let expr = StateExpr::Call(
                    funcs[0].clone(),
                    arguments.iter().map(|v| args[v]).collect(),
                );

                let mut used = false;

                let mut outputs: Vec<StateExpr> = outputs
                    .iter()
                    .map(|s| {
                        if s == dest {
                            used = true;
                            expr.clone()
                        } else {
                            StateExpr::Arg(args[s])
                        }
                    })
                    .collect();

                if !used {
                    outputs.push(expr);
                }

                Some(Rvsdg::StateFul { outputs })
            }
            _ => None,
        },
        _ => None,
    }
}

fn to_rvsdg_block(codes: &[Code], args: &HashMap<String, usize>, outputs: &[String]) -> Rvsdg {
    if codes.len() == 1 {
        if let Some(rvsdg) = to_rvsdg_state(&codes[0], args, outputs) {
            return rvsdg;
        }
    }

    let mut vars = args
        .iter()
        .map(|(k, &v)| (k, Expr::Arg(v)))
        .collect::<HashMap<_, _>>();

    for code in codes {
        match code {
            Code::Instruction(instr) => match instr {
                Instruction::Constant { dest, value, .. } => match value {
                    Literal::Int(i) => {
                        vars.insert(dest, Expr::ConstInt(*i));
                    }
                    Literal::Bool(b) => {
                        vars.insert(dest, Expr::ConstBool(*b));
                    }
                },
                Instruction::Value { args, dest, op, .. } => {
                    let args = args
                        .iter()
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
                Instruction::Effect { .. } => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    Rvsdg::Simple {
        outputs: outputs
            .iter()
            .map(|var| vars.remove(var).unwrap())
            .collect(),
    }
}

fn to_rvsdg(
    demand: Annotation<HashSet<String>>,
    args: &HashMap<String, usize>,
    outputs: &[String],
) -> Rvsdg {
    match demand {
        Annotation::Block(codes, _) => to_rvsdg_block(&codes, args, outputs),
        Annotation::Branch(cond_var, branches, _) => {
            let branches = branches
                .into_iter()
                .map(|a| to_rvsdg(a, args, outputs))
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

            for v in outputs {
                if let Some(i) = args.get(v) {
                    output_indices.push(*i);
                } else {
                    output_indices.push(new_outputs.len());
                    new_outputs.push(v.clone());
                }
            }

            let cond_index = new_outputs.len();
            new_outputs.push(StructureAnalysis::VAR_R.to_string());

            Rvsdg::Loop {
                body: Box::new(to_rvsdg(*body, args, &new_outputs)),
                cond_index,
                outputs: output_indices,
            }
        }

        Annotation::Linear(v, _) => {
            if v.is_empty() {
                Rvsdg::Simple {
                    outputs: outputs.iter().map(|v| Expr::Arg(args[v])).collect(),
                }
            } else {
                let mut args = args.clone();
                let mut out = Vec::new();
                for i in 0..v.len() {
                    let outputs = v
                        .get(i + 1)
                        .map(|a| Cow::Owned(a.annotation().iter().cloned().collect::<Vec<_>>()))
                        .unwrap_or(Cow::Borrowed(outputs));

                    out.push(to_rvsdg(v[i].clone(), &args, &outputs));

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

                let mut sa = StructureAnalysis::new(cfg);
                sa.split_effect();
                let rw = read_write_annotation(sa);
                let ds = demand_set_annotation(rw);
                // eprintln!("{}", &ds);
                let rvsdg = to_rvsdg(
                    ds,
                    &function
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
