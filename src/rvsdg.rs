use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
};

use bril_rs::{Argument, Code, ConstOps, EffectOps, Instruction, Literal, Type, ValueOps};
use egglog::Term;

use crate::{
    annotation::{demand_set_annotation, read_write_annotation, Annotation},
    restructure::StructureAnalysis,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StateExpr {
    Arg(usize),
    Print(usize),
    Return(Option<usize>),
    Call(String, Vec<usize>),
}
fn to_list<T: Display>(v: &[T], cons: &str, nil: &str) -> String {
    if v.is_empty() {
        format!("({})", nil)
    } else {
        format!("({} {} {})", cons, v[0], to_list(&v[1..], cons, nil))
    }
}

fn to_list_rvsdg(
    v: &[Rvsdg],
    f: &mut std::fmt::Formatter<'_>,
    id: &mut usize,
    cons: &str,
    nil: &str,
) -> std::fmt::Result {
    if v.is_empty() {
        writeln!(f, "({})", nil)
    } else {
        write!(f, "({} ", cons,)?;
        v[0].fmt_id(f, id)?;
        write!(f, " ")?;
        to_list_rvsdg(&v[1..], f, id, cons, nil)?;
        write!(f, ")")
    }
}

fn to_listi<T: Display>(v: &[T], cons: &str, nil: &str) -> String {
    fn to_list_impl<T: Display>(v: &[T], i: usize, cons: &str, nil: &str) -> String {
        if v.is_empty() {
            format!("({})", nil)
        } else {
            format!(
                "({} {} {} {})",
                cons,
                i,
                v[0],
                to_list_impl(&v[1..], i + 1, cons, nil)
            )
        }
    }

    to_list_impl(v, 0, cons, nil)
}

impl Display for StateExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arg(n) => write!(f, "(SArg {})", n),
            Self::Print(i) => write!(f, "(Print {})", i),
            Self::Return(r) => {
                if let Some(r) = r {
                    write!(f, "(Return (SomeI {}))", r)
                } else {
                    write!(f, "(Return (NoneI))")
                }
            }
            Self::Call(func, args) => {
                write!(f, "(Call {} {})", func, to_list(args, "ConsI", "NilI"))
            }
        }
    }
}

impl StateExpr {
    pub fn from_egglog(term: &Term, nodes: &[Term]) -> Self {
        match term {
            Term::App(head, tail) => match head.as_str() {
                "Return" => {
                    let n = match &nodes[tail[0]] {
                        Term::App(head, tail) => match head.as_str() {
                            "NoneI" => None,
                            "SomeI" => Some(term_i64(&nodes[tail[0]]) as usize),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    };
                    Self::Return(n)
                }
                "Print" => {
                    let n = term_i64(&nodes[tail[0]]) as usize;
                    Self::Print(n)
                }
                "SArg" => {
                    let n = term_i64(&nodes[tail[0]]) as usize;
                    Self::Arg(n)
                }
                _ => todo!("{}", head),
            },
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Nop,
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

impl Expr {
    pub fn from_egglog(term: &Term, nodes: &[Term]) -> Self {
        match term {
            Term::Lit(egglog::ast::Literal::Int(i)) => Self::ConstInt(*i),
            Term::Lit(_) => todo!(),
            Term::App(head, tail) => match head.as_str() {
                "Arg" => {
                    let n = term_i64(&nodes[tail[0]]) as usize;
                    Self::Arg(n)
                }
                "ConstInt" => {
                    let i = term_i64(&nodes[tail[0]]);
                    Self::ConstInt(i)
                }
                "ConstBool" => {
                    let b = term_bool(&nodes[tail[0]]);
                    Self::ConstBool(b)
                }
                "Add" => Self::Add(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                "Sub" => Self::Sub(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                "Mul" => Self::Mul(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                "Gt" => Self::Gt(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                "Lt" => Self::Lt(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                "Eq" => Self::Eq(
                    Box::new(Self::from_egglog(&nodes[tail[0]], nodes)),
                    Box::new(Self::from_egglog(&nodes[tail[1]], nodes)),
                ),
                _ => todo!("{}", head),
            },
            Term::Var(_) => unreachable!(),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nop => write!(f, "(Nop)"),
            Self::Arg(n) => write!(f, "(Arg {})", n),
            Self::ConstInt(i) => write!(f, "(ConstInt {})", i),
            Self::ConstBool(b) => write!(f, "(ConstBool {})", if *b { "true" } else { "false" }),
            Self::Add(l, r) => write!(f, "(Add {} {})", l, r),
            Self::Sub(l, r) => write!(f, "(Sub {} {})", l, r),
            Self::Mul(l, r) => write!(f, "(Mul {} {})", l, r),
            Self::Div(l, r) => write!(f, "(Div {} {})", l, r),
            Self::Eq(l, r) => write!(f, "(Eq {} {})", l, r),
            Self::Lt(l, r) => write!(f, "(Lt {} {})", l, r),
            Self::Gt(l, r) => write!(f, "(Gt {} {})", l, r),
            Self::Le(l, r) => write!(f, "(Le {} {})", l, r),
            Self::Ge(l, r) => write!(f, "(Ge {} {})", l, r),
            Self::Not(e) => write!(f, "(Not {})", e),
            Self::And(l, r) => write!(f, "(And {} {})", l, r),
            Self::Or(l, r) => write!(f, "(Or {} {})", l, r),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Rvsdg {
    Simple {
        outputs: Vec<Expr>,
    },
    /// Original RVSDG has state edges but I've chosen to introduce a new node type that has single stateful operation
    /// and its order is preserved by the linear node to (hopefully) make the representation egglog friendly.
    StateFul {
        /// one of the outputs is not a StateExpr::Arg if side_effect is None
        outputs: Vec<StateExpr>,
        /// Some() if the stateful operation hasn't return value
        side_effect: Option<StateExpr>,
    },
    Linear(Vec<Rvsdg>),
    /// Gamma node
    /// cond_var is a bool
    BranchIf {
        cond_index: usize,
        /// then else
        branches: [Box<Rvsdg>; 2],
    },
    /// cond_var is an int
    BranchSwitch {
        cond_index: usize,
        branches: Vec<Rvsdg>,
    },
    /// Theta node
    Loop {
        body: Box<Rvsdg>,
        cond_index: usize,
        outputs: Vec<usize>,
    },
}

impl Display for Rvsdg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_id(f, &mut 0)
    }
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

    fn new_label(&mut self, info: Option<&str>) -> String {
        let label = format!("L{}{}", info.unwrap_or_default(), self.label_counter);
        self.label_counter += 1;
        label
    }

    fn add_expr(
        &mut self,
        args: &[Argument],
        expr: &Expr,
        cache: &mut HashMap<Expr, Argument>,
    ) -> Argument {
        if let Some(var) = cache.get(expr) {
            var.clone()
        } else {
            // FIXME: use macro
            let var: Argument = match expr {
                Expr::Nop =>
                // todo
                {
                    Argument {
                        name: "nop".to_string(),
                        arg_type: Type::Bool,
                    }
                }
                Expr::Arg(n) => return args[*n].clone(),
                Expr::ConstInt(i) => {
                    let dest = self.new_var();
                    self.add_code(Code::Instruction(Instruction::Constant {
                        dest: dest.clone(),
                        op: ConstOps::Const,
                        value: Literal::Int(*i),
                        const_type: Type::Int,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Int,
                    }
                }
                Expr::ConstBool(b) => {
                    let dest = self.new_var();
                    self.add_code(Code::Instruction(Instruction::Constant {
                        dest: dest.clone(),
                        op: ConstOps::Const,
                        value: Literal::Bool(*b),
                        const_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Add(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Add,
                        op_type: Type::Int,
                    }));

                    Argument {
                        name: dest,
                        arg_type: lhs.arg_type,
                    }
                }
                Expr::Sub(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Sub,
                        op_type: Type::Int,
                    }));

                    Argument {
                        name: dest,
                        arg_type: lhs.arg_type,
                    }
                }
                Expr::Mul(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Mul,
                        op_type: Type::Int,
                    }));
                    Argument {
                        name: dest,
                        arg_type: lhs.arg_type,
                    }
                }
                Expr::Div(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Div,
                        op_type: Type::Int,
                    }));
                    Argument {
                        name: dest,
                        arg_type: lhs.arg_type,
                    }
                }
                Expr::Eq(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Eq,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Lt(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Lt,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Gt(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Gt,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Le(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Le,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Ge(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Ge,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Not(arg) => {
                    let arg = self.add_expr(args, arg, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![arg.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Not,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::And(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::And,
                        op_type: Type::Bool,
                    }));

                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
                Expr::Or(lhs, rhs) => {
                    let lhs = self.add_expr(args, lhs, cache);
                    let rhs = self.add_expr(args, rhs, cache);
                    let dest = self.new_var();

                    self.add_code(Code::Instruction(Instruction::Value {
                        args: vec![lhs.name, rhs.name],
                        dest: dest.clone(),
                        funcs: vec![],
                        labels: vec![],
                        op: ValueOps::Or,
                        op_type: Type::Bool,
                    }));
                    Argument {
                        name: dest,
                        arg_type: Type::Bool,
                    }
                }
            };

            cache.insert(expr.clone(), var.clone());
            var
        }
    }

    fn add_state_expr(
        &mut self,
        args: &[Argument],
        state_expr: StateExpr,
        need_call_ret: bool,
    ) -> Option<Argument> {
        match state_expr {
            StateExpr::Arg(n) => Some(args[n].clone()),
            StateExpr::Print(n) => {
                self.add_code(Code::Instruction(Instruction::Effect {
                    op: EffectOps::Print,
                    args: vec![args[n].name.clone()],
                    funcs: vec![],
                    labels: vec![],
                }));
                None
            }
            StateExpr::Return(n) => {
                self.add_code(Code::Instruction(Instruction::Effect {
                    op: EffectOps::Return,
                    args: n.into_iter().map(|n| args[n].name.clone()).collect(),
                    funcs: vec![],
                    labels: vec![],
                }));
                None
            }
            StateExpr::Call(func, call_args) => {
                if need_call_ret {
                    let var = self.new_var();
                    self.add_code(Code::Instruction(Instruction::Value {
                        args: call_args
                            .into_iter()
                            .map(|n| args[n].name.clone())
                            .collect(),
                        dest: var.clone(),
                        funcs: vec![func],
                        labels: vec![],
                        op: ValueOps::Call,
                        op_type: Type::Int,
                    }));

                    // FIXME: detect correct return type
                    Some(Argument {
                        name: var,
                        arg_type: Type::Int,
                    })
                } else {
                    self.add_code(Code::Instruction(Instruction::Effect {
                        op: EffectOps::Call,
                        args: call_args
                            .into_iter()
                            .map(|n| args[n].name.clone())
                            .collect(),
                        funcs: vec![func],
                        labels: vec![],
                    }));

                    None
                }
            }
        }
    }

    fn var_map(&mut self, from: &[Argument], to: &[Argument]) {
        for (f, t) in from.iter().zip(to.iter()) {
            // TODO: add phi node
            if f != t {
                self.add_code(Code::Instruction(Instruction::Value {
                    args: vec![f.name.clone()],
                    dest: t.name.clone(),
                    funcs: vec![],
                    labels: vec![],
                    op: ValueOps::Id,
                    // FIXME
                    op_type: t.arg_type.clone(),
                }));
            }
        }
    }
}

fn term_i64(term: &Term) -> i64 {
    match term {
        Term::Lit(egglog::ast::Literal::Int(i)) => *i,
        _ => unreachable!(),
    }
}

fn term_bool(term: &Term) -> bool {
    match term {
        Term::Lit(egglog::ast::Literal::Bool(b)) => *b,
        _ => unreachable!(),
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

    fn fmt_id(&self, f: &mut std::fmt::Formatter<'_>, id: &mut usize) -> std::fmt::Result {
        let mut new_id = || {
            let i = *id;
            *id += 1;
            i
        };
        match self {
            Rvsdg::Simple { outputs } => {
                writeln!(
                    f,
                    "(Simple {} {})",
                    new_id(),
                    to_listi(outputs, "ConsE", "NilE")
                )
            }
            Rvsdg::StateFul {
                outputs,
                side_effect,
            } => {
                if let Some(se) = side_effect {
                    writeln!(
                        f,
                        "(StateFul {} {} (SomeS {}))",
                        new_id(),
                        to_listi(outputs, "ConsS", "NilS"),
                        se
                    )
                } else {
                    writeln!(
                        f,
                        "(StateFul {} {} (NoneS))",
                        new_id(),
                        to_listi(outputs, "ConsS", "NilS"),
                    )
                }
            }
            Rvsdg::Linear(v) => {
                write!(f, "(Linear {} ", new_id(),)?;
                to_list_rvsdg(v, f, id, "Cons", "Nil")?;
                writeln!(f, ")")
            }
            Rvsdg::BranchIf {
                cond_index,
                branches,
            } => {
                write!(f, "(BranchIf {} {} ", new_id(), cond_index,)?;
                branches[0].fmt_id(f, id)?;
                write!(f, " ")?;
                branches[1].fmt_id(f, id)?;
                writeln!(f, ")")
            }
            Rvsdg::BranchSwitch { .. } => {
                todo!()
            }
            Rvsdg::Loop {
                body,
                cond_index,
                outputs,
            } => {
                writeln!(f, "(Loop {} {} ", new_id(), cond_index,)?;

                body.fmt_id(f, id)?;
                write!(f, " ")?;
                writeln!(f, "{})", to_listi(outputs, "ConsII", "NilII"))
            }
        }
    }

    pub fn from_egglog(term: &Term, nodes: &[Term]) -> Self {
        match term {
            Term::App(head, tail) => match head.as_str() {
                "Simple" => {
                    let mut node = &nodes[tail[1]];
                    let mut map = HashMap::new();

                    loop {
                        match node {
                            Term::App(head, tail) => match head.as_str() {
                                "NilE" => {
                                    break;
                                }
                                "ConsE" => {
                                    let id = term_i64(&nodes[tail[0]]);
                                    map.insert(id, Expr::from_egglog(&nodes[tail[1]], nodes));

                                    node = &nodes[tail[2]];
                                }
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    }

                    let size = map.keys().max().unwrap_or(&0) + 1;
                    let mut exprs = vec![Expr::Nop; size as usize];

                    for (k, v) in map {
                        exprs[k as usize] = v;
                    }

                    Rvsdg::Simple { outputs: exprs }
                }
                "Linear" => {
                    let mut node = &nodes[tail[1]];
                    let mut v = Vec::new();

                    loop {
                        match node {
                            Term::App(head, tail) => match head.as_str() {
                                "Nil" => {
                                    break;
                                }
                                "Cons" => {
                                    v.push(Self::from_egglog(&nodes[tail[0]], nodes));
                                    node = &nodes[tail[1]];
                                }
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    }

                    Rvsdg::Linear(v)
                }
                "StateFul" => {
                    let mut map = HashMap::new();

                    let mut node = &nodes[tail[1]];

                    loop {
                        match node {
                            Term::App(head, tail) => match head.as_str() {
                                "NilS" => {
                                    break;
                                }
                                "ConsS" => {
                                    map.insert(
                                        term_i64(&nodes[tail[0]]),
                                        StateExpr::from_egglog(&nodes[tail[1]], nodes),
                                    );
                                    node = &nodes[tail[2]];
                                }
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    }

                    let size = map.keys().max().unwrap_or(&0) + 1;
                    let mut exprs = vec![StateExpr::Arg(0); size as usize];

                    for (k, v) in map {
                        exprs[k as usize] = v;
                    }

                    match &nodes[tail[2]] {
                        Term::App(head, tail) => match head.as_str() {
                            "NoneS" => Rvsdg::StateFul {
                                outputs: exprs,
                                side_effect: None,
                            },
                            "SomeS" => Rvsdg::StateFul {
                                outputs: exprs,
                                side_effect: Some(StateExpr::from_egglog(&nodes[tail[0]], nodes)),
                            },
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }
                "BranchIf" => {
                    let cond_index = term_i64(&nodes[tail[1]]) as usize;
                    let branches = [
                        Box::new(Rvsdg::from_egglog(&nodes[tail[2]], nodes)),
                        Box::new(Rvsdg::from_egglog(&nodes[tail[3]], nodes)),
                    ];

                    Rvsdg::BranchIf {
                        cond_index,
                        branches,
                    }
                }
                "Loop" => {
                    let cond_index = term_i64(&nodes[tail[1]]) as usize;
                    let body = Self::from_egglog(&nodes[tail[2]], nodes);

                    let mut map = HashMap::new();

                    let mut node = &nodes[tail[3]];

                    loop {
                        match node {
                            Term::App(head, tail) => match head.as_str() {
                                "NilII" => {
                                    break;
                                }
                                "ConsII" => {
                                    map.insert(
                                        term_i64(&nodes[tail[0]]),
                                        term_i64(&nodes[tail[1]]),
                                    );
                                    node = &nodes[tail[2]];
                                }
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    }

                    let size = map.keys().max().unwrap_or(&0) + 1;
                    let mut outputs = vec![0; size as usize];
                    for (k, v) in map {
                        outputs[k as usize] = v as usize;
                    }
                    Rvsdg::Loop {
                        body: Box::new(body),
                        cond_index,
                        outputs,
                    }
                }
                _ => todo!("{}", head),
            },
            _ => unreachable!(),
        }
    }

    pub fn to_bril(&self, args: &[Argument]) -> Vec<Code> {
        let mut builder = BrilBuilder {
            codes: Vec::new(),
            var_counter: 0,
            label_counter: 0,
        };

        self.build_bril(args, &mut builder);

        builder.codes
    }

    fn build_bril(&self, args: &[Argument], builder: &mut BrilBuilder) -> Vec<Argument> {
        match self {
            Rvsdg::Simple { outputs } => {
                let mut cache = HashMap::new();
                let mut outs: Vec<Argument> = outputs
                    .iter()
                    .map(|v| builder.add_expr(args, v, &mut cache))
                    .collect();

                // make each outputs distinct
                let mut used: HashSet<&str> = HashSet::new();
                for v in &mut outs {
                    if used.contains(v.name.as_str()) {
                        let var = builder.new_var();
                        builder.add_code(Code::Instruction(Instruction::Value {
                            args: vec![v.name.clone()],
                            dest: var.clone(),
                            funcs: vec![],
                            labels: vec![],
                            op: ValueOps::Id,
                            op_type: v.arg_type.clone(),
                        }));
                        v.name = var;
                    } else {
                        used.insert(&v.name);
                    }
                }
                outs
            }
            Rvsdg::StateFul {
                outputs,
                side_effect,
            } => {
                if let Some(state_expr) = side_effect {
                    builder.add_state_expr(args, state_expr.clone(), false);
                }
                outputs
                    .iter()
                    .map(|v| builder.add_state_expr(args, v.clone(), true).unwrap())
                    .collect()
            }
            Rvsdg::Linear(v) => {
                let mut args = args.to_vec();
                for rvsdg in v {
                    args = rvsdg.build_bril(&args, builder);
                }
                args
            }
            Rvsdg::BranchIf {
                cond_index,
                branches,
            } => {
                let end_label = builder.new_label(Some("branch_end"));
                let then_label = builder.new_label(Some("then"));
                let else_label = builder.new_label(Some("else"));

                let cond_var = args[*cond_index].clone();

                builder.add_code(Code::Instruction(Instruction::Effect {
                    op: EffectOps::Branch,
                    args: vec![cond_var.name],
                    funcs: vec![],
                    labels: vec![then_label.clone(), else_label.clone()],
                }));

                // then block
                builder.add_code(Code::Label { label: then_label });
                let then_outputs = branches[0].build_bril(args, builder);
                builder.add_code(Code::Instruction(Instruction::Effect {
                    args: vec![],
                    funcs: vec![],
                    labels: vec![end_label.clone()],
                    op: EffectOps::Jump,
                }));

                // else block
                builder.add_code(Code::Label { label: else_label });
                let else_outputs = branches[1].build_bril(args, builder);

                builder.var_map(&else_outputs, &then_outputs);
                builder.add_code(Code::Label { label: end_label });

                then_outputs
            }
            Rvsdg::BranchSwitch {
                cond_index,
                branches,
            } => {
                let end_label = builder.new_label(Some("branch_end"));

                let is0 = builder.add_expr(
                    args,
                    &Expr::Eq(
                        Box::new(Expr::Arg(*cond_index)),
                        Box::new(Expr::ConstInt(0)),
                    ),
                    &mut HashMap::new(),
                );
                let then0 = builder.new_label(Some("then"));
                let else0 = builder.new_label(Some("else"));

                builder.add_code(Code::Instruction(Instruction::Effect {
                    args: vec![is0.name],
                    funcs: vec![],
                    labels: vec![then0.clone(), else0.clone()],
                    op: EffectOps::Branch,
                }));

                builder.add_code(Code::Label { label: then0 });
                let outputs = branches[0].build_bril(args, builder);

                let mut else_label = else0;

                for (b, i) in branches[1..].iter().zip(1..) {
                    builder.add_code(Code::Label {
                        label: else_label.clone(),
                    });
                    let then_label = builder.new_label(Some("then"));
                    let new_else_label = builder.new_label(Some("else"));

                    let is_i = builder.add_expr(
                        args,
                        &Expr::Eq(
                            Box::new(Expr::Arg(*cond_index)),
                            Box::new(Expr::ConstInt(i as i64)),
                        ),
                        &mut HashMap::new(),
                    );

                    builder.add_code(Code::Instruction(Instruction::Effect {
                        args: vec![is_i.name],
                        funcs: vec![],
                        labels: vec![then_label.clone(), new_else_label.clone()],
                        op: EffectOps::Branch,
                    }));

                    builder.add_code(Code::Label { label: then_label });
                    let outs = b.build_bril(args, builder);

                    builder.var_map(&outs, &outputs);

                    if i + 1 < branches.len() {
                        builder.add_code(Code::Instruction(Instruction::Effect {
                            args: vec![],
                            funcs: vec![],
                            labels: vec![end_label.clone()],
                            op: EffectOps::Jump,
                        }));
                    }

                    else_label = new_else_label;
                }
                builder.add_code(Code::Label {
                    label: else_label.clone(),
                });

                builder.add_code(Code::Label { label: end_label });

                outputs
            }
            Rvsdg::Loop {
                body,
                cond_index,
                outputs,
            } => {
                let loop_head = builder.new_label(Some("loop_head"));

                builder.add_code(Code::Label {
                    label: loop_head.clone(),
                });

                let outs = body.build_bril(args, builder);
                builder.var_map(&outs, args);
                let loop_end = builder.new_label(Some("loop_end"));
                builder.add_code(Code::Instruction(Instruction::Effect {
                    args: vec![outs[*cond_index].name.clone()],
                    funcs: vec![],
                    labels: vec![loop_head.clone(), loop_end.clone()],
                    op: EffectOps::Branch,
                }));

                builder.add_code(Code::Label { label: loop_end });
                outputs.iter().map(|i| args[*i].clone()).collect()
            }
        }
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
                        outputs: outputs.iter().map(|s| StateExpr::Arg(args[s])).collect(),
                        side_effect: Some(expr),
                    })
                }
                EffectOps::Return => {
                    let arg = arguments.get(0).map(|v| args[v]);
                    let expr = StateExpr::Return(arg);

                    Some(Rvsdg::StateFul {
                        outputs: outputs.iter().map(|s| StateExpr::Arg(args[s])).collect(),
                        side_effect: Some(expr),
                    })
                }
                EffectOps::Call => {
                    let expr = StateExpr::Call(
                        funcs[0].clone(),
                        arguments.iter().map(|v| args[v]).collect(),
                    );

                    Some(Rvsdg::StateFul {
                        outputs: outputs.iter().map(|s| StateExpr::Arg(args[s])).collect(),
                        side_effect: Some(expr),
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

                Some(Rvsdg::StateFul {
                    outputs,
                    side_effect: None,
                })
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
                        ValueOps::Call => unreachable!(),
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

            match cond_var.as_str() {
                StructureAnalysis::VAR_P | StructureAnalysis::VAR_Q => Rvsdg::BranchSwitch {
                    cond_index: args.get(&cond_var).copied().unwrap(),
                    branches,
                },
                _ => Rvsdg::BranchIf {
                    cond_index: args.get(&cond_var).copied().unwrap(),
                    branches: [Box::new(branches[0].clone()), Box::new(branches[1].clone())],
                },
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
    use egglog::{EGraph, ExtractReport};
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

                println!("{}", rvsdg);
            }
        }
    }

    #[test]
    fn test_rvsdg_bril() {
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

                let codes = rvsdg.to_bril(&function.args);

                // dbg!(&rvsdg);

                eprintln!();

                let mut f = function.clone();
                f.instrs = codes;
                eprintln!("{}", f);
            }
        }
    }

    #[test]
    fn test_rvsdg_brili() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("bril/examples/test/dom/*.bril").unwrap())
            .chain(glob("tests/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            print!("checking {} ... ", path.to_str().unwrap());
            for function in &mut program.functions {
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

                let codes = rvsdg.to_bril(&function.args);

                function.instrs = codes;
            }

            let json_after = serde_json::to_string_pretty(&program).unwrap();

            assert_eq!(brili(&json_before).0, brili(&json_after).0);
            println!("ok");
        }
    }

    #[test]
    fn test_rvsdg_egglog_brili() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("bril/examples/test/dom/*.bril").unwrap())
            .chain(glob("tests/*.bril").unwrap())
        {
            let path = entry.unwrap();
            if path.ends_with("call.bril") || path.ends_with("rec.bril") {
                // TODO support call
                continue;
            }
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            print!("checking {} ... ", path.to_str().unwrap());
            for function in &mut program.functions {
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
                const SCHEMA: &str = include_str!("../schema.egg");
                let mut egraph = EGraph::default();

                egraph.parse_and_run_program(SCHEMA).unwrap();

                egraph
                    .parse_and_run_program(&format!("(let e {})\n(run 100)\n(extract e)", &rvsdg))
                    .unwrap();

                let rvsdg = match egraph.get_extract_report().as_ref().unwrap() {
                    ExtractReport::Best { termdag, term, .. } => {
                        Rvsdg::from_egglog(&term, &termdag.nodes)
                    }
                    _ => panic!("No best term found"),
                };

                let codes = rvsdg.to_bril(&function.args);

                function.instrs = codes;
            }

            let json_after = serde_json::to_string_pretty(&program).unwrap();

            assert_eq!(brili(&json_before).0, brili(&json_after).0);
            println!("ok");
        }
    }
}
