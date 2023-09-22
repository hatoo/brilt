use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

use bril_rs::{Code, ConstOps, EffectOps, Instruction, Type, ValueOps};
use petgraph::prelude::DiGraphMap;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Label {
    Root,
    Label(String),
}

impl Label {
    pub fn label(&self) -> Option<&str> {
        match self {
            Self::Root => None,
            Self::Label(s) => Some(s),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Ret(Option<String>),
    Jmp(usize),
    Br(String, usize, usize),
}

impl Terminator {
    fn cond_value(self) -> Option<String> {
        match self {
            Self::Br(cond_value, _, _) => Some(cond_value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum StructuredCfg {
    // terminates with jmp or br or ret
    Block(Vec<Code>, Option<Terminator>),
    // terminates with jmp or br or ret
    Linear(Vec<StructuredCfg>),
    // terminates with jmp (implicit)
    Branch {
        cond_value: String,
        then_block: Box<StructuredCfg>,
        else_block: Box<StructuredCfg>,
    },
    // terminates with jmp (implicit)
    Loop {
        cond_value: String,
        body_block: Box<StructuredCfg>,
    },
}

#[derive(Default, Debug)]
pub struct StructuredCfgBuilder {
    block_map: HashMap<usize, StructuredCfg>,
    graph: DiGraphMap<usize, ()>,
    var_counter: usize,
}

impl StructuredCfg {
    pub fn remove_terminator(&mut self) -> Option<Terminator> {
        match self {
            StructuredCfg::Block(_, t) => t.take(),
            StructuredCfg::Linear(blocks) => blocks.last_mut().unwrap().remove_terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    pub fn terminator(&self) -> Option<&Terminator> {
        match self {
            StructuredCfg::Block(_, t) => t.as_ref(),
            StructuredCfg::Linear(blocks) => blocks.last().unwrap().terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    pub fn flatten(&mut self) {
        match self {
            Self::Linear(blocks) => {
                let mut item: Option<(Vec<Code>, Option<Terminator>)> = None;
                let mut v = Vec::new();

                for block in blocks {
                    block.flatten();

                    let linear = match block.clone() {
                        Self::Linear(v) => v,
                        b => vec![b],
                    };

                    for block in linear {
                        match block {
                            Self::Block(block, t_later) => {
                                if let Some((codes, t)) = &mut item {
                                    codes.extend_from_slice(block.as_slice());
                                    *t = t_later;
                                } else {
                                    item = Some((block, t_later));
                                }
                            }
                            b => {
                                if let Some((codes, t)) = item.take() {
                                    v.push(StructuredCfg::Block(codes, t));
                                }
                                v.push(b);
                            }
                        }
                    }
                }
                if let Some((item, t)) = item.take() {
                    v.push(StructuredCfg::Block(item, t));
                }
                *self = Self::Linear(v);
            }
            StructuredCfg::Branch {
                cond_value: _,
                then_block,
                else_block,
            } => {
                then_block.flatten();
                else_block.flatten();
            }
            StructuredCfg::Loop {
                cond_value: _,
                body_block,
            } => {
                body_block.flatten();
            }
            _ => {}
        }
    }
}

impl StructuredCfgBuilder {
    // TODO: Ensure to actually unique
    fn new_var(&mut self, prefix: &str) -> String {
        let var = format!("__v{}_{}", prefix, self.var_counter);
        self.var_counter += 1;
        var
    }

    fn merge(&mut self, from: usize, to: usize) {
        for t in self.graph.neighbors(from).collect::<Vec<_>>() {
            self.graph.remove_edge(from, t);
        }
        for target in self.graph.neighbors(to).collect::<Vec<_>>() {
            self.graph.add_edge(from, target, ());
        }
        self.graph.remove_node(to);

        let mut from_body = self.block_map.remove(&from).unwrap();
        from_body.remove_terminator();

        let to_body = self.block_map.remove(&to).unwrap();

        self.block_map
            .insert(from, StructuredCfg::Linear(vec![from_body, to_body]));
    }

    pub fn merge_linear(&mut self) -> bool {
        let mut changed = false;
        for i in self.graph.nodes().collect::<Vec<_>>() {
            if !self.graph.contains_node(i) {
                continue;
            }

            let out = self.graph.neighbors(i).collect::<Vec<_>>();
            if out.len() != 1 {
                continue;
            }

            let to = out[0];

            if self
                .graph
                .neighbors_directed(to, petgraph::Direction::Incoming)
                .count()
                != 1
            {
                continue;
            }

            if self.graph.neighbors(to).any(|t| t == to) {
                continue;
            }

            self.merge(i, to);

            changed = true;
        }

        changed
    }

    pub fn merge_branch(&mut self) -> bool {
        let mut changed = false;
        for i in self.graph.nodes().collect::<Vec<_>>() {
            if !self.graph.contains_node(i) {
                continue;
            }

            let out = self.graph.neighbors(i);

            if out.count() != 2 {
                continue;
            }

            let (left, right) = match self.block_map[&i].terminator() {
                Some(Terminator::Br(_, left, right)) => (*left, *right),
                _ => panic!("{:?}", &self.graph),
            };

            if i == left || i == right {
                continue;
            }

            if self
                .graph
                .neighbors_directed(left, petgraph::Direction::Incoming)
                .any(|t| t != left && t != right && t != i)
            {
                continue;
            }

            if self
                .graph
                .neighbors_directed(right, petgraph::Direction::Incoming)
                .any(|t| t != left && t != right && t != i)
            {
                continue;
            }

            let left_succ = {
                let left_succ = self.graph.neighbors(left).collect::<Vec<_>>();
                if left_succ.len() > 1 {
                    continue;
                }
                left_succ.first().copied()
            };

            let right_succ = {
                let right_succ = self.graph.neighbors(right).collect::<Vec<_>>();
                if right_succ.len() > 1 {
                    continue;
                }
                right_succ.first().copied()
            };

            match (left_succ, right_succ) {
                (None, None) => {
                    let left_body = self.block_map.remove(&left).unwrap();
                    let right_body = self.block_map.remove(&right).unwrap();

                    let mut body = self.block_map.remove(&i).unwrap();
                    let terminator = body.remove_terminator().unwrap();
                    let cond_value = terminator.cond_value().unwrap();

                    let new_branch = StructuredCfg::Branch {
                        cond_value,
                        then_block: Box::new(left_body),
                        else_block: Box::new(right_body),
                    };

                    self.block_map
                        .insert(i, StructuredCfg::Linear(vec![body, new_branch]));
                    self.graph.remove_node(left);
                    self.graph.remove_node(right);
                    changed = true;
                    continue;
                }
                (Some(left_succ), None) if left_succ != right => {
                    let mut left_body = self.block_map.remove(&left).unwrap();
                    let right_body = self.block_map.remove(&right).unwrap();

                    left_body.remove_terminator();

                    let terminator = self
                        .block_map
                        .get_mut(&i)
                        .unwrap()
                        .remove_terminator()
                        .unwrap();
                    let cond_value = terminator.cond_value().unwrap();

                    let left_body = StructuredCfg::Branch {
                        cond_value,
                        then_block: Box::new(left_body),
                        else_block: Box::new(right_body),
                    };

                    self.block_map.insert(left, left_body);

                    self.graph.remove_node(right);
                    self.merge(i, left);
                    changed = true;
                    continue;
                }
                (None, Some(right_succ)) if right_succ != left => {
                    let left_body = self.block_map.remove(&left).unwrap();
                    let mut right_body = self.block_map.remove(&right).unwrap();

                    right_body.remove_terminator();

                    let terminator = self
                        .block_map
                        .get_mut(&i)
                        .unwrap()
                        .remove_terminator()
                        .unwrap();
                    let cond_value = terminator.cond_value().unwrap();

                    let right_body = StructuredCfg::Branch {
                        cond_value,
                        then_block: Box::new(left_body),
                        else_block: Box::new(right_body),
                    };

                    self.block_map.insert(right, right_body);

                    self.graph.remove_node(left);
                    self.merge(i, right);
                    changed = true;
                    continue;
                }
                _ => {}
            }

            let Some(left_succ) = left_succ else {
                continue;
            };
            let Some(right_succ) = right_succ else {
                continue;
            };

            if left_succ == right_succ {
                let succ_succ = left_succ;
                if succ_succ == left || succ_succ == right {
                    continue;
                }
                let mut left_body = self.block_map.remove(&left).unwrap();
                let mut right_body = self.block_map.remove(&right).unwrap();

                let terminator = self
                    .block_map
                    .get_mut(&i)
                    .unwrap()
                    .remove_terminator()
                    .unwrap();
                let cond_value = terminator.cond_value().unwrap();

                left_body.remove_terminator();
                right_body.remove_terminator();

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(left_body),
                    else_block: Box::new(right_body),
                };

                self.block_map.insert(left, new_branch);
                self.merge(i, left);
                self.graph.remove_node(right);
                return true;
            } else if left == right_succ {
                let terminator = self
                    .block_map
                    .get_mut(&i)
                    .unwrap()
                    .remove_terminator()
                    .unwrap();
                let cond_value = terminator.cond_value().unwrap();

                let mut right_body = self.block_map.remove(&right).unwrap();
                right_body.remove_terminator();

                self.block_map.insert(
                    right,
                    StructuredCfg::Branch {
                        cond_value,
                        then_block: Box::new(StructuredCfg::Block(Vec::new(), None)),
                        else_block: Box::new(right_body),
                    },
                );

                self.merge(i, right);

                changed = true;
            } else if right == left_succ {
                let terminator = self
                    .block_map
                    .get_mut(&i)
                    .unwrap()
                    .remove_terminator()
                    .unwrap();
                let cond_value = terminator.cond_value().unwrap();

                let mut left_body = self.block_map.remove(&left).unwrap();
                left_body.remove_terminator();

                self.block_map.insert(
                    left,
                    StructuredCfg::Branch {
                        cond_value,
                        then_block: Box::new(left_body),
                        else_block: Box::new(StructuredCfg::Block(Vec::new(), None)),
                    },
                );

                self.merge(i, left);

                changed = true;
            }
        }

        changed
    }

    pub fn merge_loop(&mut self) -> bool {
        let mut changed = false;
        for i in self.graph.nodes().collect::<Vec<_>>() {
            if !self.graph.contains_node(i) {
                continue;
            }

            let out = self.graph.neighbors(i).collect::<Vec<_>>();

            if !out.contains(&i) {
                continue;
            }

            match out.len() {
                1 => {
                    // unconditional infinite loop
                    let mut body = self.block_map.remove(&i).unwrap();
                    body.remove_terminator();

                    let true_var = self.new_var("true");
                    body = StructuredCfg::Loop {
                        cond_value: true_var.clone(),
                        body_block: Box::new(StructuredCfg::Linear(vec![
                            body,
                            StructuredCfg::Block(
                                vec![Code::Instruction(Instruction::Constant {
                                    dest: true_var.clone(),
                                    op: ConstOps::Const,
                                    const_type: Type::Bool,
                                    value: bril_rs::Literal::Bool(true),
                                })],
                                None,
                            ),
                        ])),
                    };

                    self.graph.remove_edge(i, i);
                    self.block_map.insert(i, body);
                    changed = true;
                }
                2 => {
                    let mut body = self.block_map.remove(&i).unwrap();
                    let terminator = body.remove_terminator().unwrap();

                    body = match terminator {
                        Terminator::Br(cond_value, t, _f) => {
                            if t == i {
                                StructuredCfg::Loop {
                                    cond_value,
                                    body_block: Box::new(body),
                                }
                            } else {
                                let new_cond_value = self.new_var("cond");
                                StructuredCfg::Loop {
                                    cond_value: new_cond_value.clone(),
                                    body_block: Box::new(StructuredCfg::Linear(vec![
                                        body,
                                        StructuredCfg::Block(
                                            vec![Code::Instruction(Instruction::Value {
                                                dest: new_cond_value.clone(),
                                                op: ValueOps::Not,
                                                args: vec![cond_value],
                                                funcs: vec![],
                                                labels: vec![],
                                                op_type: Type::Bool,
                                            })],
                                            None,
                                        ),
                                    ])),
                                }
                            }
                        }
                        _ => unreachable!(),
                    };

                    self.graph.remove_edge(i, i);
                    self.block_map.insert(i, body);
                    changed = true;
                }
                _ => unreachable!(),
            }
        }
        changed
    }

    pub fn root(&self) -> StructuredCfg {
        self.block_map[&0].clone()
    }
}

#[derive(Default, Debug)]
pub struct Cfg {
    pub(crate) block_map: HashMap<usize, Vec<Code>>,
    pub(crate) graph: DiGraphMap<usize, ()>,
    pub(crate) label_map: HashMap<Label, usize>,
}

impl Cfg {
    pub fn new(codes: &[Code]) -> Self {
        let mut cfg = Self::default();

        let mut id = 0;
        let mut current_state = Some((Label::Root, Vec::new()));

        let mut node = |label: Label| {
            *cfg.label_map.entry(label).or_insert_with(|| {
                let ret = id;
                id += 1;
                ret
            })
        };

        for code in codes {
            match code {
                Code::Label { label } => {
                    if let Some((current_label, mut block)) = current_state {
                        block.push(Code::Instruction(Instruction::Effect {
                            args: Vec::new(),
                            funcs: Vec::new(),
                            labels: vec![label.clone()],
                            op: EffectOps::Jump,
                        }));
                        cfg.block_map.insert(node(current_label.clone()), block);
                        cfg.graph.add_edge(
                            node(current_label.clone()),
                            node(Label::Label(label.clone())),
                            (),
                        );
                    }
                    current_state = Some((Label::Label(label.clone()), vec![code.clone()]));
                }
                Code::Instruction(inst) => match inst {
                    Instruction::Effect { labels, op, .. } => match op {
                        EffectOps::Jump => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(node(label.clone()), block);
                                cfg.graph.add_edge(
                                    node(label.clone()),
                                    node(Label::Label(labels[0].clone())),
                                    (),
                                );
                            }
                            current_state = None;
                        }

                        EffectOps::Branch => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(node(label.clone()), block);
                                cfg.graph.add_edge(
                                    node(label.clone()),
                                    node(Label::Label(labels[0].clone())),
                                    (),
                                );
                                cfg.graph.add_edge(
                                    node(label.clone()),
                                    node(Label::Label(labels[1].clone())),
                                    (),
                                );
                            }
                            current_state = None;
                        }

                        EffectOps::Return => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(node(label), block);
                            }
                            current_state = None;
                        }

                        _ => {
                            if let Some((_, block)) = &mut current_state {
                                block.push(code.clone());
                            }
                        }
                    },
                    _ => {
                        if let Some((_, block)) = &mut current_state {
                            block.push(code.clone());
                        }
                    }
                },
            }
        }

        if let Some((label, mut block)) = current_state {
            if block
                .last()
                .map(|code| {
                    !matches!(
                        code,
                        Code::Instruction(Instruction::Effect {
                            op: EffectOps::Return,
                            ..
                        })
                    )
                })
                .unwrap_or(false)
            {
                block.push(Code::Instruction(Instruction::Effect {
                    args: Vec::new(),
                    funcs: Vec::new(),
                    labels: Vec::new(),
                    op: EffectOps::Return,
                }));
            }
            cfg.block_map.insert(node(label), block);
        }

        cfg
    }

    pub fn into_structure_cfg_builder(self) -> StructuredCfgBuilder {
        let block_map = self
            .block_map
            .into_iter()
            .map(|(label, mut block)| {
                if matches!(block.first(), Some(Code::Label { .. })) {
                    block.remove(0);
                }

                let terminator = match block.pop() {
                    Some(Code::Instruction(Instruction::Effect {
                        args, labels, op, ..
                    })) => match op {
                        EffectOps::Jump => {
                            debug_assert!(labels.len() == 1);
                            Terminator::Jmp(self.label_map[&Label::Label(labels[0].clone())])
                        }
                        EffectOps::Branch => {
                            debug_assert!(labels.len() == 2);
                            Terminator::Br(
                                args[0].clone(),
                                self.label_map[&Label::Label(labels[0].clone())],
                                self.label_map[&Label::Label(labels[1].clone())],
                            )
                        }
                        EffectOps::Return => Terminator::Ret(args.get(0).cloned()),
                        _ => panic!(),
                    },
                    _ => panic!(),
                };
                (label, StructuredCfg::Block(block, Some(terminator)))
            })
            .collect();

        StructuredCfgBuilder {
            block_map,
            graph: self.graph,
            var_counter: 0,
        }
    }

    pub fn flatten(&self) -> Vec<Code> {
        let mut codes = self.block_map[&0].clone();

        for (_, block) in self.block_map.iter().filter(|(&label, _)| label != 0) {
            codes.extend(block.iter().cloned());
        }

        codes
    }
}

impl Display for Terminator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ret(None) => write!(f, "  ret;"),
            Self::Ret(Some(v)) => write!(f, "  ret {};", v),
            Self::Jmp(l) => write!(f, "  jmp {};", l),
            Self::Br(v, l1, l2) => write!(f, "  br {} {} {};", v, l1, l2),
        }
    }
}

impl Display for StructuredCfg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.display_impl(1, f)
    }
}

impl StructuredCfg {
    fn display_impl(&self, indent_level: usize, fmt: &mut Formatter) -> fmt::Result {
        let tab = " ".repeat(indent_level * 2);
        let ctab = " ".repeat(indent_level * 2 - 2);
        match self {
            Self::Block(codes, terminator) => {
                for code in codes {
                    writeln!(fmt, "{}{}", &ctab, code)?;
                }
                if let Some(terminator) = terminator {
                    writeln!(fmt, "{}{}", &ctab, terminator)?;
                }
            }
            Self::Linear(blocks) => {
                for block in blocks {
                    block.display_impl(indent_level, fmt)?;
                }
            }
            Self::Branch {
                cond_value,
                then_block,
                else_block,
            } => {
                writeln!(fmt, "{}if ({}) {{", &tab, cond_value)?;
                then_block.display_impl(indent_level + 1, fmt)?;
                writeln!(fmt, "{}}} else {{", &tab)?;
                else_block.display_impl(indent_level + 1, fmt)?;
                writeln!(fmt, "{}}}", &tab)?;
            }
            Self::Loop {
                cond_value,
                body_block,
            } => {
                writeln!(fmt, "{}do {{", &tab)?;
                body_block.display_impl(indent_level + 1, fmt)?;
                writeln!(fmt, "{}}} while ({});", &tab, cond_value)?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::io::Cursor;

    use super::*;
    use crate::test::{bril2json, brili};
    use glob::glob;

    #[test]
    fn test_cfg_reconstruct() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("tests/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            for function in &mut program.functions {
                let cfg = Cfg::new(&function.instrs);
                let codes = cfg.flatten();
                function.instrs = codes;
            }

            let json_after = serde_json::to_string_pretty(&program).unwrap();

            println!("checking {} ... ", path.to_str().unwrap());
            // println!("after: {}", &json_after);
            assert_eq!(brili(&json_before).0, brili(&json_after).0);
        }
    }

    #[test]
    fn test_scfg() {
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
                let cfg = Cfg::new(&function.instrs);
                let mut builder = cfg.into_structure_cfg_builder();

                while builder.merge_linear() || builder.merge_branch() || builder.merge_loop() {}

                let mut root = builder.root();
                root.flatten();

                eprintln!("{}", root);
                assert_eq!(builder.graph.neighbors(0).count(), 0);
            }
        }
    }
}
