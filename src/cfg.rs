use std::collections::{HashMap, HashSet};

use bril_rs::{Code, EffectOps, Instruction};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Label {
    Root,
    Label(String),
}

#[derive(Debug, Clone)]
pub enum StructuredCfg {
    // terminates with jmp or br or ret
    Block(Vec<Code>),
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
struct StructuredCfgBuilder {
    block_map: HashMap<Label, StructuredCfg>,
    successors: HashMap<Label, HashSet<Label>>,
    predecessors: HashMap<Label, HashSet<Label>>,
}

impl StructuredCfg {
    fn remove_terminator(&mut self) -> Option<Code> {
        match self {
            StructuredCfg::Block(block) => {
                if let Some(t) = block.pop() {
                    debug_assert!(match t {
                        Code::Instruction(Instruction::Effect { op, .. }) => {
                            match op {
                                EffectOps::Jump => true,
                                EffectOps::Branch => true,
                                EffectOps::Return => true,
                                _ => false,
                            }
                        }
                        _ => false,
                    });

                    Some(t)
                } else {
                    None
                }
            }
            StructuredCfg::Linear(blocks) => blocks.last_mut().unwrap().remove_terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    fn terminator(&self) -> Option<&Code> {
        match self {
            StructuredCfg::Block(block) => {
                if let Some(t) = block.last() {
                    debug_assert!(match t {
                        Code::Instruction(Instruction::Effect { op, .. }) => {
                            match op {
                                EffectOps::Jump => true,
                                EffectOps::Branch => true,
                                EffectOps::Return => true,
                                _ => false,
                            }
                        }
                        _ => false,
                    });

                    Some(t)
                } else {
                    None
                }
            }
            StructuredCfg::Linear(blocks) => blocks.last().unwrap().terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    fn flatten(&mut self) {
        match self {
            Self::Linear(blocks) => {
                let mut item: Option<Vec<Code>> = None;
                let mut v = Vec::new();

                for block in blocks {
                    block.flatten();

                    let linear = match block.clone() {
                        Self::Linear(v) => v,
                        b => vec![b],
                    };

                    for block in linear {
                        match block {
                            Self::Block(block) => {
                                if let Some(codes) = &mut item {
                                    codes.extend_from_slice(block.as_slice());
                                } else {
                                    item = Some(block);
                                }
                            }
                            b => {
                                if let Some(codes) = item.take() {
                                    v.push(StructuredCfg::Block(codes));
                                }
                                v.push(b);
                            }
                        }
                    }
                }
                if let Some(item) = item.take() {
                    v.push(StructuredCfg::Block(item));
                }
                *self = Self::Linear(v);
            }
            _ => {}
        }
    }
}

impl StructuredCfgBuilder {
    fn remove_all(&mut self, label: &Label) {
        self.block_map.remove(label);
        self.predecessors.remove(label);
        self.predecessors.iter_mut().for_each(|(_, v)| {
            v.remove(label);
        });
        self.successors.remove(label);
        self.successors.iter_mut().for_each(|(_, v)| {
            v.remove(label);
        });
    }

    fn merge(&mut self, left: Label, right: Label) {
        let mut left_body = self.block_map.remove(&left).unwrap();
        let right_body = self.block_map.remove(&right).unwrap();

        left_body.remove_terminator();

        // flatten later
        let new_body = StructuredCfg::Linear(vec![left_body, right_body]);

        self.block_map.insert(left.clone(), new_body);
        self.predecessors.remove(&right);

        if let Some(succ) = self.successors.remove(&right) {
            self.successors.insert(left, succ);
        } else {
            self.successors.remove(&left);
        }
    }

    fn merge_linear(&mut self) -> bool {
        let mut changed = false;

        let labels = self.block_map.keys().cloned().collect::<Vec<_>>();

        for label in labels {
            if !self.block_map.contains_key(&label) {
                continue;
            }

            let Some(succ) = self.successors.get(&label) else {
                continue;
            };

            if succ.len() != 1 {
                continue;
            }

            let succ = succ.iter().next().unwrap().clone();

            if self.predecessors[&succ].len() != 1 {
                continue;
            }

            if let Some(succ_succ) = self.successors.get(&succ) {
                if succ_succ.contains(&label) || succ_succ.contains(&succ) {
                    // continue;
                }
            }

            self.merge(label, succ);
            changed = true;
        }

        changed
    }

    fn merge_branch(&mut self) -> bool {
        let mut changed = false;

        let labels = self.block_map.keys().cloned().collect::<Vec<_>>();

        for label in labels {
            if !self.block_map.contains_key(&label) {
                continue;
            }

            let Some(succ) = self.successors.get(&label) else {
                continue;
            };

            if succ.len() != 2 {
                continue;
            }

            let br = self.block_map.get(&label).unwrap().terminator().unwrap();
            let (left, right) = match br {
                Code::Instruction(Instruction::Effect { labels, .. }) => (
                    Label::Label(labels[0].clone()),
                    Label::Label(labels[1].clone()),
                ),
                _ => panic!(),
            };

            if left == label || right == label {
                continue;
            }

            if self.predecessors[&left].len() != 1 || self.predecessors[&right].len() != 1 {
                continue;
            }

            if self.successors.get(&left).map(|s| s.len()).unwrap_or(0) == 0
                && self.successors.get(&right).map(|s| s.len()).unwrap_or(0) == 0
            {
                let left_body = self.block_map.remove(&left).unwrap();
                let right_body = self.block_map.remove(&right).unwrap();

                let terminator = self
                    .block_map
                    .get_mut(&label)
                    .unwrap()
                    .terminator()
                    .unwrap();
                let cond_value = match terminator {
                    Code::Instruction(Instruction::Effect { args, .. }) => args[0].clone(),
                    _ => panic!(),
                };

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(left_body),
                    else_block: Box::new(right_body),
                };

                self.block_map.insert(left.clone(), new_branch);
                self.merge(label, left.clone());
                self.remove_all(&right);
                changed = true;
                continue;
            }

            let left_succ = {
                let Some(ls) = self.successors.get(&left) else {
                    continue;
                };
                if ls.len() != 1 {
                    continue;
                }
                ls.iter().next().unwrap().clone()
            };

            let right_succ = {
                let Some(rs) = self.successors.get(&right) else {
                    continue;
                };
                if rs.len() != 1 {
                    continue;
                }
                rs.iter().next().unwrap().clone()
            };

            if left_succ == right_succ {
                let succ_succ = left_succ;
                let mut left_body = self.block_map.remove(&left).unwrap();
                let mut right_body = self.block_map.remove(&right).unwrap();

                let terminator = self
                    .block_map
                    .get_mut(&label)
                    .unwrap()
                    .terminator()
                    .unwrap();
                let cond_value = match terminator {
                    Code::Instruction(Instruction::Effect { args, .. }) => args[0].clone(),
                    _ => panic!(),
                };

                left_body.remove_terminator();
                right_body.remove_terminator();

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(left_body),
                    else_block: Box::new(right_body),
                };

                if succ_succ == left {
                    self.block_map.insert(left.clone(), new_branch);
                    self.merge(label.clone(), left.clone());
                    self.remove_all(&right);
                } else {
                    self.block_map.insert(right.clone(), new_branch);
                    self.merge(label.clone(), right.clone());
                    self.remove_all(&left);
                }
                changed = true;
            } else if left == right_succ {
                let terminator = self
                    .block_map
                    .get_mut(&label)
                    .unwrap()
                    .terminator()
                    .unwrap();
                let cond_value = match terminator {
                    Code::Instruction(Instruction::Effect { args, .. }) => args[0].clone(),
                    _ => panic!(),
                };

                let mut right_body = self.block_map.remove(&right).unwrap();
                right_body.remove_terminator();

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(StructuredCfg::Block(Vec::new())),
                    else_block: Box::new(right_body),
                };

                self.block_map.insert(right.clone(), new_branch);

                self.merge(label, right.clone());

                changed = true;
            } else if right == left_succ {
                let terminator = self
                    .block_map
                    .get_mut(&label)
                    .unwrap()
                    .terminator()
                    .unwrap();
                let cond_value = match terminator {
                    Code::Instruction(Instruction::Effect { args, .. }) => args[0].clone(),
                    _ => panic!(),
                };

                let mut left_body = self.block_map.remove(&left).unwrap();
                left_body.remove_terminator();

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(left_body),
                    else_block: Box::new(StructuredCfg::Block(Vec::new())),
                };

                self.block_map.insert(left.clone(), new_branch);

                self.merge(label, left.clone());

                changed = true;
            }
        }

        changed
    }
}

#[derive(Default, Debug)]
pub struct Cfg {
    block_map: HashMap<Label, Vec<Code>>,
    successors: HashMap<Label, HashSet<Label>>,
    predecessors: HashMap<Label, HashSet<Label>>,
}

impl Cfg {
    pub fn new(codes: &[Code]) -> Self {
        let mut cfg = Self::default();

        let mut current_state = Some((Label::Root, Vec::new()));

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
                        cfg.block_map.insert(current_label.clone(), block);
                        cfg.successors
                            .entry(current_label.clone())
                            .or_default()
                            .insert(Label::Label(label.clone()));
                        cfg.predecessors
                            .entry(Label::Label(label.clone()))
                            .or_default()
                            .insert(current_label.clone());
                    }
                    current_state = Some((Label::Label(label.clone()), vec![code.clone()]));
                }
                Code::Instruction(inst) => match inst {
                    Instruction::Effect { labels, op, .. } => match op {
                        EffectOps::Jump => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(label.clone(), block);
                                cfg.successors
                                    .entry(label.clone())
                                    .or_default()
                                    .insert(Label::Label(labels[0].clone()));
                                cfg.predecessors
                                    .entry(Label::Label(labels[0].clone()))
                                    .or_default()
                                    .insert(label.clone());
                            }
                            current_state = None;
                        }

                        EffectOps::Branch => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(label.clone(), block);
                                cfg.successors
                                    .entry(label.clone())
                                    .or_default()
                                    .insert(Label::Label(labels[0].clone()));
                                cfg.successors
                                    .entry(label.clone())
                                    .or_default()
                                    .insert(Label::Label(labels[1].clone()));
                                cfg.predecessors
                                    .entry(Label::Label(labels[0].clone()))
                                    .or_default()
                                    .insert(label.clone());
                                cfg.predecessors
                                    .entry(Label::Label(labels[1].clone()))
                                    .or_default()
                                    .insert(label.clone());
                            }
                            current_state = None;
                        }

                        EffectOps::Return => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(label, block);
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
            cfg.block_map.insert(label, block);
        }

        cfg
    }

    pub fn merge_linear(&mut self) -> bool {
        let mut changed = false;

        let labels = self.block_map.keys().cloned().collect::<Vec<_>>();

        for label in labels {
            if !self.block_map.contains_key(&label) {
                continue;
            }

            let Some(succ) = self.successors.get(&label) else {
                continue;
            };

            if succ.len() != 1 {
                continue;
            }

            let succ = succ.iter().next().unwrap().clone();

            if self.predecessors[&succ].len() != 1 {
                continue;
            }

            let succ_body = self.block_map.remove(&succ).unwrap();
            let body = self.block_map.get_mut(&label).unwrap();
            body.pop();
            body.extend(succ_body);

            let succ_succ = self.successors.remove(&succ).unwrap_or_default();
            self.successors.insert(label.clone(), succ_succ);
            self.predecessors.remove(&succ);
            changed = true;
        }

        changed
    }

    fn into_structure_cfg_builder(self) -> StructuredCfgBuilder {
        StructuredCfgBuilder {
            block_map: self
                .block_map
                .into_iter()
                .map(|(k, mut v)| {
                    if matches!(v.first(), Some(Code::Label { .. })) {
                        v.remove(0);
                    }

                    (k, StructuredCfg::Block(v))
                })
                .collect(),
            successors: self.successors,
            predecessors: self.predecessors,
        }
    }

    pub fn flatten(&self) -> Vec<Code> {
        let mut codes = self.block_map[&Label::Root].clone();

        for (_, block) in self
            .block_map
            .iter()
            .filter(|(label, _)| label != &&Label::Root)
        {
            codes.extend(block.iter().cloned());
        }

        codes
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
                let mut cfg = Cfg::new(&function.instrs);
                while cfg.merge_linear() {}
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
            .chain(glob("tests/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            for function in &mut program.functions {
                println!("checking {} ... ", path.to_str().unwrap());
                let cfg = Cfg::new(&function.instrs);
                let mut builder = cfg.into_structure_cfg_builder();

                while builder.merge_linear() || builder.merge_branch() {}

                let mut root = builder.block_map.remove(&Label::Root).unwrap();
                root.flatten();

                dbg!(root);
                dbg!(builder);
            }
        }
    }
}
