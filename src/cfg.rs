use std::collections::{HashMap, HashSet};

use bril_rs::{Code, EffectOps, Instruction};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Label {
    Root,
    Label(String),
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
                    if let Some((label, block)) = current_state {
                        cfg.block_map.insert(label, block);
                    }
                    current_state = Some((Label::Label(label.clone()), Vec::new()));
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

        if let Some((label, block)) = current_state {
            cfg.block_map.insert(label, block);
        }

        cfg
    }
}
