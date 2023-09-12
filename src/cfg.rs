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
                    if let Some((current_label, mut block)) = current_state {
                        block.push(Code::Instruction(Instruction::Effect {
                            args: Vec::new(),
                            funcs: Vec::new(),
                            labels: vec![label.clone()],
                            op: EffectOps::Jump,
                        }));
                        cfg.block_map.insert(current_label, block);
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
}
