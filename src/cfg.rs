use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

use bril_rs::{Code, EffectOps, Instruction};
use petgraph::prelude::DiGraphMap;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Label {
    Root,
    Label(String),
}

impl Display for Label {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Root => write!(f, "root"),
            Self::Label(s) => write!(f, "{}", s),
        }
    }
}

impl Label {
    pub fn label(&self) -> Option<&str> {
        match self {
            Self::Root => None,
            Self::Label(s) => Some(s),
        }
    }
}

#[derive(Default, Debug)]
/// Control flow graph
pub struct Cfg {
    pub block_map: HashMap<usize, Vec<Code>>,
    pub graph: DiGraphMap<usize, ()>,
    pub label_map: HashMap<Label, usize>,
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

    pub fn flatten(&self) -> Vec<Code> {
        let mut codes = self.block_map[&0].clone();

        for (_, block) in self.block_map.iter().filter(|(&label, _)| label != 0) {
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
        for entry in glob("bril/examples/test/df/*.bril").unwrap() {
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
}
