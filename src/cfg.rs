use std::collections::{HashMap, HashSet};

use bril_rs::{Code, EffectOps, Instruction};
use petgraph::{
    graph::NodeIndex,
    prelude::DiGraph,
    visit::{EdgeRef, IntoEdges, IntoEdgesDirected},
    Graph,
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Label {
    Root,
    Label(String),
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Ret(Option<String>),
    Jmp(NodeIndex),
    Br(String, NodeIndex, NodeIndex),
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
struct StructuredCfgBuilder {
    graph: Graph<StructuredCfg, ()>,
}

impl StructuredCfg {
    fn remove_terminator(&mut self) -> Option<Terminator> {
        match self {
            StructuredCfg::Block(_, t) => t.take(),
            StructuredCfg::Linear(blocks) => blocks.last_mut().unwrap().remove_terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    fn terminator(&self) -> Option<&Terminator> {
        match self {
            StructuredCfg::Block(_, t) => t.as_ref(),
            StructuredCfg::Linear(blocks) => blocks.last().unwrap().terminator(),
            StructuredCfg::Branch { .. } => None,
            StructuredCfg::Loop { .. } => None,
        }
    }

    fn flatten(&mut self) {
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
            _ => {}
        }
    }
}

impl StructuredCfgBuilder {
    fn merge(&mut self, from: NodeIndex, to: NodeIndex) {
        for target in self.graph.edges(to).map(|e| e.target()).collect::<Vec<_>>() {
            self.graph.add_edge(from, target, ());
        }
        self.graph[from].remove_terminator();
        self.graph[from] = StructuredCfg::Linear(vec![
            self.graph[from].clone(),
            self.graph.remove_node(to).unwrap(),
        ]);
    }

    fn merge_linear(&mut self) -> bool {
        for i in self.graph.node_indices() {
            let out = self.graph.edges(i).collect::<Vec<_>>();
            if out.len() != 1 {
                continue;
            }

            let to = out[0].target();

            if self
                .graph
                .edges_directed(to, petgraph::Direction::Incoming)
                .count()
                != 1
            {
                continue;
            }

            if self.graph.edges(to).any(|e| e.target() == to) {
                continue;
            }

            self.merge(i, to);
            return true;
        }
        false
    }

    fn merge_branch(&mut self) -> bool {
        for i in self.graph.node_indices() {
            let out = self.graph.edges(i);

            if out.count() != 2 {
                continue;
            }

            let (left, right) = match self.graph[i].terminator() {
                Some(Terminator::Br(_, left, right)) => (*left, *right),
                _ => panic!(),
            };

            if i == left || i == right {
                continue;
            }

            if self
                .graph
                .edges_directed(left, petgraph::Direction::Incoming)
                .count()
                != 1
            {
                continue;
            }

            if self
                .graph
                .edges_directed(right, petgraph::Direction::Incoming)
                .count()
                != 1
            {
                continue;
            }

            if self.graph.edges(left).count() == 0 && self.graph.edges(right).count() == 0 {
                let left_body = self.graph.remove_node(left).unwrap();
                let right_body = self.graph.remove_node(right).unwrap();

                let terminator = self.graph[i].remove_terminator().unwrap();
                let cond_value = match terminator {
                    Terminator::Br(cond_value, _, _) => cond_value,
                    _ => panic!(),
                };

                let new_branch = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(left_body),
                    else_block: Box::new(right_body),
                };

                self.graph[i] = StructuredCfg::Linear(vec![self.graph[i].clone(), new_branch]);
                self.graph.remove_node(left);
                self.graph.remove_node(right);
                return true;
            }

            let left_succ = {
                let left_succ = self.graph.edges(left).collect::<Vec<_>>();
                if left_succ.len() != 1 {
                    continue;
                }
                left_succ[0].target()
            };

            let right_succ = {
                let right_succ = self.graph.edges(right).collect::<Vec<_>>();
                if right_succ.len() != 1 {
                    continue;
                }
                right_succ[0].target()
            };

            if left_succ == right_succ {
                let succ_succ = left_succ;
                let mut left_body = self.graph.remove_node(left).unwrap();
                let mut right_body = self.graph.remove_node(right).unwrap();

                let terminator = self.graph[i].remove_terminator().unwrap();
                let cond_value = match terminator {
                    Terminator::Br(cond_value, _, _) => cond_value,
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
                    self.graph[left] = new_branch;
                    self.merge(i, left);
                    self.graph.remove_node(right);
                } else {
                    self.graph[right] = new_branch;
                    self.merge(i, right);
                    self.graph.remove_node(left);
                }
                return true;
            } else if left == right_succ {
                let terminator = self.graph[i].remove_terminator().unwrap();
                let cond_value = match terminator {
                    Terminator::Br(cond_value, _, _) => cond_value,
                    _ => panic!(),
                };

                self.graph[right] = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new(StructuredCfg::Block(Vec::new(), None)),
                    else_block: Box::new({
                        self.graph[right].remove_terminator();
                        self.graph[right].clone()
                    }),
                };

                self.merge(i, right);

                return true;
            } else if right == left_succ {
                let terminator = self.graph[i].remove_terminator().unwrap();
                let cond_value = match terminator {
                    Terminator::Br(cond_value, _, _) => cond_value,
                    _ => panic!(),
                };

                self.graph[left] = StructuredCfg::Branch {
                    cond_value,
                    then_block: Box::new({
                        self.graph[left].remove_terminator();
                        self.graph[left].clone()
                    }),
                    else_block: Box::new(StructuredCfg::Block(Vec::new(), None)),
                };

                self.merge(i, left);

                return true;
            }
        }

        false
    }
}

#[derive(Default, Debug)]
pub struct Cfg {
    block_map: HashMap<Label, Vec<Code>>,
    node_map: HashMap<Label, NodeIndex>,
    graph: DiGraph<Label, ()>,
}

impl Cfg {
    pub fn new(codes: &[Code]) -> Self {
        let mut cfg = Self::default();

        let mut current_state = Some((Label::Root, Vec::new()));

        let mut add_edge = |from: Label, to: Label| {
            let from = *cfg
                .node_map
                .entry(from.clone())
                .or_insert_with(|| cfg.graph.add_node(from));
            let to = *cfg
                .node_map
                .entry(to.clone())
                .or_insert_with(|| cfg.graph.add_node(to));
            cfg.graph.add_edge(from, to, ());
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
                        cfg.block_map.insert(current_label.clone(), block);
                        add_edge(current_label.clone(), Label::Label(label.clone()));
                    }
                    current_state = Some((Label::Label(label.clone()), vec![code.clone()]));
                }
                Code::Instruction(inst) => match inst {
                    Instruction::Effect { labels, op, .. } => match op {
                        EffectOps::Jump => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(label.clone(), block);
                                add_edge(label.clone(), Label::Label(labels[0].clone()));
                            }
                            current_state = None;
                        }

                        EffectOps::Branch => {
                            if let Some((label, mut block)) = current_state {
                                block.push(code.clone());
                                cfg.block_map.insert(label.clone(), block);
                                add_edge(label.clone(), Label::Label(labels[0].clone()));
                                add_edge(label.clone(), Label::Label(labels[1].clone()));
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

    fn into_structure_cfg_builder(self) -> StructuredCfgBuilder {
        let mut graph = Graph::new();

        let mut label_map = HashMap::new();
        for label in self.block_map.keys() {
            label_map.insert(
                label.clone(),
                // dummy cfg
                graph.add_node(StructuredCfg::Linear(Vec::new())),
            );
        }

        for (label, mut block) in self.block_map {
            if matches!(block.first(), Some(Code::Label { .. })) {
                block.remove(0);
            }

            let terminator = match block.pop() {
                Some(Code::Instruction(Instruction::Effect {
                    args, labels, op, ..
                })) => match op {
                    EffectOps::Jump => {
                        debug_assert!(labels.len() == 1);
                        Terminator::Jmp(label_map[&Label::Label(labels[0].clone())])
                    }
                    EffectOps::Branch => {
                        debug_assert!(labels.len() == 2);
                        Terminator::Br(
                            args[0].clone(),
                            label_map[&Label::Label(labels[0].clone())],
                            label_map[&Label::Label(labels[1].clone())],
                        )
                    }
                    EffectOps::Return => Terminator::Ret(args.get(0).cloned()),
                    _ => panic!(),
                },
                _ => panic!(),
            };

            graph[label_map[&label]] = StructuredCfg::Block(block, Some(terminator));
        }

        StructuredCfgBuilder { graph }
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
                // while cfg.merge_linear() {}
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

                let mut root = builder
                    .graph
                    .remove_node(builder.graph.node_indices().next().unwrap())
                    .unwrap();
                root.flatten();

                dbg!(root);
                dbg!(builder);
            }
        }
    }
}
