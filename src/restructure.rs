use crate::{
    cfg::{Cfg, Label},
    graph::scc_sub,
};
use bimap::BiMap;
use bril_rs::{Code, ConstOps, Instruction, Literal, Type};
use petgraph::{prelude::DiGraphMap, Direction};
use std::collections::{HashMap, HashSet};

pub struct RestructuredCfg {
    block_map: HashMap<usize, Vec<Code>>,
    graph: DiGraphMap<usize, ()>,
    label_map: BiMap<Label, usize>,
    loop_edge: DiGraphMap<usize, ()>,
    label_counter: usize,
}

impl RestructuredCfg {
    // Those must not be used in the original cfg
    const VAR_Q: &'static str = "__var_q";
    const VAR_R: &'static str = "__var_r";
    const VAR_P: &'static str = "__var_p";

    pub fn new(cfg: Cfg) -> Self {
        let loop_edge = DiGraphMap::new();
        Self {
            block_map: cfg.block_map,
            graph: cfg.graph,
            label_map: cfg.label_map.into_iter().collect(),
            loop_edge,
            label_counter: 0,
        }
    }

    fn new_label(&mut self) -> usize {
        let name = format!("__label_{}", self.label_counter);
        self.label_counter += 1;
        let v = self.label_map.len();
        self.label_map.insert(Label::Label(name.clone()), v);

        v
    }

    fn add_fan_node(&mut self, cond_var: &str, vs: &[usize]) -> usize {
        let fan_v = self.new_label();

        let code = Code::Instruction(Instruction::Effect {
            args: vec![cond_var.to_string()],
            funcs: vec![],
            labels: vs
                .iter()
                .map(|v| self.label_map.get_by_right(v).unwrap().clone())
                .map(|l| match l {
                    Label::Label(s) => s,
                    _ => unreachable!(),
                })
                .collect(),
            op: bril_rs::EffectOps::Branch,
        });

        self.block_map.insert(fan_v, vec![code]);

        for to in vs {
            self.graph.add_edge(fan_v, *to, ());
        }

        fan_v
    }

    fn new_null_node(&mut self) -> usize {
        let v = self.new_label();
        self.block_map.insert(v, vec![]);
        v
    }

    fn new_goto_node(&mut self, to_index: usize, to: usize) -> usize {
        let v = self.new_label();
        let code = Code::Instruction(Instruction::Constant {
            dest: Self::VAR_P.to_string(),
            op: ConstOps::Const,
            const_type: Type::Int,
            value: Literal::Int(to_index as i64),
        });
        self.block_map.insert(v, vec![code]);
        self.graph.add_edge(v, to, ());
        v
    }

    fn replace_edge(&mut self, from: usize, old_to: usize, new_to: usize) {
        let codes = self.block_map.get_mut(&from).unwrap();
        let old_to_label = self
            .label_map
            .get_by_right(&old_to)
            .unwrap()
            .label()
            .unwrap();
        let new_to_label = self
            .label_map
            .get_by_right(&new_to)
            .unwrap()
            .label()
            .unwrap();
        match codes.last_mut().unwrap() {
            Code::Instruction(Instruction::Effect { labels, .. }) => {
                for l in labels.iter_mut() {
                    if l == old_to_label {
                        *l = new_to_label.to_string();
                    }
                }
            }
            _ => unreachable!(),
        }

        self.graph.remove_edge(from, old_to);
        self.graph.add_edge(from, new_to, ());
    }

    fn loop_restructure_impl(&mut self, vs: &HashSet<usize>) {
        let entry_arcs = vs
            .iter()
            .flat_map(|&v| self.graph.edges_directed(v, petgraph::Direction::Incoming))
            .map(|e| (e.0, e.1))
            .filter(|e| !vs.contains(&e.0))
            .collect::<HashSet<_>>();
        let entry_vs = entry_arcs.iter().map(|e| e.1).collect::<HashSet<_>>();
        let repetition_arcs = entry_vs
            .iter()
            .flat_map(|&e| self.graph.edges_directed(e, petgraph::Direction::Incoming))
            .map(|e| (e.0, e.1))
            .filter(|e| vs.contains(&e.0))
            .collect::<HashSet<_>>();
        let exit_arcs = vs
            .iter()
            .flat_map(|&v| self.graph.edges_directed(v, petgraph::Direction::Outgoing))
            .map(|e| (e.0, e.1))
            .filter(|e| !vs.contains(&e.1))
            .collect::<HashSet<_>>();
        let exit_vs = exit_arcs.iter().map(|e| e.1).collect::<HashSet<_>>();

        let (single_entry, entry_index) = if entry_vs.len() > 0 {
            let mut entries = entry_vs.iter().copied().collect::<Vec<_>>();
            entries.sort();
            let entry_index = entries
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i))
                .collect::<HashMap<_, _>>();

            let fan_v = self.add_fan_node(Self::VAR_Q, &entries);

            // Update incoming edges to entries
            for (from, to) in entry_arcs {
                let code = Code::Instruction(Instruction::Constant {
                    dest: Self::VAR_Q.to_string(),
                    op: bril_rs::ConstOps::Const,
                    const_type: bril_rs::Type::Int,
                    value: bril_rs::Literal::Int(entry_index[&to] as i64),
                });
                let codes = self.block_map.get_mut(&from).unwrap();
                codes.insert(codes.len() - 1, code);
                self.replace_edge(from, to, fan_v);
            }
            (fan_v, entry_index)
        } else {
            // dead codes
            for &v in vs {
                self.graph.remove_node(v);
            }
            return;
        };

        let mut exits = exit_vs.iter().copied().collect::<Vec<_>>();
        exits.sort();
        let exit_index = exits
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, i))
            .collect::<HashMap<_, _>>();

        let exit_fan = self.add_fan_node(Self::VAR_Q, &exits);
        let single_exit = self.add_fan_node(Self::VAR_R, &[exit_fan, single_entry]);

        for (from, to) in repetition_arcs {
            let code0 = Code::Instruction(Instruction::Constant {
                dest: Self::VAR_Q.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(entry_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: Self::VAR_R.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Bool,
                value: bril_rs::Literal::Bool(true),
            });

            let codes = self.block_map.get_mut(&from).unwrap();
            codes.insert(codes.len() - 1, code0);
            codes.insert(codes.len() - 1, code1);
            self.replace_edge(from, to, single_exit);
        }

        for (from, to) in exit_arcs {
            let code0 = Code::Instruction(Instruction::Constant {
                dest: Self::VAR_Q.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(exit_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: Self::VAR_R.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Bool,
                value: bril_rs::Literal::Bool(false),
            });
            let codes = self.block_map.get_mut(&from).unwrap();
            codes.insert(codes.len() - 1, code0);
            codes.insert(codes.len() - 1, code1);
            self.replace_edge(from, to, exit_fan);
        }

        self.graph.remove_edge(single_exit, single_entry);
        self.loop_edge.add_edge(single_exit, single_entry, ());
    }

    fn loop_restructure_rec(&mut self, sub_vs: &HashSet<usize>) {
        for sc in scc_sub(&self.graph, sub_vs) {
            if sc.len() > 1 {
                self.loop_restructure_impl(&sc);
                self.loop_restructure_rec(&sc);
            }
        }
    }

    pub fn loop_restructure(&mut self) {
        self.loop_restructure_rec(&self.graph.nodes().collect());
    }

    // Assume graph's a DAG
    fn dominants(&self, node: usize, sub_vs: &HashSet<usize>) -> HashSet<usize> {
        let mut dominants = HashSet::new();
        dominants.insert(node);

        let mut stack = vec![node];

        while let Some(v) = stack.pop() {
            for n in self.graph.neighbors(v) {
                if sub_vs.contains(&n) {
                    dominants.insert(n);
                    stack.push(n);
                }
            }
        }

        dominants
    }

    // Call this after loop_restructure
    // graph's now a DAG
    fn branch_restructure_rec(&mut self, start: usize, sub_vs: &HashSet<usize>) {
        let mut node = start;

        while sub_vs.contains(&node) {
            let succs = self.graph.neighbors(node).collect::<Vec<_>>();

            if succs.len() == 0 {
                break;
            }

            if succs.len() == 1 {
                node = succs[0];
                continue;
            }

            // brnach
            let dominants = succs
                .into_iter()
                .map(|s| (s, self.dominants(s, sub_vs)))
                .collect::<Vec<_>>();

            let tails = dominants.iter().fold(HashSet::new(), |acc, (_, d)| {
                acc.intersection(d).copied().collect()
            });

            let branches = dominants
                .iter()
                .map(|(s, d)| (*s, d.difference(&tails).copied().collect::<HashSet<_>>()))
                .collect::<Vec<_>>();

            let continuation_points: HashSet<usize> = branches
                .iter()
                .flat_map(|(_, b)| {
                    b.iter()
                        .flat_map(|&d| self.graph.neighbors(d))
                        .filter(|s| tails.contains(s))
                })
                .collect();

            let succ_of_aux = continuation_points.iter().filter(|&&c| {
                self.graph
                    .neighbors_directed(c, Direction::Incoming)
                    .any(|p| {
                        self.block_map
                            .get(&p)
                            .and_then(|codes| codes.last())
                            .map(|code| match code {
                                Code::Instruction(Instruction::Constant { dest, .. }) => {
                                    dest == Self::VAR_P
                                }
                                _ => false,
                            })
                            == Some(true)
                    })
            });

            let pull: HashSet<usize> = succ_of_aux
                .into_iter()
                .filter_map(|&n| {
                    let preds = self
                        .graph
                        .neighbors_directed(n, Direction::Incoming)
                        .collect::<HashSet<_>>();
                    if !branches
                        .iter()
                        .any(|(_, b)| preds.iter().all(|p| b.contains(p)))
                    {
                        Some(preds)
                    } else {
                        None
                    }
                })
                .flatten()
                .collect();

            let continuation_points = continuation_points
                .union(&pull)
                .copied()
                .collect::<HashSet<_>>();

            let branches = branches
                .into_iter()
                .map(|(s, b)| (s, b.difference(&pull).copied().collect::<HashSet<_>>()))
                .collect::<Vec<_>>();

            drop(dominants);
            drop(tails);

            if continuation_points.len() == 0 {
                let null_node = self.new_null_node();

                for (_, b) in branches {
                    for n in b {
                        if self.graph.neighbors(n).count() == 0 {
                            self.graph.add_edge(n, null_node, ());
                        }
                    }
                }
                return;
            }

            if continuation_points.len() == 1 {
                node = *continuation_points.iter().next().unwrap();
                continue;
            }

            let mut continuation_points_array =
                continuation_points.iter().copied().collect::<Vec<_>>();
            continuation_points_array.sort();
            let continuation_index = continuation_points_array
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i))
                .collect::<HashMap<_, _>>();

            let fan_v = self.add_fan_node(Self::VAR_P, &continuation_points_array);

            for (branch_start, mut b) in branches.into_iter().filter(|(_, b)| !b.is_empty()) {
                let null_node = self.new_null_node();
                self.graph.add_edge(null_node, fan_v, ());

                let mut added = Vec::new();

                for &n in b.iter() {
                    for c in self
                        .graph
                        .neighbors(n)
                        .filter(|s| continuation_points.contains(s))
                        .collect::<Vec<_>>()
                    {
                        let goto_c = self.new_goto_node(continuation_index[&c], null_node);
                        self.replace_edge(n, c, goto_c);
                        added.push(goto_c)
                    }
                }

                b.insert(null_node);
                b.extend(added);

                self.branch_restructure_rec(branch_start, &b);
            }

            for c in self
                .graph
                .neighbors(node)
                .filter(|s| continuation_points.contains(s))
                .collect::<Vec<_>>()
            {
                let goto_c = self.new_goto_node(continuation_index[&c], fan_v);
                self.replace_edge(node, c, goto_c);
            }
        }
    }

    pub fn branch_restructure(&mut self) {
        self.branch_restructure_rec(0, &self.graph.nodes().collect());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::*;
    use glob::glob;
    use std::io::Cursor;

    #[test]
    // At least no panic
    fn test_loop_restructure() {
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
                dbg!(&cfg.graph);
                let mut r = RestructuredCfg::new(cfg);
                r.loop_restructure();

                dbg!(&r.graph);
                dbg!(&r.loop_edge);
            }
        }
    }
}
