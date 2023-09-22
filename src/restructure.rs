use crate::{
    cfg::{Cfg, Label},
    graph::scc,
};
use bimap::BiMap;
use bril_rs::{Code, Instruction};
use petgraph::prelude::DiGraphMap;
use std::collections::{HashMap, HashSet};

pub struct RestructuredCfg {
    block_map: HashMap<usize, Vec<Code>>,
    graph: DiGraphMap<usize, ()>,
    label_map: BiMap<Label, usize>,
    loop_edge: DiGraphMap<usize, ()>,
    var_counter: usize,
}

impl RestructuredCfg {
    pub fn new(cfg: Cfg) -> Self {
        let loop_edge = DiGraphMap::new();
        Self {
            block_map: cfg.block_map,
            graph: cfg.graph,
            label_map: cfg.label_map.into_iter().collect(),
            loop_edge,
            var_counter: 0,
        }
    }

    fn new_var(&mut self) -> String {
        let name = format!("__var_{}", self.var_counter);
        self.var_counter += 1;
        name
    }

    fn new_label(&mut self) -> usize {
        let name = format!("__label_{}", self.var_counter);
        self.var_counter += 1;
        let v = self.label_map.len();
        self.label_map.insert(Label::Label(name.clone()), v);

        v
    }

    fn add_fan_node(&mut self, vs: &[usize]) -> (usize, String) {
        let fan_v = self.new_label();
        let cond_var = self.new_var();

        let code = Code::Instruction(Instruction::Effect {
            args: vec![cond_var.clone()],
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

        (fan_v, cond_var)
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

        let (single_entry, entry_cond_var, entry_index) = if entry_vs.len() > 0 {
            let mut entries = entry_vs.iter().copied().collect::<Vec<_>>();
            entries.sort();
            let entry_index = entries
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i))
                .collect::<HashMap<_, _>>();

            let (fan_v, fan_cond_var) = self.add_fan_node(&entries);

            // Update incoming edges to entries
            for (from, to) in entry_arcs {
                let code = Code::Instruction(Instruction::Constant {
                    dest: fan_cond_var.clone(),
                    op: bril_rs::ConstOps::Const,
                    const_type: bril_rs::Type::Int,
                    value: bril_rs::Literal::Int(entry_index[&to] as i64),
                });
                let codes = self.block_map.get_mut(&from).unwrap();
                codes.insert(codes.len() - 1, code);
                self.replace_edge(from, to, fan_v);
            }
            (fan_v, fan_cond_var, entry_index)
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

        let (exit_fan, exit_fan_cond_var) = self.add_fan_node(&exits);
        let (single_exit, exit_cond_var) = self.add_fan_node(&[exit_fan, single_entry]);

        for (from, to) in repetition_arcs {
            let code0 = Code::Instruction(Instruction::Constant {
                dest: entry_cond_var.clone(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(entry_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: exit_cond_var.clone(),
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
                dest: exit_fan_cond_var.clone(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(exit_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: exit_cond_var.clone(),
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

    pub fn loop_restructure(&mut self) {
        loop {
            let scs = scc(&self.graph);
            let mut changed = false;

            for sc in scs {
                if sc.len() > 1 {
                    self.loop_restructure_impl(&sc);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
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
