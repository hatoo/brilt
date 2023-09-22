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

    fn new_label(&mut self) -> (String, usize) {
        let name = format!("__label_{}", self.var_counter);
        self.var_counter += 1;
        let v = self.label_map.len();
        self.label_map.insert(Label::Label(name.clone()), v);

        (name, v)
    }

    fn add_fan_node(&mut self, vs: &[usize]) -> (String, usize, String) {
        let (fan_label, fan_v) = self.new_label();
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

        (fan_label, fan_v, cond_var)
    }

    fn loop_reconstruct_impl(&mut self, vs: &HashSet<usize>) {
        let entry_arcs = vs
            .iter()
            .flat_map(|&v| self.graph.edges_directed(v, petgraph::Direction::Incoming))
            .map(|e| (e.0, e.1))
            .filter(|e| !vs.contains(&e.0))
            .collect::<HashSet<_>>();
        let entry_vs = entry_arcs.iter().map(|e| e.1).collect::<HashSet<_>>();
        let exit_arcs = vs
            .iter()
            .flat_map(|&v| self.graph.edges_directed(v, petgraph::Direction::Outgoing))
            .map(|e| (e.0, e.1))
            .filter(|e| !vs.contains(&e.1))
            .collect::<HashSet<_>>();
        let exit_vs = exit_arcs.iter().map(|e| e.1).collect::<HashSet<_>>();
        let repetition_arcs = entry_vs
            .iter()
            .flat_map(|&e| self.graph.edges_directed(e, petgraph::Direction::Incoming))
            .map(|e| (e.0, e.1))
            .filter(|e| vs.contains(&e.0))
            .collect::<HashSet<_>>();

        if entry_vs.len() > 1 {
            let mut entries = entry_vs.iter().copied().collect::<Vec<_>>();
            entries.sort();

            let (fan_label, fan_v, fan_cond_var) = self.add_fan_node(&entries);
        }

        todo!()
    }

    pub fn loop_reconstruct(&mut self) {
        loop {
            let scs = scc(&self.graph);
            let mut changed = false;

            for sc in scs {
                if sc.len() > 1 {
                    self.loop_reconstruct_impl(&sc);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }
}
