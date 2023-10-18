use crate::{
    cfg::{Cfg, Label},
    graph::{dominants_sub, scc_sub},
};
use bimap::BiMap;
use bril_rs::{Code, ConstOps, Instruction, Literal, Type, ValueOps};
use petgraph::{prelude::DiGraphMap, Direction};
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display, Formatter},
};

struct RestructuredCfg {
    block_map: HashMap<usize, Vec<Code>>,
    graph: DiGraphMap<usize, ()>,
    label_map: BiMap<Label, usize>,
    loop_edge: DiGraphMap<usize, ()>,
    label_counter: usize,
}

// Structured Code has an instruction which is not valid in original Bril
// br x .label1 .label2 .label3 ...
// This instruction act as a switch statement and x maybe an int (which isn't valid in Bril)
#[derive(Debug, Clone)]
/// Structured control flow
pub enum StructureAnalysis {
    Block(Vec<Code>),
    Linear(Vec<StructureAnalysis>),
    // loop variable is always StructureAnalysis::VAR_R
    Loop(Box<StructureAnalysis>),
    Branch(String, Vec<StructureAnalysis>),
}

impl Display for StructureAnalysis {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        self.display_impl(1, fmt)
    }
}

impl StructureAnalysis {
    // Those must not be used in the original cfg
    pub const VAR_Q: &'static str = "__var_q";
    pub const VAR_R: &'static str = "__var_r";
    pub const VAR_P: &'static str = "__var_p";

    fn display_impl(&self, indent_level: usize, fmt: &mut Formatter) -> fmt::Result {
        let tab = " ".repeat(indent_level * 2);
        let ctab = " ".repeat(indent_level * 2 - 2);

        match self {
            StructureAnalysis::Block(codes) => {
                for code in codes.iter() {
                    writeln!(fmt, "{}{}", ctab, code)?;
                }
            }
            StructureAnalysis::Linear(ss) => {
                for s in ss {
                    s.display_impl(indent_level, fmt)?;
                }
            }
            StructureAnalysis::Loop(s) => {
                writeln!(fmt, "{}do {{", tab)?;
                s.display_impl(indent_level + 1, fmt)?;
                writeln!(fmt, "{}}} while({});", tab, Self::VAR_R)?;
            }
            StructureAnalysis::Branch(cond_var, ss) => match cond_var.as_str() {
                Self::VAR_P | Self::VAR_Q | Self::VAR_R => {
                    writeln!(fmt, "{}switch ({}) {{", tab, cond_var)?;
                    for (i, s) in ss.iter().enumerate() {
                        writeln!(fmt, "{}  case {}: {{", tab, i)?;
                        s.display_impl(indent_level + 2, fmt)?;
                        writeln!(fmt, "{}  }}", tab)?;
                    }
                    writeln!(fmt, "{}}}", tab)?;
                }
                _ => {
                    assert!(ss.len() == 2);
                    writeln!(fmt, "{}if ({}) {{", tab, cond_var)?;
                    ss[0].display_impl(indent_level + 1, fmt)?;
                    writeln!(fmt, "{}}} else {{", tab)?;
                    ss[1].display_impl(indent_level + 1, fmt)?;
                    writeln!(fmt, "{}}}", tab)?;
                }
            },
        }

        Ok(())
    }

    fn clean(&mut self) {
        match self {
            StructureAnalysis::Block(codes) => {
                codes.retain(|code| match code {
                    Code::Instruction(Instruction::Effect { op, .. }) => {
                        op != &bril_rs::EffectOps::Jump && op != &bril_rs::EffectOps::Branch
                    }
                    Code::Label { .. } => false,
                    _ => true,
                });
            }
            StructureAnalysis::Linear(ss) => {
                let mut new_linear = Vec::new();
                for s in ss {
                    s.clean();

                    match s {
                        Self::Block(codes) => {
                            if !codes.is_empty() {
                                match new_linear.last_mut() {
                                    Some(StructureAnalysis::Block(last_codes)) => {
                                        last_codes.extend(codes.iter().cloned());
                                    }
                                    _ => new_linear.push(s.clone()),
                                }
                            }
                        }
                        Self::Linear(ss) => {
                            for s in ss {
                                match s {
                                    Self::Block(codes) => match new_linear.last_mut() {
                                        Some(StructureAnalysis::Block(last_codes)) => {
                                            codes.extend(last_codes.iter().cloned());
                                        }
                                        _ => new_linear.push(s.clone()),
                                    },
                                    _ => new_linear.push(s.clone()),
                                }
                            }
                        }
                        _ => new_linear.push(s.clone()),
                    }
                }
                *self = StructureAnalysis::Linear(new_linear);
            }
            StructureAnalysis::Loop(s) => {
                s.clean();
            }
            StructureAnalysis::Branch(_, ss) => {
                for s in ss {
                    s.clean();
                }
            }
        }
    }

    // Make EffectOps has its own block to Rvsdg
    pub(crate) fn split_effect(&mut self) {
        match self {
            StructureAnalysis::Block(codes) => {
                let mut new_block = Vec::new();

                let mut current_block = Vec::new();

                for code in codes {
                    let code = code.clone();
                    match code {
                        Code::Instruction(Instruction::Effect { .. }) => {
                            if !current_block.is_empty() {
                                new_block.push(current_block);
                                current_block = Vec::new();
                            }

                            new_block.push(vec![code]);
                        }
                        Code::Instruction(Instruction::Value {
                            op: ValueOps::Call, ..
                        }) => {
                            if !current_block.is_empty() {
                                new_block.push(current_block);
                                current_block = Vec::new();
                            }

                            new_block.push(vec![code]);
                        }
                        _ => {
                            current_block.push(code);
                        }
                    }
                }

                if !current_block.is_empty() {
                    new_block.push(current_block);
                }

                if new_block.len() == 1 {
                    *self = StructureAnalysis::Block(new_block.pop().unwrap());
                } else {
                    *self = StructureAnalysis::Linear(
                        new_block
                            .into_iter()
                            .map(StructureAnalysis::Block)
                            .collect(),
                    );
                }
            }
            StructureAnalysis::Linear(ss) => {
                for s in ss {
                    s.split_effect();
                }
            }
            StructureAnalysis::Loop(s) => {
                s.split_effect();
            }
            StructureAnalysis::Branch(_, ss) => {
                for s in ss {
                    s.split_effect();
                }
            }
        }
    }

    pub fn new(cfg: Cfg) -> Self {
        RestructuredCfg::new(cfg).structure_analysis()
    }
}

impl RestructuredCfg {
    fn new(cfg: Cfg) -> Self {
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
            dest: StructureAnalysis::VAR_P.to_string(),
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

        let (single_entry, entry_index) = if !entry_vs.is_empty() {
            let mut entries = entry_vs.iter().copied().collect::<Vec<_>>();
            entries.sort();
            let entry_index = entries
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i))
                .collect::<HashMap<_, _>>();

            if entries.len() == 1 {
                (entries[0], entry_index)
            } else {
                let fan_v = self.add_fan_node(StructureAnalysis::VAR_Q, &entries);

                // Update incoming edges to entries
                for (from, to) in entry_arcs {
                    let code = Code::Instruction(Instruction::Constant {
                        dest: StructureAnalysis::VAR_Q.to_string(),
                        op: bril_rs::ConstOps::Const,
                        const_type: bril_rs::Type::Int,
                        value: bril_rs::Literal::Int(entry_index[&to] as i64),
                    });
                    let codes = self.block_map.get_mut(&from).unwrap();
                    codes.insert(codes.len() - 1, code);
                    self.replace_edge(from, to, fan_v);
                }
                (fan_v, entry_index)
            }
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

        let exit_fan = self.add_fan_node(StructureAnalysis::VAR_Q, &exits);
        let single_exit = self.add_fan_node(StructureAnalysis::VAR_R, &[exit_fan, single_entry]);

        for (from, to) in repetition_arcs {
            let code0 = Code::Instruction(Instruction::Constant {
                dest: StructureAnalysis::VAR_Q.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(entry_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: StructureAnalysis::VAR_R.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Bool,
                value: bril_rs::Literal::Bool(true),
            });

            let codes = self.block_map.get_mut(&from).unwrap();
            if entry_index.len() > 1 {
                codes.insert(codes.len() - 1, code0);
            }
            codes.insert(codes.len() - 1, code1);
            self.replace_edge(from, to, single_exit);
        }

        for (from, to) in exit_arcs {
            let code0 = Code::Instruction(Instruction::Constant {
                dest: StructureAnalysis::VAR_Q.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Int,
                value: bril_rs::Literal::Int(exit_index[&to] as i64),
            });
            let code1 = Code::Instruction(Instruction::Constant {
                dest: StructureAnalysis::VAR_R.to_string(),
                op: bril_rs::ConstOps::Const,
                const_type: bril_rs::Type::Bool,
                value: bril_rs::Literal::Bool(false),
            });
            let codes = self.block_map.get_mut(&from).unwrap();
            if exit_index.len() > 1 {
                codes.insert(codes.len() - 1, code0);
            }
            codes.insert(codes.len() - 1, code1);
            self.replace_edge(from, to, single_exit);
        }

        self.graph.remove_edge(single_exit, single_entry);
        self.loop_edge.add_edge(single_exit, single_entry, ());
    }

    fn loop_restructure_rec(&mut self, sub_vs: &HashSet<usize>) {
        for sc in scc_sub(&self.graph, sub_vs) {
            if sc.len() > 1 || sc.iter().any(|&v| self.graph.neighbors(v).any(|s| s == v)) {
                self.loop_restructure_impl(&sc);
                self.loop_restructure_rec(&sc);
            }
        }
    }

    fn loop_restructure(&mut self) {
        self.loop_restructure_rec(&self.graph.nodes().collect());
    }

    // Call this after loop_restructure
    // graph's now a DAG
    fn branch_restructure_rec(&mut self, start: usize, sub_vs: &HashSet<usize>) {
        let mut node = start;

        while sub_vs.contains(&node) {
            let succs = self.graph.neighbors(node).collect::<Vec<_>>();

            if succs.is_empty() {
                break;
            }

            if succs.len() == 1 {
                node = succs[0];
                continue;
            }

            // brnach
            let dominants = succs
                .into_iter()
                .map(|s| (s, dominants_sub(s, &self.graph, sub_vs)))
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
                                    dest == StructureAnalysis::VAR_P
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

            if continuation_points.is_empty() {
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

            let fan_v = self.add_fan_node(StructureAnalysis::VAR_P, &continuation_points_array);

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
            node = fan_v;
        }
    }

    fn branch_restructure(&mut self) {
        self.branch_restructure_rec(0, &self.graph.nodes().collect());
    }

    fn restructure(&mut self) {
        self.loop_restructure();
        self.branch_restructure();
    }

    fn structure_rec(&self, start: &mut usize) -> StructureAnalysis {
        let mut linear = Vec::new();
        let mut last_exit_branch = false;

        loop {
            if self.loop_edge.neighbors(*start).count() > 0
                || (self
                    .graph
                    .neighbors_directed(*start, Direction::Incoming)
                    .count()
                    > 1
                    && !last_exit_branch)
            {
                break;
            }
            last_exit_branch = false;

            let succs = self.graph.neighbors(*start).collect::<Vec<_>>();

            let s0 = StructureAnalysis::Block(self.block_map.get(start).unwrap().clone());

            if succs.is_empty() {
                linear.push(s0);
                break;
            }

            let is_loop_entry = self
                .loop_edge
                .neighbors_directed(*start, Direction::Incoming)
                .count()
                > 0;
            let s = if succs.len() == 1 {
                if is_loop_entry {
                    *start = succs[0];

                    StructureAnalysis::Linear(vec![s0, self.structure_rec(start)])
                } else {
                    *start = succs[0];
                    s0
                }
            } else {
                last_exit_branch = true;
                let (cond_var, branch_labels) =
                    match self.block_map.get(start).unwrap().last().unwrap() {
                        Code::Instruction(Instruction::Effect { labels, args, .. }) => {
                            (&args[0], labels)
                        }
                        _ => unreachable!(),
                    };

                let branches: Vec<_> = branch_labels
                    .iter()
                    .map(|l| {
                        let mut v = *self
                            .label_map
                            .get_by_left(&Label::Label(l.clone()))
                            .unwrap();
                        let s = self.structure_rec(&mut v);
                        (v, s)
                    })
                    .collect();

                // debug_assert!(branches.iter().all(|(v, _)| *v == branches[0].0));
                *start = branches[0].0;
                StructureAnalysis::Linear(vec![
                    s0,
                    StructureAnalysis::Branch(
                        cond_var.clone(),
                        branches.into_iter().map(|(_, s)| s).collect(),
                    ),
                ])
            };

            if is_loop_entry {
                linear.push(StructureAnalysis::Loop(Box::new(s)));
                // now on loop exit
                debug_assert!(self.loop_edge.neighbors(*start).count() == 1);
                *start = self.graph.neighbors(*start).next().unwrap();
            } else {
                linear.push(s);
            }
        }

        if linear.len() == 1 {
            linear.pop().unwrap()
        } else {
            StructureAnalysis::Linear(linear)
        }
    }

    fn structure_analysis(&mut self) -> StructureAnalysis {
        self.restructure();
        let mut start = *self.label_map.get_by_left(&Label::Root).unwrap();
        let mut sa = self.structure_rec(&mut start);
        sa.clean();
        sa
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::*;
    use glob::glob;
    use std::io::Cursor;

    fn show_graph(graph: &DiGraphMap<usize, ()>, label_map: &BiMap<Label, usize>) {
        for n in graph.nodes() {
            println!("{}: ", label_map.get_by_right(&n).unwrap());
            for s in graph.neighbors(n) {
                println!("  -> {}", label_map.get_by_right(&s).unwrap());
            }
        }
    }

    #[test]
    // At least no panic
    fn test_restructure() {
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
                // dbg!(&cfg.graph);
                let mut r = RestructuredCfg::new(cfg);
                r.restructure();

                show_graph(&r.graph, &r.label_map);
                eprintln!("loop:");
                show_graph(&r.loop_edge, &r.label_map);
                // dbg!(&r.graph);
                // dbg!(&r.loop_edge);
            }
        }
    }

    #[test]
    fn test_structure_analysis() {
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

                let sa = StructureAnalysis::new(cfg);
                eprintln!("{}", &sa);

                dbg!(sa);
            }
        }
    }
}
