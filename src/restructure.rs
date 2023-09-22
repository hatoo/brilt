use std::collections::HashSet;

use petgraph::prelude::DiGraphMap;

use crate::{cfg::Cfg, graph::scc};

pub struct RestructuredCfg {
    cfg: Cfg,
    loop_edge: DiGraphMap<usize, ()>,
}

impl RestructuredCfg {
    pub fn new(cfg: Cfg) -> Self {
        let loop_edge = DiGraphMap::new();
        Self { cfg, loop_edge }
    }

    fn loop_reconstruct_impl(&mut self, vs: &HashSet<usize>) {
        todo!()
    }

    pub fn loop_reconstruct(&mut self) {
        loop {
            let scs = scc(&self.cfg.graph);
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
