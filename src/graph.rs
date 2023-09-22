use petgraph::graphmap::NodeTrait;
use petgraph::prelude::DiGraphMap;
use std::collections::HashSet;

pub fn scc<N: Eq + NodeTrait, E>(graph: &DiGraphMap<N, E>) -> Vec<HashSet<N>> {
    fn dfs<N: Eq + NodeTrait, E>(
        graph: &DiGraphMap<N, E>,
        used: &mut HashSet<N>,
        visited: &mut Vec<N>,
        v: N,
    ) {
        used.insert(v);
        for n in graph.neighbors(v) {
            if !used.contains(&n) {
                dfs(graph, used, visited, n);
            }
        }
        visited.push(v);
    }

    fn rdfs<N: Eq + NodeTrait, E>(
        graph: &DiGraphMap<N, E>,
        used: &mut HashSet<N>,
        set: &mut HashSet<N>,
        v: N,
    ) {
        used.insert(v);
        set.insert(v);
        for n in graph.neighbors_directed(v, petgraph::Direction::Incoming) {
            if !used.contains(&n) {
                rdfs(graph, used, set, n);
            }
        }
    }

    let mut used = HashSet::new();
    let mut visited = Vec::new();

    for v in graph.nodes() {
        if !used.contains(&v) {
            dfs(graph, &mut used, &mut visited, v);
        }
    }

    used.clear();

    visited
        .iter()
        .rev()
        .flat_map(|&v| {
            if !used.contains(&v) {
                let mut set = HashSet::new();
                rdfs(graph, &mut used, &mut set, v);
                Some(set)
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn test_scc() {
    let mut graph = DiGraphMap::new();
    graph.add_edge(0, 1, ());
    graph.add_edge(1, 2, ());
    graph.add_edge(2, 3, ());
    graph.add_edge(3, 1, ());

    let mut scc = scc(&graph);
    scc.sort_by_key(|s| s.len());

    assert_eq!(scc[0], HashSet::from_iter(vec![0]));
    assert_eq!(scc[1], HashSet::from_iter(vec![1, 2, 3]));
}
