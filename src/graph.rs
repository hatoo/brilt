use petgraph::graphmap::NodeTrait;
use petgraph::prelude::DiGraphMap;
use std::collections::HashSet;

pub fn scc_sub<N: Eq + NodeTrait, E>(
    graph: &DiGraphMap<N, E>,
    sub_vs: &HashSet<N>,
) -> Vec<HashSet<N>> {
    fn dfs<N: Eq + NodeTrait, E>(
        graph: &DiGraphMap<N, E>,
        used: &mut HashSet<N>,
        visited: &mut Vec<N>,
        sub_vs: &HashSet<N>,
        v: N,
    ) {
        used.insert(v);
        for n in graph.neighbors(v) {
            if !used.contains(&n) && sub_vs.contains(&n) {
                dfs(graph, used, visited, sub_vs, n);
            }
        }
        visited.push(v);
    }

    fn rdfs<N: Eq + NodeTrait, E>(
        graph: &DiGraphMap<N, E>,
        used: &mut HashSet<N>,
        set: &mut HashSet<N>,
        sub_vs: &HashSet<N>,
        v: N,
    ) {
        used.insert(v);
        set.insert(v);
        for n in graph.neighbors_directed(v, petgraph::Direction::Incoming) {
            if !used.contains(&n) && sub_vs.contains(&n) {
                rdfs(graph, used, set, sub_vs, n);
            }
        }
    }

    let mut used = HashSet::new();
    let mut visited = Vec::new();

    for &v in sub_vs {
        if !used.contains(&v) {
            dfs(graph, &mut used, &mut visited, sub_vs, v);
        }
    }

    used.clear();

    visited
        .iter()
        .rev()
        .flat_map(|&v| {
            if !used.contains(&v) {
                let mut set = HashSet::new();
                rdfs(graph, &mut used, &mut set, sub_vs, v);
                Some(set)
            } else {
                None
            }
        })
        .collect()
}

// Assume graph's a DAG
pub fn dominants_sub<N: Eq + NodeTrait, E>(
    node: N,
    graph: &DiGraphMap<N, E>,
    sub_vs: &HashSet<N>,
) -> HashSet<N> {
    let mut dominants = HashSet::new();
    dominants.insert(node);

    let mut stack = vec![node];

    while let Some(v) = stack.pop() {
        for n in graph.neighbors(v) {
            if sub_vs.contains(&n) && dominants.insert(n) {
                stack.push(n);
            }
        }
    }

    dominants
}

#[test]
fn test_scc() {
    let mut graph = DiGraphMap::new();
    graph.add_edge(0, 1, ());
    graph.add_edge(1, 2, ());
    graph.add_edge(2, 3, ());
    graph.add_edge(3, 1, ());

    let mut scc = scc_sub(&graph, &graph.nodes().collect());
    scc.sort_by_key(|s| s.len());

    assert_eq!(scc[0], HashSet::from_iter(vec![0]));
    assert_eq!(scc[1], HashSet::from_iter(vec![1, 2, 3]));
}
