use brilt::{cfg::Cfg, restructure::StructureAnalysis, rvsdg::Rvsdg};
use egglog::EGraph;

fn main() {
    let program = bril_rs::load_program();

    let cfg = Cfg::new(&program.functions[0].instrs);
    let sa = StructureAnalysis::new(cfg);
    let rvsdg = Rvsdg::new(
        &program.functions[0]
            .args
            .iter()
            .map(|a| a.name.clone())
            .collect::<Vec<_>>(),
        sa,
    );

    const SCHEMA: &str = include_str!("../schema.egg");
    let mut egraph = EGraph::default();

    egraph.parse_and_run_program(SCHEMA).unwrap();

    let outputs = egraph
        .parse_and_run_program(&format!("(let e {})\n(run 100)\n(extract e)", &rvsdg))
        .unwrap();

    println!("{}", outputs[0]);

    // TODO: Back optimized egglog to bril
}
