use brilt::{cfg::Cfg, restructure::StructureAnalysis, rvsdg::Rvsdg};

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

    println!("{:#?}", rvsdg);
}
