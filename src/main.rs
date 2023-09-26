use brilt::{cfg::Cfg, restructure::StructureAnalysis};

fn main() {
    let program = bril_rs::load_program();

    let cfg = Cfg::new(&program.functions[0].instrs);
    let sa = StructureAnalysis::new(cfg);

    println!("{}", sa);
}
