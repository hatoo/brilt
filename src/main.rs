use brilt::{cfg::Cfg, restructure::RestructuredCfg};

fn main() {
    let program = bril_rs::load_program();

    let cfg = Cfg::new(&program.functions[0].instrs);
    let mut r = RestructuredCfg::new(cfg);

    r.restructure();
    println!("{}", r.structure_analysys());
}
