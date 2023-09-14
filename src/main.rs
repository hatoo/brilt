use brilt::cfg::Cfg;

fn main() {
    let program = bril_rs::load_program();

    let cfg = Cfg::new(&program.functions[0].instrs);
    let mut builder = cfg.into_structure_cfg_builder();
    while builder.merge_branch() || builder.merge_loop() || builder.merge_linear() {}

    let mut root = builder.root();
    root.flatten();
    dbg!(root);
}
