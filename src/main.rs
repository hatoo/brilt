use brilt::cfg::Cfg;

fn main() {
    let program = bril_rs::load_program();

    let cfg = Cfg::new(&program.functions[0].instrs);

    println!("{:?}", &cfg);
}
