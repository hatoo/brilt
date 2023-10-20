use brilt::{cfg::Cfg, restructure::StructureAnalysis, rvsdg::Rvsdg};
use clap::Parser;
use egglog::{EGraph, ExtractReport};

#[derive(Parser)]
struct Opt {
    #[clap(long)]
    debug: bool,
}

fn main() {
    let args = Opt::parse();

    let mut program = bril_rs::load_program();

    for func in &mut program.functions {
        let cfg = Cfg::new(&func.instrs);
        let sa = StructureAnalysis::new(cfg);
        let rvsdg = Rvsdg::new(
            &func.args.iter().map(|a| a.name.clone()).collect::<Vec<_>>(),
            sa,
        );

        if args.debug {
            eprintln!("Pre RVSDG:\n{}", rvsdg);
        }

        const SCHEMA: &str = include_str!("../schema.egg");
        let mut egraph = EGraph::default();

        egraph.parse_and_run_program(SCHEMA).unwrap();

        egraph
            .parse_and_run_program(&format!("(let e {})\n(run 100)\n(extract e)", &rvsdg))
            .unwrap();

        let (cost, out) = match egraph.get_extract_report().as_ref().unwrap() {
            ExtractReport::Best {
                termdag,
                term,
                cost,
            } => (*cost, Rvsdg::from_egglog(term, &termdag.nodes)),
            _ => panic!("No best term found"),
        };

        if args.debug {
            eprintln!("Post RVSDG (cost: {}):\n{}", cost, out);

            let output = egraph.parse_and_run_program("(print-stats)").unwrap();
            eprintln!("stats:\n{}", output[0]);
        }

        func.instrs = out.to_bril(&func.args);
    }

    serde_json::to_writer_pretty(std::io::stdout(), &program).unwrap();
}
