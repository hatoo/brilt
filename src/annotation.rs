use std::{
    collections::HashSet,
    fmt::{self, Debug, Display, Formatter},
};

use bril_rs::Code;

use crate::restructure::StructureAnalysis;

/// Annotation for structured control flow.

#[derive(Debug, Clone)]
pub enum Annotation<T> {
    Block(Vec<Code>, T),
    Linear(Vec<Annotation<T>>, T),
    Loop(Box<Annotation<T>>, T),
    Branch(String, Vec<Annotation<T>>, T),
}

impl<T> Annotation<T> {
    pub fn annotation(&self) -> &T {
        match self {
            Self::Block(_, a) => a,
            Self::Linear(_, a) => a,
            Self::Loop(_, a) => a,
            Self::Branch(_, _, a) => a,
        }
    }
}

impl<T: Debug> Display for Annotation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.display_impl(1, f)
    }
}

impl<T: Debug> Annotation<T> {
    fn display_impl(&self, indent_level: usize, fmt: &mut Formatter) -> fmt::Result {
        let tab = " ".repeat(indent_level * 2);
        let ctab = " ".repeat(indent_level * 2 - 2);

        match self {
            Self::Block(codes, a) => {
                writeln!(fmt, "{}{:?}", tab, a)?;
                for code in codes.iter() {
                    writeln!(fmt, "{}{}", ctab, code)?;
                }
            }
            Self::Linear(ss, a) => {
                writeln!(fmt, "{}{:?}", tab, a)?;
                for s in ss {
                    s.display_impl(indent_level, fmt)?;
                }
            }
            Self::Loop(s, a) => {
                writeln!(fmt, "{}{:?}", tab, a)?;
                writeln!(fmt, "{}do {{", tab)?;
                s.display_impl(indent_level + 1, fmt)?;
                writeln!(fmt, "{}}} while({});", tab, StructureAnalysis::VAR_R)?;
            }
            Self::Branch(cond_var, ss, a) => match cond_var.as_str() {
                StructureAnalysis::VAR_P | StructureAnalysis::VAR_Q | StructureAnalysis::VAR_R => {
                    writeln!(fmt, "{}{:?}", tab, a)?;
                    writeln!(fmt, "{}switch ({}) {{", tab, cond_var)?;
                    for (i, s) in ss.iter().enumerate() {
                        writeln!(fmt, "{}  case {}: {{", tab, i)?;
                        s.display_impl(indent_level + 2, fmt)?;
                        writeln!(fmt, "{}  }}", tab)?;
                    }
                    writeln!(fmt, "{}}}", tab)?;
                }
                _ => {
                    writeln!(fmt, "{}{:?}", tab, a)?;
                    assert!(ss.len() == 2);
                    writeln!(fmt, "{}if ({}) {{", tab, cond_var)?;
                    ss[0].display_impl(indent_level + 1, fmt)?;
                    writeln!(fmt, "{}}} else {{", tab)?;
                    ss[1].display_impl(indent_level + 1, fmt)?;
                    writeln!(fmt, "{}}}", tab)?;
                }
            },
        }

        Ok(())
    }
}

#[derive(Default, Debug, Clone)]
pub struct ReadWrite {
    pub read: HashSet<String>,
    pub write: HashSet<String>,
}

pub fn read_write_annotation(sa: StructureAnalysis) -> Annotation<ReadWrite> {
    match sa {
        StructureAnalysis::Block(codes) => {
            let mut read_write = ReadWrite::default();

            for code in codes.iter().rev() {
                match code {
                    Code::Instruction(instr) => match instr {
                        bril_rs::Instruction::Constant { dest, .. } => {
                            read_write.read.remove(dest);
                            read_write.write.insert(dest.clone());
                        }
                        bril_rs::Instruction::Value { args, dest, .. } => {
                            read_write.read.remove(dest);
                            read_write.write.insert(dest.clone());

                            read_write.read.extend(args.iter().cloned());
                        }
                        bril_rs::Instruction::Effect { args, .. } => {
                            read_write.read.extend(args.iter().cloned());
                        }
                    },

                    _ => {}
                }
            }

            Annotation::Block(codes, read_write)
        }
        StructureAnalysis::Linear(ss) => {
            let mut read_write = ReadWrite::default();

            let ss: Vec<_> = ss.into_iter().map(read_write_annotation).collect();

            for a in ss.iter().rev() {
                let rw = a.annotation();

                for w in rw.write.iter() {
                    read_write.read.remove(w);
                    read_write.write.insert(w.clone());
                }

                for r in rw.read.iter() {
                    read_write.read.insert(r.clone());
                }
            }

            Annotation::Linear(ss, read_write)
        }
        StructureAnalysis::Branch(cond_var, ss) => {
            let ss: Vec<_> = ss.into_iter().map(read_write_annotation).collect();

            let mut read = ss.iter().fold(HashSet::new(), |acc, item| {
                acc.union(&item.annotation().read).cloned().collect()
            });

            read.insert(cond_var.clone());

            let write = ss
                .iter()
                .fold(None, |acc: Option<HashSet<_>>, item| {
                    if let Some(acc) = acc {
                        Some(
                            acc.intersection(&item.annotation().write)
                                .cloned()
                                .collect(),
                        )
                    } else {
                        Some(item.annotation().write.clone())
                    }
                })
                .unwrap_or_default();

            Annotation::Branch(cond_var, ss, ReadWrite { read, write })
        }
        StructureAnalysis::Loop(sa) => {
            let a = read_write_annotation(*sa);
            let mut read_write = a.annotation().clone();

            read_write.read.insert(StructureAnalysis::VAR_R.to_string());

            Annotation::Loop(Box::new(a), read_write)
        }
    }
}

fn demand_set_annotation_rec(
    rwa: Annotation<ReadWrite>,
    dt: &mut HashSet<String>,
) -> Annotation<HashSet<String>> {
    match rwa {
        Annotation::Block(codes, rw) => {
            for w in rw.write.iter() {
                dt.remove(w);
            }

            for r in rw.read.iter() {
                dt.insert(r.clone());
            }

            Annotation::Block(codes, dt.clone())
        }
        Annotation::Linear(v, rw) => {
            let mut new_v = v
                .into_iter()
                .rev()
                .map(|a| demand_set_annotation_rec(a, dt))
                .collect::<Vec<_>>();
            new_v.reverse();

            for w in rw.write.iter() {
                dt.remove(w);
            }

            for r in rw.read.iter() {
                dt.insert(r.clone());
            }

            Annotation::Linear(new_v, dt.clone())
        }
        Annotation::Branch(cond_var, branches, rw) => {
            let new_branches = branches
                .into_iter()
                .map(|a| demand_set_annotation_rec(a, &mut dt.clone()))
                .collect::<Vec<_>>();

            for w in rw.write.iter() {
                dt.remove(w);
            }

            for r in rw.read.iter() {
                dt.insert(r.clone());
            }

            Annotation::Branch(cond_var, new_branches, dt.clone())
        }
        Annotation::Loop(body, rw) => {
            for r in rw.read.iter() {
                dt.insert(r.clone());
            }

            let new_body = demand_set_annotation_rec(*body, dt);

            Annotation::Loop(Box::new(new_body), dt.clone())
        }
    }
}

pub fn demand_set_annotation(rwa: Annotation<ReadWrite>) -> Annotation<HashSet<String>> {
    let mut dt = HashSet::new();

    demand_set_annotation_rec(rwa, &mut dt)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{cfg::Cfg, test::*};
    use glob::glob;
    use std::io::Cursor;

    #[test]
    fn test_rw_annotation() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("bril/examples/test/dom/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            for function in &mut program.functions {
                println!("checking {} ... ", path.to_str().unwrap());
                let cfg = Cfg::new(&function.instrs);

                let sa = StructureAnalysis::new(cfg);

                let rw = read_write_annotation(sa);

                eprintln!("{}", rw);
            }
        }
    }

    #[test]
    fn test_demand_set_annotation() {
        for entry in glob("bril/examples/test/df/*.bril")
            .unwrap()
            .chain(glob("bril/examples/test/dom/*.bril").unwrap())
        {
            let path = entry.unwrap();
            let src = std::fs::read_to_string(&path).unwrap();
            let json_before = bril2json(src.as_str());
            let mut program = bril_rs::load_program_from_read(Cursor::new(json_before.clone()));

            for function in &mut program.functions {
                println!("checking {} ... ", path.to_str().unwrap());
                let cfg = Cfg::new(&function.instrs);

                let sa = StructureAnalysis::new(cfg);
                let rw = read_write_annotation(sa);
                let ds = demand_set_annotation(rw);

                eprintln!("{}", ds);
            }
        }
    }
}
