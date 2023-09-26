use std::collections::HashSet;

use bril_rs::Code;

use crate::restructure::StructureAnalysis;

/// Annotaion for structured control flow.

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
