use core::fmt::Display;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use crate::logic::{VarId, Binder};
use crate::logic::print::{Print, Printer, DisplayWithPrinter};
use crate::logic::visit::{self, Visit, Visitor};

pub struct CheckWfVisitor {
    num_vars: Vec<usize>,
    vars_reported: BTreeSet<VarId>,
    errs: Vec<String>,
}

impl CheckWfVisitor {
    pub fn new(num_vars: Vec<usize>) -> CheckWfVisitor {
        CheckWfVisitor {
            num_vars,
            vars_reported: BTreeSet::new(),
            errs: Vec::new(),
        }
    }

    pub fn print<'b, P: Print>(&self, p: &'b P) -> DisplayWithPrinter<'b, P> {
        Printer::new(self.num_vars.len() as u32).display(p)
    }

    fn report(&mut self, v: VarId, err: impl Display) {
        if self.vars_reported.insert(v) {
            self.errs.push(err.to_string());
        }
    }
}

impl Visitor for CheckWfVisitor {
    fn visit_var_id(&mut self, x: VarId) {
        if x.scope() >= self.num_vars.len() as u32 {
            self.report(x, format_args!("unexpected free variable {}", self.print(&x)));
            return;
        }

        let scope_num_vars = self.num_vars[self.num_vars.len() - 1 - x.scope() as usize];
        if x.index() >= scope_num_vars as u32 {
            match scope_num_vars {
                0 => self.report(x, format_args!(
                    "undefined variable {}; no vars are bound at this level",
                    self.print(&x))),
                1 => {
                    let bound = VarId::new(x.scope(), 0);
                    self.report(x, format_args!(
                        "undefined variable {}; only {} is bound at this level",
                        self.print(&x), self.print(&bound)));
                },
                n => {
                    let lo = VarId::new(x.scope(), 0);
                    let hi = VarId::new(x.scope(), n as u32 - 1);
                    self.report(x, format_args!(
                        "undefined variable {}; only {} ... {} are bound at this level",
                        self.print(&x), self.print(&lo), self.print(&hi)));
                },
            }
            return;
        }
    }

    fn visit_binder<T>(&mut self, x: &Binder<T>, f: impl FnOnce(&mut Self, &T)) {
        self.num_vars.push(x.vars.len());
        visit::default_visit_binder(self, x, f);
        self.num_vars.pop();
    }
}


pub trait WfExt: Sized {
    fn check_wf(&self, num_vars: Vec<usize>) -> Result<(), String>;
}

impl<T: Visit + Clone> WfExt for T {
    fn check_wf(&self, num_vars: Vec<usize>) -> Result<(), String> {
        let mut v = CheckWfVisitor::new(num_vars);
        self.visit_with(&mut v);
        if v.errs.len() == 0 {
            Ok(())
        } else {
            Err(v.errs.join("\n"))
        }
    }
}
