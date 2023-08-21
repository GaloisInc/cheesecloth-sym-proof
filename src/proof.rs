use std::collections::HashMap;
use std::iter;
use std::mem;
use std::ops::Deref;
use crate::{Word, Addr};
use crate::logic::{
    Term, VarId, VarCounter, Binder, Prop, StepProp, ReachableProp, StatePred, Subst, SubstTable,
    IdentitySubsts, EqAlpha,
};
use crate::logic::print::{Print, Printer, DisplayWithPrinter, debug_print, PrintBinder};
use crate::logic::shift::ShiftExt;
use crate::logic::subst::SubstExt;
use crate::logic::wf::WfExt;
use crate::symbolic::{self, Memory};
use crate::micro_ram::{self, Instr, Opcode, Reg, Operand, MemWidth};



pub struct Proof<'a> {
    prog: &'a HashMap<u64, Instr>,
    /// Enclosing scopes.  `scopes[0]` is the outermost and `scopes.last()` is the innermost.  For
    /// each one, we have a list of propositions that are known to hold over the variables of that
    /// scope and outer scopes.
    outer_scopes: Box<[Scope<'a>]>,

    /// Number of variables bound by the binder of the current scope.  This will be zero if the
    /// current scope doesn't correspond to a binder.
    num_vars: usize,

    /// Propositions known to hold over variables in the current scope.
    props: &'a mut Vec<Prop>,
}

#[derive(Clone, Debug)]
struct Scope<'a> {
    num_vars: usize,
    props: &'a [Prop],
}

impl<'a> Proof<'a> {
    pub fn print<'b, P: Print>(&self, p: &'b P) -> DisplayWithPrinter<'b, P> {
        self.printer().display(p)
    }

    pub fn print_adj<'b, P: Print>(&self, adj_depth: u32, p: &'b P) -> DisplayWithPrinter<'b, P> {
        self.printer_adj(adj_depth).display(p)
    }

    pub fn print_depth<'b, P: Print>(&self, depth: u32, p: &'b P) -> DisplayWithPrinter<'b, P> {
        self.printer_depth(depth).display(p)
    }

    pub fn printer(&self) -> Printer {
        self.printer_adj(0)
    }

    pub fn printer_adj(&self, adj_depth: u32) -> Printer {
        self.printer_depth(self.outer_scopes.len() as u32 + adj_depth)
    }

    pub fn printer_depth(&self, depth: u32) -> Printer {
        Printer::new(depth)
    }

    pub fn prove(
        prog: &HashMap<u64, Instr>,
        f: impl FnOnce(&mut Proof) -> Result<(), String>,
    ) -> Result<Vec<Prop>, String> {
        let mut props = Vec::new();
        f(&mut Proof {
            prog,
            outer_scopes: Box::new([]),
            num_vars: 0,
            props: &mut props,
        })?;
        Ok(props)
    }

    /// Enter a nested scope with `props` as premises.  This mutates `props` into a collection of
    /// `Prop`s that are implied by the original premises.
    fn enter<R>(
        &mut self,
        num_vars: usize,
        props: &mut Vec<Prop>,
        f: impl FnOnce(&mut Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        self.enter_owned(num_vars, props, |mut pf| f(&mut pf))
    }

    fn enter_owned<R>(
        &mut self,
        num_vars: usize,
        props: &mut Vec<Prop>,
        f: impl FnOnce(Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        let mut outer_scopes = Vec::<Scope>::with_capacity(self.outer_scopes.len() + 1);
        for s in self.outer_scopes.iter() {
            outer_scopes.push(s.clone());
        }
        outer_scopes.push(Scope {
            num_vars: self.num_vars,
            props: self.props,
        });
        let outer_scopes = outer_scopes.into_boxed_slice();

        f(Proof {
            prog: self.prog,
            outer_scopes,
            num_vars,
            props,
        })
    }

    fn reenter_owned<R>(
        &mut self,
        f: impl FnOnce(Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        let outer_scopes = self.outer_scopes.clone();

        f(Proof {
            prog: self.prog,
            outer_scopes,
            num_vars: self.num_vars,
            props: self.props,
        })
    }

    pub fn show_context(&self) {
        self.show_context_common(false);
    }

    pub fn show_context_verbose(&self) {
        self.show_context_common(true);
    }

    fn show_context_common(&self, verbose: bool) {
        for (i, s) in self.outer_scopes.iter().rev().enumerate() {
            for (j, p) in s.props.iter().enumerate() {
                eprintln!(
                    "{}.{}: {}", i, j,
                    self.printer_depth(i as u32).verbose(verbose).display(p),
                );
            }
        }

        let i = self.outer_scopes.len();
        for (j, p) in self.props.iter().enumerate() {
            eprintln!(
                "{}.{}: {}", i, j,
                self.printer_depth(i as u32).verbose(verbose).display(p),
            );
        }
    }

    fn add_prop(&mut self, prop: Prop) -> usize {
        #[cfg(debug_assertions)] {
            let num_vars = self.outer_scopes.iter().map(|s| s.num_vars)
                .chain(iter::once(self.num_vars))
                .collect::<Vec<_>>();
            if let Err(e) = prop.check_wf(num_vars) {
                panic!("tried to add ill-formed proposition {}\n{}", self.print(&prop), e);
            }
        }
        let depth = self.outer_scopes.len();
        let i = self.props.len();
        println!("proved {}.{}: {}", depth, i, self.print(&prop));
        self.props.push(prop);
        i
    }

    /// Copy a `Prop` from an outer scope into the current scope.  This shifts the free variables
    /// to make it valid in the current scope.
    pub fn rule_shift(&mut self, depth: usize, index: usize) -> usize {
        let amount = (self.outer_scopes.len() - depth) as u32;
        eprintln!("rule_shift: shift by {amount}, prop = {}",
            self.print_depth(depth as u32, &self.outer_scopes[depth].props[index]));
        let prop = self.outer_scopes[depth].props[index].shift_by(amount);
        self.add_prop(prop)
    }

    /// Duplicate a `Prop` in scope.  This can only be applied to the innermost scope.
    pub fn rule_clone(&mut self, index: usize) -> usize {
        let prop = self.props[index].clone();
        self.add_prop(prop)
    }

    pub fn admit(&mut self, prop: Prop) -> usize {
        println!("ADMITTED: {}", self.print(&prop));
        self.add_prop(prop)
    }

    /// Ensure that `premise` appears somewhere in the current scope.
    fn require_premise(&self, premise: &Prop) -> Result<(), String> {
        for (i, s) in self.outer_scopes.iter().enumerate() {
            let shift_amount = (self.outer_scopes.len() - i) as u32;
            for p in s.props.iter() {
                if premise.check_eq(&p.shift_by(shift_amount)) {
                    return Ok(())
                }
            }
        }
        for p in self.props.iter() {
            if premise.check_eq(p) {
                return Ok(())
            }
        }

        Err(format!("missing premise: {}", self.print(premise)))
    }

    fn require_premise_shifted(&self, shift: u32, premise: &Prop) -> Result<(), String> {
        for (i, s) in self.outer_scopes.iter().enumerate() {
            let shift_amount = shift + (self.outer_scopes.len() - i) as u32;
            for p in s.props.iter() {
                if premise.check_eq(&p.shift_by(shift_amount)) {
                    return Ok(())
                }
            }
        }
        for p in self.props.iter() {
            if premise.check_eq(&p.shift_by(shift)) {
                return Ok(())
            }
        }

        Err(format!("missing premise: {}", self.print(premise)))
    }

    /// Apply a `Prop::Forall` to arguments.  `subst` provides `Term`s to be substituted for the
    /// bound variables.  After substitution, the premises of the `Forall` are required to hold,
    /// and the conclusion is introduced into the current scope.
    pub fn rule_apply(
        &mut self,
        index: usize,
        args: &[Term],
    ) -> Result<usize, String> {
        let prop = &self.props[index];
        let binder = match *prop {
            Prop::Forall(ref b) => b,
            _ => return Err(format!("rule_apply: expected forall, but got {}", self.print(prop))),
        };

        let premises = binder.map(|&(ref ps, _)| ps);
        let conclusion = binder.map(|&(_, ref q)| &**q);
        for premise in premises.iter() {
            self.require_premise(&premise.subst_ref(args))?;
        }

        Ok(self.add_prop(conclusion.subst_ref(args)))
    }

    pub fn tactic_apply0(
        &mut self,
        index: usize,
    ) -> Result<usize, String> {
        self.rule_apply(index, &[])
    }

    /// Prove a theorem of the form `forall xs, Ps(xs) => Q(xs)`.  `mk_premises` sets up `xs` and
    /// `Ps`, and it can return some extra data such as `VarId`s to be passed to `prove`.  `prove`
    /// derives some conclusion from the premises.  After running `prove`, the final `Prop` it
    /// proved becomes the conclusion of the `forall`.
    ///
    /// Note that the closures run under a binder, so terms from outside should be `shift`-ed
    /// before use.
    pub fn rule_forall_intro<T>(
        &mut self,
        mk_premises: impl FnOnce(&mut VarCounter) -> (Vec<Prop>, T),
        prove: impl FnOnce(&mut Proof, T) -> Result<(), String>,
    ) -> Result<usize, String> {
        let b = Binder::try_new(|vars| {
            // TODO: what happens if the closure fails to shift and introduces an out-of-range
            // variable for this binder?  failure at application time?
            let (mut props, extra) = mk_premises(vars);
            let premises = props.clone();
            let inner_depth = self.outer_scopes.len() + 1;
            for (i, p) in premises.iter().enumerate() {
                eprintln!("introduced {}.{}: {}", inner_depth, i, self.print_adj(1, p));
            }
            self.enter(vars.len(), &mut props, |pf| prove(pf, extra))?;
            let conclusion = props.pop().unwrap();
            Ok((premises, Box::new(conclusion)))
        })?;
        Ok(self.add_prop(Prop::Forall(b)))
    }

    pub fn tactic_implies_intro(
        &mut self,
        premises: Vec<Prop>,
        prove: impl FnOnce(&mut Proof) -> Result<(), String>,
    ) -> Result<usize, String> {
        self.rule_forall_intro(
            |_| (premises.shift(), ()),
            |pf, ()| prove(pf),
        )
    }

    /// Prove a trivial `Prop::Step` of the form `{P} ->0 {P}`.
    ///
    /// Note that the closure runs under a binder, so terms from outside should be `shift`-ed
    /// before use.
    pub fn rule_step_zero(
        &mut self,
        f: impl FnOnce(&mut VarCounter) -> StatePred,
    ) -> usize {
        let pred = Binder::new(f);
        let prop = Prop::Step(StepProp {
            pre: pred.clone(),
            post: pred,
            min_cycles: 0.into(),
        });
        self.add_prop(prop)
    }

    fn take_step_prop(&mut self, index: usize) -> Result<StepProp, String> {
        let dummy_prop = Prop::Nonzero(1.into());
        match mem::replace(&mut self.props[index], dummy_prop) {
            Prop::Step(sp) => Ok(sp),
            prop => {
                let msg = format!("expected step at index {}, but got {}",
                    index, self.print(&prop));
                self.props[index] = prop;
                Err(msg)
            },
        }
    }

    /// Extend a `Prop::Step`, mutating it into another `Prop::Step` that's implied by the
    /// original.
    pub fn rule_step_extend<R>(
        &mut self,
        index: usize,
        f: impl FnOnce(&mut StepProof) -> Result<R, String>,
    ) -> Result<R, String> {
        let mut sp = self.take_step_prop(index)?;
        let r = self.reenter_owned(|pf| {
            f(&mut StepProof { pf, sp: &mut sp })
        });
        self.props[index] = Prop::Step(sp);
        r
    }

    /// Join two `Prop::Step`s together.  Both inputs will be consumed (replaced with the trivial
    /// proposition `1`).
    pub fn rule_step_seq(
        &mut self,
        index1: usize,
        index2: usize,
    ) -> Result<usize, String> {
        // Note this may destroy both props on error.
        let sp1 = self.take_step_prop(index1)?;
        let sp2 = self.take_step_prop(index2)?;

        eprintln!("ADMITTED: implication of middle states ({}) => ({})",
            self.print(&PrintBinder::exists(&sp1.post)),
            self.print(&PrintBinder::exists(&sp2.pre)));

        Ok(self.add_prop(Prop::Step(StepProp {
            pre: sp1.pre,
            post: sp2.post,
            min_cycles: Term::add(sp1.min_cycles, sp2.min_cycles),
        })))
    }

    /// Admit as an axiom that the program can execute at least `min_cycles` and end in the given
    /// state.
    ///
    /// Note that the closure runs under a binder, so terms from outside should be `shift`-ed
    /// before use.
    pub fn admit_reachable(
        &mut self,
        min_cycles: Term,
        f: impl FnOnce(&mut VarCounter) -> StatePred,
    ) -> usize {
        let pred = Binder::new(f);
        let prop = Prop::Reachable(ReachableProp { pred, min_cycles });
        self.add_prop(prop)
    }

    /// ```
    /// forall (Hzero: P 0),
    /// forall (Hsucc: forall n, (n + 1 > 0) -> P n -> P (n + 1)),
    /// (forall n, P n)
    /// ```
    ///
    /// This is equivalent to Coq's `nat_ind`, except `Hsucc` gets the extra premise `n + 1 > 0`,
    /// which means the inductive case only needs to hold in cases where `n + 1` doesn't overflow.
    /// This is still sufficient to prove `forall n, P n` by the following reasoning: `P 0 -> P 1
    /// -> ... -> P (2^64 - 2) -> P (2^64 - 1)`.  We can't extend this chain any further because
    /// `Hsucc` no longer applies (`(2^64 - 1) + 1 = 0`), but we've already covered all 2^64
    /// possible values of `n`.
    pub fn rule_induction(
        &mut self,
        zero_index: usize,
        succ_index: usize,
    ) -> Result<usize, String> {
        // Check that `Hsucc` has the form `forall n, P n -> P (n + 1)`.
        let succ_prop = &self.props[succ_index];
        let succ_binder = match succ_prop {
            &Prop::Forall(ref b) => b,
            ref p => return Err(format!(
                "expected Hsucc to be a forall, but got {}", self.print(p))),
        };

        let vars = &succ_binder.vars;
        if vars.len() != 1 {
            return Err(format!(
                "expected Hsucc to bind exactly one variable, but got {}", self.print(succ_prop)));
        }

        let premises = succ_binder.map(|&(ref ps, _)| ps);
        let conclusion = succ_binder.map(|&(_, ref q)| &**q);
        if premises.inner.len() != 2 {
            return Err(format!(
                "expected Hsucc to have exactly two premises, but got {}", self.print(succ_prop)));
        }
        let no_overflow = premises.map(|ps| &ps[0]);
        let predicate = premises.map(|ps| &ps[1]);

        let expect_no_overflow = Binder::new(|vars| {
            Prop::Nonzero(Term::cmpa(Term::add(vars.fresh(), 1.into()), 0.into()))
        });
        debug_assert_eq!(succ_binder.vars.len(), expect_no_overflow.vars.len());
        if !EqAlpha::compare_props(&no_overflow.inner, &expect_no_overflow.inner) {
            return Err(format!("expected Hsucc first premise to be ({}), but got ({})",
                self.print(&PrintBinder::forall(&expect_no_overflow)),
                self.print(&PrintBinder::forall(&no_overflow))));
        }

        let expect_conclusion = Binder::new(|vars| {
            let predicate = predicate.map(|prop| prop.shift_free(1, 1));
            predicate.subst(&[Term::add(vars.fresh(), 1.into())])
        });
        if !EqAlpha::compare_props(&conclusion.inner, &expect_conclusion.inner) {
            return Err(format!("expected Hsucc conclusion to be ({}), but got ({})",
                self.print(&PrintBinder::forall(&expect_conclusion)),
                self.print(&PrintBinder::forall(&conclusion))));
        }

        // We have now extracted `P` as `predicate`.

        // Check that `Hzero` has the form `P 0`.
        let zero_prop = &self.props[zero_index];
        let expect_zero = predicate.subst_ref(&[0.into()]);
        if !EqAlpha::compare_props(&zero_prop, &expect_zero) {
            return Err(format!("expected Hzero to be ({}), but got ({})",
                self.print(&expect_zero), self.print(zero_prop)));
        }

        // Add `forall n, P n`.
        Ok(self.add_prop(Prop::Forall(Binder::new(|vars| {
            // We don't shift `predicate` because we already skipped a binder to get it.
            assert_eq!(vars.fresh_var(), VarId::new(0, 0));
            (Vec::new(), Box::new(predicate.inner.clone()))
        }))))
    }

    pub fn rule_gt_ne_unsigned(&mut self, x: Term, y: Term) -> Result<(), String> {
        self.require_premise(&Prop::Nonzero(Term::cmpa(x.clone(), y.clone())))?;
        self.add_prop(Prop::Nonzero(Term::cmpe(Term::cmpe(x.clone(), y.clone()), 0.into())));
        Ok(())
    }
}


pub struct StepProof<'a> {
    pf: Proof<'a>,
    sp: &'a mut StepProp,
}

impl<'a> StepProof<'a> {
    fn pc(&self) -> Addr {
        self.sp.post.inner.state.pc
    }
    fn fetch_instr(&self) -> Result<Instr, String> {
        let pc = self.pc();
        self.pf.prog.get(&pc).cloned()
            .ok_or_else(|| format!("program executed out of bounds at {}", pc))
    }

    fn reg_value(&self, reg: Reg) -> Term {
        self.sp.post.inner.state.reg_value(reg)
    }

    fn operand_value(&self, op: Operand) -> Term {
        self.sp.post.inner.state.operand_value(op)
    }

    fn set_reg(&mut self, reg: Reg, value: Term) {
        self.sp.post.inner.state.set_reg(reg, value);
    }

    fn mem_store(&mut self, w: MemWidth, addr: Term, value: Term) -> Result<(), String> {
        self.sp.post.inner.state.mem.store(w, addr, value, &[])
    }

    fn mem_load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        todo!()
    }

    fn finish_instr(&mut self) {
        self.finish_instr_jump(self.pc() + 1);
    }

    fn finish_instr_jump(&mut self, pc: Addr) {
        self.sp.post.inner.state.pc = pc;

        let min_cycles = mem::replace(&mut self.sp.min_cycles, Term::const_(0));
        self.sp.min_cycles = Term::add(min_cycles, Term::const_(1));
    }

    fn require_premise(&self, premise: &Prop) -> Result<(), String> {
        // Check `sp.props` first.
        if self.sp.post.inner.props.iter().any(|p| premise.check_eq(p)) {
            return Ok(())
        }

        // Otherwise, look through the various outer scopes.
        self.pf.require_premise_shifted(1, premise)
    }

    fn fresh_var(&mut self) -> Term {
        self.sp.post.vars.fresh()
    }

    /// Perform one step of execution.  In some cases, this may fail due to a missing precondition.
    pub fn rule_step(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let x = self.reg_value(instr.r1);
        let y = self.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Binary(b) => {
                let z = Term::binary(b, x, y);
                self.set_reg(instr.rd, z);
            },
            Opcode::Not => {
                self.set_reg(instr.rd, Term::not(y));
            },
            Opcode::Mov => {
                self.set_reg(instr.rd, y);
            },
            Opcode::Cmov => {
                let old = self.reg_value(instr.rd);
                let z = Term::mux(x, y, old);
                self.set_reg(instr.rd, z);
            },

            Opcode::Jmp => {
                let dest = y.as_const_or_err()
                    .map_err(|e| format!("when evaluating jmp dest: {e}"))?;
                eprintln!("run {}: {:?} (simple)", self.pc(), instr);
                self.finish_instr_jump(dest);
                return Ok(());
            },
            Opcode::Cjmp => return Err("can't use rule_step for Cjmp".into()),
            Opcode::Cnjmp => return Err("can't use rule_step for Cnjmp".into()),

            Opcode::Store(w) |
            Opcode::Poison(w) => {
                self.mem_store(w, y, x)?;
            },
            Opcode::Load(w) => {
                let z = self.mem_load(w, y)?;
                self.set_reg(instr.rd, z);
            },

            Opcode::Answer => {
                // Don't advance the PC.
                eprintln!("run {}: {:?} (simple)", self.pc(), instr);
                self.finish_instr_jump(self.pc());
                return Ok(());
            },
            Opcode::Advise => Err("can't use step_simple for Advise")?,
        }

        eprintln!("run {}: {:?} (simple)", self.pc(), instr);
        self.finish_instr();
        Ok(())
    }

    pub fn rule_step_jump(&mut self, taken: bool) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let x = self.reg_value(instr.r1);
        let y = self.operand_value(instr.op2);

        // Check that the precondition for taking / not taking the jump has been established.
        match instr.opcode {
            Opcode::Jmp => {
                if !taken {
                    return Err("can't fall through an unconditional Jmp".into());
                }
            },
            Opcode::Cjmp => {
                if taken {
                    self.require_premise(&Prop::Nonzero(x))?;
                } else {
                    self.require_premise(&Prop::Nonzero(Term::cmpe(x, 0.into())))?;
                }
            },
            Opcode::Cnjmp => {
                if taken {
                    self.require_premise(&Prop::Nonzero(Term::cmpe(x, 0.into())))?;
                } else {
                    self.require_premise(&Prop::Nonzero(x))?;
                }
            },

            op => return Err(format!("can't use rule_step_jump for {:?}", op)),
        }

        if taken {
            let dest = y.as_const_or_err()
                .map_err(|e| format!("when evaluating jmp dest: {e}"))?;
            eprintln!("run {}: {:?} (jump, taken)", self.pc(), instr);
            self.finish_instr_jump(dest);
        } else {
            eprintln!("run {}: {:?} (jump, not taken)", self.pc(), instr);
            self.finish_instr();
        }
        Ok(())
    }

    /// Handle a load instruction by introducing a fresh variable for the result.  This gives no
    /// information about the value that was actually loaded.
    pub fn rule_step_load_fresh(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;

        match instr.opcode {
            Opcode::Load(_) => {
                let z = self.fresh_var();
                self.set_reg(instr.rd, z);
            },

            op => Err(format!("can't use rule_step_load_fresh for {:?}", op))?,
        }

        eprintln!("run {}: {:?} (load_fresh)", self.pc(), instr);
        self.finish_instr();
        Ok(())
    }

    /// Replace the value of `reg` with a fresh symbolic variable.
    pub fn rule_forget_reg(&mut self, reg: Reg) {
        let z = self.fresh_var();
        self.set_reg(reg, z);
    }
}
