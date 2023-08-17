use std::collections::HashMap;
use std::mem;
use std::ops::Deref;
use crate::{Word, Addr};
use crate::logic::{
    Term, VarId, VarCounter, Binder, Prop, StepProp, ReachableProp, StatePred, Subst, SubstTable,
    IdentitySubsts, EqAlpha,
};
use crate::symbolic::{self, Memory};
use crate::micro_ram::{self, Instr, Opcode, Reg, Operand, MemWidth};



pub struct Proof<'a> {
    prog: &'a HashMap<u64, Instr>,
    /// Enclosing scopes.  `scopes[0]` is the innermost and `scopes.last()` is the outermost.  For
    /// each one, we have a `u32` scope ID (as returned by `VarId::scope`) and a list of
    /// propositions that are known to hold over the variables of that scope and outer scopes.
    scopes: Box<[(u32, &'a mut Vec<Prop>)]>,
}

impl<'a> Proof<'a> {
    pub fn prove(
        prog: &HashMap<u64, Instr>,
        f: impl FnOnce(&mut Proof) -> Result<(), String>,
    ) -> Result<Vec<Prop>, String> {
        let mut props = Vec::new();
        f(&mut Proof {
            prog,
            scopes: Box::new([(0, &mut props)]),
        })?;
        Ok(props)
    }

    /// Enter a nested scope with `props` as premises.  This mutates `props` into a collection of
    /// `Prop`s that are implied by the original premises.
    fn enter<R>(
        &mut self,
        scope: u32,
        props: &mut Vec<Prop>,
        f: impl FnOnce(&mut Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        self.enter_owned(scope, props, |mut pf| f(&mut pf))
    }

    fn enter_owned<R>(
        &mut self,
        scope: u32,
        props: &mut Vec<Prop>,
        f: impl FnOnce(Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        let mut scopes = Vec::with_capacity(self.scopes.len() + 1);
        scopes.push((scope, props));
        for &mut (s, ref mut ps) in self.scopes.iter_mut() {
            scopes.push((s, ps));
        }
        let scopes = scopes.into_boxed_slice();

        f(Proof { prog: self.prog, scopes })
    }

    fn reenter_owned<R>(
        &mut self,
        f: impl FnOnce(Proof) -> Result<R, String>,
    ) -> Result<R, String> {
        let mut scopes = Vec::with_capacity(self.scopes.len());
        for &mut (s, ref mut ps) in self.scopes.iter_mut() {
            scopes.push((s, &mut **ps));
        }
        let scopes = scopes.into_boxed_slice();

        f(Proof { prog: self.prog, scopes })
    }

    pub fn show_context(&self) {
        for (i, &(_, ref ps)) in self.scopes.iter().rev().enumerate() {
            for (j, p) in ps.iter().enumerate() {
                eprintln!("{}.{}: {}", i, j, p);
            }
        }
    }

    fn get_prop(&self, depth: usize, index: usize) -> &Prop {
        let scope = self.scopes.len() - 1 - depth;
        &self.scopes[scope].1[index]
    }

    fn add_prop(&mut self, prop: Prop) -> usize {
        let depth = self.scopes.len();
        let props = &mut self.scopes[0].1;
        let i = props.len();
        println!("proved {}.{}: {}", depth - 1, i, prop);
        props.push(prop);
        i
    }

    /// Duplicate a `Prop` in scope.  This can only be applied to the innermost scope.
    pub fn rule_clone(&mut self, index: usize) -> usize {
        let prop = self.scopes[0].1[index].clone();
        self.add_prop(prop)
    }

    pub fn admit(&mut self, prop: Prop) -> usize {
        println!("ADMITTED: {}", prop);
        self.add_prop(prop)
    }

    /// Ensure that `premise` appears somewhere in the current scope.
    fn require_premise(&self, premise: &Prop) -> Result<(), String> {
        for s in self.scopes.iter() {
            for p in s.1.iter() {
                if premise.check_eq(p) {
                    return Ok(())
                }
            }
        }

        Err(format!("missing premise: {}", premise))
    }

    /// Apply a `Prop::Forall` to arguments.  `subst` provides `Term`s to be substituted for the
    /// bound variables.  After substitution, the premises of the `Forall` are required to hold,
    /// and the conclusion is introduced into the current scope.
    // FIXME (unsound): restrict what subst can be performed here
    pub fn rule_apply(
        &mut self,
        depth: usize,
        index: usize,
        subst: &mut impl Subst,
    ) -> Result<usize, String> {
        let prop = self.get_prop(depth, index);
        let binder = match *prop {
            Prop::Forall(ref b) => b,
            _ => return Err(format!("rule_apply: expected forall, but got {}", prop)),
        };

        let (ref premises, ref conclusion) = binder.inner;
        for premise in premises {
            self.require_premise(&premise.subst(subst))?;
        }

        Ok(self.add_prop(conclusion.subst(subst)))
    }

    pub fn tactic_apply0(
        &mut self,
        depth: usize,
        index: usize,
    ) -> Result<usize, String> {
        self.rule_apply(depth, index, &mut IdentitySubsts::new())
    }

    fn next_scope(&self) -> u32 {
        let scope = self.scopes.len() as u32;
        assert!(self.scopes.iter().all(|s| s.0 != scope));
        scope
    }

    /// Prove a theorem of the form `forall xs, Ps(xs) => Q(xs)`.  `mk_premises` sets up `xs` and
    /// `Ps`, and it can return some extra data such as `VarId`s to be passed to `prove`.  `prove`
    /// derives some conclusion from the premises.  After running `prove`, the final `Prop` it
    /// proved becomes the conclusion of the `forall`.
    pub fn rule_forall_intro<T>(
        &mut self,
        mk_premises: impl FnOnce(&mut VarCounter) -> (Vec<Prop>, T),
        prove: impl FnOnce(&mut Proof, T) -> Result<(), String>,
    ) -> Result<usize, String> {
        let scope = self.next_scope();

        let inner_depth = self.scopes.len();
        let b = Binder::try_new(scope, |vars| {
            let (mut props, extra) = mk_premises(vars);
            let premises = props.clone();
            for (i, p) in premises.iter().enumerate() {
                eprintln!("introduced {}.{}: {}", inner_depth, i, p);
            }
            self.enter(scope, &mut props, |pf| prove(pf, extra))?;
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
            |_| (premises, ()),
            |pf, ()| prove(pf),
        )
    }

    /// Prove a trivial `Prop::Step` of the form `{P} ->0 {P}`.
    pub fn rule_step_zero(
        &mut self,
        f: impl FnOnce(&mut VarCounter) -> StatePred,
    ) -> usize {
        let scope = self.next_scope();
        let pred = Binder::new(scope, f);
        let prop = Prop::Step(StepProp {
            pre: pred.clone(),
            post: pred,
            min_cycles: 0.into(),
        });
        self.add_prop(prop)
    }

    /// Extend a `Prop::Step`, mutating it into another `Prop::Step` that's implied by the
    /// original.
    pub fn rule_step_extend<R>(
        &mut self,
        index: usize,
        f: impl FnOnce(&mut StepProof) -> Result<R, String>,
    ) -> Result<R, String> {
        let dummy_prop = Prop::Nonzero(1.into());
        let mut sp = match mem::replace(&mut self.scopes[0].1[index], dummy_prop) {
            Prop::Step(sp) => sp,
            prop => {
                let msg = format!("rule_step_extend expected step, but got {}", prop);
                self.scopes[0].1[index] = prop;
                return Err(msg);
            },
        };
        let r = self.reenter_owned(|pf| {
            f(&mut StepProof { pf, sp: &mut sp })
        });
        self.scopes[0].1[index] = Prop::Step(sp);
        r
    }

    /// Admit as an axiom that the program can execute at least `min_cycles` and end in the given
    /// state.
    pub fn admit_reachable(
        &mut self,
        min_cycles: Term,
        f: impl FnOnce(&mut VarCounter) -> StatePred,
    ) -> usize {
        let scope = self.next_scope();
        let pred = Binder::new(scope, f);
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
        zero_depth: usize,
        zero_index: usize,
        succ_depth: usize,
        succ_index: usize,
    ) -> Result<usize, String> {
        // Check that `Hsucc` has the form `forall n, P n -> P (n + 1)`.
        let succ_prop = self.get_prop(succ_depth, succ_index);
        let succ_b = match succ_prop {
            &Prop::Forall(ref b) => b,
            ref p => return Err(format!("expected Hsucc to be a forall, but got {}", p)),
        };

        let vars = &succ_b.vars;
        if vars.len() != 1 {
            return Err(format!(
                "expected Hsucc to bind exactly one variable, but got {}", succ_prop));
        }
        let scope = vars.scope();
        let var = VarId::new(scope, 0);

        let (ref premises, ref conclusion) = succ_b.inner;
        if premises.len() != 2 {
            return Err(format!(
                "expected Hsucc to have exactly two premises, but got {}", succ_prop));
        }
        let no_overflow = &premises[0];
        let predicate = &premises[1];

        let expect_no_overflow = Prop::Nonzero(
            Term::cmpa(Term::add(Term::var_unchecked(var), 1.into()), 0.into()));
        if !EqAlpha::compare_props(&no_overflow, &expect_no_overflow) {
            return Err(format!("expected Hsucc first premise to be ({}), but got ({})",
                expect_no_overflow, no_overflow));
        }

        let expect_conclusion = predicate.subst(&mut SubstTable::new(|v| {
            if v == var {
                Term::add(Term::var_unchecked(v), 1.into())
            } else {
                Term::var_unchecked(v)
            }
        }));
        if !EqAlpha::compare_props(&conclusion, &expect_conclusion) {
            return Err(format!("expected Hsucc conclusion to be ({}), but got ({})",
                expect_conclusion, conclusion));
        }

        // We have now extracted `P` as `predicate`.

        // Check that `Hzero` has the form `P 0`.
        let zero_prop = self.get_prop(zero_depth, zero_index);
        let expect_zero = predicate.subst(&mut SubstTable::new(|v| {
            if v == var {
                0.into()
            } else {
                Term::var_unchecked(v)
            }
        }));
        if !EqAlpha::compare_props(&zero_prop, &expect_zero) {
            return Err(format!("expected Hzero to be ({}), but got ({})",
                expect_zero, zero_prop));
        }

        // Add `forall n, P n`.
        Ok(self.add_prop(Prop::Forall(Binder::new(scope, |vars| {
            assert_eq!(vars.fresh_var(), var);
            (Vec::new(), Box::new(predicate.clone()))
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
        self.pf.require_premise(premise)
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
