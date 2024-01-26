use crate::Addr;
use crate::kernel::{Proof, ReachProof, PropId};
use crate::logic::{Term, Prop, VarCounter, Binder};
use crate::logic::shift::ShiftExt;


pub trait Tactics<'a> {
    fn proof(&self) -> &Proof<'a>;
    fn proof_mut(&mut self) -> &mut Proof<'a>;

    fn tactic_admit(&mut self, prop: Prop) -> PropId {
        let pf = self.proof_mut();
        let new_pid = next_prop_id(pf);
        pf.rule_admit(prop);
        new_pid
    }

    fn tactic_clone(&mut self, pid: PropId) -> PropId {
        let pf = self.proof_mut();
        let new_pid = next_prop_id(pf);
        pf.rule_clone(pid);
        new_pid
    }

    fn tactic_swap(&mut self, pid1: PropId, pid2: PropId) -> (PropId, PropId) {
        let pf = self.proof_mut();
        let index1 = require_local_prop(pf, pid1);
        let index2 = require_local_prop(pf, pid2);
        pf.rule_swap(index1, index2);
        (pid2, pid1)
    }

    fn tactic_apply(&mut self, pid: PropId, args: &[Term]) -> PropId {
        let pf = self.proof_mut();
        let new_pid = next_prop_id(pf);
        let index = require_local_prop(pf, pid);
        pf.rule_apply(index, args);
        new_pid
    }

    /// Apply a `Prop::Forall` with no bound variables.
    fn tactic_apply0(&mut self, pid: PropId) -> PropId {
        self.tactic_apply(pid, &[])
    }

    fn tactic_forall_intro<T>(
        &mut self,
        mk_premises: impl FnOnce(&mut VarCounter) -> (Vec<Prop>, T),
        prove: impl FnOnce(&mut Proof, T),
    ) -> PropId {
        let mut vars = VarCounter::new();
        let (premises, x) = mk_premises(&mut vars);
        let pf = self.proof_mut();
        let new_pid = next_prop_id(pf);
        pf.rule_forall_intro(vars, premises.into(), move |pf| prove(pf, x));
        new_pid
    }

    fn tactic_implies_intro(
        &mut self,
        premises: Vec<Prop>,
        prove: impl FnOnce(&mut Proof),
    ) -> PropId {
        self.tactic_forall_intro(
            |_| (premises.shift(), ()),
            |pf, ()| prove(pf),
        )
    }

    fn tactic_reach_extend(
        &mut self,
        pid: PropId,
        f: impl FnOnce(&mut ReachProof),
    ) {
        let pf = self.proof_mut();
        let index = require_local_prop(pf, pid);
        assert_eq!(index, pf.props().len() - 1,
            "tactic_reach_extend can only operate on the last prop ({}, {}), not {:?}",
            pf.scopes().len(), pf.props().len() - 1, pid);
        pf.rule_reach_extend(f);
    }

    fn tactic_reach_shrink(
        &mut self,
        pid: PropId,
        new_min_cycles: Term,
    ) {
        let pf = self.proof_mut();
        let index = require_local_prop(pf, pid);
        pf.rule_reach_shrink(index, new_min_cycles);
    }

    fn tactic_reach_rename_vars<T: AsRef<[Option<u32>]>>(
        &mut self,
        pid: PropId,
        f: impl FnOnce(&mut VarCounter) -> T,
    ) {
        let pf = self.proof_mut();
        let mut new_vars = VarCounter::new();
        let var_map = f(&mut new_vars);
        let index = require_local_prop(pf, pid);
        pf.rule_reach_rename_vars(index, new_vars, var_map.as_ref());
    }

    /// Prove a goal by induction.  This is a combination of `rule_induction` and several calls to
    /// `rule_forall_intro`.  It works as follows:
    ///
    /// 1. Calls `mk_goal` to obtain a goal.  The goal must be a `Prop::Forall` with exactly one
    ///    bound variable.  The first variable of the goal is treated as the induction variable
    ///    `n`, and the rest of the goal as `P n`.
    /// 2. Calls `prove_base(pf)`.  This callback will have the premises of `P 0` in scope and must
    ///    establish the conclusion, as in the `prove` callback of `tactic_forall_intro`.
    /// 3. Calls `prove_ind(pf, n)` to show that `forall n, n + 1 > 0 -> P n -> P (n + 1)`.  This
    ///    callback runs under two nested scopes: the outer scope has the variable `n` and the
    ///    premises `n + 1 > 0` and `P n`, and the inner scope has the premises of `P (n + 1)`.
    ///    The callback must establish the conclusion of `P (n + 1)`.
    /// 4. Applies induction to the base and inductive cases, producing the goal.
    ///
    /// This introduces three new `Prop`s into scope, but returns only the `PropId` of the final
    /// conclusion.
    fn tactic_induction(
        &mut self,
        goal: Prop,
        prove_base: impl FnOnce(&mut Proof),
        prove_ind: impl FnOnce(&mut Proof, Term),
    ) -> PropId {
        let pf = self.proof_mut();
        eprintln!("induction: trying to prove {}", pf.print(&goal));
        let b = match goal {
            Prop::Forall(b) => b,
            p => panic!("expected Prop::Forall, but got {}", pf.print(&p)),
        };
        assert_eq!(b.vars.len(), 1,
            "expected goal with exactly 1 var, but got {}",
            pf.print(&Prop::Forall(b)));

        let premises: Binder<Box<[Prop]>> = b.as_ref().map(|&(ref ps, _)| (*ps).clone());
        let conclusion: Binder<Prop> = b.as_ref().map(|&(_, ref q)| (**q).clone());

        let p_zero = pf.tactic_implies_intro(
            premises.subst(&[0.into()]).into(),
            |pf| {
                let expected = conclusion.shift().subst(&[0.into()]);
                println!("tactic_induction: prove zero case");
                println!("GOAL: {}", pf.print(&expected));
                prove_base(pf);

                let proved = pf.props().last()
                    .unwrap_or_else(|| panic!("`prove` callback did not prove anything"));
                // Note we are still in the inner scope, so we need to shift `conclusion`.
                assert!(
                    proved == &expected,
                    "`prove` callback failed to prove the expected conclusion\
                    \n  proved:   {}\
                    \n  expected: {}",
                    pf.print(proved), pf.print(&expected),
                );
            },
        );

        let p_succ = pf.tactic_forall_intro(
            |vars| {
                let n = vars.fresh();
                // `n + 1 > 0`
                let premise1 = Prop::Nonzero(Term::cmpa(Term::add(n.clone(), 1.into()), 0.into()));
                // `P n`
                let premise2 = Prop::Forall(Binder::new(|_| {
                    let n = n.shift();
                    let premises = premises.shift_by(2);
                    let conclusion = conclusion.shift_by(2);
                    (
                        premises.subst(&[n.clone()]),
                        Box::new(conclusion.subst(&[n.clone()])),
                    )
                }));
                (vec![premise1, premise2], n)
            },
            |pf, n| {
                let premises = premises.shift();
                let conclusion = conclusion.shift();
                let n_plus_1 = Term::add(n.clone(), 1.into());
                pf.tactic_implies_intro(
                    premises.subst(&[n_plus_1.clone()]).into(),
                    |pf| {
                        let n = n.shift();
                        let n_plus_1 = n_plus_1.shift();
                        let conclusion = conclusion.shift();
                        let expected = conclusion.subst(&[n_plus_1.clone()]);
                        println!("tactic_induction: prove successor case");
                        println!("GOAL: {}", pf.print(&expected));
                        prove_ind(pf, n.clone());

                        let proved = pf.props().last()
                            .unwrap_or_else(|| panic!("`prove` callback did not prove anything"));
                        assert!(
                            proved == &expected,
                            "`prove` callback failed to prove the expected conclusion\
                            \n  proved:   {}\
                            \n  expected: {}",
                            pf.print(proved), pf.print(&expected),
                        );
                    },
                );
            },
        );

        let new_pid = next_prop_id(pf);
        let index_zero = require_local_prop(pf, p_zero);
        let index_succ = require_local_prop(pf, p_succ);
        pf.rule_induction(index_zero, index_succ);
        new_pid
    }


    fn show_context(&self) {
        show_context_common(self.proof(), false)
    }
    fn show_prop(&self, id:PropId) {
        show_prop_common(self.proof(), false, id)
    }

    
    fn show_context_verbose(&self) {
        show_context_common(self.proof(), true)
    }
}

impl<'a> Tactics<'a> for Proof<'a> {
    fn proof(&self) -> &Proof<'a> { self }
    fn proof_mut(&mut self) -> &mut Proof<'a> { self }
}


pub trait ReachTactics<'a, 'b: 'a> {
    fn proof(&self) -> &ReachProof<'a, 'b>;
    fn proof_mut(&mut self) -> &mut ReachProof<'a, 'b>;

    /// Apply `rule_step` repeatedly until it returns `Err`.

    fn tactic_run(&mut self) {
        let pf = self.proof_mut();
        while pf.try_rule_step().is_ok() {
            // No-op
        }
    }

    /// Apply `rule_step` repeatedly until it returns `Err`, showing the error when it fails
    fn tactic_run_db(&mut self) {
        let pf = self.proof_mut();
        while true {
            match pf.try_rule_step() {
                Err (msg) => {
                    eprintln!("Simple step failed with {}", msg);
                    return
                }
                Ok (_) => ()
            }
        }
    }

    /// Apply `rule_step` repeatedly until it returns `Err`, showing the error when it fails
    fn tactic_run_concrete(&mut self) {
        let pf = self.proof_mut();
        while true {
            match pf.try_rule_step_concrete() {
                Err (msg) => {
                    eprintln!("Concrete step failed with {}", msg);
                    return
                }
                Ok (_) => ()
            }
        }
    }

    /// Apply `rule_step` until we reach the given `pc`.  Returns `Err` if `rule_step` reports an
    /// error before `pc` is reached.
    fn tactic_run_until(&mut self, pc: Addr) {
        let pf = self.proof_mut();
        while pf.pc() != pc && pf.try_rule_step().is_ok() {
            // No-op
        }
    }


    fn show_state(&self) {
        show_state_common(self.proof(), false)
    }

    fn show_state_verbose(&self) {
        show_state_common(self.proof(), true)
    }
}

impl<'a, 'b> ReachTactics<'a, 'b> for ReachProof<'a, 'b> {
    fn proof(&self) -> &ReachProof<'a, 'b> { self }
    fn proof_mut(&mut self) -> &mut ReachProof<'a, 'b> { self }
}


fn next_prop_id(pf: &Proof) -> PropId {
    (
        pf.scopes().len(),
        pf.props().len(),
    )
}

fn require_local_prop(pf: &Proof, pid: PropId) -> usize {
    let (s, i) = pid;
    assert_eq!(
        s, pf.scopes().len(),
        "expected a local PropId (in scope {}), but got one in scope {}",
        pf.scopes().len(), s,
    );
    i
}

fn show_prop_common(pf: &Proof, verbose: bool, id:PropId) {
    let (scope, index) = id;
    let scope_len = pf.scopes().len();
    if scope < scope_len {
        let p = &pf.scopes()[scope].props[index];
        eprintln!(
            "{}.{}: {}", scope, index,
            pf.printer_depth(scope as u32).verbose(verbose).display(&p),
        );
    } else if scope == scope_len {
        let p = &pf.props()[index];
        eprintln!(
            "{}.{}: {}", scope_len, index,
            pf.printer_depth(index as u32).verbose(verbose).display(&p),
        );
    } else {
        eprintln!("Error: Printing prop id not in scope: {}.{} not in {}", scope, index, pf.scopes().len());
    }
}

fn show_context_common(pf: &Proof, verbose: bool) {
    for (i, s) in pf.scopes().iter().enumerate() {
        for (j, p) in s.props.iter().enumerate() {
            eprintln!(
                "{}.{}: {}", i, j,
                pf.printer_depth(i as u32).verbose(verbose).display(p),
            );
        }
    }

    let i = pf.scopes().len();
    for (j, p) in pf.props().iter().enumerate() {
        eprintln!(
            "{}.{}: {}", i, j,
            pf.printer_depth(i as u32).verbose(verbose).display(p),
        );
    }
}

fn show_state_common(rpf: &ReachProof, verbose: bool) {
    let s = rpf.state();

    eprintln!("pc = {}", s.pc);

    for (i, x) in s.regs.iter().enumerate() {
        eprintln!(
            "  {}r{} = {}",
            if i < 10 { " " } else { "" },
            i,
            rpf.printer().verbose(verbose).display(x),
        );
    }

    eprintln!("mem = (TODO)");
    eprintln!("cycles = {}", rpf.cycles());
}
