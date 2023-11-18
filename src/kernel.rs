use std::array;
use std::borrow::Cow;
use std::convert::TryFrom;
use std::fmt::{Display, Write as _};
use std::iter;
use std::mem;
use std::ops::{Deref, DerefMut};
use crate::{Word, Addr};
use crate::advice;
use crate::advice::vec::AVec;
#[allow(unused)] use crate::advice::{PlaybackStreamTag, RecordingStreamTag};
use crate::interp::{Rule, ReachRule};
use crate::logic::{Prop, Term, Binder, VarCounter, ReachableProp, StatePred};
use crate::logic::eq_shifted::EqShifted;
use crate::logic::print::{Print, Printer, DisplayWithPrinter};
use crate::logic::rename_vars::RenameVarsExt;
use crate::logic::shift::ShiftExt;
use crate::logic::wf::WfExt;
use crate::micro_ram::{Instr, Opcode, Reg, Operand, MemWidth, Program};
use crate::symbolic::{self, Memory, MemState, MemLog};


#[cfg(feature = "verbose")]
macro_rules! die {
    ($($args:tt)*) => {
        panic!("proof failed: {}", format_args!($($args)*))
    };
}

#[cfg(not(feature = "verbose"))]
macro_rules! die {
    ($($args:tt)*) => {
        {
            let _ = format_args!($($args)*);
            panic!("proof failed")
        }
    };
}

// TODO: microram version, which just triggers an assertion fail and doesn't panic


macro_rules! require {
    ($cond:expr) => {
        require!($cond, stringify!($cond))
    };
    ($cond:expr, $($args:tt)*) => {
        if !$cond {
            die!($($args)*);
        }
    };
}

macro_rules! require_eq {
    ($x:expr, $y:expr) => {
        require!($x == $y)
    };
    ($x:expr, $y:expr, $($args:tt)*) => {
        require!(
            $x == $y,
            "{} (when checking {} == {})",
            format_args!($($args)*),
            stringify!($x),
            stringify!($y),
        )
    };
}


#[cfg(any(feature = "recording_rules", feature = "recording_term_index"))]
macro_rules! record {
    ($($x:expr),*) => {{
        $( advice::recording::rules::Tag.record(&$x); )*
    }};
}

#[cfg(not(any(feature = "recording_rules", feature = "recording_term_index")))]
macro_rules! record {
    ($($x:expr),*) => {{
    }};
}


/// Identifier for a `Prop` in the current context.  The first part is the scope index (0 for the
/// outermost scope, `pf.scopes.len()` for the innermost) and the second is an index into
/// `scope.props`.
pub type PropId = (usize, usize);

pub struct Proof<'a> {
    prog: Program<'a>,

    /// Enclosing scopes.  `scopes[0]` is the outermost and `scopes.last()` is the innermost.  For
    /// each one, we have a list of propositions that are known to hold over the variables of that
    /// scope and outer scopes.
    ///
    /// In the proof, we can refer to variables from outer scopes (using normal de Bruijn indices),
    /// but we can't directly refer to `Prop`s established in outer scopes.  To use those `Prop`s,
    /// the proof must first call `rule_shift`, which copies the outer `Prop` into the current
    /// scope and shifts its variables to account for the additional binders.
    scopes: AVec<Scope>,

    /// The current, innermost scope.
    cur: Scope,
}

pub struct Scope {
    pub vars: VarCounter,
    pub props: AVec<Prop>,
}

impl<'a> Proof<'a> {
    pub fn new(prog: Program<'a>) -> Proof<'a> {
        Proof {
            prog,
            scopes: AVec::new(),
            cur: Scope {
                vars: VarCounter::new(),
                props: AVec::new(),
            },
        }
    }


    // Provide read-only access to all fields.  Mutation must go through `rule_*` methods, which
    // only add provable `Prop`s to the context.

    pub fn prog(&self) -> &Program<'a> {
        &self.prog
    }

    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }

    pub fn cur(&self) -> &Scope {
        &self.cur
    }

    pub fn props(&self) -> &[Prop] {
        &self.cur().props
    }


    pub fn enter<R>(
        &mut self,
        vars: VarCounter,
        props: AVec<Prop>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.enter_ex(vars, props, f).0
    }

    fn enter_ex<R>(
        &mut self,
        vars: VarCounter,
        props: AVec<Prop>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> (R, Scope) {
        #[cfg(feature = "verbose")] {
            println!("entered scope {} with {} vars", self.scopes.len() + 1, vars.len());
            for (i, p) in props.iter().enumerate() {
                println!("introduced {}.{}: {}", self.scopes.len() + 1, i, self.print_adj(1, p));
            }
        }
        let scope = mem::replace(&mut self.cur, Scope { vars, props });
        self.scopes.push(scope);
        #[cfg(debug_assertions)] let old_scopes_len = self.scopes.len();

        // Note that if `f` returns `Result`, we do the following cleanup and return the final
        // `Scope` even when it fails.
        let r = f(self);

        #[cfg(debug_assertions)] assert_eq!(old_scopes_len, self.scopes.len());
        let inner_scope = mem::replace(&mut self.cur, self.scopes.pop().unwrap());
        #[cfg(feature = "verbose")] {
            println!("exited scope {}", self.scopes.len() + 1);
        }
        (r, inner_scope)
    }


    // Helper functions for printing.
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
        self.printer_depth(self.scopes.len() as u32 + adj_depth)
    }

    pub fn printer_depth(&self, depth: u32) -> Printer {
        Printer::new(depth)
    }


    fn add_prop(&mut self, prop: Prop) {
        #[cfg(debug_assertions)] {
            let num_vars = self.scopes.iter().map(|s| s.vars.len())
                .chain(iter::once(self.cur.vars.len()))
                .collect::<Vec<_>>();
            if let Err(e) = prop.check_wf(num_vars) {
                panic!("tried to add ill-formed proposition {}\n{}", self.print(&prop), e);
            }
        }

        #[cfg(feature = "verbose")] {
            let depth = self.scopes.len();
            let i = self.cur.props.len();
            println!("proved {}.{}: {}", depth, i, self.print(&prop));
        }

        self.cur.props.push(prop);
    }

    fn check_updated_prop(&self, i: usize) {
        #[cfg(debug_assertions)] {
            let prop = self.prop(i);

            let num_vars = self.scopes.iter().map(|s| s.vars.len())
                .chain(iter::once(self.cur.vars.len()))
                .collect::<Vec<_>>();
            if let Err(e) = prop.check_wf(num_vars) {
                panic!("update produced ill-formed proposition {}\n{}", self.print(prop), e);
            }
        }

        #[cfg(feature = "verbose")] {
            let prop = self.prop(i);
            let depth = self.scopes.len();
            println!("updated {}.{}: {}", depth, i, self.print(prop));
        }
    }

    /// Like `add_prop`, but for the case where `prop` was popped, mutated, and now is being pushed
    /// back onto `self.cur.props`.  This uses `check_updated_prop` to provide clearer wording in
    /// error messages.
    fn push_updated_prop(&mut self, prop: Prop) {
        let i = self.cur.props.len();
        self.cur.props.push(prop);
        self.check_updated_prop(i);
    }

    fn prop(&self, i: usize) -> &Prop {
        &self.cur.props[i]
    }

    fn prop_mut(&mut self, i: usize) -> &mut Prop {
        &mut self.cur.props[i]
    }


    fn prop_ptr(p: &Prop) -> *const () {
        match *p {
            Prop::Nonzero(ref t) => t.as_ptr(),
            _ => std::ptr::null(),
        }
    }

    /// Ensure that `premise` appears somewhere in the current context.  Panics if a matching
    /// `Prop` is not found.
    fn require_premise(&self, premise: &Prop) {
        self.require_premise_one_of([&|| Cow::Borrowed(premise)]);
    }

    /// Ensure the context contains some `Prop` for which `f(prop)` returns true.  `Prop`s from
    /// outer scopes are shifted automatically, so `f` always receives a `Prop` suitable for use in
    /// the current innermost scope.  Panics if a matching `Prop` is not found.
    ///
    /// `desc` is a human-readable description of what `f` was searching for, used for error
    /// messages.
    fn require_premise_one_of<'b, const N: usize>(
        &self,
        premises: [&dyn Fn() -> Cow<'b, Prop>; N],
    ) {
        #[cfg(feature = "playback_search_index")] {
            let ps = advice::playback::search_index::Tag;

            let (k, premise_fn) = ps.take_index_and_elem(&premises);
            let premise: Cow<Prop> = premise_fn();
            let premise: &Prop = &*premise;

            if ps.playback::<bool>() {
                let (j, prop) = ps.take_index_and_elem(&self.cur.props);
                require!(premise == prop,
                    "bad advice: premise not found (j = {}, k = {})", j, k);
            } else {
                let (i, scope) = ps.take_index_and_elem(&self.scopes);
                let (j, prop) = ps.take_index_and_elem(&scope.props);
                let shift_amount = (self.scopes.len() - i) as u32;
                require!(premise.eq_shifted(&prop, shift_amount),
                    "bad advice: premise not found (i = {}, j = {}, k = {})", i, j, k);
            }

            return;
        }

        let premises: [Cow<Prop>; N] = array::from_fn(|i| premises[i]());
        let premises: [&Prop; N] = array::from_fn(|i| &*premises[i]);

        let check = |prop, shift_amount| {
            for (k, &expect_prop) in premises.iter().enumerate() {
                if expect_prop.eq_shifted(prop, shift_amount) {
                    return Some(k);
                }
            }
            None
        };

        for (j, prop) in self.cur.props.iter().enumerate() {
            if let Some(k) = check(prop, 0) {
                #[cfg(feature = "recording_search_index")] {
                    let rs = advice::recording::search_index::Tag;
                    rs.record(&k);
                    rs.record(&true);
                    rs.record(&j);
                }
                return;
            }
        }

        for (i, s) in self.scopes.iter().enumerate().rev() {
            let shift_amount = (self.scopes.len() - i) as u32;
            for (j, prop) in s.props.iter().enumerate() {
                if let Some(k) = check(prop, shift_amount) {
                    #[cfg(feature = "recording_search_index")] {
                        let rs = advice::recording::search_index::Tag;
                        rs.record(&k);
                        rs.record(&false);
                        rs.record(&i);
                        rs.record(&j);
                    }
                    return;
                }
            }
        }

        #[cfg(feature = "verbose")] {
            let mut desc = String::new();
            for (i, p) in premises.iter().enumerate() {
                if i > 0 {
                    desc.push_str(" or ");
                }
                write!(desc, "{}", self.print(p)).unwrap();
            }
            die!("missing premise: {}", desc);
        }
        #[cfg(not(feature = "verbose"))] {
            die!("missing premise");
        }
    }


    pub fn rule_admit(&mut self, prop: Prop) {
        record!(Rule::Admit, prop);
        #[cfg(feature = "verbose")] {
            println!("ADMITTED: {}", self.print(&prop));
        }
        self.add_prop(prop);
    }

    /// Introduce the trivial proposition `1`.
    pub fn rule_trivial(&mut self) {
        record!(Rule::Trivial);
        self.add_prop(Prop::Nonzero(1.into()));
    }

    /// Duplicate a `Prop` into the innermost scope.
    pub fn rule_clone(&mut self, pid: PropId) {
        record!(Rule::Clone, pid);
        let (s, i) = pid;
        let prop = if s == self.scopes.len() {
            self.cur.props[i].clone()
        } else {
            let shift_amount = u32::try_from(self.scopes.len() - s).unwrap();
            self.scopes[s].props[i].shift_by(shift_amount)
        };
        self.add_prop(prop);
    }

    /// Swap two `Prop`s in the current scope.  This is useful for rules like `rule_reach_extend`
    /// that operate specifically on the last `Prop` in scope.
    pub fn rule_swap(&mut self, index1: usize, index2: usize) {
        record!(Rule::Swap, index1, index2);
        require!(index1 < self.cur.props.len());
        require!(index2 < self.cur.props.len());
        self.cur.props.swap(index1, index2);
    }

    /// Apply a `Prop::Forall` to arguments.  `args` provides `Term`s to be substituted for the
    /// bound variables.  After substitution, the premises of the `Forall` are required to hold,
    /// and the conclusion is introduced into the current scope.
    pub fn rule_apply(
        &mut self,
        index: usize,
        args: &[Term],
    ) {
        record!(Rule::Apply, index, args);
        let prop = self.prop(index);
        let binder = match *prop {
            Prop::Forall(ref b) => b,
            _ => die!("rule_apply: expected forall, but got {}", self.print(prop)),
        };

        let premises = binder.map(|&(ref ps, _)| &**ps);
        for premise in premises.iter() {
            let premise = premise.subst_ref(args);
            self.require_premise(&premise);
        }

        let conclusion = binder.map(|&(_, ref q)| &**q);
        let conclusion = conclusion.subst_ref(args);
        self.add_prop(conclusion);
    }

    /// Prove a theorem of the form `forall xs, Ps(xs) -> Q(xs)`.  `vars` gives the number of bound
    /// variables (the `xs`), `premises` is the `Ps`, and `conclusion` is `Q`.  The `prove`
    /// callback is run in an inner scope containing the `premises`; it must establish the
    /// `conclusion` and then return.
    ///
    /// Note that the `prove` callback runs under a binder, so terms from outside should be
    /// `shift`-ed before use.
    pub fn rule_forall_intro(
        &mut self,
        vars: VarCounter,
        premises: Box<[Prop]>,
        prove: impl FnOnce(&mut Proof),
    ) {
        record!(Rule::ForallIntro, vars, premises);
        // Check that `conclusion` can be proved given `premises`.
        let ((), mut inner_scope) = self.enter_ex(
            vars,
            premises.clone().into(),
            |pf| {
                prove(pf);
                record!(Rule::Done);
            },
        );
        let vars = inner_scope.vars;
        let conclusion = inner_scope.props.pop()
            .unwrap_or_else(|| die!("`prove` callback did not prove anything"));

        // Add the new `Prop::Forall` to the current scope.
        let b = Binder::from_parts(
            vars,
            (premises, Box::new(conclusion)),
        );
        self.add_prop(Prop::Forall(b));
    }

    /// Extend a `Prop::Reachable`, updating it in-place to another `Prop::Reachable` that's
    /// implied by the first.  This always extends the last `Prop` in the current scope; use
    /// `rule_swap` to reorder the scope if you need to operate on a different `Prop`.
    pub fn rule_reach_extend(
        &mut self,
        f: impl FnOnce(&mut ReachProof),
    ) {
        record!(Rule::ReachExtend);
        let last_prop = self.cur.props.pop()
            .unwrap_or_else(|| die!("there are no props in the current scope"));
        let rp = match last_prop {
            Prop::Reachable(rp) => rp,
            prop =>
                die!("expected last prop to be Prop::Reachable, but got {}", self.print(&prop)),
        };

        // Disassemble `rp` into its component parts.
        //
        // Note that `rp.pred` is a `Binder`.  `min_cycles` is outside the binder, and the rest are
        // inside.
        let min_cycles: Term = rp.min_cycles;
        let vars: VarCounter = rp.pred.vars;
        let state: symbolic::State = rp.pred.inner.state;
        let props: Box<[Prop]> = rp.pred.inner.props;

        // Open the existential binder.
        //
        // In Coq terms, we're trying to prove something like `(exists x, P x) -> (exists y, Q y)`.
        // We start by destructing the premise to bring `x` and `H : P x` into scope (this code),
        // do some work on the context (`f`), and finally give a witness `y` such that `H' : Q y`
        // is in scope (below).  To simplify the design, `y` is always `x` together with any fresh
        // variables introduced by `f`, and `Q` is always all the `Prop`s in scope at the end of
        // `f`.
        let ((state, add_cycles), inner_scope) = self.enter_ex(
            vars,
            props.into(),
            |pf| -> (symbolic::State, Word) {
                let mut rpf = ReachProof {
                    pf,
                    state,
                    cycles: 0,
                };
                f(&mut rpf);
                record!(Rule::Done);
                (rpf.state, rpf.cycles)
            },
        );

        let rp = ReachableProp {
            pred: Binder::from_parts(
                inner_scope.vars,
                StatePred {
                    state,
                    props: inner_scope.props.into(),
                },
            ),
            min_cycles: Term::add(min_cycles, add_cycles.into()),
        };
        self.push_updated_prop(Prop::Reachable(rp));
    }

    /// Reduce the `min_cycles` of the `Prop::Reachable` to `new_min_cycles`.  Requires the premise
    /// `min_cycles >= new_min_cycles` to be available in the context.  This is valid because
    /// `min_cycles` is a lower bound, not the exact execution time.  This method mutates the
    /// `Prop::Reachable` in-place.
    ///
    /// This also accepts comparisons of the form `x >u y` and `x == y`, both of which imply the
    /// required `x >=u y`.
    pub fn rule_reach_shrink(
        &mut self,
        reach_index: usize,
        new_min_cycles: Term,
    ) {
        record!(Rule::ReachShrink, reach_index, new_min_cycles);
        let rp = match *self.prop_mut(reach_index) {
            Prop::Reachable(ref mut rp) => rp,
            _ => die!("expected prop {} to be Prop::Reachable, but got {}",
                reach_index, self.print(self.prop(reach_index))),
        };
        let old_min_cycles = mem::replace(&mut rp.min_cycles, new_min_cycles);
        self.require_premise_one_of([
            &|| Cow::Owned(Prop::Nonzero(Term::cmpae(old_min_cycles, new_min_cycles))),
            &|| Cow::Owned(Prop::Nonzero(Term::cmpa(old_min_cycles, new_min_cycles))),
            &|| Cow::Owned(Prop::Nonzero(Term::cmpe(old_min_cycles, new_min_cycles))),
        ]);
        self.check_updated_prop(reach_index);
    }

    /// Rename the existential variables in a `Prop::Reachable`.  Each variable `v` is replaced
    /// with `var_map[v]` (or a panic occurs if `var_map[v]` is `None`), and the resulting
    /// `Prop::Reachable` has `new_vars.len()` vars.  This updates the `Prop::Reachable` at `index`
    /// in-place.
    pub fn rule_reach_rename_vars(
        &mut self,
        index: usize,
        new_vars: VarCounter,
        var_map: &[Option<u32>],
    ) {
        record!(Rule::ReachRenameVars, index, new_vars, var_map);
        let rp = match *self.prop_mut(index) {
            Prop::Reachable(ref mut rp) => rp,
            _ => die!("expected prop {} to be Prop::Reachable, but got {}",
                index, self.print(self.prop(index))),
        };

        #[cfg(debug_assertions)] {
            assert!(var_map.len() <= rp.pred.vars.len(),
                "too many vars in var_map; expected at most {}, but got {}",
                rp.pred.vars.len(), var_map.len());
            for &new_index in var_map {
                if let Some(new_index) = new_index {
                    assert!(new_index < new_vars.len() as u32,
                        "var index {} out of range for binder with {} variables",
                        new_index, new_vars.len());
                }
            }
        }

        // TODO: walk `Prop` and rewrite terms in-place (avoiding reallocation)
        rp.pred.inner = rp.pred.inner.rename_vars(var_map);
        rp.pred.vars = new_vars;
        self.check_updated_prop(index);
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
    ///
    /// We take only the indices of `Hzero` and `Hsucc` as inputs.  The predicate `P` is inferred
    /// from the second premise of `Hsucc`.
    pub fn rule_induction(
        &mut self,
        index_zero: usize,
        index_succ: usize,
    ) {
        record!(Rule::Induction, index_zero, index_succ);
        // Process `Hsucc` first, since it lets us infer the predicate `P`.
        let succ_prop = self.prop(index_succ);
        let succ_binder = match *succ_prop {
            Prop::Forall(ref b) => b,
            ref p => die!("expected successor prop {} to be Prop::Reachable, but got {}",
                index_succ, self.print(p)),
        };
        require_eq!(succ_binder.vars.len(), 1,
            "expected successor prop to have exactly one bound var, but found {} in {}",
            succ_binder.vars.len(), self.print(succ_prop));
        require_eq!(succ_binder.inner.0.len(), 2,
            "expected successor prop to have exactly two premises, but found {} in {}",
            succ_binder.inner.0.len(), self.print(succ_prop));

        let succ_p1 = succ_binder.as_ref().map(|&(ref ps, _)| &ps[0]);
        let succ_p2 = succ_binder.as_ref().map(|&(ref ps, _)| &ps[1]);
        let succ_q = succ_binder.as_ref().map(|&(_, ref q)| &**q);

        // The first premise must be `n + 1 > 0`.
        let expect_p1 = Binder::new(|vars| {
            let n = vars.fresh();
            Prop::Nonzero(Term::cmpa(Term::add(n, 1.into()), 0.into()))
        });
        require_eq!(succ_p1, expect_p1.as_ref(),
            "expected first premise to be {}, but got {}",
            self.print_adj(1, &expect_p1.inner), self.print_adj(1, succ_p1.inner));

        // Extract the second premise as `P`.
        let predicate = succ_p2;

        // The conclusion must be `P (n + 1)`.
        let expect_q = Binder::new(|vars| {
            let n = vars.fresh();
            let n_plus_1 = Term::add(n, 1.into());
            predicate.subst_ref(&[n_plus_1])
        });
        require_eq!(succ_q, expect_q.as_ref(),
            "expected conclusion to be {}, but got {}",
            self.print_adj(1, &expect_q.inner), self.print_adj(1, succ_q.inner));

        // Process `Hzero`.  It must be exactly `P 0`.
        let zero_prop = self.prop(index_zero);
        let expect_zero_prop = predicate.subst_ref(&[0.into()]);
        require_eq!(zero_prop, &expect_zero_prop,
            "expected conclusion to be {}, but got {}",
            self.print(&expect_zero_prop), self.print(zero_prop));

        // Add the conclusion.
        let conclusion = Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            (vec![].into(), Box::new(predicate.subst_ref(&[n])))
        }));
        self.add_prop(conclusion);
    }
}


/// A `Proof` state where the innermost scope represents the existential binder of a
/// `ReachableProp`.  This scope contains a few extra things that are not representable in a normal
/// `Proof`:
///
/// - A MicroRAM state `s`
/// - The proposition that `s` refines the symbolic state `self.state`
/// - A step count `n` (we could represent this explicitly as a `Word` variable, but we don't)
/// - The proposition that `s0 ->(n) s`
/// - The proposition that `n >= min_cycles + self.cycles`
///
/// The fact that the inner scope is an existential doesn't matter, as described in
/// `rule_reach_extend`, so `ReachProof` exposes all the usual methods of `Proof`, as well as a few
/// that are specific to symbolic execution.
pub struct ReachProof<'a, 'b> {
    pf: &'a mut Proof<'b>,
    state: symbolic::State,
    cycles: Word,
}

impl<'b> Deref for ReachProof<'_, 'b> {
    type Target = Proof<'b>;
    fn deref(&self) -> &Proof<'b> {
        &*self.pf
    }
}

impl<'b> DerefMut for ReachProof<'_, 'b> {
    fn deref_mut(&mut self) -> &mut Proof<'b> {
        &mut *self.pf
    }
}

impl<'a, 'b> ReachProof<'a, 'b> {
    pub fn state(&self) -> &symbolic::State {
        &self.state
    }

    pub fn cycles(&self) -> Word {
        self.cycles
    }


    pub fn pc(&self) -> Addr {
        self.state.pc
    }

    fn get_instr_at(&self, pc:Addr) -> Instr {
        self.pf.prog.get(pc).cloned()
            .unwrap_or_else(|| die!("program executed out of bounds at {}", pc))
    }
    
    fn fetch_instr(&self) -> Instr {
        let pc = self.pc();
        self.get_instr_at(pc)
    }

    fn reg_value(&self, reg: Reg) -> Term {
        self.state.reg_value(reg)
    }

    fn operand_value(&self, op: Operand) -> Term {
        self.state.operand_value(op)
    }

    fn set_reg(&mut self, reg: Reg, value: Term) {
        self.state.set_reg(reg, value);
    }

    fn mem_store(&mut self, w: MemWidth, addr: Term, value: Term) {
        self.state.mem.store(w, addr, value, &[])
            .unwrap_or_else(|e| die!("mem_store failed: {}", e))
    }

    fn mem_load(&self, w: MemWidth, addr: Term) -> Term {
        let _ = (w, addr);
        die!("StepProof::mem_load not yet implemented")
    }

    fn finish_instr(&mut self) {
        self.finish_instr_jump(self.pc() + 1);
    }

    fn finish_instr_jump(&mut self, pc: Addr) {
        self.state.pc = pc;
        self.cycles += 1;

        // Execute one step with the concrete state and validate the
        // symbolic state with it
        #[cfg(feature = "debug_symbolic")]
        self.conc_step();
    }

    fn fresh_var(&mut self) -> Term {
        self.pf.cur.vars.fresh()
    }

    #[cfg(feature = "debug_symbolic")]
    fn conc_step(&mut self) {
        // We shouldn't have advice in proofs.
        // Advice should be handled explicitely.
        let advice = None;
        let conc_pc = self.state.conc_pc().unwrap_or(0);
        let instr = self.get_instr_at(conc_pc);
        self.state.conc_step(instr, advice);
    }

    /// Introduce a new unconstrained variable.
    pub fn rule_var_fresh(&mut self) -> Term {
        record!(ReachRule::VarFresh);
        self.fresh_var()
    }

    /// Introduce a new variable `x` and add the equality `x == t` to the context.  Returns the new
    /// variable as a `Term`.
    pub fn rule_var_eq(&mut self, t: Term) -> Term {
        record!(ReachRule::VarEq, t);
        let x = self.fresh_var();
        self.pf.add_prop(Prop::Nonzero(Term::cmpe(x, t)));
        x
    }

    /// Perform one step of execution.  In some cases, this may fail due to a missing precondition.
    pub fn rule_step(&mut self) {
        record!(ReachRule::Step);
        let instr = self.fetch_instr();
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
                    .unwrap_or_else(|e| die!("error evaluating jmp dest: {e}"));
                self.finish_instr_jump(dest);
                return;
            },
            Opcode::Cjmp => die!("can't use rule_step for Cjmp"),
            Opcode::Cnjmp => die!("can't use rule_step for Cnjmp"),

            // Note: `mem_store` and `mem_load` can fail.  For `try_rule_step`, it's important that
            // we not perform any side effects prior to a panic.
            Opcode::Store(w) |
            Opcode::Poison(w) => {
                self.mem_store(w, y, x);
            },
            Opcode::Load(w) => {
                let z = self.mem_load(w, y);
                self.set_reg(instr.rd, z);
            },

            Opcode::Answer => {
                // Don't advance the PC.
                #[cfg(feature = "verbose")] {
                    println!("run {}: {:?} (simple)", self.pc(), instr);
                }
                self.finish_instr_jump(self.pc());
                return;
            },
            Opcode::Advise => die!("can't use step_simple for Advise"),
        }

        #[cfg(feature = "verbose")] {
            println!("run {}: {:?} (simple)", self.pc(), instr);
        }
        self.finish_instr();
    }

    /// Try to take a step.  Returns `true` on success or `false` if `rule_step` panics.  On
    /// failure, the proof state remains unchanged.
    pub fn try_rule_step(&mut self) -> bool {
        use std::panic::{self, AssertUnwindSafe};

        // Use an empty panic hook to suppress the "thread 'main' panicked at ..." message.
        let old_hook = panic::take_hook();
        panic::set_hook(Box::new(|_| {}));

        let f = AssertUnwindSafe(|| {
            self.rule_step();
        });
        let ok = panic::catch_unwind(|| {
            advice::rollback_on_panic(f);
        }).is_ok();

        panic::set_hook(old_hook);

        ok
    }

    /// Handle a conditional jump (`Opcode::Cjmp` or `Opcode::Cnjmp`), taking the jump if `taken`
    /// is set and falling through otherwise.  There must be a `Prop` in scope (either in the
    /// current scope or an outer scope) showing that the jump condition will result in the
    /// behavior indicated by `taken`.
    pub fn rule_step_jump(&mut self, taken: bool) {
        record!(ReachRule::StepJump, taken);
        let instr = self.fetch_instr();
        let x = self.reg_value(instr.r1);
        let y = self.operand_value(instr.op2);

        // Check that the precondition for taking / not taking the jump has been established.
        match instr.opcode {
            Opcode::Jmp => {
                if !taken {
                    die!("can't fall through an unconditional Jmp");
                }
            },
            Opcode::Cjmp => {
                if taken {
                    self.pf.require_premise(&Prop::Nonzero(x));
                } else {
                    self.pf.require_premise(&Prop::Nonzero(Term::cmpe(x, 0.into())));
                }
            },
            Opcode::Cnjmp => {
                if taken {
                    self.pf.require_premise(&Prop::Nonzero(Term::cmpe(x, 0.into())));
                } else {
                    self.pf.require_premise(&Prop::Nonzero(x));
                }
            },

            op => die!("can't use rule_step_jump for {:?}", op),
        }

        if taken {
            let dest = y.as_const_or_err()
                .unwrap_or_else(|e| die!("error evaluating jmp dest: {e}"));
            #[cfg(feature = "verbose")] {
                println!("run {}: {:?} (jump, taken)", self.pc(), instr);
            }
            self.finish_instr_jump(dest);
        } else {
            #[cfg(feature = "verbose")] {
                println!("run {}: {:?} (jump, not taken)", self.pc(), instr);
            }
            self.finish_instr();
        }
    }

    /// Handle a load instruction by introducing a fresh variable for the result.  This gives no
    /// information about the value that was actually loaded.
    pub fn rule_step_load_fresh(&mut self) {
        record!(ReachRule::StepLoadFresh);
        let instr = self.fetch_instr();

        match instr.opcode {
            Opcode::Load(_) => {
                let z = self.fresh_var();
                self.set_reg(instr.rd, z);
            },

            op => die!("can't use rule_step_load_fresh for {:?}", op),
        }

        #[cfg(feature = "verbose")] {
            println!("run {}: {:?} (load_fresh)", self.pc(), instr);
        }
        self.finish_instr();
    }

    /// Rewrite the value of `reg` to `new`.  Requires the premise `old == new` to be available in
    /// the context.
    pub fn rule_rewrite_reg(&mut self, reg: Reg, new: Term) {
        record!(ReachRule::RewriteReg, reg, new);
        let old = self.reg_value(reg);
        self.require_premise_one_of([
            &|| Cow::Owned(Prop::Nonzero(Term::cmpe(old, new))),
            &|| Cow::Owned(Prop::Nonzero(Term::cmpe(new, old))),
        ]);
        self.set_reg(reg, new);
    }

    /// Replace the value of `reg` with a fresh symbolic variable.
    pub fn rule_forget_reg(&mut self, reg: Reg) {
        record!(ReachRule::ForgetReg, reg);
        let z = self.fresh_var();
        self.set_reg(reg, z);
    }

    /// Forget all known facts about memory.
    pub fn rule_forget_mem(&mut self) {
        record!(ReachRule::ForgetMem);
        self.state.mem = MemState::Log(MemLog::new());
    }
}
