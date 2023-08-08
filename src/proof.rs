use std::collections::HashMap;
use std::ops::Deref;
use crate::Addr;
use crate::symbolic::{State, Term, Pred, Memory, VarCounter};
use crate::micro_ram::{Instr, Opcode, Reg};


#[derive(Clone, Debug)]
pub enum Prop {
    Step(StepProp),
}

/// There exist `x0 ... xN` (`vars`) such that:
/// * `preds` hold, and
/// * for every concrete state `s` such that `pre(s)` holds, there exists some `M` and `s'` such
///   that `s ->M s'` and `post(s')` holds.
#[derive(Clone, Debug)]
pub struct StepProp {
    vars: VarCounter,
    preds: Vec<Pred>,
    pre: State,
    post: State,
}

impl StepProp {
    pub fn preds(&self) -> &[Pred] {
        &self.preds
    }

    pub fn pre(&self) -> &State {
        &self.pre
    }

    pub fn post(&self) -> &State {
        &self.post
    }
}


/// A collection of facts that have been proved so far.
///
/// In addition to appending new lemmas to the list, in some cases it's possible to mutate an
/// existing lemma.  In particular, if `P` implies `Q`, we might implement a rule that mutates `P`
/// to produce `Q`.  If you want the traditional behavior where applying the rule with `P` in scope
/// introduces a new `Q` lemma, clone the `P` lemma first using `rule_clone` and then apply the
/// mutating rule.
///
/// Naming convention: Functions named `rule_*` are the primitive rules of the proof system;
/// soundness of the system depends on their correctness.  Functions named `tactic_*` call other
/// rules and tactics, but don't directly manipulate the proof state, so they cannot introduce
/// unsoundness.
pub struct Proof {
    /// The program.  This is stored in the proof state to ensure that all lemmas are using the
    /// same program.
    prog: HashMap<u64, Instr>,

    lemmas: Vec<Prop>,
}

type LemmaId = usize;

impl Proof {
    pub fn new(prog: HashMap<u64, Instr>) -> Proof {
        Proof {
            prog,
            lemmas: Vec::new(),
        }
    }

    pub fn prog(&self) -> &HashMap<u64, Instr> {
        &self.prog
    }

    pub fn lemma(&self, id: LemmaId) -> &Prop {
        &self.lemmas[id]
    }

    fn add_lemma(&mut self, lemma: Prop) -> LemmaId {
        let i = self.lemmas.len();
        self.lemmas.push(lemma);
        i
    }

    /// Clone an existing lemma.  This is useful if you want to mutate a lemma but still keep the
    /// original.
    pub fn rule_clone(&mut self, id: LemmaId) -> LemmaId {
        self.add_lemma(self.lemmas[id].clone())
    }

    /// Introduce `{P} ->* {P}`.  Every state steps to itself in zero steps.
    ///
    /// All vars mentioned in `preds` and `state` must have been produced by `vars`.  Currently,
    /// this is not checked.
    pub fn rule_step_zero(&mut self, vars: VarCounter, preds: Vec<Pred>, state: State) -> LemmaId {
        self.add_lemma(Prop::Step(StepProp {
            vars,
            preds,
            pre: state.clone(),
            post: state,
        }))
    }

    /// Extend a `Prop::Step` lemma by adding more steps.
    pub fn rule_step_extend<R>(
        &mut self,
        id: LemmaId,
        f: impl FnOnce(StepProof) -> Result<R, String>,
    ) -> Result<R, String> {
        let p = match self.lemmas[id] {
            Prop::Step(ref mut p) => p,
            ref prop => panic!("expected Prop::Step, but got {:?}", prop),
        };
        f(StepProof { prog: &self.prog, p })
    }
}


pub struct StepProof<'a> {
    prog: &'a HashMap<u64, Instr>,
    p: &'a mut StepProp,
}

impl Deref for StepProof<'_> {
    type Target = State;
    fn deref(&self) -> &State {
        &self.p.post
    }
}

impl StepProof<'_> {
    fn fetch_instr(&self) -> Result<Instr, String> {
        let pc = self.p.post.pc;
        self.prog.get(&pc).cloned()
            .ok_or_else(|| format!("program executed out of bounds at {}", pc))
    }

    /// Handle a simple instruction that has no preconditions.
    pub fn rule_step_simple(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let x = self.p.post.reg_value(instr.r1);
        let y = self.p.post.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Binary(b) => {
                let z = Term::binary(b, x, y);
                self.p.post.set_reg(instr.rd, z);
            },
            Opcode::Not => {
                self.p.post.set_reg(instr.rd, Term::not(y));
            },
            Opcode::Mov => {
                self.p.post.set_reg(instr.rd, y);
            },
            Opcode::Cmov => {
                let old = self.reg_value(instr.rd);
                let z = Term::mux(x, y, old);
                self.p.post.set_reg(instr.rd, z);
            },

            Opcode::Jmp => Err("can't use step_simple for Jmp")?,
            Opcode::Cjmp => Err("can't use step_simple for Cjmp")?,
            Opcode::Cnjmp => Err("can't use step_simple for Cnjmp")?,

            Opcode::Store(_) => Err("can't use step_simple for Store")?,
            Opcode::Load(_) => Err("can't use step_simple for Load")?,
            Opcode::Poison(_) => Err("can't use step_simple for Poison")?,

            Opcode::Answer => {
                // Don't advance the PC.
                eprintln!("run {}: {:?} (simple)", self.pc, instr);
                return Ok(());
            },
            Opcode::Advise => Err("can't use step_simple for Advise")?,
        }

        eprintln!("run {}: {:?} (simple)", self.pc, instr);
        self.p.post.pc += 1;
        Ok(())
    }

    /// Handle a jump instruction with a concrete destination and/or condition.
    pub fn rule_step_jmp_concrete(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let old_pc = self.p.post.pc;
        let x = self.p.post.reg_value(instr.r1);
        let y = self.p.post.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Jmp => {
                // Always taken; dest must be concrete.
                self.p.post.pc = y.as_const_or_err()?;
            },
            Opcode::Cjmp => {
                // Conditionally taken; the condition must be concrete, and if the branch is taken,
                // then the dest must be concrete.
                if x.as_const_or_err()? != 0 {
                    self.p.post.pc = y.as_const_or_err()
                        .map_err(|e| format!("when evaluating dest: {e}"))?;
                } else {
                    self.p.post.pc += 1;
                }
            },
            Opcode::Cnjmp => {
                if x.as_const_or_err()? == 0 {
                    self.p.post.pc = y.as_const_or_err()
                        .map_err(|e| format!("when evaluating dest: {e}"))?;
                } else {
                    self.p.post.pc += 1;
                }
            },
            op => Err(format!("can't use step_jmp_concrete for {:?}", op))?,
        }

        eprintln!("run {}: {:?} (jmp_concrete)", old_pc, instr);
        Ok(())
    }

    /// Handle a memory instruction that accesses a concrete address and falls within a concrete
    /// memory region.
    pub fn rule_step_mem_concrete(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let x = self.p.post.reg_value(instr.r1);
        let y = self.p.post.operand_value(instr.op2);

        let addr = y.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;

        match instr.opcode {
            Opcode::Store(w) |
            Opcode::Poison(w) => {
                self.p.post.mem.store_concrete(w, addr, x)?;
            },

            Opcode::Load(w) => {
                let z = self.p.post.mem.load_concrete(w, addr)?;
                self.p.post.set_reg(instr.rd, z);
            },

            op => Err(format!("can't use step_mem_concrete for {:?}", op))?,
        }

        eprintln!("run {}: {:?} (mem_concrete)", self.pc, instr);
        self.p.post.pc += 1;
        Ok(())
    }

    /// Handle a memory instruction that accesses a symbolic address but requires no preconditions.
    pub fn rule_step_mem_symbolic(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        let x = self.p.post.reg_value(instr.r1);
        let y = self.p.post.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Store(w) |
            Opcode::Poison(w) => {
                self.p.post.mem.store(w, y, x)?;
            },

            Opcode::Load(w) => {
                let z = self.p.post.mem.load(w, y)?;
                self.p.post.set_reg(instr.rd, z);
            },

            op => Err(format!("can't use step_mem_symbolic for {:?}", op))?,
        }

        eprintln!("run {}: {:?} (mem_symbolic)", self.pc, instr);
        self.p.post.pc += 1;
        Ok(())
    }

    /// Handle a load instruction by introducing a fresh variable for the result.  This gives no
    /// information about the value that was actually loaded.
    pub fn rule_step_mem_load_fresh(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;

        match instr.opcode {
            Opcode::Load(w) => {
                let z = self.p.vars.var();
                self.p.post.set_reg(instr.rd, z);
            },

            op => Err(format!("can't use step_mem_load_fresh for {:?}", op))?,
        }

        eprintln!("run {}: {:?} (mem_load_fresh)", self.pc, instr);
        self.p.post.pc += 1;
        Ok(())
    }

    pub fn tactic_step_concrete(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        match instr.opcode {
            Opcode::Binary(_) |
            Opcode::Not |
            Opcode::Mov |
            Opcode::Cmov |
            Opcode::Answer => self.rule_step_simple(),

            Opcode::Jmp |
            Opcode::Cjmp |
            Opcode::Cnjmp => self.rule_step_jmp_concrete(),

            Opcode::Store(_) |
            Opcode::Poison(_) |
            Opcode::Load(_) => self.rule_step_mem_concrete(),

            op => Err(format!("can't use step_concrete for {:?}", op)),
        }
    }

    /// Take as many steps as possible with `tactic_step_concrete`.  Stops running when
    /// `tactic_step_concrete` returns an error.  The error from `tactic_step_concrete` is
    /// discarded; this method only returns `Err` if `self.pc` goes outside of `prog`.
    pub fn tactic_run_concrete(&mut self) -> Result<(), String> {
        loop {
            let instr = self.fetch_instr()?;
            if instr.opcode == Opcode::Answer {
                break;
            }
            let r = self.tactic_step_concrete();
            if r.is_err() {
                break;
            }
        }
        Ok(())
    }

    pub fn tactic_run_concrete_until(&mut self, pc: Addr) -> Result<(), String> {
        while self.p.post.pc != pc {
            let instr = self.fetch_instr()?;
            if instr.opcode == Opcode::Answer {
                return Err(format!("encountered Answer at {} before reaching pc = {}",
                    self.p.post.pc, pc));
            }
            self.tactic_step_concrete()?;
        }
        Ok(())
    }

    pub fn admit(&mut self, pred: Pred) {
        eprintln!("ADMITTED: {}", pred);
        self.p.preds.push(pred);
    }

    pub fn rule_rewrite_reg(&mut self, reg: Reg, t: Term) -> Result<(), String> {
        let reg_val = self.p.post.reg_value(reg);
        let need_pred = Pred::Eq(reg_val.clone(), t.clone());
        if !self.p.preds.contains(&need_pred) {
            return Err(format!("missing precondition: {} == {}", reg_val, t));
        }
        self.p.post.set_reg(reg, t);
        Ok(())
    }

    pub fn tactic_step_jmp_taken(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        match instr.opcode {
            Opcode::Cjmp => {
                self.rule_rewrite_reg(instr.r1, Term::const_(1))?;
            },
            Opcode::Cnjmp => {
                self.rule_rewrite_reg(instr.r1, Term::const_(0))?;
            },
            _ => {},
        }
        self.rule_step_jmp_concrete()
    }

    pub fn tactic_step_jmp_not_taken(&mut self) -> Result<(), String> {
        let instr = self.fetch_instr()?;
        match instr.opcode {
            Opcode::Cjmp => {
                self.rule_rewrite_reg(instr.r1, Term::const_(0))?;
            },
            Opcode::Cnjmp => {
                self.rule_rewrite_reg(instr.r1, Term::const_(1))?;
            },
            _ => {},
        }
        self.rule_step_jmp_concrete()
    }
}
