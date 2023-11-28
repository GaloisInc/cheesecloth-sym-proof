use alloc::boxed::Box;
use alloc::vec::Vec;
use crate::Addr;
use crate::advice::{Record, Playback, RecordingStreamTag, PlaybackStreamTag};
use crate::kernel::{Proof, ReachProof, PropId};
use crate::logic::{Prop, Term, VarCounter};
use crate::micro_ram::{Reg, MemWidth};

define_numbered_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
    pub enum Rule {
        Done,
        Admit,
        Trivial,
        Clone,
        Swap,
        Apply,
        ForallIntro,
        ReachExtend,
        ReachShrink,
        ReachRenameVars,
        Induction,
    }
}

define_numbered_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
    pub enum ReachRule {
        Done,
        VarFresh,
        VarEq,
        Step,
        StepJump,
        StepLoadFresh,
        RewriteReg,
        ForgetReg,
        MemAbsConcrete,
        MemAbsMap,
        MemAbsLog,
        RewriteMem,
    }
}

impl Record for Rule {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.as_raw());
    }
}

impl Playback for Rule {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        Rule::from_raw(ps.playback())
    }
}

impl Record for ReachRule {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.as_raw());
    }
}

impl Playback for ReachRule {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        ReachRule::from_raw(ps.playback())
    }
}


pub fn playback_proof(pf: &mut Proof, ps: impl PlaybackStreamTag) {
    loop {
        match ps.playback() {
            Rule::Done => {
                break;
            },
            Rule::Admit => {
                let prop = ps.playback::<Prop>();
                pf.rule_admit(prop);
            },
            Rule::Trivial => {
                pf.rule_trivial();
            },
            Rule::Clone => {
                let pid = ps.playback::<PropId>();
                pf.rule_clone(pid);
            },
            Rule::Swap => {
                let index1 = ps.playback::<usize>();
                let index2 = ps.playback::<usize>();
                pf.rule_swap(index1, index2);
            },
            Rule::Apply => {
                let index = ps.playback::<usize>();
                let args = ps.playback::<Box<[Term]>>();
                pf.rule_apply(index, &args);
            },
            Rule::ForallIntro => {
                let vars = ps.playback::<VarCounter>();
                let premises = ps.playback::<Box<[Prop]>>();
                pf.rule_forall_intro(vars, premises, |pf| {
                    playback_proof(pf, ps);
                });
            },
            Rule::ReachExtend => {
                pf.rule_reach_extend(|rpf| {
                    playback_reach_proof(rpf, ps);
                });
            },
            Rule::ReachShrink => {
                let reach_index = ps.playback::<usize>();
                let new_min_cycles = ps.playback::<Term>();
                pf.rule_reach_shrink(reach_index, new_min_cycles);
            },
            Rule::ReachRenameVars => {
                let index = ps.playback::<usize>();
                let new_vars = ps.playback::<VarCounter>();
                let var_map = ps.playback::<Box<[Option<u32>]>>();
                pf.rule_reach_rename_vars(index, new_vars, &var_map);
            },
            Rule::Induction => {
                let index_zero = ps.playback::<usize>();
                let index_succ = ps.playback::<usize>();
                pf.rule_induction(index_zero, index_succ);
            },
        }
    }
}

pub fn playback_reach_proof(rpf: &mut ReachProof, ps: impl PlaybackStreamTag) {
    loop {
        match ps.playback() {
            ReachRule::Done => {
                break;
            },
            ReachRule::VarFresh => {
                let _: Term = rpf.rule_var_fresh();
            },
            ReachRule::VarEq => {
                let t = ps.playback::<Term>();
                let _: Term = rpf.rule_var_eq(t);
            },
            ReachRule::Step => {
                rpf.rule_step();
            },
            ReachRule::StepJump => {
                let taken = ps.playback::<bool>();
                rpf.rule_step_jump(taken);
            },
            ReachRule::StepLoadFresh => {
                rpf.rule_step_load_fresh();
            },
            ReachRule::RewriteReg => {
                let reg = ps.playback::<Reg>();
                let new = ps.playback::<Term>();
                rpf.rule_rewrite_reg(reg, new);
            },
            ReachRule::ForgetReg => {
                let reg = ps.playback::<Reg>();
                rpf.rule_forget_reg(reg);
            },
            ReachRule::MemAbsConcrete => {
                let addrs = ps.playback::<Vec<(Addr, MemWidth)>>();
                rpf.rule_mem_abs_concrete(&addrs);
            },
            ReachRule::MemAbsMap => {
                let addrs = ps.playback::<Vec<(Addr, MemWidth)>>();
                rpf.rule_mem_abs_map(&addrs);
            },
            ReachRule::MemAbsLog => {
                let addrs = ps.playback::<Vec<(Addr, MemWidth)>>();
                rpf.rule_mem_abs_log(&addrs);
            },
            ReachRule::RewriteMem => {
                let w = ps.playback::<MemWidth>();
                let addr = ps.playback::<Term>();
                let new = ps.playback::<Term>();
                rpf.rule_rewrite_mem(w, addr, new);
            },
        }
    }
}
