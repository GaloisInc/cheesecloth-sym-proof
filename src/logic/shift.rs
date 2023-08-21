use crate::logic::{VarId, Binder};
use crate::logic::fold::{self, Fold, Folder};

pub struct ShiftFolder {
    free_scope: u32,
    amount: u32,
}

impl ShiftFolder {
    pub fn new(free_scope: u32, amount: u32) -> ShiftFolder {
        ShiftFolder { free_scope, amount }
    }
}

impl Folder for ShiftFolder {
    fn fold_var_id(&mut self, x: VarId) -> VarId {
        if x.scope() >= self.free_scope {
            VarId::new(x.scope() + self.amount, x.index())
        } else {
            x
        }
    }
    fn fold_binder<T>(&mut self, x: &Binder<T>, f: impl FnOnce(&mut Self, &T) -> T) -> Binder<T> {
        self.free_scope += 1;
        let y = fold::default_fold_binder(self, x, f);
        self.free_scope -= 1;
        y
    }
}


pub trait ShiftExt: Sized {
    /// Increment the scope depth of every free variable in `self`.
    fn shift(&self) -> Self {
        self.shift_by(1)
    }
    fn shift_by(&self, amount: u32) -> Self {
        self.shift_free(0, amount)
    }
    /// Increase the scope depth of every free variable in `self` by `amount`.  A variable at top
    /// level is considered free if its scope depth is at least `free_scope`, or `free_scope + k`
    /// if the variable is under `k` binders.
    fn shift_free(&self, free_scope: u32, amount: u32) -> Self;
}

impl<T: Fold + Clone> ShiftExt for T {
    fn shift_free(&self, free_scope: u32, amount: u32) -> Self {
        if amount == 0 {
            return self.clone();
        }
        self.fold_with(&mut ShiftFolder::new(free_scope, amount))
    }
}
