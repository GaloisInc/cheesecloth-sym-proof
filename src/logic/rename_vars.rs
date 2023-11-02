use crate::logic::{VarId, Term, Binder};
use crate::logic::fold::{self, Fold, Folder};


pub struct RenameVarsFolder<'a> {
    free_scope: u32,
    var_map: &'a [Option<u32>],
}

impl<'a> RenameVarsFolder<'a> {
    pub fn new(free_scope: u32, var_map: &'a [Option<u32>]) -> RenameVarsFolder<'a> {
        RenameVarsFolder { free_scope, var_map }
    }
}

impl Folder for RenameVarsFolder<'_> {
    fn fold_term(&mut self, x: &Term) -> Term {
        if let Some(v) = x.as_var() {
            if v.scope() == self.free_scope {
                let new_index = self.var_map.get(v.index() as usize).cloned().flatten()
                    .unwrap_or_else(|| {
                        panic!("term uses variable {}, which has no replacement in `var_map`",
                            v.index());
                    });
                Term::var_unchecked(VarId::new(self.free_scope, new_index))
            } else {
                x.clone()
            }
        } else {
            fold::default_fold_term(self, x)
        }
    }

    fn fold_binder<T>(&mut self, x: &Binder<T>, f: impl FnOnce(&mut Self, &T) -> T) -> Binder<T> {
        self.free_scope += 1;
        let y = fold::default_fold_binder(self, x, f);
        self.free_scope -= 1;
        y
    }
}


pub trait RenameVarsExt: Sized {
    /// Rename the free variables of `Self` using `var_map`.  Only the immediate free variables
    /// (those in scope 0 at top level, or scope `k` when under `k` binders) will be substituted;
    /// free variables from outer scopes will be left unchanged.
    ///
    /// Entries in `var_map` consist of variable indices only, not `VarId`s, because the variables
    /// must always be at the same scope depth as the variables being substituted.
    ///
    /// `var_map` may contain `None` for variables that are unused in `self`.  If `self` refers to
    /// a variable whose `var_map` entry is `None`, a panic occurs.
    ///
    /// This does not shift any variables.  The assumption is that if `self` is under a binder,
    /// then the result will be wrapped in a new binder with different variables.
    fn rename_vars(&self, var_map: &[Option<u32>]) -> Self {
        self.rename_vars_free(0, var_map)
    }

    /// Rename the free variables of `Self` using `var_map`.  All other variables will be left
    /// unchanged.
    fn rename_vars_free(&self, free_scope: u32, var_map: &[Option<u32>]) -> Self;
}

impl<T: Fold> RenameVarsExt for T {
    fn rename_vars_free(&self, free_scope: u32, var_map: &[Option<u32>]) -> Self {
        self.fold_with(&mut RenameVarsFolder::new(free_scope, var_map))
    }
}
