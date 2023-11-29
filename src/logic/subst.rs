use crate::logic::{VarId, Term, Binder};
use crate::logic::fold::{self, Fold, Folder};
use crate::logic::shift::ShiftExt;


pub struct SubstFolder<'a> {
    free_scope: u32,
    terms: &'a [Term],
}

impl<'a> SubstFolder<'a> {
    pub fn new(free_scope: u32, terms: &'a [Term]) -> SubstFolder<'a> {
        SubstFolder { free_scope, terms }
    }
}

impl Folder for SubstFolder<'_> {
    fn fold_term(&mut self, x: &Term) -> Term {
        if let Some(v) = x.as_var() {
            if v.scope() == self.free_scope {
                self.terms[v.index() as usize].shift_by(self.free_scope)
            } else if v.scope() > self.free_scope {
                Term::var_unchecked(VarId::new(v.scope() - 1, v.index()))
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


pub trait SubstExt: Sized {
    /// Substitute `terms` for the free variables of `Self`.  Only the immediate free variables
    /// (those in scope 0 at top level, or scope `k` when under `k` binders) will be substituted;
    /// free variables from outer scopes will be left unchanged.
    ///
    /// TODO: we also shift some vars, on the assumption that we're removing a binder
    fn subst(&self, terms: &[Term]) -> Self {
        self.subst_free(0, terms)
    }

    /// Substitute `terms` for the free variables in scope `free_scope`.  All other variables will
    /// be left unchanged.
    fn subst_free(&self, free_scope: u32, terms: &[Term]) -> Self;
}

impl<T: Fold> SubstExt for T {
    fn subst_free(&self, free_scope: u32, terms: &[Term]) -> Self {
        self.fold_with(&mut SubstFolder::new(free_scope, terms))
    }
}
