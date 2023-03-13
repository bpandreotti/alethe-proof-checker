use super::{Identifier, Rc, Sort, Term, Terminal};
use ahash::{AHashMap, AHashSet};

/// A structure to store and manage all allocated terms.
///
/// You can add a `Term` to the pool using [`TermPool::add`], which will return an `Rc<Term>`. This
/// struct ensures that, if two equal terms are added to a pool, they will be in the same
/// allocation. This invariant allows terms to be safely compared and hashed by reference, instead
/// of by value (see [`Rc`]).
///
/// This struct also provides other utility methods, like computing the sort of a term (see
/// [`TermPool::sort`]) or its free variables (see [`TermPool::free_vars`]).
pub struct TermPool {
    pub(crate) terms: AHashMap<Term, Rc<Term>>,
    free_vars_cache: AHashMap<Rc<Term>, AHashSet<Rc<Term>>>,
    sorts_cache: AHashMap<Rc<Term>, Sort>,
    bool_true: Rc<Term>,
    bool_false: Rc<Term>,
}

impl Default for TermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl TermPool {
    /// Constructs a new `TermPool`. This new pool will already contain the boolean constants `true`
    /// and `false`, as well as the `Bool` sort.
    pub fn new() -> Self {
        let mut terms = AHashMap::new();
        let mut sorts_cache = AHashMap::new();
        let bool_sort = Self::add_term_to_map(&mut terms, Term::Sort(Sort::Bool));

        let [bool_true, bool_false] = ["true", "false"].map(|b| {
            Self::add_term_to_map(
                &mut terms,
                Term::Terminal(Terminal::Var(
                    Identifier::Simple(b.into()),
                    bool_sort.clone(),
                )),
            )
        });

        sorts_cache.insert(bool_false.clone(), Sort::Bool);
        sorts_cache.insert(bool_true.clone(), Sort::Bool);
        sorts_cache.insert(bool_sort, Sort::Bool);

        Self {
            terms,
            free_vars_cache: AHashMap::new(),
            sorts_cache,
            bool_true,
            bool_false,
        }
    }

    /// Return the term corresponding to the boolean constant `true`.
    pub fn bool_true(&self) -> Rc<Term> {
        self.bool_true.clone()
    }

    /// Return the term corresponding to the boolean constant `false`.
    pub fn bool_false(&self) -> Rc<Term> {
        self.bool_false.clone()
    }

    /// Return the term corresponding to the boolean constant determined by `value`.
    pub fn bool_constant(&self, value: bool) -> Rc<Term> {
        match value {
            true => self.bool_true(),
            false => self.bool_false(),
        }
    }

    fn add_term_to_map(terms_map: &mut AHashMap<Term, Rc<Term>>, term: Term) -> Rc<Term> {
        use std::collections::hash_map::Entry;

        match terms_map.entry(term) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => {
                let term = vacant_entry.key().clone();
                vacant_entry.insert(Rc::new(term)).clone()
            }
        }
    }

    /// Takes a term and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the term was not originally in the term pool, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation. This method also computes the
    /// term's sort, and adds it to the sort cache.
    pub fn add(&mut self, term: Term) -> Rc<Term> {
        let term = Self::add_term_to_map(&mut self.terms, term);
        self.compute_sort(&term);
        term
    }

    /// Takes a vector of terms and calls [`TermPool::add`] on each.
    pub fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        terms.into_iter().map(|t| self.add(t)).collect()
    }

    /// Returns the sort of the given term.
    ///
    /// This method assumes that the sorts of any subterms have already been checked, and are
    /// correct. If `term` is itself a sort, this simply returns that sort.
    pub fn sort(&self, term: &Rc<Term>) -> &Sort {
        &self.sorts_cache[term]
    }

    /// Computes the sort of a term and adds it to the sort cache.
    fn compute_sort<'a, 'b: 'a>(&'a mut self, term: &'b Rc<Term>) -> &'a Sort {
        use super::Operator;

        if self.sorts_cache.contains_key(term) {
            return &self.sorts_cache[term];
        }

        let result = match term.as_ref() {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => Sort::Int,
                Terminal::Real(_) => Sort::Real,
                Terminal::String(_) => Sort::String,
                Terminal::Var(_, sort) => sort.as_sort().unwrap().clone(),
            },
            Term::Op(op, args) => match op {
                Operator::Not
                | Operator::Implies
                | Operator::And
                | Operator::Or
                | Operator::Xor
                | Operator::Equals
                | Operator::Distinct
                | Operator::LessThan
                | Operator::GreaterThan
                | Operator::LessEq
                | Operator::GreaterEq
                | Operator::IsInt => Sort::Bool,
                Operator::Ite => self.compute_sort(&args[1]).clone(),
                Operator::Add | Operator::Sub | Operator::Mult => {
                    if args.iter().any(|a| *self.compute_sort(a) == Sort::Real) {
                        Sort::Real
                    } else {
                        Sort::Int
                    }
                }
                Operator::RealDiv | Operator::ToReal => Sort::Real,
                Operator::IntDiv | Operator::Mod | Operator::Abs | Operator::ToInt => Sort::Int,
                Operator::Select => match self.compute_sort(&args[0]) {
                    Sort::Array(_, y) => y.as_sort().unwrap().clone(),
                    _ => unreachable!(),
                },
                Operator::Store => self.compute_sort(&args[0]).clone(),
            },
            Term::App(f, _) => {
                match self.compute_sort(f) {
                    Sort::Function(sorts) => sorts.last().unwrap().as_sort().unwrap().clone(),
                    _ => unreachable!(), // We assume that the function is correctly sorted
                }
            }
            Term::Sort(sort) => sort.clone(),
            Term::Quant(_, _, _) => Sort::Bool,
            Term::Choice((_, sort), _) => sort.as_sort().unwrap().clone(),
            Term::Let(_, inner) => self.compute_sort(inner).clone(),
            Term::Lambda(bindings, body) => {
                let mut result: Vec<_> =
                    bindings.iter().map(|(_name, sort)| sort.clone()).collect();
                let return_sort = Term::Sort(self.compute_sort(body).clone());
                result.push(self.add(return_sort));
                Sort::Function(result)
            }
        };
        self.sorts_cache.insert(term.clone(), result);
        &self.sorts_cache[term]
    }

    /// Returns an `AHashSet` containing all the free variables in the given term.
    ///
    /// This method uses a cache, so there is no additional cost to computing the free variables of
    /// a term multiple times.
    pub fn free_vars<'t>(&mut self, term: &'t Rc<Term>) -> &AHashSet<Rc<Term>> {
        // Here, I would like to do
        // ```
        // if let Some(vars) = self.free_vars_cache.get(term) {
        //     return vars;
        // }
        // ```
        // However, because of a limitation in the borrow checker, the compiler thinks that
        // this immutable borrow of `cache` has to live until the end of the function, even
        // though the code immediately returns. This would stop me from mutating `cache` in the
        // rest of the function. Because of that, I have to check if the hash map contains
        // `term` as a key, and then get the value associated with it, meaning I have to access
        // the hash map twice, which is a bit slower. This is an example of problem case #3
        // from the non-lexical lifetimes RFC:
        // https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md
        if self.free_vars_cache.contains_key(term) {
            return self.free_vars_cache.get(term).unwrap();
        }
        let set = match term.as_ref() {
            Term::App(f, args) => {
                let mut set = self.free_vars(f).clone();
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned());
                }
                set
            }
            Term::Op(_, args) => {
                let mut set = AHashSet::new();
                for a in args {
                    set.extend(self.free_vars(a).iter().cloned());
                }
                set
            }
            Term::Quant(_, bindings, inner) | Term::Lambda(bindings, inner) => {
                let mut vars = self.free_vars(inner).clone();
                for bound_var in bindings {
                    let term = self.add(bound_var.clone().into());
                    vars.remove(&term);
                }
                vars
            }
            Term::Let(bindings, inner) => {
                let mut vars = self.free_vars(inner).clone();
                for (var, value) in bindings {
                    let sort = Term::Sort(self.sort(value).clone());
                    let sort = self.add(sort);
                    let term = self.add((var.clone(), sort).into());
                    vars.remove(&term);
                }
                vars
            }
            Term::Choice(bound_var, inner) => {
                let mut vars = self.free_vars(inner).clone();
                let term = self.add(bound_var.clone().into());
                vars.remove(&term);
                vars
            }
            Term::Terminal(Terminal::Var(Identifier::Simple(_), _)) => {
                let mut set = AHashSet::with_capacity(1);
                set.insert(term.clone());
                set
            }
            Term::Terminal(_) | Term::Sort(_) => AHashSet::new(),
        };
        self.free_vars_cache.insert(term.clone(), set);
        self.free_vars_cache.get(term).unwrap()
    }
}
