use crate::ast::*;
use indexmap::IndexSet;
use std::borrow::{Borrow, BorrowMut};
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use thiserror::Error;

#[derive(Debug)]
pub enum Implied<T, X> {
    Pivot(T, X),
    Bottom(X),
    NotUnsat(),
}
// A RUP Addition is a vector of the clause plus the unit clause and the hash of the clause
pub type RupAdition = Vec<(IndexSet<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>, u64)>;

//This enum is used to bookkeeping the action perfomed by a reverse unit propagation
pub enum DRupProofAction {
    RupStory(IndexSet<(bool, Rc<Term>)>, RupAdition),
    Delete(Rc<Term>),
}

pub type DRupStory = Vec<DRupProofAction>;

#[derive(Debug, Error)]
pub enum DrupFormatError {
    #[error("couldn't find conclusion term in the premise clauses")]
    NoConclusionInPremise,
    #[error(
        "couldn't elaborate drup because bottom wasn't derived from the premises and the argument"
    )]
    NoFinalBottomInDrup,
    #[error("couldn't elaborate drup because the argument might not be in RUP")]
    PotentialNoDrupFormat,
    #[error("a clause in RAT should be non-empty")]
    CheckingRatInEmptyClause,
    #[error("the clause isn't in RAT format")]
    NotInRatFormat,
}

pub fn hash_term<T: Borrow<Rc<Term>>>(pool: &mut dyn TermPool, term: T) -> u64 {
    let term: Rc<Term> = {
        let (p, regular_term): (bool, &Rc<Term>) =
            term.borrow().remove_all_negations_with_polarity();
        if p {
            regular_term.clone()
        } else {
            build_term!(pool, (not { (*regular_term).clone() }))
        }
    };

    let mut s = DefaultHasher::new();
    term.hash(&mut s);
    let hash = s.finish();
    return hash;
}

// This function search for a unit clause by using the two literals in the pair associated in each indexset
// additionally clauses is mutable since this function also fix the two watched literal whenever a new unit clause is propagated
fn get_implied_clause(
    clauses: &mut Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, Rc<Term>)>, u64),
    )>,
    env: &HashMap<(bool, Rc<Term>), bool>,
) -> Implied<(bool, Rc<Term>), (IndexSet<(bool, Rc<Term>)>, u64)> {
    if clauses.is_empty() {
        return Implied::NotUnsat();
    }

    for (schema, (lits, key)) in clauses {
        match schema {
            (None, None) => return Implied::Bottom(((*lits).clone(), *key)),

            (Some((b, t)), None) | (None, Some((b, t))) => match env.get(&(*b, (*t).clone())) {
                Some(false) => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Bottom(((*lits).clone(), *key));
                }
                Some(true) => continue,
                None => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Pivot((*b, (*t).clone()), ((*lits).clone(), *key));
                }
            },

            (Some((b, t)), Some((b0, t0))) => {
                match (env.get(&(*b, (*t).clone())), env.get(&(*b0, (*t0).clone()))) {
                    (Some(true), _) => continue,
                    (_, Some(true)) => continue,
                    (None, None) => continue,
                    (_, _) => {
                        let mut unset_literal = None;
                        let mut not_unit = false;

                        for (b1, t1) in lits.iter() {
                            let assign_state = env.get(&(*b1, (*t1).clone()));

                            match assign_state {
                                None => {
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    if unset_literal.is_some() {
                                        not_unit = true;
                                        continue;
                                    }

                                    unset_literal = Some((b1, (*t1).clone()));
                                }
                                Some(true) => {
                                    // Set the true clause as a watched literal to avoid searching O(n) in this "deleted" clause
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    not_unit = true;
                                    continue;
                                }
                                Some(false) => (),
                            }
                        }

                        if not_unit {
                            continue;
                        }

                        return match unset_literal {
                            Some((p, polarity)) => {
                                Implied::Pivot((*p, polarity.clone()), ((*lits).clone(), *key))
                            }
                            _ => Implied::Bottom(((*lits).clone(), *key)),
                        };
                    }
                }
            }
        }
    }
    Implied::NotUnsat()
}

// Perform *only* rup (reverse unit propagation) in a set of clauses and a "goal", here the goal is the implied clause by
// F /\ ~ C |- \bottom
fn rup<'a, 'b>(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<(bool, Rc<Term>)>>,
    goal: &'a [Rc<Term>],
) -> Option<RupAdition> {
    let mut unit_story: RupAdition = vec![];

    let mut clauses: Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, Rc<Term>)>, u64),
    )> = vec![];

    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        let mut clause: IndexSet<(bool, Rc<Term>)> = IndexSet::new();
        clause.insert((!p, regular_term.clone()));
        clauses.push((
            (Some((!p, regular_term.clone())), None),
            (clause, hash_term(pool, term)),
        ));
    }

    for (key, clause) in drup_clauses {
        let mut watched_literals = clause.iter().take(2);
        let clause = (
            (
                watched_literals.next().map(|v| (v.0, v.1.clone())),
                watched_literals.next().map(|v| (v.0, v.1.clone())),
            ),
            (
                clause.iter().map(|(k, v)| (*k, (*v).clone())).collect(),
                *key,
            ),
        );
        clauses.push(clause);
    }

    loop {
        let unit = get_implied_clause(clauses.borrow_mut(), env.borrow());

        match unit {
            Implied::Bottom(clause) => {
                unit_story.push((clause.0, None, clause.1));
                return Some(unit_story);
            }
            Implied::Pivot(literal, clause) => {
                env.insert(literal.clone(), true);
                let negated_literal = (!literal.0, literal.1.clone());
                env.insert(negated_literal.clone(), false);
                unit_story.push((clause.0, Some((literal.0, literal.1)), clause.1));
            }
            Implied::NotUnsat() => return None,
        }
    }
}

// This implements the rule for drup checking, by using a chain of goals that calls RUP, check_rat is optional in case if you
// want to check also for RAT format
pub fn check_drup<'a>(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premises: &[Rc<Term>],
    args: &'a [Rc<Term>],
    check_rat: bool,
) -> Result<DRupStory, DrupFormatError> {
    let mut premises: HashMap<u64, _> = premises
        .iter()
        .map(|p| {
            let mut indexset = IndexSet::new();
            let terms = if let Some(terms) = match_term!((cl ...) = p) {
                terms.to_vec()
            } else {
                vec![(*p).clone()]
            };
            for term in terms {
                let (polarity, new_term) = term.remove_all_negations_with_polarity();
                indexset.insert((polarity, (*new_term).clone()));
            }
            (hash_term(pool, p), indexset)
        })
        .collect();

    let mut drup_history: DRupStory = vec![];
    for t in args {
        match match_term!((delete (cl ...)) = &t) {
            Some(terms) => {
                let clause_term = if terms.len() > 0 {
                    build_term!(pool, (cl[terms.to_vec()]))
                } else {
                    terms[0].clone()
                };
                premises.remove(&hash_term(pool, &clause_term));
                drup_history.push(DRupProofAction::Delete(clause_term));
                continue;
            }
            None => (),
        }

        let terms = match_term!((cl ...) = &t).unwrap();
        let mut unit_history: Option<
            Vec<(IndexSet<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>, u64)>,
        > = rup(pool, premises.borrow(), terms);
        if unit_history == None && terms.len() > 0 && check_rat {
            unit_history = check_drat(pool, premises.borrow(), terms);
        }

        if unit_history == None {
            return if check_rat {
                Err(DrupFormatError::NotInRatFormat)
            } else {
                Err(DrupFormatError::NoFinalBottomInDrup)
            };
        }

        let terms_indexed_set = terms
            .iter()
            .map(|term| {
                let (p, term) = Rc::remove_all_negations_with_polarity(term);
                (p, term.clone())
            })
            .collect::<IndexSet<_>>();

        drup_history.push(DRupProofAction::RupStory(
            terms_indexed_set.clone(),
            unit_history.unwrap(),
        ));

        premises.insert(hash_term(pool, t), terms_indexed_set);
    }

    if !premises.contains_key(&hash_term(pool, conclusion)) {
        return Err(DrupFormatError::NoConclusionInPremise);
    }

    Ok(drup_history)
}

// Checks RAT, essentially rat is equivalent to RUP plus a blocked clause
// (eg. given a clause C \/ p, we look for RUP in every D \/ ~ p in the set clause)
pub fn check_drat<'a>(
    pool: &mut dyn TermPool,
    drup_clauses: &HashMap<u64, IndexSet<(bool, Rc<Term>)>>,
    goal: &'a [Rc<Term>],
) -> Option<RupAdition> {
    let pivot = &goal[0];
    let mut unit_history = vec![];
    for (_, clause) in drup_clauses {
        let (p, regular_term) = pivot.remove_all_negations_with_polarity();
        let negated_pivot = (!p, regular_term.clone());

        if clause.contains(&negated_pivot) {
            let mut resolvent = clause.clone();
            resolvent.remove(&negated_pivot);
            let mut resolvent = resolvent
                .iter()
                .map(|(p, literal)| {
                    if *p {
                        return (*literal).clone();
                    } else {
                        return build_term!(pool, (not { (*literal).clone() }));
                    };
                })
                .collect::<Vec<_>>();

            resolvent.append(&mut goal[1..].to_vec());
            if let Some(history) = rup(pool, drup_clauses, resolvent.borrow()) {
                unit_history.extend_from_slice(&history);
                continue;
            }
            return None;
        }
    }

    return Some(unit_history);
}
