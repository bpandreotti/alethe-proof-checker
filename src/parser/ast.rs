use num_rational::Ratio;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    // Arithmetic
    Add,
    Sub,
    Mult,
    Div,

    // Logic
    Eq,
    Or,
    And,
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Terminal(Terminal),
    App(Rc<Term>, Vec<Rc<Term>>),
    Op(Operator, Vec<Rc<Term>>),
    // TODO: binders
}

impl Term {
    pub fn sort(&self) -> Sort {
        match self {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => Sort::int(),
                Terminal::Real(_) => Sort::real(),
                Terminal::String(_) => Sort::string(),
                Terminal::Var(Identifier::Simple(iden)) if iden == "true" || iden == "false" => {
                    Sort::bool()
                }
                _ => todo!(),
            },
            Term::Op(op, args) => match op {
                Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => args[0].sort(),
                Operator::Eq | Operator::Or | Operator::And | Operator::Not => Sort::bool(),
            },
            _ => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Sort(Term);

macro_rules! sort_from_iden {
    ($iden:expr) => {
        Sort(Term::Terminal(Terminal::Var(Identifier::Simple(
            $iden.into(),
        ))))
    };
}

impl Sort {
    pub fn bool() -> Self {
        sort_from_iden!("Bool")
    }

    pub fn int() -> Self {
        sort_from_iden!("Int")
    }

    pub fn real() -> Self {
        sort_from_iden!("Real")
    }

    pub fn string() -> Self {
        sort_from_iden!("String")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Integer(u64),
    Real(Ratio<u64>),
    String(String),
    Var(Identifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Identifier {
    Simple(String),
    Indexed(String, Vec<Index>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Index {
    Numeral(u64),
    Symbol(String),
}
