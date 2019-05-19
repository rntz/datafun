use std::collections::HashMap;

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord)]
pub enum Type {
    Rel(Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    Str, Num,
}

type Var = String;

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord)]
pub enum Expr {
    Var(Var),
    Num(i32), Str(String),          // scalar literals
    Eq(Box<Expr>, Box<Expr>),       // equality tests
    Row(Vec<Expr>),                 // singleton relation
    Asc(Type, Box<Expr>),           // type ascription
    Let(Var, Box<Expr>, Box<Expr>), // let binding
    // functions
    Lam(Var, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    // semilattices
    Join(Vec<Expr>),
    For(Vec<Var>, Box<Expr>, Box<Expr>),
    // conditionals
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}
use Expr::*;

type Cx = HashMap<Var, Type>;

//const boolean: Type = Type::Rel(vec![]);
lazy_static::lazy_static!{
    static ref BOOL: Type = Type::Rel(vec![]);
}

pub fn type_check(cx: &Cx, expect: Option<&Type>, expr: &Expr) -> Type {
    let infers = |got| {
        match expect {
            None => got,
            Some(t) if subtype(&got, t) => got,
            Some(t) => type_error(&format!("expected: {:?}
but got:  {:?}", t, got))
        }
    };
    let check = || {
        match expect {
            Some(t) => t,
            None => type_error("cannot infer this expression"),
        }
    };
    match expr {
        Asc(a, e) => infers(type_check(cx, Some(a), e)),
        Var(x) => match cx.get(x) {
            None => type_error("unbound variable"),
            Some(tp) => infers(tp.clone()),
        },
        Num(_) => { infers(Type::Num) }
        Str(_) => { infers(Type::Str) }
        Eq(e1,e2) => {
            let t1 = type_check(cx, None, e1);
            let t2 = type_check(cx, None, e2);
            if t1 != t2 { type_error("types are not equal") }
            if !equality_type(&t1) { type_error("cannot compare at that type") }
            infers(BOOL.clone())
        }

        Row(es) => match expect {
            // for now, we can't infer singleton relations. TODO.
            None => { panic!() },
            Some(Type::Rel(ts)) => {
                if es.len() != ts.len() {
                    type_error("relation has wrong # columns")
                }
                Type::Rel(ts.iter().zip(es.iter())
                          .map(|(t,e)| type_check(cx, Some(t), e))
                          .collect())
            },
            Some(_) => type_error("relation must have relation type"),
        },

        Let(_x,_e,_f) => { panic!() }

        Lam(x,e) => match check() {
            Type::Fn(a,b) => {
                let mut cx2 = cx.clone(); // stupidly inefficient
                cx2.insert(x.clone(), *a.clone());
                type_check(&cx2, Some(b), e);
                Type::Fn(a.clone(), b.clone())
            }
            _ => type_error("lambda needs function type"),
        },

        App(e,f) => match type_check(cx, None, e) {
            Type::Fn(a,b) => {
                type_check(cx, Some(&a), f);
                *b
            }
            _ => type_error("can't apply a non-function"),
        },

        Join(es) => match expect {
            // TODO: implement inferring the types of non-empty joins
            None => { panic!() },
            Some(a) => {
                if !lattice_type(a) { type_error("can't take join at non-lattice type") }
                for e in es { type_check(cx, Some(a), e); }
                a.clone()
            }
        },

        For(xs,e,f) => match type_check(cx, None, e) {
            Type::Rel(ts) => {
                if xs.len() != ts.len() {
                    type_error("wrong number of variables for relation")
                }
                let mut cx2 = cx.clone();
                for (x,t) in xs.iter().zip(ts.iter()) {
                    cx2.insert(x.clone(), t.clone());
                }
                let got = type_check(&cx2, expect, f);
                if !lattice_type(&got) { type_error("cannot loop at non-lattice type") }
                got
            }
            _ => type_error("cannot loop over non-relation")
        },

        If(e,f,g) => {
            type_check(cx, Some(&BOOL), e);
            let got = type_check(cx, expect, f);
            type_check(cx, Some(&got), g);
            got
        }
    }
}

// for now our only lattices are relations
// later:
// - tuples of lattice types
// - booleans?
// - numbers under max?
fn lattice_type(x: &Type) -> bool {
    assert_valid(x);
    match x {
        Type::Fn(_,_) | Type::Str | Type::Num => false,
        Type::Rel(_) => true
    }
}

fn equality_type(x: &Type) -> bool {
    match x {
        Type::Fn(_,_) => false,
        Type::Num | Type::Str | Type::Rel(_) => true,
    }
}

fn scalar_type(x: &Type) -> bool {
    assert_valid(x);
    match x {
        Type::Rel(_) | Type::Fn(_,_) => false,
        _ => true,
    }
}

// TODO: smart constructors so we never make invalid types.
fn assert_valid(x: &Type) {
    match x {
        Type::Rel(ts) =>
            if !ts.iter().all(scalar_type) {
                type_error("columns of relation must be scalars");
            },
        _ => {}
    }
}

fn type_error(s: &str) -> ! {
    panic!("\n\n{}\n\n", s);
}
fn subtype(x: &Type, y: &Type) -> bool { x == y }

// match e {
//     Asc(a,e) => { panic!() }
//     Var(x) => { panic!() }
//     Num(x) => { panic!() }
//     Str(x) => { panic!() }
//     Eq(e1,e2) => { panic!() }
//     Set(es) => { panic!() }
//     Let(x,e,f) => { panic!() }
//     Lam(x,e) => { panic!() }
//     App(e,f) => { panic!() }
//     Join(es) => { panic!() }
//     For(x,e,f) => { panic!() }
//     If(e,f,g) => { panic!() }
// }

fn test_check(tp: &Type, e: &Expr) {
    let cx = HashMap::new();
    type_check(&cx, Some(tp), &e);
}

fn main() {
    test_check(&Type::Rel(vec![Type::Num]), &Row(vec![Num(2)]));
    test_check(
        &Type::Fn(Box::new(Type::Num), Box::new(Type::Num)),
        &Lam("x".to_string(), Box::new(Var("x".to_string())))
    );
}
