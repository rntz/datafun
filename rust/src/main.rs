use std::collections::HashMap;

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord)]
pub enum Type {
    Rel(Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    Str, Num,
}

type Var = String;

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
            Some(t) if subtype(&got, t) => got,
            None => got,
            _ => typeError("fux")
        }
    };
    let check = || {
        match expect {
            Some(t) => t,
            None => typeError("cannot infer this expression"),
        }
    };
    match expr {
        Asc(a, e) => infers(type_check(cx, Some(a), e)),
        Var(x) => match cx.get(x) {
            None => typeError("unbound variable"),
            Some(tp) => infers(tp.clone()),
        },
        Num(_) => { infers(Type::Num) }
        Str(_) => { infers(Type::Str) }
        Eq(e1,e2) => {
            let t1 = type_check(cx, None, e1);
            let t2 = type_check(cx, None, e2);
            if t1 != t2 { typeError("types are not equal") }
            if !equality_type(&t1) { typeError("cannot compare at that type") }
            infers(BOOL.clone())
        }

        Row(es) => match expect {
            // for now, we can't infer singleton relations. TODO.
            None => { panic!() },
            Some(Type::Rel(ts)) => {
                if es.len() != ts.len() {
                    typeError("relation has wrong # columns")
                }
                Type::Rel(ts.iter().zip(es.iter())
                          .map(|(t,e)| type_check(cx, Some(t), e))
                          .collect())
            },
            Some(_) => typeError("relation must have relation type"),
        },

        Let(_x,_e,_f) => { panic!() }

        Lam(x,e) => match check() {
            Type::Fn(a,b) => {
                let mut cx2 = cx.clone(); // stupidly inefficient
                cx2.insert(x.clone(), *a.clone());
                type_check(&cx2, Some(b), e);
                Type::Fn(a.clone(), b.clone())
            }
            _ => typeError("lambda needs function type"),
        },

        App(e,f) => match type_check(cx, None, e) {
            Type::Fn(a,b) => {
                type_check(cx, Some(&a), f);
                *b
            }
            _ => typeError("can't apply a non-function"),
        },

        Join(es) => match expect {
            // TODO: implement inferring the types of non-empty joins
            None => { panic!() },
            Some(a) => {
                if !lattice_type(a) { typeError("can't take join at non-lattice type") }
                for e in es { type_check(cx, Some(a), e); }
                a.clone()
            }
        },

        For(xs,e,f) => match type_check(cx, None, e) {
            Type::Rel(ts) => {
                if xs.len() != ts.len() {
                    typeError("wrong number of variables for relation")
                }
                let mut cx2 = cx.clone();
                for (x,t) in xs.iter().zip(ts.iter()) {
                    cx2.insert(x.clone(), t.clone());
                }
                let got = type_check(&cx2, expect, f);
                if !lattice_type(&got) { typeError("cannot loop at non-lattice type") }
                got
            }
            _ => typeError("cannot loop over non-relation")
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
    assertValid(x);
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

fn scalarType(x: &Type) -> bool {
    assertValid(x);
    match x {
        Type::Rel(_) | Type::Fn(_,_) => false,
        _ => true,
    }
}

// TODO: smart constructors so we never make invalid types.
fn assertValid(x: &Type) {
    match x {
        Type::Rel(ts) =>
            if !ts.iter().all(scalarType) {
                typeError("columns of relation must be scalars");
            },
        _ => {}
    }
}

fn typeError(_: &str) -> ! { panic!() } // TODO
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

fn main() {
    println!("Hello, world!");
}
