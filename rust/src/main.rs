use lalrpop_util::lalrpop_mod;
use std::collections::HashMap;

lalrpop_mod!(pub syntax);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Rel(Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    Str,
    Num,
}

type Var = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr {
    Var(Var),
    Num(i32),
    Str(String),                         // scalar literals
    Eq(Box<Expr>, Box<Expr>),            // equality tests
    Row(Vec<Expr>),                      // singleton relation
    Asc(Type, Box<Expr>),                // type ascription
    Let(Var, Box<Expr>, Box<Expr>),      // let binding
    If(Box<Expr>, Box<Expr>, Box<Expr>), // conditionals
    // functions
    Lam(Var, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    // semilattices
    Bottom(),                            // 0-ary lubs
    Join(Box<Expr>, Box<Expr>),          // binary lubs
    For(Vec<Var>, Box<Expr>, Box<Expr>), // comprehensions / big lubs
    Fix(Var, Box<Expr>),                 // fixed points
}
use Expr::*;

type TypeError = String;
type Check<A> = Result<A, TypeError>;
type Cx = HashMap<Var, Type>;

macro_rules! type_error {
    ($($arg:tt)*) => ({
        return Err(format!($($arg)*));
    })
}

lazy_static::lazy_static! { static ref BOOL: Type = Type::Rel(vec![]); }

impl Type {
    fn subtype(self: &Type, other: &Type) -> bool {
        self == other
    }

    fn check(self: &Type) -> Check<()> {
        match self {
            Type::Rel(ts) => ts.iter().map(|x| x.check_column()).collect(),
            _ => Ok(()),
        }
    }

    fn check_column(self: &Type) -> Check<()> {
        match self {
            Type::Rel(_) | Type::Fn(_, _) => type_error!("columns of relation must be scalars"),
            _ => self.check(),
        }
    }

    // For now our only semilattices are relations
    // later:
    // - tuples of semilattice types
    // - booleans?
    // - numbers under max?
    fn is_semilattice(self: &Type) -> bool {
        match self {
            Type::Rel(_) => true,
            Type::Fn(_, _) | Type::Str | Type::Num => false,
        }
    }

    fn has_equality(self: &Type) -> bool {
        match self {
            Type::Fn(_, _) => false,
            Type::Num | Type::Str | Type::Rel(_) => true,
        }
    }
}

pub fn type_check(cx: &Cx, expect: Option<&Type>, expr: &Expr) -> Check<Type> {
    // Called when we infer a type to check it matches the expected type, if any.
    let infers = |got: Type| match expect {
        Some(t) if !got.subtype(t) => type_error!(
            "expected: {:?}
but got:  {:?}",
            t,
            got
        ),
        _ => Ok(got),
    };

    // Called when we cannot infer a type, to get the type to check against, or
    // fail if no type was provided.
    let check = || match expect {
        Some(t) => Ok(t),
        None => type_error!("cannot infer this expression; try adding a type annotation"),
    };

    let typ: Type = match expr {
        Asc(a, e) => infers(type_check(cx, Some(a), e)?)?,
        Var(x) => match cx.get(x) {
            None => type_error!("unbound variable"),
            Some(tp) => infers(tp.clone())?,
        },
        Num(_) => infers(Type::Num)?,
        Str(_) => infers(Type::Str)?,
        Eq(e1, e2) => {
            let t1 = type_check(cx, None, e1)?;
            let t2 = type_check(cx, None, e2)?;
            if t1 != t2 {
                type_error!("types are not equal: {:?} versus {:?}", t1, t2)
            }
            if !t1.has_equality() {
                type_error!("cannot test equality at type {:?}", t1)
            }
            infers(BOOL.clone())?
        }

        If(e, f, g) => {
            type_check(cx, Some(&BOOL), e)?;
            let got = type_check(cx, expect, f)?;
            type_check(cx, Some(&got), g)?;
            got
        }

        Row(es) => match expect {
            // Infer each column
            None => Type::Rel(
                es.iter()
                    .map(|e: &Expr| type_check(cx, None, e))
                    .collect::<Check<_>>()?,
            ),
            // Check each column
            Some(Type::Rel(ts)) => {
                if es.len() != ts.len() {
                    type_error!("relation has wrong # columns")
                }
                Type::Rel(
                    ts.iter()
                        .zip(es.iter())
                        .map(|(t, e)| type_check(cx, Some(t), e))
                        .collect::<Check<Vec<_>>>()?,
                )
            }
            Some(_) => type_error!("relation must have relation type"),
        },

        Let(x, e, f) => {
            let etype = type_check(cx, None, e)?;
            let mut cx2 = cx.clone();
            cx2.insert(x.clone(), etype);
            type_check(&cx2, expect, f)?
        }

        Lam(x, e) => match check()? {
            Type::Fn(a, b) => {
                let mut cx2 = cx.clone(); // stupidly inefficient
                cx2.insert(x.clone(), *a.clone());
                type_check(&cx2, Some(b), e)?;
                Type::Fn(a.clone(), b.clone())
            }
            _ => type_error!("lambda needs function type"),
        },

        App(e, f) => match type_check(cx, None, e)? {
            Type::Fn(a, b) => {
                type_check(cx, Some(&a), f)?;
                *b
            }
            _ => type_error!("can't apply a non-function"),
        },

        Bottom() => {
            let tp = check()?;
            if !tp.is_semilattice() {
                type_error!("'nil' must have semilattice type")
            };
            tp.clone()
        }

        Join(e1, e2) => {
            // Check or infer our subterms as appropriate.
            let got = type_check(cx, expect, e1)?;
            let got2 = type_check(cx, expect, e2)?;
            if got != got2 {
                type_error!("arguments to 'or' must have same type")
            }
            if !got.is_semilattice() {
                type_error!("'or' must be used at semilattice type")
            }
            got
        }

        For(xs, e, f) => match type_check(cx, None, e)? {
            Type::Rel(ts) => {
                if xs.len() != ts.len() {
                    type_error!("wrong number of variables for relation")
                }
                let mut cx2 = cx.clone();
                for (x, t) in xs.iter().zip(ts.iter()) {
                    cx2.insert(x.clone(), t.clone());
                }
                let got = type_check(&cx2, expect, f)?;
                if !got.is_semilattice() {
                    type_error!("cannot loop at non-lattice type")
                }
                got
            }
            _ => type_error!("cannot loop over non-relation"),
        },

        Fix(x, body) => {
            // We can't infer 'fix' expressions, only check them.
            let tp = check()?;
            if !tp.is_semilattice() {
                type_error!("'fix' can only be used at semilattice type")
            };
            let mut cx2 = cx.clone();
            cx2.insert(x.clone(), tp.clone());
            type_check(&cx2, expect, body)?
        }
    };
    typ.check()?; // don't return ill-formed types.
    Ok(typ)
}

fn main() {
    let expr = syntax::ExprParser::new()
        .parse("@ {} -> {} x -> {} or x")
        .unwrap();
    let cx = HashMap::new();
    println!("{:?}", type_check(&cx, None, &expr));
}

#[cfg(test)]
mod test {
    use super::*;

    fn parse_and_infer(code: &str) -> (Expr, Check<Type>) {
        let e = syntax::ExprParser::new().parse(code).unwrap();
        let cx = HashMap::new();
        let t = type_check(&cx, None, &e);
        (e, t)
    }

    #[test]
    fn test_this_thing() {
        assert_eq!(
            parse_and_infer("@ {} -> {} x -> {} or x").1,
            Ok(Type::Fn(
                Box::new(Type::Rel(vec![])),
                Box::new(Type::Rel(vec![]))
            ))
        );
        assert!(parse_and_infer("@ {} -> {} x -> {x} or x").1.is_err())
    }

    #[test]
    fn test_for() {
        // TODO: write the code so that we don't need a type annotation here
        assert_eq!(
            parse_and_infer(
                "@{}
for x in {0} do x = 0"
            )
            .1,
            Ok(Type::Rel(vec![]))
        )
    }
}
