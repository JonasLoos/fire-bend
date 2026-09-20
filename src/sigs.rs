// src/bend/sigs.rs
// Type signatures of builtin functions and methods, as the inference sees
// them. Each entry produces fresh types for one use, so overloaded builtins
// (`len`, `sum`, `+`) resolve per call once the receiver type is known.

use crate::types::{Type, TypeStore};

/// The record id of the builtin pair shape `{key, value}` used by
/// `entries()`, `zip`, and `enumerate`.
pub const PAIR_REC: usize = 0;

/// The signature of a builtin method call `recv.name(args)` for a receiver
/// whose type is already known (not a variable). Returns the parameter
/// types (excluding the receiver) and the result type, or None if the
/// receiver has no such method.
pub fn method_sig(store: &mut TypeStore, recv: &Type, name: &str, nargs: usize) -> Option<(Vec<Type>, Type)> {
    let fresh = |s: &mut TypeStore| s.fresh();
    match recv {
        Type::Str => Some(match name {
            "length" => (vec![], Type::Int),
            "upper" | "lower" | "trim" | "trim_start" | "trim_end" => (vec![], Type::Str),
            "split" => (if nargs == 0 { vec![] } else { vec![Type::Str] }, Type::list(Type::Str)),
            "lines" => (vec![], Type::list(Type::Str)),
            "replace" => (vec![Type::Str, Type::Str], Type::Str),
            "contains" | "starts_with" | "ends_with" => (vec![Type::Str], Type::Bool),
            "index_of" => (vec![Type::Str], Type::maybe(Type::Int)),
            "chars" => (vec![], Type::list(Type::Str)),
            "repeat" => (vec![Type::Int], Type::Str),
            "to_int" => (vec![], Type::Int),
            "to_float" => (vec![], Type::Float),
            "parse_int" => (vec![], Type::result(Type::Str, Type::Int)),
            "parse_float" => (vec![], Type::result(Type::Str, Type::Float)),
            "is_empty" => (vec![], Type::Bool),
            "reverse" | "reversed" => (vec![], Type::Str),
            "join" => (vec![Type::list(Type::Str)], Type::Str),
            "to_str" => (vec![], Type::Str),
            "char_code" => (vec![], Type::Int),
            "take" | "drop" => (vec![Type::Int], Type::Str),
            _ => return None,
        }),
        Type::Int => Some(match name {
            "abs" => (vec![], Type::Int),
            "to_str" => (vec![], Type::Str),
            "to_float" => (vec![], Type::Float),
            "sqrt" => (vec![], Type::Float),
            "floor" | "ceil" | "round" => (vec![], Type::Int),
            _ => return None,
        }),
        Type::Float => Some(match name {
            "abs" | "floor" | "ceil" | "sqrt" => (vec![], Type::Float),
            "round" => (if nargs == 0 { vec![] } else { vec![Type::Int] }, Type::Float),
            "to_str" => (vec![], Type::Str),
            "to_int" => (vec![], Type::Int),
            _ => return None,
        }),
        Type::List(elem) => {
            let e = (**elem).clone();
            Some(match name {
                "length" => (vec![], Type::Int),
                "map" => {
                    let b = fresh(store);
                    let f = store.fresh_fn(vec![e], b.clone());
                    (vec![f], Type::list(b))
                }
                "filter" => {
                    let f = store.fresh_fn(vec![e.clone()], Type::Bool);
                    (vec![f], Type::list(e))
                }
                "each" => {
                    let r = fresh(store);
                    let f = store.fresh_fn(vec![e], r);
                    (vec![f], Type::Unit)
                }
                "reduce" => {
                    if nargs == 1 {
                        let f = store.fresh_fn(vec![e.clone(), e.clone()], e.clone());
                        (vec![f], e)
                    } else {
                        let acc = fresh(store);
                        let f = store.fresh_fn(vec![acc.clone(), e], acc.clone());
                        (vec![f, acc.clone()], acc)
                    }
                }
                "any" | "all" => {
                    let f = store.fresh_fn(vec![e], Type::Bool);
                    (vec![f], Type::Bool)
                }
                "find" => {
                    let f = store.fresh_fn(vec![e.clone()], Type::Bool);
                    (vec![f], Type::maybe(e))
                }
                "sum" | "min" | "max" => (vec![], e),
                "join" => (vec![Type::Str], Type::Str),
                "contains" => (vec![e], Type::Bool),
                "index_of" => (vec![e], Type::maybe(Type::Int)),
                "first" | "last" => (vec![], Type::maybe(e)),
                "reverse" | "reversed" => (vec![], Type::list(e)),
                "sort" | "sorted" => {
                    if nargs == 0 {
                        (vec![], Type::list(e))
                    } else {
                        let k = fresh(store);
                        let f = store.fresh_fn(vec![e.clone()], k);
                        (vec![f], Type::list(e))
                    }
                }
                "push" => ((0..nargs).map(|_| e.clone()).collect(), Type::list(e)),
                "pop" => (vec![], e),
                "drop_last" => (vec![], Type::list(e)),
                "take" | "drop" => (vec![Type::Int], Type::list(e)),
                "to_list" => (vec![], Type::list(e)),
                "is_empty" => (vec![], Type::Bool),
                "flatten" => {
                    let inner = fresh(store);
                    store.unify(&e, &Type::list(inner.clone())).ok()?;
                    (vec![], Type::list(inner))
                }
                "enumerate" => (vec![], Type::list(Type::Record(PAIR_REC, vec![Type::Int, e]))),
                "zip" => {
                    let other = fresh(store);
                    (vec![Type::list(other.clone())], Type::list(Type::Record(PAIR_REC, vec![e, other])))
                }
                "count" => {
                    let f = store.fresh_fn(vec![e], Type::Bool);
                    (vec![f], Type::Int)
                }
                _ => return None,
            })
        }
        Type::Range => Some(match name {
            "to_list" | "reversed" | "reverse" => (vec![], Type::list(Type::Int)),
            "map" => {
                let b = fresh(store);
                let f = store.fresh_fn(vec![Type::Int], b.clone());
                (vec![f], Type::list(b))
            }
            "filter" => {
                let f = store.fresh_fn(vec![Type::Int], Type::Bool);
                (vec![f], Type::list(Type::Int))
            }
            "each" => {
                let r = fresh(store);
                let f = store.fresh_fn(vec![Type::Int], r);
                (vec![f], Type::Unit)
            }
            "sum" | "min" | "max" | "length" | "first" | "last" => (vec![], Type::Int),
            "contains" => (vec![Type::Int], Type::Bool),
            "take" | "drop" => (vec![Type::Int], Type::list(Type::Int)),
            "reduce" => {
                let acc = fresh(store);
                let f = store.fresh_fn(vec![acc.clone(), Type::Int], acc.clone());
                (vec![f, acc.clone()], acc)
            }
            _ => return None,
        }),
        Type::Stream(elem) => {
            let e = (**elem).clone();
            Some(match name {
                "take" => (vec![Type::Int], Type::list(e)),
                "drop" => (vec![Type::Int], Type::stream(e)),
                "first" => (vec![], e),
                _ => return None,
            })
        }
        Type::Map(v) => {
            let v = (**v).clone();
            Some(match name {
                "keys" => (vec![], Type::list(Type::Str)),
                "values" => (vec![], Type::list(v)),
                "entries" => (vec![], Type::list(Type::Record(PAIR_REC, vec![Type::Str, v]))),
                "has" => (vec![Type::Str], Type::Bool),
                "length" | "size" => (vec![], Type::Int),
                "get" => (vec![Type::Str], Type::maybe(v)),
                "set" => (vec![Type::Str, v.clone()], Type::map(v)),
                "remove" | "delete" => (vec![Type::Str], Type::map(v)),
                _ => return None,
            })
        }
        Type::Maybe(_) => None,
        Type::Result(_, _) => None,
        _ => None,
    }
}

/// Global builtin functions whose signature does not depend on the
/// argument types. Overloaded ones (`len`, `sum`, `min`, `max`, `sorted`,
/// `reversed`, `abs`, `round`, `print`, `str`, `float`, `int`) are handled
/// in the inference directly.
pub fn global_sig(store: &mut TypeStore, name: &str, nargs: usize) -> Option<(Vec<Type>, Type)> {
    Some(match name {
        "range" => {
            if nargs == 1 {
                (vec![Type::Int], Type::Range)
            } else {
                (vec![Type::Int, Type::Int], Type::Range)
            }
        }
        "error" => {
            let r = store.fresh();
            (vec![Type::Str], r)
        }
        "assert" => {
            if nargs == 1 {
                (vec![Type::Bool], Type::Unit)
            } else {
                (vec![Type::Bool, Type::Str], Type::Unit)
            }
        }
        "bool" => {
            let a = store.fresh();
            (vec![a], Type::Bool)
        }
        _ => return None,
    })
}

/// Members of the builtin modules (`$math`, `$strings`, `$lists`, `$io`,
/// `$time`) as (parameter types, return type), or a constant's type.
pub fn module_member(store: &mut TypeStore, module: &str, name: &str, nargs: usize) -> Option<Type> {
    Some(match (module, name) {
        ("math", "pi") | ("math", "e") | ("math", "tau") | ("math", "inf") => Type::Float,
        ("math", "sqrt") | ("math", "sin") | ("math", "cos") | ("math", "tan") | ("math", "exp")
        | ("math", "floor") | ("math", "ceil") | ("math", "abs") | ("math", "log2") | ("math", "log10")
        | ("math", "asin") | ("math", "acos") | ("math", "atan") => store.fresh_fn(vec![Type::Float], Type::Float),
        ("math", "log") => {
            if nargs == 1 {
                store.fresh_fn(vec![Type::Float], Type::Float)
            } else {
                store.fresh_fn(vec![Type::Float, Type::Float], Type::Float)
            }
        }
        ("math", "pow") | ("math", "atan2") | ("math", "min") | ("math", "max") => {
            store.fresh_fn(vec![Type::Float, Type::Float], Type::Float)
        }
        ("strings", "join") => {
            if nargs == 1 {
                store.fresh_fn(vec![Type::list(Type::Str)], Type::Str)
            } else {
                store.fresh_fn(vec![Type::list(Type::Str), Type::Str], Type::Str)
            }
        }
        ("strings", "char_code") => store.fresh_fn(vec![Type::Str], Type::Int),
        ("strings", "from_char_code") => store.fresh_fn(vec![Type::Int], Type::Str),
        ("lists", "flatten") => {
            let a = store.fresh();
            store.fresh_fn(vec![Type::list(Type::list(a.clone()))], Type::list(a))
        }
        ("lists", "repeat") => {
            let a = store.fresh();
            store.fresh_fn(vec![a.clone(), Type::Int], Type::list(a))
        }
        ("lists", "enumerate") => {
            let a = store.fresh();
            store.fresh_fn(vec![Type::list(a.clone())], Type::list(Type::Record(PAIR_REC, vec![Type::Int, a])))
        }
        ("lists", "zip") => {
            let a = store.fresh();
            let b = store.fresh();
            store.fresh_fn(vec![Type::list(a.clone()), Type::list(b.clone())], Type::list(Type::Record(PAIR_REC, vec![a, b])))
        }
        ("io", "read_file") => store.fresh_fn(vec![Type::Str], Type::result(Type::Str, Type::Str)),
        ("io", "write_file") => store.fresh_fn(vec![Type::Str, Type::Str], Type::result(Type::Str, Type::Unit)),
        ("time", "now") => store.fresh_fn(vec![], Type::Int),
        _ => return None,
    })
}

/// The builtin type that is the only one with a method of this name, if
/// any (used to resolve `x.parse_int()` when nothing else fixes `x`).
pub fn unique_receiver(name: &str) -> Option<Type> {
    let str_only = ["upper", "lower", "trim", "trim_start", "trim_end", "split", "lines", "replace", "starts_with", "ends_with", "chars", "repeat", "to_int", "parse_int", "parse_float", "char_code"];
    let list_only = ["map", "filter", "each", "reduce", "any", "all", "find", "push", "pop", "drop_last", "sort", "sorted", "flatten", "enumerate", "zip", "count", "to_list"];
    let map_only = ["keys", "values", "entries", "has", "set", "remove", "delete"];
    if str_only.contains(&name) {
        Some(Type::Str)
    } else if list_only.contains(&name) {
        None
    } else if map_only.contains(&name) {
        None
    } else {
        None
    }
}
