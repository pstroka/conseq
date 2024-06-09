//! [![github]](https://github.com/pstroka/conseq)&ensp;[![crates-io]](https://crates.io/crates/conseq)&ensp;[![docs-rs]](https://docs.rs/conseq)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! # Imagine for-loops in a macro
//!
//! This crate provides a `conseq!` macro to conditionally repeat a fragment of source code and
//! substitute into each repetition a sequential numeric counter.
//!
//! ```
//! use conseq::conseq;
//!
//! let tuple = (1000, 100, 10);
//! let mut sum = 0;
//!
//! // Expands to:
//! //
//! //     sum += tuple.0;
//! //     sum += tuple.1;
//! //     sum += tuple.2;
//! //
//! // This cannot be written using an ordinary for-loop because elements of
//! // a tuple can only be accessed by their integer literal index, not by a
//! // variable.
//! conseq!(N in 0..=2 {
//!     sum += tuple.N;
//! });
//!
//! assert_eq!(sum, 1110);
//! ```
//!
//! - If the input tokens contain a section surrounded by `$[N](` ... `)*`, where N is the name of
//!   the numeric counter, then only that part is repeated.
//!
//! - The numeric counter can be pasted onto the end of some prefix to form
//!   sequential identifiers.
//!
//! ```
//! use conseq::conseq;
//!
//! conseq!(N in 64..=127 {
//!     #[derive(Debug)]
//!     enum Demo {
//!         // Expands to Variant64, Variant65, ...
//!         $[N](
//!             Variant~N,
//!         )*
//!     }
//! });
//!
//! assert_eq!("Variant99", format!("{:?}", Demo::Variant99));
//! ```
//! - You can also use comparison operators (>, >=, <, <=, ==) inside `$[` ... `]` to repeat the
//!   sequence conditionally.
//!
//! ```
//! use conseq::conseq;
//!
//! let tuple = (1000, 100, 10);
//! let mut sum1 = 0;
//! let mut sum2 = 0;
//! let mut sum3 = 0;
//! let mut sum4 = 0;
//! let mut sum5 = 0;
//!
//! conseq!(N in 0..=2 {
//!     $[N](sum1 += tuple.N;)*
//!     $[N < 1](sum2 += tuple.N;)*
//!     $[N < 2](sum3 += tuple.N;)*
//!     $[N >= 1](sum4 += tuple.N;)*
//!     $[N == 2](sum5 += tuple.N;)*
//! });
//!
//! assert_eq!(sum1, 1110);
//! assert_eq!(sum2, 1000);
//! assert_eq!(sum3, 1100);
//! assert_eq!(sum4, 110);
//! assert_eq!(sum5, 10);
//! ```
//! - Here is a more useful example
//!
//! ```
//! use conseq::conseq;
//!
//! struct VarArgs<T> {
//!     tuple: T,
//! }
//! 
//! conseq!(N in 0..3 {
//!     impl<$[N < 1](T~N: PartialEq,)*> From<($[N < 1](T~N,)*)> for VarArgs<($[N < 1](T~N,)*)> {
//!         fn from(tuple: ($[N < 1](T~N,)*)) -> Self {
//!             VarArgs { tuple }
//!         }
//!     }
//!     impl<$[N < 2](T~N: PartialEq,)*> From<($[N < 2](T~N,)*)> for VarArgs<($[N < 2](T~N,)*)> {
//!         fn from(tuple: ($[N < 2](T~N,)*)) -> Self {
//!             VarArgs { tuple }
//!         }
//!     }
//!     impl<$[N < 3](T~N: PartialEq,)*> From<($[N < 3](T~N,)*)> for VarArgs<($[N < 3](T~N,)*)> {
//!         fn from(tuple: ($[N < 3](T~N,)*)) -> Self {
//!             VarArgs { tuple }
//!         }
//!     }
//! });
//!
//! let args1 = VarArgs::from((123,));
//! let args2 = VarArgs::from((123, "text"));
//! let args3 = VarArgs::from((123, "text", 1.5));
//! assert_eq!(args1.tuple, (123,));
//! assert_eq!(args2.tuple, (123, "text"));
//! assert_eq!(args3.tuple, (123, "text", 1.5));
//! ```
//! - You can also use a `conseq!` macro inside another `conseq!` macro
//!
//! ```
//! use conseq::conseq;
//!
//! conseq!(N in 1..=3 {
//!     struct Struct<$[N](T~N,)*> {
//!         $[N](field~N: T~N,)*
//!         another_field: String,
//!     }
//!     impl<$[N](T~N,)*> Struct<$[N](T~N,)*> {
//!         fn new($[N](field~N: T~N,)*) -> Self {
//!             let mut another_field = String::from("");
//!             // I know, this is a stupid example, 
//!             // but I wanted to demonstrate that you can actually do that 
//!             conseq!(L in 'a'..='z'{ another_field.push(L); });
//!             Struct { $[N](field~N,)* another_field }
//!         }
//!     }
//! });
//!
//! let s = Struct::new(1, 35.6, "abc");
//! assert_eq!(s.field1, 1);
//! assert_eq!(s.field2, 35.6);
//! assert_eq!(s.field3, "abc");
//! assert_eq!(s.another_field, "abcdefghijklmnopqrstuvwxyz");
//! ```
//! - Byte and character ranges are supported: `b'a'..=b'z'`, `'a'..='z'`.
//!
//! - If the range bounds are written in binary, octal, hex, or with zero
//!   padding, those features are preserved in any generated tokens.
//!
//! ```
//! use conseq::conseq;
//!
//! conseq!(P in 0x000..=0x00F {
//!     // expands to structs Pin000, ..., Pin009, Pin00A, ..., Pin00F
//!     struct Pin~P;
//! });
//! ```
mod parse;

use crate::parse::*;
use core::panic;
use proc_macro::{Delimiter, Group, Ident, Literal, Span, TokenStream, TokenTree};
use std::iter::{self, FromIterator};
use std::{char, str::FromStr};

#[proc_macro]
pub fn conseq(input: TokenStream) -> TokenStream {
    match seq_impl(input) {
        Ok(expanded) => expanded,
        Err(error) => error.into_compile_error(),
    }
}

struct Range {
    begin: u64,
    end: u64,
    inclusive: bool,
    kind: Kind,
    suffix: String,
    width: usize,
    radix: Radix,
}

struct Value {
    int: u64,
    kind: Kind,
    suffix: String,
    width: usize,
    radix: Radix,
    span: Span,
}

struct Splice<'a> {
    int: u64,
    kind: Kind,
    suffix: &'a str,
    width: usize,
    radix: Radix,
}

#[derive(Copy, Clone, PartialEq)]
enum Kind {
    Int,
    Byte,
    Char,
}

#[derive(Copy, Clone, PartialEq)]
enum Radix {
    Binary,
    Octal,
    Decimal,
    LowerHex,
    UpperHex,
}

enum Comp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
}

impl Comp {
    fn compare(&self, lhs: &Splice, rhs: &Value) -> bool {
        assert!(lhs.kind == rhs.kind, "expected value of the same kind");
        match self {
            Comp::Gt => lhs.int > rhs.int,
            Comp::Ge => lhs.int >= rhs.int,
            Comp::Lt => lhs.int < rhs.int,
            Comp::Le => lhs.int <= rhs.int,
            Comp::Eq => lhs.int == rhs.int,
        }
    }
}

impl FromStr for Comp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            ">" => Ok(Comp::Gt),
            ">=" => Ok(Comp::Ge),
            "<" => Ok(Comp::Lt),
            "<=" => Ok(Comp::Le),
            "==" => Ok(Comp::Eq),
            _ => panic!("expected a comparison operator"),
        }
    }
}

enum Condition {
    Ident(Ident),
    Compare(Ident, Comp, Value),
}

impl Condition {
    fn is_met(&self, repetition: &Splice, var: &Ident) -> bool {
        match self {
            Condition::Ident(ident) => ident.to_string() == var.to_string(),
            Condition::Compare(ident, comp, value) => {
                ident.to_string() == var.to_string() && comp.compare(repetition, value)
            }
        }
    }
}

impl<'a> IntoIterator for &'a Range {
    type Item = Splice<'a>;
    type IntoIter = Box<dyn Iterator<Item = Splice<'a>> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        let splice = move |int| Splice {
            int,
            kind: self.kind,
            suffix: &self.suffix,
            width: self.width,
            radix: self.radix,
        };
        match self.kind {
            Kind::Int | Kind::Byte => {
                if self.inclusive {
                    Box::new((self.begin..=self.end).map(splice))
                } else {
                    Box::new((self.begin..self.end).map(splice))
                }
            }
            Kind::Char => {
                let begin = char::from_u32(self.begin as u32).unwrap();
                let end = char::from_u32(self.end as u32).unwrap();
                let int = |ch| u64::from(u32::from(ch));
                if self.inclusive {
                    Box::new((begin..=end).map(int).map(splice))
                } else {
                    Box::new((begin..end).map(int).map(splice))
                }
            }
        }
    }
}

fn seq_impl(input: TokenStream) -> Result<TokenStream, SyntaxError> {
    let mut iter = input.into_iter();
    let var = require_ident(&mut iter)?;
    require_keyword(&mut iter, "in")?;
    let begin = require_value(&mut iter)?;
    require_punct(&mut iter, '.')?;
    require_punct(&mut iter, '.')?;
    let inclusive = require_if_punct(&mut iter, '=')?;
    let end = require_value(&mut iter)?;
    let body = require_braces(&mut iter)?;
    require_end(&mut iter)?;

    let range = validate_range(begin, end, inclusive)?;

    let mut found_repetition = false;
    let expanded = expand_repetitions(&var, &range, body.clone(), &mut found_repetition);
    if found_repetition {
        Ok(expanded)
    } else {
        // If no `$[...](...)*`, repeat the entire body.
        Ok(repeat(&var, &range, &body))
    }
}

fn repeat(var: &Ident, range: &Range, body: &TokenStream) -> TokenStream {
    let mut repeated = TokenStream::new();
    for value in range {
        repeated.extend(substitute_value(var, &value, body.clone()));
    }
    repeated
}

fn substitute_value(var: &Ident, splice: &Splice, body: TokenStream) -> TokenStream {
    let mut tokens = Vec::from_iter(body);

    let mut i = 0;
    while i < tokens.len() {
        // Substitute our variable by itself, e.g. `N`.
        let replace = match &tokens[i] {
            TokenTree::Ident(ident) => ident.to_string() == var.to_string(),
            _ => false,
        };
        if replace {
            let original_span = tokens[i].span();
            let mut literal = splice.literal();
            literal.set_span(original_span);
            tokens[i] = TokenTree::Literal(literal);
            i += 1;
            continue;
        }

        // Substitute our variable concatenated onto some prefix, `Prefix~N`.
        if i + 3 <= tokens.len() {
            let prefix = match &tokens[i..i + 3] {
                [first, TokenTree::Punct(tilde), TokenTree::Ident(ident)]
                    if tilde.as_char() == '~' && ident.to_string() == var.to_string() =>
                {
                    match first {
                        TokenTree::Ident(ident) => Some(ident.clone()),
                        TokenTree::Group(group) => {
                            let mut iter = group.stream().into_iter().fuse();
                            match (iter.next(), iter.next()) {
                                (Some(TokenTree::Ident(ident)), None) => Some(ident),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(prefix) = prefix {
                let number = match splice.kind {
                    Kind::Int => match splice.radix {
                        Radix::Binary => format!("{0:01$b}", splice.int, splice.width),
                        Radix::Octal => format!("{0:01$o}", splice.int, splice.width),
                        Radix::Decimal => format!("{0:01$}", splice.int, splice.width),
                        Radix::LowerHex => format!("{0:01$x}", splice.int, splice.width),
                        Radix::UpperHex => format!("{0:01$X}", splice.int, splice.width),
                    },
                    Kind::Byte | Kind::Char => {
                        char::from_u32(splice.int as u32).unwrap().to_string()
                    }
                };
                let concat = format!("{}{}", prefix, number);
                let ident = Ident::new(&concat, prefix.span());
                tokens.splice(i..i + 3, iter::once(TokenTree::Ident(ident)));
                i += 1;
                continue;
            }
        }

        // Recursively substitute content nested in a group.
        if let TokenTree::Group(group) = &mut tokens[i] {
            let original_span = group.span();
            let content = substitute_value(var, splice, group.stream());
            *group = Group::new(group.delimiter(), content);
            group.set_span(original_span);
        }

        i += 1;
    }

    TokenStream::from_iter(tokens)
}

const TOKENS: usize = 4;

fn enter_repetition(tokens: &[TokenTree], var: &Ident) -> Option<(TokenStream, Condition)> {
    assert!(tokens.len() == TOKENS);
    match &tokens[0] {
        TokenTree::Punct(punct) if punct.as_char() == '$' => {}
        _ => return None,
    }
    match &tokens[3] {
        TokenTree::Punct(punct) if punct.as_char() == '*' => {}
        _ => return None,
    }
    let condition = match &tokens[1] {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Bracket => {
            match parse_condition(group.stream(), var) {
                Some(condition) => condition,
                None => return None,
            }
        }
        _ => return None,
    };
    match &tokens[2] {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Parenthesis => {
            Some((group.stream(), condition))
        }
        _ => None,
    }
}

// TODO: add templates/variables e.g #X = N < 3 or #Y = (something<~N>)
// #Types=($[N](T~N: PartialEq,)*)
// impl<#Types>
fn parse_condition(body: TokenStream, var: &Ident) -> Option<Condition> {
    let tokens = Vec::from_iter(body);
    let tokens = tokens.as_slice();
    match tokens {
        [TokenTree::Ident(ident)] if ident.to_string() == var.to_string() => {
            Some(Condition::Ident(ident.clone()))
        }
        [TokenTree::Ident(ident), TokenTree::Punct(p), TokenTree::Literal(literal)]
            if ident.to_string() == var.to_string() =>
        {
            Some(Condition::Compare(
                ident.clone(),
                Comp::from_str(&p.to_string()).unwrap(),
                parse_literal(literal).unwrap(),
            ))
        }
        [TokenTree::Ident(ident), TokenTree::Punct(p1), TokenTree::Punct(p2), TokenTree::Literal(literal)]
            if ident.to_string() == var.to_string() =>
        {
            Some(Condition::Compare(
                ident.clone(),
                Comp::from_str(&format!("{p1}{p2}")).unwrap(),
                parse_literal(literal).unwrap(),
            ))
        }
        [TokenTree::Literal(literal), TokenTree::Punct(p), TokenTree::Ident(ident)]
            if ident.to_string() == var.to_string() =>
        {
            Some(Condition::Compare(
                ident.clone(),
                Comp::from_str(&p.to_string()).unwrap(),
                parse_literal(literal).unwrap(),
            ))
        }
        [TokenTree::Literal(literal), TokenTree::Punct(p1), TokenTree::Punct(p2), TokenTree::Ident(ident)]
            if ident.to_string() == var.to_string() =>
        {
            Some(Condition::Compare(
                ident.clone(),
                Comp::from_str(&format!("{p1}{p2}")).unwrap(),
                parse_literal(literal).unwrap(),
            ))
        }
        _ => None,
    }
}

fn expand_repetitions(
    var: &Ident,
    range: &Range,
    body: TokenStream,
    found_repetition: &mut bool,
) -> TokenStream {
    let mut tokens = Vec::from_iter(body.clone());
    // Look for `$[...](...)*`.
    let mut i = 0;
    while i < tokens.len() {
        if let TokenTree::Group(group) = &mut tokens[i] {
            let content = expand_repetitions(var, range, group.stream(), found_repetition);
            let original_span = group.span();
            *group = Group::new(group.delimiter(), content);
            group.set_span(original_span);
            i += 1;
            continue;
        }
        if i + TOKENS > tokens.len() {
            i += 1;
            continue;
        }
        let (template, condition) = match enter_repetition(&tokens[i..i + TOKENS], var) {
            Some(repetition) => repetition,
            None => {
                i += 1;
                continue;
            }
        };
        *found_repetition = true;
        let mut repeated = Vec::new();
        for value in range {
            if condition.is_met(&value, var) {
                repeated.extend(substitute_value(var, &value, template.clone()));
            }
        }
        let repeated_len = repeated.len();
        tokens.splice(i..i + TOKENS, repeated);
        i += repeated_len;
    }

    TokenStream::from_iter(tokens)
}

impl Splice<'_> {
    fn literal(&self) -> Literal {
        match self.kind {
            Kind::Int | Kind::Byte => {
                let repr = match self.radix {
                    Radix::Binary => format!("0b{0:02$b}{1}", self.int, self.suffix, self.width),
                    Radix::Octal => format!("0o{0:02$o}{1}", self.int, self.suffix, self.width),
                    Radix::Decimal => format!("{0:02$}{1}", self.int, self.suffix, self.width),
                    Radix::LowerHex => format!("0x{0:02$x}{1}", self.int, self.suffix, self.width),
                    Radix::UpperHex => format!("0x{0:02$X}{1}", self.int, self.suffix, self.width),
                };
                let tokens = repr.parse::<TokenStream>().unwrap();
                let mut iter = tokens.into_iter();
                let literal = match iter.next() {
                    Some(TokenTree::Literal(literal)) => literal,
                    _ => unreachable!(),
                };
                assert!(iter.next().is_none());
                literal
            }
            Kind::Char => {
                let ch = char::from_u32(self.int as u32).unwrap();
                Literal::character(ch)
            }
        }
    }
}
