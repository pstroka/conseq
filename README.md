`conseq!`
======

[<img alt="github" src="https://img.shields.io/badge/github-pstroka/conseq-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/pstroka/conseq)
[<img alt="crates.io" src="https://img.shields.io/crates/v/conseq.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/conseq)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-conseq-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs" height="20">](https://docs.rs/conseq)

A `conseq!` macro to conditionally repeat a fragment of source code and
substitute into each repetition a sequential numeric counter.

This is a fork of [`seq!`](https://github.com/dtolnay/seq-macro), extended with the following features:
- apply the repetitions conditionally 
- use the `conseq!` macro inside another `conseq!` macro


```toml
[dependencies]
conseq = "0.1.0"
```

```rust
use conseq::conseq;

fn main() {
    let tuple = (1000, 100, 10);
    let mut sum = 0;
    
    // Expands to:
    //
    //     sum += tuple.0;
    //     sum += tuple.1;
    //     sum += tuple.2;
    //
    // This cannot be written using an ordinary for-loop because elements of
    // a tuple can only be accessed by their integer literal index, not by a
    // variable.
    conseq!(N in 0..=2 {
        sum += tuple.N;
    });
    
    assert_eq!(sum, 1110);
}
```

- If the input tokens contain a section surrounded by `$[N](` ... `)*`, where N is the name of
  the numeric counter, then only that part is repeated.

- The numeric counter can be pasted onto the end of some prefix to form
  sequential identifiers.

```rust
use conseq::conseq;

conseq!(N in 64..=127 {
    #[derive(Debug)]
    enum Demo {
        // Expands to Variant64, Variant65, ...
        $[N](
            Variant~N,
        )*
    }
});

fn main() {
    assert_eq!("Variant99", format!("{:?}", Demo::Variant99));
}
```

- You can also use comparison operators (>, >=, <, <=, ==) inside `$[` ... `]` to repeat the
  sequence conditionally.

```rust
use conseq::conseq;

fn main() {
    let tuple = (1000, 100, 10);
    let mut sum1 = 0;
    let mut sum2 = 0;
    let mut sum3 = 0;
    let mut sum4 = 0;
    let mut sum5 = 0;

    conseq!(N in 0..=2 {
        $[N](sum1 += tuple.N;)*
        $[N < 1](sum2 += tuple.N;)*
        $[N < 2](sum3 += tuple.N;)*
        $[N >= 1](sum4 += tuple.N;)*
        $[N == 2](sum5 += tuple.N;)*
    });

    assert_eq!(sum1, 1110);
    assert_eq!(sum2, 1000);
    assert_eq!(sum3, 1100);
    assert_eq!(sum4, 110);
    assert_eq!(sum5, 10);
}
```

- Here is a more useful example

```rust
use conseq::conseq;

struct VarArgs<T> {
    tuple: T,
}

conseq!(N in 0..3 {
    impl<$[N < 1](T~N: PartialEq,)*> From<($[N < 1](T~N,)*)> for VarArgs<($[N < 1](T~N,)*)> {
        fn from(tuple: ($[N < 1](T~N,)*)) -> Self {
            VarArgs { tuple }
        }
    }
    impl<$[N < 2](T~N: PartialEq,)*> From<($[N < 2](T~N,)*)> for VarArgs<($[N < 2](T~N,)*)> {
        fn from(tuple: ($[N < 2](T~N,)*)) -> Self {
            VarArgs { tuple }
        }
    }
    impl<$[N < 3](T~N: PartialEq,)*> From<($[N < 3](T~N,)*)> for VarArgs<($[N < 3](T~N,)*)> {
        fn from(tuple: ($[N < 3](T~N,)*)) -> Self {
            VarArgs { tuple }
        }
    }
});

fn main() {
    let args1 = VarArgs::from((123,));
    let args2 = VarArgs::from((123, "text"));
    let args3 = VarArgs::from((123, "text", 1.5));
    assert_eq!(args1.tuple, (123,));
    assert_eq!(args2.tuple, (123, "text"));
    assert_eq!(args3.tuple, (123, "text", 1.5));
}
```

- You can also use a `conseq!` macro inside another `conseq!` macro

```rust
use conseq::conseq;

conseq!(N in 1..=3 {
    struct Struct<$[N](T~N,)*> {
        $[N](field~N: T~N,)*
        another_field: String,
    }
    impl<$[N](T~N,)*> Struct<$[N](T~N,)*> {
        fn new($[N](field~N: T~N,)*) -> Self {
            let mut another_field = String::from("");
            // I know, this is a stupid example, 
            // but I wanted to demonstrate that you can actually do that 
            conseq!(L in 'a'..='z'{ another_field.push(L); });
            Struct { $[N](field~N,)* another_field }
        }
    }
});

fn main() {
    let s = Struct::new(1, 35.6, "abc");
    assert_eq!(s.field1, 1);
    assert_eq!(s.field2, 35.6);
    assert_eq!(s.field3, "abc");
    assert_eq!(s.another_field, "abcdefghijklmnopqrstuvwxyz");
}
```

- Byte and character ranges are supported: `b'a'..=b'z'`, `'a'..='z'`.

- If the range bounds are written in binary, octal, hex, or with zero padding,
  those features are preserved in any generated tokens.

```rust
use conseq::conseq;

conseq!(P in 0x000..=0x00F {
    // expands to structs Pin000, ..., Pin009, Pin00A, ..., Pin00F
    struct Pin~P;
});
```

<br>

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
