# Delta

The Delta language is a functional programming language that compiles to stream-processing automata. 

Delta has a number of features that set it apart from existing stream-processing languages:

1. Delta is not combinator-based. Unlike every other stream processing language, which provides a limited set of combinators like `map`, `filter`, and `fold`, Delta programs are written as standard functional list programs. All of the afformentioned standard streaming combinators can be written in Delta, but programmers are not required to fit their programs into a composition of ad-hoc stateful recursion schemes. This is enabled by a novel ordered type system, which statically rejects list programs that cannot be run a stream programs.

2. Delta has rich ``stream types'', which allow programmers to express and rely on complex temporal patterns in their streams.

3. Delta is deterministic by default: all well-typed programs are guaranteed to run deterministically, even in the presence of parallel input streams.

A simple Delta program is the running sum function, which takes a stream of integers (written `Int*`), and produces the stream that is a running sum of the input.

```
fun runningSum(xs : Int*) : Int* =
     go(0;xs)

fun go(n : Int; xs : Int*) : Int* = 
    case xs of
      nil => n :: nil
    | y::ys => wait y do
                 let k = {n + y} in
                 {n + y} :: rec({n + y} ys)
               end
```


While this looks like a mostly normal functional program (albiet annotated with some extra nonsense), it runs like a stateful stream processing function: accepting and producing one element of the input at a time, and updating an internal state. We can demonstrate this by first running it for one step: sending in a `2`, produces the running total.

```
>> exec step addOneToAll(xs = [2;emp))
[2;emp)
```

And then running it for another step: sending in a `4` produces `6`, the result of `6 + 2`

```
>> exec step addOneToAll(xs =[4;emp))
[6;emp)
```

### Statically Checking Streamability

Of course, there are a lot of match/nil/cons list programs which are *not* (naturally) streaming programs. For example, one could imagine
attempting to write the `reverse` program as follows:

```
fun snoc(x : Int ; xs : Int*) =
     case xs of
       nil => [x]
     | y::ys => y :: rec(x;ys)

fun rev(xs : Int*) : Int* =
     case xs of
       nil => nil
     | y::ys => snoc(y;ys)
```

The function `snoc` is rejected by Delta with the error message "Variable `xs` can before `x` in term `...`". This is because 





### Homomorphism


### Types

Values in Delta are data streams, and so the types in Delta are *stream types*. Stream types are similar to regular expressions in that they describe the structure of a sequence of data.

The most important type in Delta is the *star* type of repeated values. This type is written like `s*`, where `s` is another stream type. For example, type `Int*` is the type of streams of ints, one int after another. A value of type `Int*` is a finite, but potentially unbounded, stream of values of type `Int`. Programming with star streams is a lot like programming with lists. Terms of type `s*` come in two forms: they are either `nil`, the empty stream of `s`s, or `e :: e'`, where `e` has type `s`, and `e'` has type `s*`.

### Ordering

### Syntax

```

pat := x | _

e ::=  x
     | sink
     | int
     | bool
     | (e1 ; e2)
     | let (pat;pat) = e in e'
     | inl e
     | inr e
     | case e of inl pat => e1 | inr pat => e2
     | nil
     | e1 :: e2
     | case e of nil => e1 | pat :: pat => e2
     | nat
     | bool
     | x
     | wait x1,...,xn do e' end
     | { hp }

hp ::= hp1 + hp2
     | hp1 - hp2
     | hp1 * hp2
     | hp1 / hp2
     | inl hp
     | inr hp
     | nil
     | hp1 :: hp2
     | (hp1,hp2)
     | ()
```

## Acknowledgements

The Delta language is actively being developed by Joseph Cutler. Delta is based on the [Stream Types](https://arxiv.org/abs/2307.09553) Calculus,
created by Joseph Cutler, Christopher Watson, Phillip Hilliard, Harrison Goldstein, Caleb Stanford, and Benjamin C. Pierce. The typechecking algorithm in Delta was developed by Emeka Nkurumeh.