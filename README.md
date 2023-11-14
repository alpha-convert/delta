# Creek

The Creek language is a functional programming language that compiles to stream-processing automata. 

A simple Creek program is the add-one-to-all function, which takes a stream of integers, and produces the stream where each integer has been incremented by one.

```
fun addOneToAll(xs : Int*) : Int* =
    case xs of
      nil => nil
    | y::ys => wait y do
                 {y + 1} :: rec(ys)
               end
```

While this looks like a mostly normal functional program (albiet annotated with some extra nonsense), it runs like a stream processing function: accepting and producing one element of the input at a time.

We can demonstrate this by running it for one step:

```
>> exec step addOneToAll([1;emp))
[2;emp)
```
And then running it for another step
```
>> exec step addOneToAll([4;emp))
[5;emp)

```

### Types

Values in Creek are data streams, and so the types in Creek are *stream types*. Stream types are similar to regular expressions in that they describe the structure of a sequence of data.

The most important type in Creek is the *star* type of repeated values. This type is written like `s*`, where `s` is another stream type. For example, type `Int*` is the type of streams of ints, one int after another. A value of type `Int*` is a finite, but potentially unbounded, stream of values of type `Int`. Programming with star streams is a lot like programming with lists. Terms of type `s*` come in two forms: they are either `nil`, the empty stream of `s`s, or `e :: e'`, where `e` has type `s`, and `e'` has type `s*`.

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

The Creek language is actively being developed by Joseph Cutler. Creek is based on the [Stream Types](https://arxiv.org/abs/2307.09553) Calculus,
created by Joseph Cutler, Christopher Watson, Phillip Hilliard, Harrison Goldstein, Caleb Stanford, and Benjamin C. Pierce. The typechecking algorithm in Creek was developed by Emeka Nkurumeh.