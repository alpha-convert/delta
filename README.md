# delta

The delta language is a functional programming language that compiles to stream-processing automata. 
For a full introduction to the core calculus that delta is based on, see [Stream Types](https://www.seas.upenn.edu/~jwc/assets/stream-types.pdf).

delta has a number of features that set it apart from existing stream-processing languages:

1. delta is not combinator-based. Unlike many stream processing languages, which provides a limited set of combinators like `map`, `filter`, and `fold`, delta programs are written as standard functional list programs. All of the afformentioned standard streaming combinators can be written in delta, but programmers are not required to fit their programs into a composition of ad-hoc recursion schemes. This is enabled by a novel ordered type system, which statically rejects list programs that cannot be run a stream programs.

2. delta has rich ``stream types'', which allow programmers to express and rely on complex temporal patterns in their streams.

3. delta is deterministic by default: all well-typed programs are guaranteed to run deterministically, even in the presence of parallel input streams.

A simple delta program is the running sum function, which takes a stream of integers (written `Int*`), and produces the stream that is a running sum of the input.

```
fun go(n : Int; xs : Int*) : Int* = 
    case xs of
      nil => n :: nil
    | y::ys => wait y do
                 let k = {n + y} in
                 {n + y} :: go({n + y};ys)
               end

fun runningSum(xs : Int*) : Int* =
     go(0;xs)
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
fun snoc(x : Int; xs : Int*) : Int* =
     case xs of
       nil => [x]
     | y::ys => y :: snoc(x;ys)

fun rev(xs : Int*) : Int* =
     case xs of
       nil => nil
     | y::ys => snoc(y;ys)
```

The function `snoc` is rejected by delta with the error message "Variable `y` used before `x`, but expected the other order".
(Actually, the error message doesn't say this, it says something much less readable and even less understandable. This is still a prototype, the error messages are terrible.)
This is because the order of arguments to a delta function matters. The order of arguments describes the order of *arrival*: `snoc`
is a function that expects first a single `Int`, bound to `x`, and then some more `Int`s, which get bound to `xs`. When we pattern match
on `xs` and get a head `y` and tails `ys`, these also have an order. The second branch of the case expects to first get `x`, and then `y`,
and then `ys`. The error arises when we *use* `y` first, out of order.

This requirement, that we use variables in the order they're listed, ensures that we can implement the program as a streaming program.
If the first-to-arrive variable is used first, we can take the first piece of input, use it to produce an initial prefix of output,
and then continue once the next piece of input arrives.

### Types

Values in delta are data streams, and so the types in delta are *stream types*. Stream types are similar to regular expressions in that they describe the structure of a sequence of data.

The most important type in delta is the *star* type of repeated values. This type is written like `s*`, where `s` is another stream type. For example, type `Int*` is the type of streams of ints, one int after another. A value of type `Int*` is a finite, but potentially unbounded, stream of values of type `Int`. Programming with star streams is a lot like programming with lists. Terms of type `s*` come in two forms: they are either `nil`, the empty stream of `s`s, or `e :: e'`, where `e` has type `s`, and `e'` has type `s*`.

### Syntax

Todo

## Compiler Structure

Todo

## Papers

## Acknowledgements

The delta language is actively being developed by Joseph Cutler. delta is based on the [Stream Types](https://arxiv.org/abs/2307.09553) Calculus,
created by Joseph Cutler, Christopher Watson, Phillip Hilliard, Harrison Goldstein, Caleb Stanford, and Benjamin C. Pierce. The typechecking algorithm in delta was developed by Emeka Nkurumeh.