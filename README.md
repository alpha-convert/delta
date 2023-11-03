# Creek

The Creek language is a functional programming language that compiles to
stream-processing automata. 

### Syntax

```

pat := x | _

e ::= let (pat;pat) = e in e'
     | inl e
     | inr e
     | case e of inl pat => e1 | inr pat => e2
```

## Acknowledgements

The Creek language is actively being developed by Joseph Cutler. Creek is based on the [Stream Types](https://arxiv.org/abs/2307.09553) Calculus,
created by Joseph Cutler, Christopher Watson, Phillip Hilliard, Harrison Goldstein, Caleb Stanford, and Benjamin C. Pierce. The typechecking algorithm in Creek was developed by Emeka Nkurumeh.
