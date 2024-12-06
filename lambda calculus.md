# Simple Typed Lambda Calculus

## Syntax

```
t ::= x # variable
    | λx.t # abstraction, function x with the body of t
    | t t # application
```

We can reduce abstractions, Coq does this but Ocaml does not.

```

    e -> e'
---------------
λx:e -> λx:e'
```

example

```
(λx:3+2+x) --> (λx:5+x)
```

The following is a rule for reducing an application

```
    e1 -> e1'
-------------------
 e1 e2 -> e1' e2


    e2 -> e2'
---------------------
 λx:e1 e2 -> λx:e1 e2'
```

basically we need to reduce the left side of the application first.

---

### Random Info

closed terms are terms that do not have free variables.
example: λx.x is a closed term but λx.y is not a closed term.
more examples:

```
λx.x # this is a closed term
λx.y # this is not a closed term
λx.λy.x # this is a closed term
λx.λy z # this is not a closed term
λx.λy.y # this is a closed term
λx.λy.x y # this is a closed term
λx.λy.y x # this is a closed term
```

---

final rule we need for the language, beta reduction

```
    e1 -> v
----------------
λx.e e1 -> [x -> v]e
```

the other rules are called congruence rules, this is the only rule that actually does something. (one ring to rule them all) it is enough to simulate the entirety of the language.

- alpha renaming: renaming the bound variable in an abstraction
- beta reduction: applying a function to an argument
- eta expansion: adding a function to an argument

### Church Encoding

#### Successor Function (Natural Numbers)

```
λ f.λ x. x                  # 0
λ f.λ x. f x                # 1
λ f.λ x. f (f x)            # 2
λ f.λ x. f (f (f x))        # 3
.... and so on
```

This can be used to encode numbers, f could be our successor
function and x could be our zero.
here is how to define `succ`

```
succ n = λ f.λ x. f(n f x) # successor function
```

the previous function can be explained as follows:

```
succ 0 = λ f.λ x. f(0 f x) = λ f.λ x. f x = 1
succ 1 = λ f.λ x. f(1 f x) = λ f.λ x. f(f x) = 2
succ 2 = λ f.λ x. f(2 f x) = λ f.λ x. f(f(f x)) = 3
```

##### Addition

```
add m n = λ f.λ x. m f (n f x)
```

#### Booleans

```
true = λ a.λ b. a
false = λ a.λ b. b
```

##### Not

p is a predicate `if p then a else b`

```
not p = λ p.λ a.λ b. p b a
```

##### Or

p1 and p2 are basically predicates `if p1 then a else b`

```
or a b = λ p1.λ p2.λ a.λ b. p1 a (p2 a b)
```

##### And

p1 and p2 are basically predicates `if p1 then a else b`

```
and a b = λ p1.λ p2.λ a.λ b. p1 (p2 a b) b
```

#### Recursion

##### The omega combinator:

```
Ω = (λx. x x) (λx. x x)
```

this is does not terminate.

##### The Y combinator:

The Y combinator is a fixed point combinator, it is a function that takes a function and returns a fixed point of that function.

```
Yg = (λy.(λx. g (x x)) (λx. g (x x)))
   = g((λx. g (x x)) (λx. g (x x)))
   = g(Yg)
```

> something to research function by name and function by value

~ very mind bending stuff. ~
$$ lisp $$
$$ haskell $$
[SICP Book](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/6515/sicp.zip/index.html)
this is the introduction book to programming at MIT.
