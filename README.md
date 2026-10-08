# Rocq-partial — A simple Rocq library for extractable partialilty

This library provides a `partial` monad for representing partiality.
Resulting programs can be composed, reasoned about, and extracted.

## Using the library

Have a look at `theories/Examples.v` to see how to use it.
For extraction, this is completed by having a look at `src/main.ml`.

A basic example is the following:
```rocq
Definition ack : nat → nat → partial nat :=
  #pfix ack (m : nat) (n : nat),
    match m, n with
    | 0, _ => ret (S n)
    | S m', 0 => ack m' 1
    | S m', S n' => k ← ack m n' ;; ack m' k
    end.

Definition ack_sum : nat → partial nat :=
  #pfix ack_sum n,
    if n =? 0 then ret 0
    else
      k ← lift (ack n n) ;;
      l ← ack_sum (n - 1) ;;
      ret (k + l).
```

It makes use of notations for monads, and shows how one can use `lift` to
combine programs in the partial and in the recursion monads.

The example file also showcases reasoning about partial programs, and
combination with other effects such as exceptions and state.

## Behind the scenes

This library works by combining several ideas from the literature:
  - Continuity and effectiveness in topoi, Giuseppe Rosolini
  - Axiomatic Domain Theory in Categories of Partial Maps, Marcelo Fiore
  - Modelling general recursion in type theory, Ana Bove and Venanzio Capretta
  - Turing-completeness totally free, Conor McBride
  - Partial Elements and Recursion via Dominances in Univalent Type Theory, Martín Escardó and Cory Knapp
  - The Braga Method: Extracting Certified Algorithms from Complex Recursive Schemes in Coq, Dominique Larchey-Wendling and Jean-François Monin

The `partial` monad is given by a *mere* proposition (in the sense of
homotopy type theory, an "hProp") which asserts whether it is defined, and a
function guarded by the proposition, which returns a value when it is.

```rocq
Record partial A := guarded {
  defined : hProp ;
  value : defined → A
}.
```

This is enough to easily show it is a monad (although its laws are only up to
propositional equality when assuming proposition and function extensionality),
and to implement `undefined {A} : partial A`.
For general recursion, we use a general recursion monad, we call `orec`, which
records recursive calls explicitly in a tree.
We use it to define a graph of the function, and then its domain, and define the
partial function by induction on said domain.

## Installing from source

You may install from source using either `opam` or `make`.
With `opam`, proceed as follows:

```sh
opam install .
```

With `make` you may perform:
```sh
make
make install
```

You can also run
```sh
make test
```
to run the extracted test in OCaml.
