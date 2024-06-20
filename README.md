__Overview__

The Theta Calculus is a conservative extension of the untyped Lambda Calculus, adding two new constructs: _annotation_ and _theta-abstraction_. It is not typed, but has "first class typing," in the sense that the new constructs and their reduction rules can capture the operational semantics of type checking for standard constructs familiar from variants of pure type systems.

__Syntax and reductions__

The Theta Calculus distinguishes terms, types and kinds on a syntactic level (note how variable capitalisation disambiguates all constructs):

* terms t, u ::= x | λx.t | λX.t | (t u) | (t T) | [t : T] 

*  types T, U ::= X | Λx.T | ΛX.T | (T U) | (T t) | θx.t | [T : κ]

* kinds κ ::= θX.T

The small-step reduction rules are:

1. (λx.t u) -> t{x := u}
2. λx.(t x) -> t
3. (θx.t u) -> θx.(t u)
4. (θx.t U) -> θx.(t U)
5. [t : θy.u] -> u{y := t}
6. [T : θY.U] -> U{Y := T}
7. [λx.t : Λx.U] -> λx.[t : U]
8. [λX.t : ΛX.U] -> λX.[t : U]
9. [t : Λx.U] -> λx.[(t x) : U]
10. [t : ΛX.U] -> λX.[(t X) : U]
11. [[t : T] : U] when T ~ U -> t
12. [[T : κ] κ'] when κ ~ κ' -> T

7 takes precedence over 9 and 8 over 10. (One can regard 9 and 10 as subsumed by 7 and 8, if one first eta-expands.)

__Examples and discussion__

An ordinary typing statement "t : T" is given the operational meaning "t and [t : T] are equivalent". As a first, trivial but still interesting example, let

Any = θx.x .

Then for all terms t, [t : Any] -> t, which we can formulate as saying that all terms have type Any. The analogous expression on the kind level, θX.X, can be considered the kind of all types (often denoted "✲").

Let's assume we have two types A and B, and define

FunAB = θf.λx.[(f [x : A]) : B] .

This, we claim, models the usual function type, traditionally written A -> B. To begin to see how, try using it to type λy.y. We get

[λy.y : FunAB] -> λx.[(λy.y [x : A]) : B] -> λx.[[x : A] : B] .

If A is equivalent to B, everything checks out and we're left with λx.x (which is equivalent to the term we started with); otherwise the reduction has deduced a type mismatch.

Dependent types can be modelled similarly by

Πx:A.B = θf.λx.[(f [x : A]) : (B x)] .

Theta-abstraction also let's us do Scott encodings in a way that bears great resemblance to the self-types studied by Peng Fu and Aaron Stump and implemented in the programming lanugages Formality and Yatima. For example, here is an encoding of a type of booleans:

Bool = θb.λP.λt.λf.[(((b P) [t : (P true)]) [f : (P false)]) : (P b)]

true = λP.λt.λf.t

false = λP.λt.λf.t

One can go further and define (G)ADTs and even more exotic types! And, we claim, the reduction rules of Theta Calculus will faithfully model the intended type-checking semantics.

__The interpreter__

The interpreter adds top-level definitions (that can be referenced in other top-level definitions) and syntax sugar for local let-bindings. Reduction is call-by-value.

__TODOs__

Prove Church-Rosser for the calculus. Prove formally the claims about faithfully modelling the type semantics of λΠ-calculus. Add the possibility to have recursive definitions (giving access to inductive encodings for types like lists). Investigate how techniques for sharing, which are crucial for fast lambda reduction, can be extended to optimized reduction engines of the Theta Calculus. Ponder if the calculus would be suitable as a core language for an optionally typed Lisp, or as an intermediate language of a theorem prover.