# An attempt to formalize Dedekind cuts in Lean 4

This repository contains an ebauche of formalization for Dedekind cuts. 

We define addition, negation, and multiplication and prove important properties about these operations.

## Dedekind Cuts

We first formalize Dedekind cuts, using the definition in `Rudin's Principles of Mathematical Analysis.`
 (p. 17):

We restate it here:

A subset `α ⊂ ℚ` is called a *cut* if it satisfies the following properties:
1. *Nontrivial*: `α` is not empty and `α ≠ ℚ`
2. *Closed Downwards*: If `p ∈ α`, `q ∈ ℚ`, and `q < p`, then `q ∈ α`
3. *Open Upwards*: If `p ∈ α`, then `p < r` for some `r ∈ α`

This is formalized by the structure `dReal` in `Dedekind.CutDefs.lean`.

Those cuts as a construction of the real numbers were first proposed by Dedekind in 1872, the same year that Cantor used Cauchy sequences to construct the real numbers. While in my opinion, Dedekind cuts make for a more elegant, natural and intuitive construction of the real numbers, Cauchy sequences are a more pedagogical choice and is what is taught in most introductory analysis classes. (Cantor stole everything from Dedekind)

Rational numbers are a subset of the reals, so for each rational number `r`, we may associate a cut `Rat.todReal r = {x ∈ ℚ | x < r}`. This clearly satisfies the condition that  `Rat.todReal r` is non-trivial, since it contains `r-1` and excludes `r`, and is closed downwards and open upwards.

Adding Dedekind cuts is fairly straightforward too: we define a.add b as the set of rational numbers that are equal to the sum of a rational number in a and the sum of a rational number in b.

Negating Dedekind cuts is a less pleasant matter. 

Multiplying Dedekind cuts is even worse. In fact, we only define cuts for multiplication of positive Dedekind reals: it is simply the set of rationals that are strictly less than the the product of two positive elements of the cuts. The definition of general multiplication will come later.

## Elementary Lemmas 

File `CutLemmas.lean`.

## Dedekind cuts form a commutative group under addition

File `GroupOperationDefs.lean` for definining identity, addition and negation. File `AddCommGroup.lean` for proving properties of addcommgroup.

## Dedekind cuts form a commutative ring with multiplication

Extend the comm group structure.

File `RingOperationDefs.lean` for definining mul identity and multiplication (important and technical, first need to define positive multiplication). File `AddCommGroup.lean` for proving properties of addcommgroup.

Before general multiplication, define what it means to be positive and negative in `SignDefs.lean` and prove some lemmas in `SignLemmas.lean`.

File `CommRing.lean` for proving properties of addcommgroup. Discuss scaling difficulties involving associativity and distributivity due to the definition of multiplication and all the cases with multiplication.