# An attempt to formalize Dedekind cuts in Lean 4

This repository contains an ebauche of formalization for Dedekind cuts. 

We define addition, negation, and multiplication and prove important properties about these operations.

## Project Structure

- **`README.md`**: Documentation for the project.
- **`Dedekind/`**: Contains the Lean source files.
  - `CutDefs.lean`: Definition of Dedekind cuts and basic properties.
  - `CutLemmas.lean`: Foundational lemmas for Dedekind cuts.
  - `GroupOperationDefs.lean`: Definitions of addition, negation, and their identities.
  - `AddCommGroup.lean`: Proofs of group properties under addition.
  - `SignDefs.lean` and `SignLemmas.lean`: Definitions and lemmas for positivity and negativity of cuts.
  - `RingOperationDefs.lean`: Definitions for multiplication and related properties.
  - `CommRing.lean`: Proofs that Dedekind cuts form a commutative ring.
  - `LoVelib.lean`: Utility functions and additional definitions.


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

Negating Dedekind cuts is a less pleasant matter. Let `a` be a Dedekind cut. Notice that the set of rationals that are the additive inverse of some rational number in `a` is *almost* the complement of what we want to be the additive inverse of `a`. Almost, because it is not open upwards. Thus to solve this minor issue, we define `a.neg` as the set of rationals `r` such that the exists a rational `e > 0` such that `-r -e ∉ a`.

Multiplying Dedekind cuts is even worse. In fact, we only define cuts for multiplication of positive Dedekind reals: it is simply the set of rationals that are strictly less than the the product of two positive elements of the cuts. The definition of general multiplication will come later.

## Elementary Lemmas 

From here, we can prove elementary structural lemmas about Dedekind cuts. Those are located in the file `CutLemmas.lean`. 

`dedekind_lemma1` expresses that if `p` and `q` are rational numbers and `p ∈ a` and `q ∉ a` then `q > p`. This encodes the fact that Dedekind cuts are continuous sets of rational numbers.

Similarly, `dedekind_lemma2` expresses that if `p ∉ a` and `q > p`, then `q ∉ a`. 

Finally, `dedekind_sup` encodes that every dedekind cut has an upper bound: given a Dedekind cut `a` there is a rational `p` that is greater than all the elements in `a`.

Additionally, the following three lemmas about Dedekind cuts of scaled integers provide structural insights:
- `nat_dedekind1`: For a Dedekind cut `a` and a positive rational number `x > 0`, there exists an integer `n` such that `n * x ∈ a.cut`. This establishes the existence of scaled integers within a Dedekind cut.
- `nat_dedekind2`: For a Dedekind cut a and a positive rational number `x > 0`, there exists an integer `n` such that `n * x ∉ a.cut`. This ensures that scaled integers can also fall outside a Dedekind cut. (the lemma is proven up to a small fact about ceilings that is not implemented in Mathlib)
- `nat_dedekind3`: For a Dedekind cut a and a positive rational number `x > 0`, there exists an integer `n` such that `n * x ∈ a.cut` but `(n + 1) * x ∉ a.cut`. This lemma demonstrates a precise boundary behavior of Dedekind cuts with respect to scaled integers. (this lemma is not proven)
 
## Dedekind cuts form a commutative group under addition

A set `G` with an operation `⬝` is called a commutative group if it satisfies the following properties:
1. *Associativity*: For all `x ∈ G`, `y ∈ G`, `z ∈ G`, we have `x⬝(y⬝z) = (x⬝y)⬝z`
2. *Identity Element*: There exists `e ∈ G`, such that for all `x ∈ G` we have `x⬝e = e⬝x = x`
3. *Inverse element*: For all `x ∈ G`, there exists `y ∈ G` such that `x⬝y = y⬝x = e`
4. *Commutativity*: For all `x ∈ G`, `y ∈ G`, we have `x⬝y = y⬝x`

Dedekind cuts form a commutative group under addition. 

In `GroupOperationDefs.lean`, the additive identity, addition and negation are defined using the above cut definitions. 

In `AddCommGroup.lean`, we prove that Dedekind form a commutative group by defining the additive identity to be `RatToReal 0` and proving the following theorems : `add_comm`, `add_assoc`, `zero_add`, `add_zero` and `add_left_neg`.

Further, we prove useful lemmas about the group operations that will be relevant to the ring structure on the Dedekind cuts.

## Dedekind cuts form a commutative ring with multiplication

A commutative ring `R` is a commutative group with a second operation `×` which satisfies the following axioms:
1. *Multiplicative Identity Element*: There exists `i ∈ R`, such that for all `x ∈ R` we have `x×i = i×x = x` (there is sometimes the additional constraint that `i≠e`, in which case `R` is a unital ring)
2. *Left Distributivity*: For all `x ∈ R`, `y ∈ R`, `z ∈ R`, we have `x×(y⬝z) = x×y ⬝ x×z`
3. *Right Distributivity*: For all `x ∈ R`, `y ∈ R`, `z ∈ R`, we have `(y⬝z)×x = y×x ⬝ z×x`
4. *Associativity*: For all `x ∈ R`, `y ∈ R`, `z ∈ R`, we have `x×(y×z) = (z×y)×z`
5. *Commutativity*: For all `x ∈ R`, `y ∈ R`, we have `x×y = y×x`

Dedekind cuts also form a commutative ring with multiplication, extending the comm group structure.

Before definining multiplication, we have to define what is meant by positive and negative. In our definition, we chose to make `dReal.zero` neither positive nor negative. 
- A positive Dedekind cut is one that contains a strictly positive rational number. 
- A negative Dedekind cut is one that only contains negative rational numbers, but not all of them. 
`ispos` and `isneg` are propositions embodying the sign of a Dedekind cut. From there, `SignLemmas.lean` contains many useful lemmas on the sign of Dedekind Cuts: mutual exclusion, how they behave under addition and negation, ...

In the file `RingOperationDefs.lean`, we definine the multiplicative identity (`dReal.one = RatToReal 1`) and multiplication. Multiplication is surprisingly difficult to define. First we define multiplication for positive cuts, `posmul`. Then we define multiplication by cases on the sign of the Dedekind cut. Let `a` and `b` be Dedekind cuts. `a.mul b` is equal to:
    - `a.posmul b` if `a` and `b` are positive
    - `(a.posmul b.neg).neg` if `a` is positive and `b` is negative
    - `(a.neg.posmul b).neg` if `a` is negative and `b` is positive
    - `a.neg.posmul b.neg` if `a` and `b` are negative
    - `dReal.zero` if either of them is zero.
This case by case definition makes proving certain theorems quite difficult, specifically those involving three separate Dedekind cuts.

In `CommRing.lean` we begin to prove that Dedekind cuts form a commutative ring. We successfully prove `zero_mul` and `mul_zero`, `mul_one`, `one_mul`, and `mul_com`, each time by proving these properties for the positive cuts before generalizing.

The issues arise when we try to prove properties involving three Dedekind cuts. The definition of multiplication by cases means that proving something on three cuts means processing at least 27 cases (more in the case of distributivity). This also means that multiple lemma variants about positive multiplication must also be proven (at least three per property). For instance, in the case where `a`.`b`.`c` are three positive dedekind cuts, left distributivity reduces to `a.posmul (b.add c) = (a.posmul b).add (a.posmul c)`. However, if `b` is negative and `b.add c` is positive, left distributivity reduces to `a.posmul (b.add c) = (a.posmul b.neg).neg.add (a.posmul c)`, which cannot be reduced to the previous case. 