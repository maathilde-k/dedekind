import Dedekind.LoVelib
open Classical

/-
Define the structure for a Dedekind cut, based on Rudin:
  A subset `α ⊂ ℚ` is called a *cut* if it satisfies the following properties:
1. *Nontrivial*: `α` is not empty and `α ≠ ℚ`
2. *Closed Downwards*: If `p ∈ α`, `q ∈ ℚ`, and `q < p`, then `q ∈ α`
3. *Open Upwards*: If `p ∈ α`, then `p < r` for some `r ∈ α`

  The name `cut` derives from the fact that the set `α` "cuts" the rationals into two parts: the rationals in `α` and the rationals greater than those in `α`.
-/

structure dReal :=
  (cut : Set ℚ)
  (nontrivial : (∃ p : ℚ, p ∈ cut) ∧ (∃ q : ℚ, q ∉ cut))
  (closedDownwards : ∀ p ∈ cut, ∀ q : ℚ, q < p → q ∈ cut)
  (openUpwards : ∀ p ∈ cut, ∃ r ∈ cut, r > p)

instance : Membership ℚ (dReal) := ⟨fun p α => p ∈ α.cut⟩

-- Define how to convert a rational number to a Dedekind cut
def Rat.todReal : ℚ → dReal :=
  fun p => {
    cut := { r : ℚ | r < p }
    nontrivial := by
      apply And.intro
      simp
      use p - 1
      linarith
      simp
      use p
    closedDownwards := by
      intro s hs q hq
      simp at hs
      simp
      linarith
    openUpwards := by
      intro s hs
      use (p + s) / 2
      simp at hs
      simp
      apply And.intro
      linarith
      linarith
  }

instance : Coe ℚ (dReal) := ⟨Rat.todReal⟩

-- Define addition of two Dedekind cuts
def dReal.addCut (a : dReal) (b : dReal) : Set ℚ := { r : ℚ | ∃ p q : ℚ, (p ∈ a.cut ∧ q ∈ b.cut ∧ p + q = r)}

-- Define negation of a Dedekind cut
def dReal.negCut (a : dReal) : Set ℚ := {r : ℚ | ∃ e : ℚ, (e > 0) ∧ (- r - e ∉ a.cut)}

-- Define multiplication of two positive Dedekind cuts
def dReal.posmulCut (a b : dReal) (ha : ∃ p : ℚ, p ∈ a.cut ∧ p > 0) (hb : ∃ p : ℚ, p ∈ b.cut ∧ p > 0): Set ℚ := {r : ℚ | ∃ p q : ℚ, (p > 0) ∧ (p ∈ a.cut) ∧ (q > 0) ∧ (q ∈ b.cut) ∧ (r < p*q)}
