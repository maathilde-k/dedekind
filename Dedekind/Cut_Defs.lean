import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
open Classical

structure dReal :=
  (cut : Set ℚ)
  (nontrivial : (∃ p : ℚ, p ∈ cut) ∧ (∃ q : ℚ, q ∉ cut))
  (closedDownwards : ∀ p ∈ cut, ∀ q : ℚ, q < p → q ∈ cut)
  (openUpwards : ∀ p ∈ cut, ∃ r ∈ cut, r > p)

instance : Membership ℚ (dReal) := ⟨fun p α => p ∈ α.cut⟩

instance : Membership ℚ (dReal) := ⟨fun p α => p ∈ α.cut⟩

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

  def dReal.negCut (a : dReal) : Set ℚ := {r : ℚ | ∃ e : ℚ, (e > 0) ∧ (- r - e ∉ a.cut)}

  def dReal.posmulCut (a b : dReal) (ha : ∃ p : ℚ, p ∈ a.cut ∧ p > 0) (hb : ∃ p : ℚ, p ∈ b.cut ∧ p > 0): Set ℚ := {r : ℚ | ∃ p q : ℚ, (p > 0) ∧ (p ∈ a.cut) ∧ (q > 0) ∧ (q ∈ b.cut) ∧ (r < p*q)}
