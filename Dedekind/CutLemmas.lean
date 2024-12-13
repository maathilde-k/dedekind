import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.Cut_Defs

open Classical

namespace Dedekind.lemmas

lemma dedekind_lemma1 (α : dReal) (p q : ℚ) (hp : p ∈ α.cut) (hq : q ∉ α.cut) : q > p := by
    induction α with
    | mk cut hnt hcd hou =>
      simp at hp hq
      let h1 := hcd p hp
      apply Classical.byContradiction
      intro hq'
      simp at hq'
      have h2 : (q < p) ∨ (q = p) := by
        apply lt_or_eq_of_le
        apply hq'
      have h3 : (q = p) → False := by
        intro h
        apply hq
        rw [h]
        apply hp
      have h4: (q < p) → False := by
        intro h
        apply hq
        apply h1 q
        apply h
      have h5: (q < p) ∨ (q = p) → False := by
        intro h
        apply Or.elim h
        apply h4
        apply h3
      apply h5
      apply h2

lemma dedekind_lemma2 (α : dReal) (s r : ℚ) (hr : r ∉ α.cut) (hs : r < s) : s ∉ α.cut := by
  induction α with
    | mk cut hnt hcd hou =>
      simp
      simp at hr
      apply byContradiction
      intro hs'
      simp at hs'
      have h1 : r ∈ cut := by
        apply hcd s hs'
        apply hs
      contradiction

lemma dedekind_sup (a : dReal) : ∃ r : ℚ, ∀ q : ℚ, q ∈ a.cut → q < r := by
  apply Classical.by_contradiction
  intro h
  simp at h
  have h0 := a.nontrivial.right
  obtain ⟨q, hq⟩ := h0
  have h1 : ∀ b :ℚ, b ∈ a.cut ∧ q < b → q ∈ a.cut := by
    intro b hqb
    apply a.closedDownwards b hqb.left q hqb.right
  have h2 : ∀ b :ℚ, b ∈ a.cut ∧ q = b → q ∈ a.cut := by
    simp
    intro b hb hqb
    rw [hqb]
    apply hb
  have h6 : ∀ b :ℚ, b ∈ a.cut ∧ (q = b ∨ q < b) → q ∈ a.cut := by
    intro b hb
    have hbeq : q = b ∨ q < b :=  hb.right
    apply Or.elim hbeq
    intro h'
    apply h2 b (And.intro hb.left h')
    intro h'
    apply h1 b (And.intro hb.left h')
  have h4 := h q
  obtain ⟨b, hb⟩ := h4
  have h5 : q < b ∨ q = b := by
    apply lt_or_eq_of_le
    apply hb.right
  have hb' : b ∈ a.cut ∧ (q = b ∨ q < b) := by
    apply And.intro
    apply hb.left
    apply h5.symm
  have h3 : q ∈ a.cut :=  h6 b hb'
  contradiction

end Dedekind.lemmas
