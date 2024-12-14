import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Dedekind.LoVelib
import Dedekind.CutDefs

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

lemma nat_dedekind1 (a : dReal) (x : ℚ) (hx :x>0) : ∃ n : ℤ, n * x ∈ a.cut := by
  obtain ⟨p, hp⟩ := a.nontrivial.left
  -- want to find n such that n*x < p
  -- so n < p/x
  -- so use floor of p/x -1 for ease
  use ↑(p/x).floor-1
  have h1 : (p/x).floor-1 < p/x := by
    have h2 : (p/x).floor ≤ p/x := by
      apply Rat.le_floor.mp
      rfl
    have h3 : ↑(p/x).floor - 1 < p/x := by
      linarith
    apply h3
  have h2 : (↑(p/x).floor-1)*x < p := by
    have h3 := mul_lt_mul_of_pos_right h1 hx
    have h34 : p/x*x = p := by
      calc
        p / x * x = x* (p / x) := by ring
        _  = p := by rw [mul_div_cancel₀ _ (ne_of_gt hx)]
    have h4 : (↑(p / x).floor - 1) * x < p := by
      rw [h34] at h3
      exact h3
    exact h4
  have h3 : (↑(p/x).floor-1)*x = ↑((p / x).floor - 1) * x := by simp
  rw [←h3]
  apply a.closedDownwards p hp (((p/x).floor-1)*x) h2

lemma nat_dedekind2 (a : dReal) (x : ℚ) (hx :x>0) : ∃ n : ℤ, n * x ∉ a.cut := by
  obtain ⟨q, hq⟩ := a.nontrivial.right
  use ↑(q/x).ceil+1
  -- want to find m such that m*x > q
  -- so m > q/x
  -- so use ceil of q/x
  -- basic facts about ceil are currrently not implemented in Mathlib so I am sorrying this out. Hopefully, it should be believable
  have h1 : q/x < ↑(q/x).ceil +1 := by sorry
  have h2 : (↑(q/x).ceil+1)*x > q := by
    have h3 := mul_lt_mul_of_pos_right h1 hx
    have h34 : q/x*x = q := by
      calc
        q / x * x = x* (q / x) := by ring
        _  = q := by rw [mul_div_cancel₀ _ (ne_of_gt hx)]
    have h4 : (↑(q / x).ceil + 1) * x > q := by
      rw [h34] at h3
      exact h3
    exact h4
  have h3 : (↑(q/x).ceil+1)*x = ↑((q/x).ceil+1)*x := by simp
  rw [←h3]
  apply dedekind_lemma2 a (((q/x).ceil+1)*x) q hq h2

lemma nat_dedekind3 (a : dReal) (x : ℚ) (hx :x>0) : ∃ n : ℤ, n * x ∈ a.cut ∧ (n+1) * x ∉ a.cut := sorry

end Dedekind.lemmas
