import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.Cut_Defs
import Dedekind.GroupOperationDefs
import Dedekind.CutLemmas
open Dedekind.lemmas
open Classical

open dReal

namespace comm.group

theorem add_comm (a b : dReal) : a.add b = b.add a := by
  simp [dReal.add]
  ext x
  apply Iff.intro
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := ha.right
  use b
  apply And.intro
  apply hb.left
  use a
  apply And.intro
  apply ha.left
  have h1 : a + b = b + a := by ring
  rw [h1] at hb
  exact hb.right
  intro h
  obtain ⟨b, hb⟩ := h
  obtain ⟨a, ha⟩ := hb.right
  use a
  apply And.intro
  apply ha.left
  use b
  apply And.intro
  apply hb.left
  have h1 : a + b = b + a := by ring
  rw [←h1] at ha
  exact ha.right

theorem add_assoc (a b c : dReal) : (a.add b).add c = a.add (b.add c) := by
  simp [dReal.add]
  ext x
  apply Iff.intro
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := ha.right
  obtain ⟨c, hc⟩ := hb.right
  use a
  apply And.intro
  apply ha.left
  use b
  apply And.intro
  apply hb.left
  use c
  apply And.intro
  apply hc.left
  ring_nf
  apply hc.right
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := ha.right
  obtain ⟨c, hc⟩ := hb.right
  use a
  apply And.intro
  apply ha.left
  use b
  apply And.intro
  apply hb.left
  use c
  apply And.intro
  apply hc.left
  rw [←hc.right]
  ring

theorem zero_add (a : dReal) : dReal.zero.add a = a := by
  cases a with
    | mk cut hnt hcd hou =>
      simp [dReal.zero, Rat.todReal, dReal, dReal.cut, dReal.add]
      ext x
      apply Iff.intro
      intro hx
      simp at hx
      obtain ⟨r, hr⟩ := hx
      obtain ⟨h1, h2⟩ := hr
      obtain ⟨q, hq⟩ := h2
      have h3 : x < q := by linarith
      apply hcd q hq.left x h3
      intro hx
      have h1 := hou x hx
      obtain ⟨r, hr⟩ := h1
      use x - r
      apply And.intro
      linarith
      use r
      apply And.intro
      apply hr.left
      ring

theorem add_zero (a : dReal) : a.add dReal.zero = a := by
  rw [add_comm]
  apply zero_add

instance Negation : Neg dReal := ⟨dReal.neg⟩

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

theorem add_left_neg (a : dReal) : (a.neg).add a = dReal.zero := by
  simp [dReal.neg, dReal.add, dReal.zero, dReal.negCut, Rat.todReal]
  ext x
  apply Iff.intro
  simp
  intro r e he hrea y hy hryx
  have h0 : y = x - r := by linarith
  have h1 : x - r ∈ a.cut := by
    rw [h0] at hy
    exact hy
  have h2 := dedekind_lemma1 a (x-r) (-r-e) h1 hrea
  linarith
  simp
  intro hx
  obtain ⟨s, hs⟩ := dedekind_sup a
  obtain ⟨p, hp⟩ :=  a.nontrivial.left
  have hx2 : -x/2 > 0 := by linarith
  obtain ⟨n, hn⟩ := nat_dedekind1 a (-x/2) hx2
  obtain ⟨m, hm⟩ := nat_dedekind2 a (-x/2) hx2
  use (m+1)*x/2
  apply And.intro
  use -x/2
  apply And.intro
  linarith
  have h3 : -((m+1)*x/2) - - x/2 = m*(-x/2) := by ring_nf
  rw [h3]
  apply hm
  use n*(-x/2)
  apply And.intro
  apply hn
  ring_nf

  sorry

lemma zero_neg_is_zero : dReal.zero = dReal.zero.neg := by
  simp [dReal.zero, dReal.neg, dReal.negCut, Rat.todReal]
  ext x
  apply Iff.intro
  intro h
  simp_all
  use -x/2
  simp
  apply And.intro
  linarith
  linarith
  simp
  intro e he hxe
  linarith

lemma negneg (a : dReal) : a.neg.neg = a := by
  cases a with
    | mk cut hnt hcd hou =>
      simp [dReal.neg, dReal.negCut]
      ext x
      apply Iff.intro
      simp
      intro p hp h
      have := h p hp
      simp at this
      apply this
      intro hx
      simp
      obtain ⟨r, hr⟩ := hou x hx
      use r - x
      apply And.intro
      linarith
      simp
      intro y hy
      have h2 : r > r-y := by linarith
      apply hcd r hr.left (r-y) h2

lemma neg_preserves_equality (a b : dReal) : a = b → a.neg = b.neg := by
  intro h
  subst h
  simp_all only

-- do i need to prove this?
lemma neg_distributes_over_addition (a b : dReal) : (a.add b).neg = a.neg.add b.neg := by
  simp [dReal.neg, dReal.negCut, dReal.add]
  ext x
  apply Iff.intro
  simp
  intro p hp h
  sorry
  simp
  intro y z hz0 hyz p q hq0 hpq hypx
  sorry

lemma sum_zero_inverse (a b : dReal) : a.add b = dReal.zero → a = b.neg := by
  intro h
  have hbneg : (a.add b).add b.neg = dReal.zero.add b.neg := by rw [h]
  simp [zero_add, add_assoc, add_comm] at hbneg
  have h1 := add_left_neg b
  have h2 := add_comm b.neg b
  rw [h2] at h1
  rw [h1] at hbneg
  simp [add_zero] at hbneg
  apply hbneg

instance dReal_addcommgroup: AddCommGroup dReal where
  add := dReal.add
  add_assoc := add_assoc
  zero := dReal.zero
  zero_add := zero_add
  add_zero := add_zero
  nsmul := @nsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩
  neg := dReal.neg
  zsmul :=
    @zsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩ ⟨dReal.neg⟩
      (@nsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩)
  add_left_neg := add_left_neg
  add_comm := add_comm

  end comm.group
