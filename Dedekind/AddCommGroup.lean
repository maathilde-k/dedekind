import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Dedekind.LoVelib
import Dedekind.CutDefs
import Dedekind.GroupOperationDefs
import Dedekind.CutLemmas
open Dedekind.lemmas
open Classical

open dReal

namespace comm.group

--===================== Commutativity =====================

theorem add_comm (a b : dReal) : a.add b = b.add a := by
  simp [dReal.add, dReal.addCut]
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

--===================== Associativity =====================

theorem add_assoc (a b c : dReal) : (a.add b).add c = a.add (b.add c) := by
  simp [dReal.add, dReal.addCut]
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

--===================== Identity Addition =====================

theorem zero_add (a : dReal) : dReal.zero.add a = a := by
  cases a with
    | mk cut hnt hcd hou =>
      simp [dReal.zero, Rat.todReal, dReal, dReal.cut, dReal.add, dReal.addCut]
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

--===================== Inverse Addition =====================

theorem add_left_neg (a : dReal) : (a.neg).add a = dReal.zero := by
  simp [dReal.neg, dReal.add, dReal.addCut, dReal.zero, dReal.negCut, Rat.todReal]
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
  obtain ⟨p, hp⟩ :=  a.nontrivial.left
  have hx2 : -x/2 > 0 := by linarith
  obtain ⟨n, hn⟩ := nat_dedekind3 a (-x/2) hx2
  obtain ⟨hn, hm⟩ := hn
  use (n+2)*x/2
  apply And.intro
  use -x/2
  apply And.intro
  linarith
  have h3 : -((n+2)*x/2) - - x/2 = (n+1)*(-x/2) := by ring_nf
  rw [h3]
  apply hm
  use n*(-x/2)
  apply And.intro
  apply hn
  ring_nf

--===================== AddCommGroup Instance =====================

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

--===================== Some Additional Useful Lemmas about Addition =====================

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

lemma neg_distributes_over_addition (a b : dReal) : (a.add b).neg = a.neg.add b.neg := by
  simp [dReal.neg, dReal.negCut, dReal.add, dReal.addCut]
  ext x
  apply Iff.intro
  simp
  intro p hp h
  sorry
  simp
  intro y z hz0 hyz p q hq0 hpq hypx
  sorry

  end comm.group
