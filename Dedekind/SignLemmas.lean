import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.CutDefs
import Dedekind.CutLemmas
import Dedekind.GroupOperationDefs
import Dedekind.SignDefs
open Dedekind.lemmas
open Classical

namespace sign.lemmas

lemma ispos_neg (a : dReal) : ispos a → isneg a.neg := by
  intro h
  simp_all [ispos, dReal.neg, dReal.negCut, isneg]
  apply And.intro
  intro x y hy hxy
  obtain ⟨p, hp⟩ := h
  -- since -x-y is not in acut, -x-y > 0, so -y > x and y is positive
  have h1 := dedekind_lemma1 a p (-x-y) hp.left hxy
  have h2 : -x-y > 0 := by linarith
  have h3 : -y > x := by linarith
  linarith
  obtain ⟨p, hp⟩ := h
  use -p
  apply And.intro
  intro x hx
  simp
  have h1 : p - x < p := by linarith
  apply a.closedDownwards p hp.left (p-x) h1
  linarith

lemma isneg_neg (a : dReal) : isneg a → ispos a.neg := by
  intro h
  simp_all [ispos, dReal.neg, dReal.negCut, isneg]
  obtain ⟨p, hp⟩ := h.right
  use -p/2
  apply And.intro
  use -p/2
  apply And.intro
  linarith
  have h1 : -(-p / 2) - -p / 2 = p := by ring
  rw [h1]
  apply hp.left
  linarith

lemma pos_neg_exclusion (a : dReal) : ispos a → ¬ isneg a := by
  intro h
  simp_all [ispos, isneg]
  intro h'
  intro x hx
  apply Classical.byContradiction
  intro h''
  simp at h''
  obtain ⟨p, hp⟩ := h
  have hxp : x < p := by linarith
  have hxa := a.closedDownwards p hp.left x hxp
  contradiction

lemma neg_pos_exclusion (a : dReal) : isneg a → ¬ ispos a := by
  intro h
  simp_all [ispos, isneg]
  intro x hx
  have h':= h.left x hx
  linarith

lemma ispos_negneg (a : dReal) : ispos a → ispos a.neg.neg := by
  intro h
  apply isneg_neg
  apply ispos_neg
  exact h

lemma isneg_negneg (a : dReal) : isneg a → isneg a.neg.neg := by
  intro h
  apply ispos_neg
  apply isneg_neg
  exact h

lemma zero_not_pos (a : dReal) (ha : a = dReal.zero) : ¬ ispos a := by
  intro h
  simp_all [ispos, dReal.zero, dReal.cut, Rat.todReal]
  subst ha
  obtain ⟨left, right⟩ := h
  linarith

lemma zero_not_neg (a : dReal) (ha : a = dReal.zero) : ¬ isneg a := by
  intro h
  simp_all [isneg, dReal.zero, dReal.cut, Rat.todReal]
  subst ha
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h3, h4⟩ := h2
  linarith

lemma zero_not_pos_not_neg (a : dReal) (h : ¬ ispos a ∧ ¬ isneg a): a = dReal.zero := by
  simp [ispos, isneg] at h
  simp [dReal.zero, Rat.todReal]
  obtain ⟨hleft, hright⟩ := h
  have h : a.cut = {r : ℚ | r < 0} := by
    ext x
    apply Iff.intro
    intro hx
    have h1 : ¬ 0 ∈ a.cut := by
      intro h0
      obtain ⟨p,hp⟩ := a.openUpwards 0 h0
      have h3 := hleft p hp.left
      linarith
    have h2 : ∀ p ∈ a.cut, p < 0 := by
      intro p hp
      have h3 := hleft p hp
      have h4 : p ≠ 0 := by
        intro h
        rw [h] at hp
        contradiction
      simp_all only [lt_iff_le_and_ne, not_and, not_lt]
      simp_all
    have h1 : ¬ x = 0 := by
      intro h'
      have h3 := h2 x hx
      linarith
    simp_all only [lt_iff_le_and_ne, not_and, not_lt]
    simp_all
    intro h
    simp at h
    have h1 : ¬ 0 ∈ a.cut := by
      intro h0
      have h2 := a.openUpwards 0 h0
      obtain ⟨p,hp⟩ := h2
      have h3 := hleft p hp.left
      linarith
    have h2 : ∀ p ∈ a.cut, p < 0 := by
      intro p hp
      have h3 : p ≤ 0 := by
        apply hleft p hp
      have h4 : p ≠ 0 := by
        intro h
        rw [h] at hp
        contradiction
      simp_all only [lt_iff_le_and_ne, not_and, not_lt]
      simp_all
    have h3 := hright h2
    apply Classical.by_contradiction
    intro h'
    have h4 := h3 x h'
    linarith
  cases a with
    | mk cut hnt hcd hou =>
      simp_all [dReal.zero, Rat.todReal, dReal, dReal.cut]

lemma zero_iff_not_pos_not_neg (a : dReal) : a = dReal.zero ↔ ¬ ispos a ∧ ¬ isneg a := by
  apply Iff.intro
  intro h
  apply And.intro
  apply zero_not_pos a h
  apply zero_not_neg a h
  intro h
  apply zero_not_pos_not_neg a h

lemma pos_or_neg_or_zero (a : dReal) : ispos a ∨ isneg a ∨ a = dReal.zero := by
  apply Classical.byCases
  intro h
  apply Or.inl
  apply h
  intro h
  apply Classical.byCases
  intro h1
  apply Or.inr
  apply Or.inl
  apply h1
  intro h1
  apply Or.inr
  apply Or.inr
  have h2 : ¬ ispos a ∧ ¬ isneg a := by
    apply And.intro
    apply h
    apply h1
  apply (zero_iff_not_pos_not_neg a).mpr h2

lemma pos_lt_mul (x y x' y' : ℚ) (hx : 0 < x) (hy : 0 < y) (hxx' : x < x') (hyy' : y < y') : x*y < x'*y' := by
  apply lt_trans (mul_lt_mul_of_pos_right hxx' hy)
  apply mul_lt_mul_of_pos_left hyy' (lt_trans hx hxx')

lemma pos_add (a b : dReal ) (ha : ispos a) (hb : ispos b) : ispos (a.add b) := by
  simp [ispos, dReal.add, dReal.addCut]
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  use p
  apply And.intro
  apply hp.left
  use q
  apply And.intro
  apply hq.left
  linarith

lemma neg_add (a b : dReal ) (ha : isneg a) (hb : isneg b) : isneg (a.add b) := by
  simp [isneg, dReal.add, dReal.addCut]
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  apply And.intro
  intro x y hy
  apply Classical.by_contradiction
  intro h
  simp at h
  obtain ⟨r, hr⟩ := h
  have hr' : r = x - y := by linarith
  have h1 : x - y ∈ b.cut := by
    rw [hr'] at hr
    exact hr.left
  have hxyneg := q (x-y) h1
  have hy_neg := p y hy
  linarith
  obtain ⟨p', hp⟩ := hp
  use p'
  apply And.intro
  intro x y z hz
  apply Classical.by_contradiction
  intro h
  simp at h
  have hfalseq : x = p' - z := by linarith
  have hxltp' := dedekind_lemma1 a x p' y hp.left
  have hmz : -z > 0 := by
    subst hfalseq
    simp_all only [sub_add_cancel, gt_iff_lt, Left.neg_pos_iff]
  have problem : x < p' - z := by linarith
  linarith
  apply hp.right

  end sign.lemmas
