import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.Cut_Defs
import Dedekind.CutLemmas
import Dedekind.GroupOperationDefs
import Dedekind.SignDefs
import Dedekind.SignLemmas
open Dedekind.lemmas
open sign.lemmas
open Classical

def dReal.one : dReal := Rat.todReal 1

def dReal.posmul (a b: dReal) (ha : ispos a) (hb : ispos b): dReal :=
  {
    cut := dReal.posmulCut a b ha hb
    nontrivial := by
      apply And.intro
      simp [dReal.posmulCut]
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      have hp2 := half_pos hp.right
      have hp2p : p > p/2 := by linarith
      have hp2a := a.closedDownwards p hp.left (p/2) hp2p
      have hq2 := half_pos hq.right
      have hq2q : q > q/2 := by linarith
      have hq2b := b.closedDownwards q hq.left (q/2) hq2q
      use p*q/6
      use p/2
      apply And.intro
      apply hp2
      apply And.intro
      apply hp2a
      use q/2
      apply And.intro
      apply hq2
      apply And.intro
      apply hq2b
      have hcalc : p / 2 * (q / 2) = p * q / 4 := by ring
      rw [hcalc]
      have hcalc2 : p * q / 4 > p * q / 6 := by
        have h0 : p*q > 0 := by aesop
        linarith
      apply hcalc2
      simp [dReal.posmulCut]
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      obtain ⟨as, has⟩ := dedekind_sup a
      obtain ⟨bs, hbs⟩ := dedekind_sup b
      use as*bs
      intro x hx hax y hy hby
      have hxas := has x hax
      have hybs := hbs y hby
      have hxyltasbs := pos_lt_mul x y as bs hx hy hxas hybs
      linarith
    closedDownwards := by
      simp [dReal.posmulCut]
      intro p x hx hax y hy hby hpxy q hqp
      use x
      apply And.intro
      apply hx
      apply And.intro
      apply hax
      use y
      apply And.intro
      apply hy
      apply And.intro
      apply hby
      linarith
    openUpwards := by
      simp [dReal.posmulCut]
      intro p x hx hax y hy hby hpxy
      use x*y
      obtain ⟨x', hax'⟩ := a.openUpwards x hax
      have hx' : 0 < x' := by linarith
      obtain ⟨y', hby'⟩ := b.openUpwards y hby
      have hy' : 0 < y' := by linarith
      apply And.intro
      use x'
      apply And.intro
      apply hx'
      apply And.intro
      apply hax'.left
      use y'
      apply And.intro
      apply hy'
      apply And.intro
      apply hby'.left
      apply pos_lt_mul x y x' y' hx hy hax'.right hby'.right
      linarith
  }

noncomputable def dReal.mul (a b: dReal) : dReal :=
  if h : ispos a ∧ ispos b then dReal.posmul a b h.left h.right
  else if h : isneg a ∧ isneg b then dReal.posmul a.neg b.neg (isneg_neg a h.left) (isneg_neg b h.right)
  else if h : ispos a ∧ isneg b then (dReal.posmul a b.neg h.left (isneg_neg b h.right)).neg
  else if h : isneg a ∧ ispos b then (dReal.posmul a.neg b (isneg_neg a h.left) h.right).neg
  else dReal.zero
