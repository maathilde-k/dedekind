import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.Cut_Defs
import Dedekind.GroupOperationDefs
import Dedekind.CutLemmas
import Dedekind.AddCommGroup
import Dedekind.SignDefs
import Dedekind.SignLemmas
import Dedekind.RingOperationDefs
open Dedekind.lemmas
open sign.lemmas
open Classical
open comm.group
open dReal

namespace Dedekind

lemma posmul_zero (a : dReal) (ha : ispos a) : a.mul dReal.zero = dReal.zero := by
  simp [dReal.mul, zero_not_pos, zero_not_neg]

lemma zero_mul (a : dReal) : dReal.zero.mul a = dReal.zero := by
  simp [dReal.mul]
  by_cases h : ispos a
  simp [h, zero_not_pos, zero_not_neg]
  simp [h, zero_not_pos, zero_not_neg]

lemma mul_zero (a : dReal) : a.mul dReal.zero = dReal.zero := by
  simp [dReal.mul]
  by_cases h : ispos a
  simp [h, zero_not_pos, zero_not_neg]
  simp [h, zero_not_pos, zero_not_neg]

lemma posmul_pos (a b : dReal) (ha : ispos a) (hb : ispos b) : ispos (a.posmul b ha hb) := by
  simp [ispos, dReal.posmul, dReal.posmulCut]
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  use p*q/2
  apply And.intro
  use p
  apply And.intro
  apply hp.right
  apply And.intro
  apply hp.left
  use q
  apply And.intro
  apply hq.right
  apply And.intro
  apply hq.left
  simp_all only [gt_iff_lt, half_lt_self_iff, mul_pos_iff_of_pos_left]
  simp
  simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]

lemma posmul_comm (a b : dReal) (ha : ispos a) (hb : ispos b) : a.posmul b ha hb = b.posmul a hb ha := by
  simp [dReal.posmul, dReal.posmulCut]
  ext x
  apply Iff.intro
  simp
  intro p hp0 hpa q hq0 hqb hxpq
  use q
  apply And.intro
  apply hq0
  apply And.intro
  apply hqb
  use p
  apply And.intro
  apply hp0
  apply And.intro
  apply hpa
  linarith
  simp
  intro q hq0 hqb p hp0 hpq hxqp
  use p
  apply And.intro
  apply hp0
  apply And.intro
  apply hpq
  use q
  apply And.intro
  apply hq0
  apply And.intro
  apply hqb
  linarith

lemma mul_comm (a b : dReal) : a.mul b = b.mul a := by
  simp [dReal.mul]
  by_cases ha : ispos a
  have hanotneg := pos_neg_exclusion a ha
  have hanotz : ¬ a = dReal.zero := by
    apply Classical.by_contradiction
    intro h
    simp at h
    apply zero_not_pos a h
    exact ha
  simp [ha, hanotneg, hanotz]
  by_cases hb : ispos b
  have hbnotneg := pos_neg_exclusion b hb
  have hbnotz : ¬ b = dReal.zero := by
    apply Classical.by_contradiction
    intro h
    simp at h
    apply zero_not_pos b h
    exact hb
  have habpos := posmul_pos a b ha hb
  have habnotneg := pos_neg_exclusion (a.posmul b _ _) habpos
  simp [hb, hbnotneg, hbnotz, habpos, habnotneg]
  apply posmul_comm a b ha hb
  have hbnegz : isneg b ∨ b = dReal.zero := by
    have h1 := pos_or_neg_or_zero b
    simp [hb] at h1
    apply h1
  cases hbnegz with
    | inr hbz =>
      simp [hb, hbz, zero_not_pos, zero_not_neg]
    | inl hbneg =>
      simp [hb, hbneg, zero_not_pos, zero_not_neg]
      apply neg_preserves_equality
      apply posmul_comm
  have hanegz : isneg a ∨ a = dReal.zero := by
    have h1 := pos_or_neg_or_zero a
    simp [ha] at h1
    apply h1
  cases hanegz with
    | inr haz =>
      simp [ha, haz, zero_not_pos, zero_not_neg]
    | inl haneg =>
      have hanotpos := neg_pos_exclusion a haneg
      have hanotz : ¬ a = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_neg a h
        exact haneg
      have hanegpos : ispos a.neg := isneg_neg a haneg
      simp [haneg, zero_not_pos, zero_not_neg, hanotpos, hanotz]
      by_cases hb : ispos b
      have hbnotneg := pos_neg_exclusion b hb
      have hbnotz : ¬ b = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_pos b h
        exact hb
      have habpos := posmul_pos a.neg b hanegpos hb
      simp [hb, hbnotneg, hbnotz, habpos]
      apply neg_preserves_equality
      apply posmul_comm
      have hbnegz : isneg b ∨ b = dReal.zero := by
        have h1 := pos_or_neg_or_zero b
        simp [hb] at h1
        apply h1
      cases hbnegz with
        | inr hbz =>
          simp [hb, hbz, zero_not_pos, zero_not_neg]
        | inl hbneg =>
          have hbnegpos := isneg_neg b hbneg
          have hbnotpos := neg_pos_exclusion b hbneg
          have hbnotz : ¬ b = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg b h
            exact hbneg
          simp [hb, hbneg, zero_not_pos, zero_not_neg, hbnotpos, hbnotz]
          apply posmul_comm

lemma pos_left_distrib (a b c : dReal) (ha : ispos a) (hb : ispos b) (hc : ispos c) (hbc : ispos (b.add c)):  a.posmul (b.add c) ha hbc = (a.posmul b ha hb).add (a.posmul c ha hc) := by
  simp [dReal.posmul, dReal.posmulCut, dReal.add, dReal.addCut]
  simp_all [ispos]
  ext x
  apply Iff.intro
  simp
  intro p hp0 hpa q hq0 r hrb s hsc hrsq hxpq
  have hqbc : q ∈ (b.add c).cut := by
    simp [dReal.add, dReal.addCut]
    use r
    apply And.intro
    apply hrb
    use s
  -- work out by hand first
  rw [hrsq.symm] at hxpq
  use x - p*s -- not quite, need a small adjustment to get precise equality
  apply And.intro
  use p
  apply And.intro
  apply hp0
  apply And.intro
  apply hpa
  use r
  apply And.intro
  -- somehow want to reduce to the fact that we can choose r and s such that they are both positive
  sorry
  apply And.intro
  apply hrb
  linarith
  use x - p*r
  apply And.intro
  use p
  apply And.intro
  apply hp0
  apply And.intro
  apply hpa
  use s
  sorry --see comment above

  sorry
  simp
  intro u y hy0 hya z hz0 hzb hxyz p q hq0 hqa r hr0 hrc hpqr hupx
  sorry

lemma pos_left_distrib_bneg (a b c : dReal) (ha : ispos a) (hb : ispos b.neg) (hc : ispos c) (hbc : ispos (b.add c)):  a.posmul (b.add c) ha hbc = (a.posmul b.neg ha hb).neg.add (a.posmul c ha hc) := by
  simp [dReal.posmul, dReal.posmulCut, dReal.add, dReal.addCut, pos_left_distrib]
  sorry

lemma pos_left_distrib_cneg (a b c : dReal) (ha : ispos a) (hb : ispos b) (hc : ispos c.neg) (hbc : ispos (b.add c)):  a.posmul (b.add c) ha hbc = (a.posmul b ha hb).add (a.posmul c.neg ha hc).neg := by
  simp [dReal.posmul, dReal.posmulCut, dReal.add, dReal.addCut, pos_left_distrib]
  sorry

lemma left_distrib (a b c : dReal) : a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  simp [dReal.mul]
  by_cases ha : ispos a
  simp [ha]
  have hanotneg := pos_neg_exclusion a ha
  by_cases hb : ispos b
  simp [hb]
  by_cases hc : ispos c
  simp [hc]
  have hbc := pos_add b c hb hc
  simp [hbc]
  apply pos_left_distrib a b c ha hb hc
  have hcnegz : isneg c ∨ c = dReal.zero := by
    have h1 := pos_or_neg_or_zero c
    simp [hc] at h1
    apply h1
  cases hcnegz with
    | inr hcz =>
      have hcnotneg : ¬ isneg c := by
        apply zero_not_neg c
        apply hcz
      have hbc : b.add c = b := by
        rw [hcz]
        apply comm.group.add_zero b
      have hbcpos : ispos (b.add c) := by
        rw [hbc]
        exact hb
      simp [hbcpos, hc, hanotneg, hcnotneg]
      simp [hcz]
      simp [comm.group.add_zero]
    | inl hcneg =>
      have hcnotz : ¬ c = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_neg c h
        exact hcneg
      simp [hc, hanotneg, hcneg, hcnotz]
      by_cases hbc : ispos (b.add c)
      simp [hbc]
      have hcneg_pos := isneg_neg c hcneg
      apply pos_left_distrib_cneg a b c ha hb hcneg_pos hbc
      have hbcnegz : isneg (b.add c) ∨ b.add c = dReal.zero := by
        have h1 := pos_or_neg_or_zero (b.add c)
        simp [hbc] at h1
        apply h1
      cases hbcnegz with
        | inr hbcz =>
          have hbcnotneg : ¬ isneg (b.add c) := by
            apply zero_not_neg (b.add c)
            apply hbcz
          simp [hbc, hbcz, hbcnotneg, hbcnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          have h3 := sum_zero_inverse b c hbcz
          simp [h3]
          simp [comm.group.add_left_neg, comm.group.add_comm]
        | inl hbcneg =>
          have hbcnotz : ¬ b.add c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg (b.add c) h
            exact hbcneg
          simp [hbc, hbcneg, hbcnotz]
          -- rip need more cases
          sorry -- need new lemma?
  have hbnegz : isneg b ∨ b = dReal.zero := by
    have h1 := pos_or_neg_or_zero b
    simp [hb] at h1
    apply h1
  cases hbnegz with
    | inr hbz =>
      have hbnotneg : ¬ isneg b := by
        apply zero_not_neg b
        apply hbz
      have hbc : b.add c = c := by
        rw [hbz]
        apply comm.group.zero_add c
      simp [hbc, hb, hanotneg, hbnotneg]
      by_cases hc : ispos c
      simp [hc]
      simp [comm.group.zero_add]
      have hcnegz : isneg c ∨ c = dReal.zero := by
        have h1 := pos_or_neg_or_zero c
        simp [hc] at h1
        apply h1
      cases hcnegz with
        | inr hcz =>
          have hcnotneg : ¬ isneg c := by
            apply zero_not_neg c
            apply hcz
          simp [hc, hcz, hcnotneg, hcnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          simp [comm.group.zero_add]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, hanotneg, hcneg, hcnotz, comm.group.zero_add]
    | inl hbneg =>
      have hbnotz : ¬ b = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_neg b h
        exact hbneg
      simp [hb, hanotneg, hbneg, hbnotz]
      by_cases hc : ispos c
      simp [hc]
      by_cases hbc : ispos (b.add c)
      simp [hbc]
      have hbneg_pos := isneg_neg b hbneg
      apply pos_left_distrib_bneg a b c ha hbneg_pos hc hbc
      simp [hbc]
      have hbcnegz : isneg (b.add c) ∨ b.add c = dReal.zero := by
        have h1 := pos_or_neg_or_zero (b.add c)
        simp [hbc] at h1
        apply h1
      cases hbcnegz with
        | inr hbcz =>
          have hbcnotneg : ¬ isneg (b.add c) := by
            apply zero_not_neg (b.add c)
            apply hbcz
          simp [hbc, hbcz, hbcnotneg, hbcnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          rw [comm.group.add_comm] at hbcz
          have h3 := sum_zero_inverse c b hbcz
          simp [h3]
          simp [comm.group.add_left_neg, comm.group.add_comm]
        | inl hbcneg =>
          have hbcnotz : ¬ b.add c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg (b.add c) h
            exact hbcneg
          simp [hbc, hbcneg, hbcnotz]
          sorry -- need new lemma?
      have hcnegz : isneg c ∨ c = dReal.zero := by
        have h1 := pos_or_neg_or_zero c
        simp [hc] at h1
        apply h1
      cases hcnegz with
        | inr hcz =>
          have hcnotneg : ¬ isneg c := by
            apply zero_not_neg c
            apply hcz
          simp [hc, hcz, hcnotneg, hcnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          simp [comm.group.zero_add, comm.group.add_comm, comm.group.add_zero, hb, hbneg]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, hanotneg, hcneg, hcnotz, comm.group.zero_add, comm.group.add_comm, comm.group.add_zero, hb, hbneg]
          have h0 := neg_add b c hbneg hcneg
          have h1 := neg_pos_exclusion (b.add c) h0
          simp [h0, h1]
          have hbneg_pos := isneg_neg b hbneg
          have hcneg_pos := isneg_neg c hcneg
          have neg_distrib := neg_distributes_over_addition b c
          have hbaddcneg : ispos (b.add c).neg := by
            simp [neg_distrib]
            apply pos_add b.neg c.neg hbneg_pos hcneg_pos
          have hbaddcneg2 : ispos ( b.neg.add c.neg) := by rw [←neg_distrib]; exact hbaddcneg
          have heqneg := pos_left_distrib a b.neg c.neg ha hbneg_pos hcneg_pos hbaddcneg2
          have heqneg2 : a.posmul (b.add c).neg ha hbaddcneg =  (a.posmul b.neg ha hbneg_pos).add (a.posmul c.neg ha hcneg_pos) := by
            simp [neg_distrib]
            apply heqneg
          --simp [←neg_distrib]
          --apply neg_preserves_equality (a.posmul (b.add c).neg _ _) ((a.posmul b.neg _ _).add (a.posmul c.neg _ _))
          --simp [neg_preserves_equality] at heqneg2
          -- neg needs taking out
          sorry -- taking a brek from this, probably need to use neg_preserves_equality, but first take out the neg of addition
  simp [ha]
  have hanegz : isneg a ∨ a = dReal.zero := by
    have h1 := pos_or_neg_or_zero a
    simp [ha] at h1
    apply h1
  cases hanegz with
    |inr haz =>
      simp [haz, zero_not_pos, zero_not_neg, comm.group.add_zero]
    |inl haneg =>
      have hanotz : ¬ a = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_neg a h
        exact haneg
      simp [haneg, hanotz, comm.group.zero_add, comm.group.add_zero]
      by_cases hb : ispos b
      simp [hb]
      by_cases hc : ispos c
      simp [hc]
      have hbc := pos_add b c hb hc
      have hbcnotneg := pos_neg_exclusion (b.add c) hbc
      simp_all [hbc, neg_pos_exclusion, pos_neg_exclusion]
      -- take out the neg and use some previous lemma
      sorry -- new lemma?
      have hcnegz : isneg c ∨ c = dReal.zero := by
        have h1 := pos_or_neg_or_zero c
        simp [hc] at h1
        apply h1
      cases hcnegz with
        | inr hcz =>
          have hcnotneg : ¬ isneg c := by
            apply zero_not_neg c
            apply hcz
          simp [hc, hcz, hcnotneg, hcnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          simp_all [comm.group.zero_add, comm.group.add_zero, neg_pos_exclusion, pos_neg_exclusion]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, haneg, hcneg, hcnotz, comm.group.zero_add, pos_neg_exclusion, neg_pos_exclusion, zero_not_neg, zero_not_pos]
          have h0 := pos_neg_exclusion b hb
          simp [h0]
          by_cases hbc : ispos (b.add c)
          simp [hbc, pos_neg_exclusion]
          sorry -- need new lemma?
          have hbcnegz : isneg (b.add c) ∨ b.add c = dReal.zero := by
            have h1 := pos_or_neg_or_zero (b.add c)
            simp [hbc] at h1
            apply h1
          cases hbcnegz with
            | inr hbcz =>
              have hbcnotneg : ¬ isneg (b.add c) := by
                apply zero_not_neg (b.add c)
                apply hbcz
              simp [hbc, hbcz, hbcnotneg, hbcnotneg]
              have h1 := zero_not_neg dReal.zero rfl
              have h2 := zero_not_pos dReal.zero rfl
              simp [h1,h2]
              have hint : c.add b = dReal.zero := by
                simp [comm.group.add_comm]
                apply hbcz
              simp [comm.group.add_comm] at hbcz
              have h3 := sum_zero_inverse c b hint
              simp [h3]
              simp [comm.group.add_left_neg, comm.group.add_comm, negneg]
            | inl hbcneg =>
              have hbcnotz : ¬ b.add c = dReal.zero := by
                apply Classical.by_contradiction
                intro h
                simp at h
                apply zero_not_neg (b.add c) h
                apply hbcneg
              simp [hbc, hbcneg, hbcnotz]
              sorry -- need new lemma?
      have hbnegz : isneg b ∨ b = dReal.zero := by
        have h1 := pos_or_neg_or_zero b
        simp [hb] at h1
        apply h1
      cases hbnegz with
        | inr hbz =>
          have hbnotneg : ¬ isneg b := by
            apply zero_not_neg b
            apply hbz
          simp [hb, hbz, hbnotneg, hbnotneg]
          have h1 := zero_not_neg dReal.zero rfl
          have h2 := zero_not_pos dReal.zero rfl
          simp [h1,h2]
          simp [comm.group.zero_add, comm.group.add_zero, negneg]
        | inl hbneg =>
          have hbnotz : ¬ b = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg b h
            apply hbneg
          simp [hb, haneg, hbneg, hbnotz, comm.group.zero_add, comm.group.add_zero, negneg]
          by_cases hc : ispos c
          simp [hc]
          by_cases hbc : ispos (b.add c)
          simp [hbc]
          sorry -- need additional lemma?
          simp [hbc]
          have hbcnegz : isneg (b.add c) ∨ b.add c = dReal.zero := by
            have h1 := pos_or_neg_or_zero (b.add c)
            simp [hbc] at h1
            apply h1
          cases hbcnegz with
            | inr hbcz =>
              have hbcnotneg : ¬ isneg (b.add c) := by
                apply zero_not_neg (b.add c)
                apply hbcz
              simp [hbc, hbcz, hbcnotneg, hbcnotneg]
              have h1 := zero_not_neg dReal.zero rfl
              have h2 := zero_not_pos dReal.zero rfl
              simp [h1,h2]
              have hint : c.add b = dReal.zero := by
                simp [comm.group.add_comm]
                apply hbcz
              have h3 := sum_zero_inverse c b hint
              simp [h3]
              have h4 := isneg_neg b hbneg
              have h5 := pos_neg_exclusion b.neg h4
              simp [negneg, ispos_neg, isneg_neg, h5]
              rw [comm.group.add_comm (a.neg.posmul b.neg _ _) (a.neg.posmul b.neg _ _).neg]
              apply (comm.group.add_left_neg (a.neg.posmul b.neg _ _) ).symm
            | inl hbcneg =>
              have hbcnotz : ¬ b.add c = dReal.zero := by
                apply Classical.by_contradiction
                intro h
                simp at h
                apply zero_not_neg (b.add c) h
                apply hbcneg
              have h0 := pos_neg_exclusion c hc
              simp [hbc, hbcneg, hbcnotz, neg_pos_exclusion, pos_neg_exclusion, h0, zero_not_neg, zero_not_pos]
              sorry -- need new lemma?
          have hcnegz : isneg c ∨ c = dReal.zero := by
            have h1 := pos_or_neg_or_zero c
            simp [hc] at h1
            apply h1
          cases hcnegz with
            | inr hcz =>
              have hcnotneg : ¬ isneg c := by
                apply zero_not_neg c
                apply hcz
              simp [hc, hcz, hcnotneg, hcnotneg]
              have h1 := zero_not_neg dReal.zero rfl
              have h2 := zero_not_pos dReal.zero rfl
              simp [h1,h2,comm.group.zero_add, comm.group.add_zero, negneg, ispos_neg, isneg_neg, hbneg]
            | inl hcneg =>
              have hcnotz : ¬ c = dReal.zero := by
                apply Classical.by_contradiction
                intro h
                simp at h
                apply zero_not_neg c h
                apply hcneg
              simp [hc, haneg, hcneg, hcnotz, comm.group.zero_add, comm.group.add_zero, negneg, ispos_neg, isneg_neg, hbneg]
              have h0 : isneg (b.add c) := by sorry
              have h1 := neg_pos_exclusion (b.add c) h0
              simp [h0, h1]
              sorry -- new lemma?

lemma right_distrib (a b c : dReal) : (a.add b).mul c = (a.mul c).add (b.mul c) := by
  rw [mul_comm, mul_comm a c, mul_comm b c, left_distrib]

lemma ineq_trans (x y z t: ℚ) (hy : y > 0) (hz : z > 0) (ht : t > 0) (hxy : x < z*y) (hyz : z < t) : x < y*t := by
  calc
    x < z * y := hxy
    _ < t * y := by exact mul_lt_mul_of_pos_right hyz hy
    _ = y * t := by rw [Rat.mul_comm t y]

lemma posmul_assoc (a b c : dReal) (ha : ispos a) (hb : ispos b) (hc : ispos c) : (a.posmul b ha hb).posmul c (posmul_pos a b ha hb) hc = a.posmul (b.posmul c hb hc) ha (posmul_pos b c hb hc) := by
  simp [dReal.posmul, dReal.posmulCut]
  ext x
  apply Iff.intro
  simp
  intro y hy0 p hp0 hpa q hq0 hqb hypq r hr0 hrc hxyr
  use p
  apply And.intro
  apply hp0
  apply And.intro
  apply hpa
  have := c.openUpwards r
  obtain ⟨r', hr'⟩ := this hrc
  use q*r
  apply And.intro
  simp_all only [mul_pos_iff_of_pos_left, half_pos]
  apply And.intro
  use q
  apply And.intro
  apply hq0
  apply And.intro
  apply hqb
  use r'
  apply And.intro
  linarith
  apply And.intro
  apply hr'.left
  have hcalc := mul_lt_mul_of_pos_left hr'.right hq0
  apply hcalc
  have hpq0 : p*q > 0 := by simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]
  have hcalc2 : x < p*(q*r) := by
    have h0 : p*(q*r) = r * (p * q) := by ring_nf
    rw [h0]
    apply ineq_trans x r y (p*q) hr0 hy0 hpq0 hxyr hypq
  apply hcalc2
  simp
  intro p hp0 hpa y hy0 q hq0 hqb r hr0 hrc hyqr hxpy
  use p*q
  apply And.intro
  simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]
  apply And.intro
  obtain ⟨p', hp'⟩ := a.openUpwards p hpa
  use p'
  apply And.intro
  linarith
  apply And.intro
  apply hp'.left
  obtain ⟨q', hq'⟩ := b.openUpwards q hqb
  use q'
  apply And.intro
  linarith
  apply And.intro
  apply hq'.left
  have hcalc := pos_lt_mul p q p' q' hp0 hq0 hp'.right hq'.right
  apply hcalc
  use r
  apply And.intro
  apply hr0
  apply And.intro
  apply hrc
  have hxyp : x < y*p := by
    have h0 : y*p = p*y := by ring_nf
    rw [h0]
    apply hxpy
  have hcalc2 := ineq_trans x p y (q*r) hp0 hy0 (by simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]) hxyp hyqr
  have hcalc3 : p*(q*r) = (p*q)*r := by ring_nf
  rw [hcalc3.symm]
  apply hcalc2

lemma mul_assoc (a b c : dReal) : (a.mul b).mul c = a.mul (b.mul c) := by
  simp [dReal.mul]
  by_cases ha : ispos a
  have hanotneg := pos_neg_exclusion a ha
  have hanotz : ¬ a = dReal.zero := by
    apply Classical.by_contradiction
    intro h
    simp at h
    apply zero_not_pos a h
    exact ha
  simp [ha, hanotneg, hanotz]
  by_cases hb : ispos b
  have hbnotneg := pos_neg_exclusion b hb
  have hbnotz : ¬ b = dReal.zero := by
    apply Classical.by_contradiction
    intro h
    simp at h
    apply zero_not_pos b h
    exact hb
  have habpos := posmul_pos a b ha hb
  have habnotneg := pos_neg_exclusion (a.posmul b _ _) habpos
  simp [hb, hbnotneg, hbnotz, habpos, habnotneg]
  by_cases hc : ispos c
  have hcnotneg := pos_neg_exclusion c hc
  have hcnotz : ¬ c = dReal.zero := by
    apply Classical.by_contradiction
    intro h
    simp at h
    apply zero_not_pos c h
    exact hc
  have hbcpos := posmul_pos b c hb hc
  have hbcnotneg := pos_neg_exclusion (b.posmul c _ _) hbcpos
  simp [hc, hcnotneg, hcnotz, hbcpos, hbcnotneg]
  apply posmul_assoc a b c ha hb hc
  have hcnegz : isneg c ∨ c = dReal.zero := by
    have h1 := pos_or_neg_or_zero c
    simp [hc] at h1
    apply h1
  cases hcnegz with
    | inr hcz =>
      simp [hc, hcz, zero_not_pos, zero_not_neg]
    | inl hcneg =>
      simp [hc, hcneg, zero_not_pos, zero_not_neg]
      have hcnegpos := isneg_neg c hcneg
      have hbcpos := posmul_pos b c.neg hb hcnegpos
      have hbcneg := ispos_neg (b.posmul c.neg hb hcnegpos) hbcpos
      have hbcnotpos : ¬ ispos (b.posmul c.neg hb hcnegpos).neg := by
        apply neg_pos_exclusion
        apply hbcneg
      simp [hbcneg, hbcnotpos, negneg]
      apply neg_preserves_equality
      apply posmul_assoc a b c.neg ha hb hcnegpos
  have hbnegz : isneg b ∨ b = dReal.zero := by
    have h1 := pos_or_neg_or_zero b
    simp [hb] at h1
    apply h1
  cases hbnegz with
    | inr hbz =>
      simp [hb, hbz, zero_not_pos, zero_not_neg]
    | inl hbneg =>
      simp [hb, hbneg, zero_not_pos, zero_not_neg]
      have hbnegpos := isneg_neg b hbneg
      have habpos := posmul_pos a b.neg ha hbnegpos
      have habneg := ispos_neg (a.posmul b.neg ha hbnegpos) habpos
      have habnotpos : ¬ ispos (a.posmul b.neg ha hbnegpos).neg := by
        apply neg_pos_exclusion
        apply habneg
      simp [habneg, habnotpos, negneg, habpos, hbneg]
      by_cases hc : ispos c
      have hcnotneg := pos_neg_exclusion c hc
      have hcnotz : ¬ c = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_pos c h
        exact hc
      simp [hc, hcnotneg, hcnotz]
      sorry
      sorry
  sorry

lemma ispos_one : ispos dReal.one := by
  simp [ispos, dReal.one, Rat.todReal]
  use 0.5
  apply And.intro
  rfl
  rfl

lemma pq_lt_one (p q : ℚ) (hp : p > 0) (hq : q > p) : p/q < 1 := by
  have hq0 : q > 0 := by linarith
  apply (@div_lt_one _ _  p q hq0).mpr hq

lemma pq_gt_one (p q : ℚ) (hp : p > 0) (hq : q > p) : q/p > 1 := by
  apply (@one_lt_div _ _  q p hp).mpr hq

lemma div_pos_pos (p q : ℚ) (hp : p > 0) (hq : q > 0) : p/q > 0 := by
  exact div_pos hp hq

lemma div_pos_preserve (p q r : ℚ) (hpq : p < q) (hr : r > 0) : p/r < q/r := by
  rw [div_eq_mul_inv p r, div_eq_mul_inv q r]
  apply mul_lt_mul_of_pos_right
  exact hpq
  exact inv_pos.mpr hr

lemma simplify_identity (p q r : ℚ) (hpq : p < q) (hr : r > 0): p < r*(q/r) := by
  rw [mul_div_cancel₀ q (ne_of_gt hr)]
  exact hpq

lemma one_posmul (a : dReal) (ha : ispos a) : dReal.one.posmul a ispos_one ha = a := by
  cases a with
    | mk cut hnt hcd hou =>
      simp [dReal.posmul, dReal.posmulCut , dReal.one, Rat.todReal, dReal.cut]
      ext x
      apply Iff.intro
      simp
      intro p hp0 hp1 q hq0 hq hqpx
      have h0 : p*q < q := by simp_all only [mul_lt_iff_lt_one_left]
      have h1 : x < q := by linarith
      apply hcd q hq x h1
      intro hx
      simp
      simp [ispos] at ha
      obtain ⟨y, hy⟩ := ha
      by_cases h : x ≤ 0
      use 1/2
      apply And.intro
      rfl
      apply And.intro
      rfl
      use y
      apply And.intro
      apply hy.right
      apply And.intro
      apply hy.left
      have h2 := half_pos hy.right
      have h3 : x < y/2 := by linarith
      ring_nf at h3
      linarith
      simp at h
      have h1 := hou x hx
      obtain ⟨r, hr⟩ := h1
      use x/r
      apply And.intro
      have h2 : r > 0 := by linarith
      simp_all only [gt_iff_lt, div_pos_iff_of_pos_left]
      apply And.intro
      have hr0 : r > 0 := by linarith
      apply pq_lt_one x r h hr.right
      have h3 := hou r hr.left
      obtain ⟨r', hr'⟩ := h3
      use r'
      apply And.intro
      linarith
      apply And.intro
      apply hr'.left
      have hr0 : r > 0 := by linarith
      have hr'0 : r' > 0 := by linarith
      have h4 : r'/r > 1 := pq_gt_one r r' hr0 hr'.right
      have h5 :  x / r * r' = x * (r' / r) := by ring_nf
      rw [h5]
      simp_all only [gt_iff_lt, lt_mul_iff_one_lt_right]

lemma posmul_one (a : dReal) (ha : ispos a) : a.posmul dReal.one ha ispos_one = a := by
  cases a with
    | mk cut hnt hcd hou =>
      simp [dReal.posmul, dReal.posmulCut , dReal.one, Rat.todReal, dReal.cut]
      ext x
      apply Iff.intro
      simp
      intro p hp0 hp q hq0 hq hqpx
      have h0 : p*q < p := by simp_all only [mul_lt_iff_lt_one_right]
      have h1 : x < p := by linarith
      apply hcd p hp x h1
      intro hx
      simp
      simp [ispos] at ha
      obtain ⟨y, hy⟩ := ha
      by_cases h : x ≤ 0
      use y
      apply And.intro
      apply hy.right
      apply And.intro
      apply hy.left
      use 1/2
      apply And.intro
      rfl
      apply And.intro
      rfl
      have h2 := half_pos hy.right
      have h3 : x < y/2 := by linarith
      linarith
      obtain ⟨r, hr⟩ := hou x hx
      obtain ⟨r', hr'⟩ := hou r hr.left
      use r'
      apply And.intro
      linarith
      apply And.intro
      apply hr'.left
      use r / r'
      apply And.intro
      have hr0 : r > 0 := by linarith
      have h3 : r' > 0 := by linarith
      apply div_pos hr0 h3
      apply And.intro
      have hr0 : r > 0 := by linarith
      apply pq_lt_one r r' hr0 hr'.right
      have hr'0 : r' > 0 := by linarith
      apply simplify_identity x r r' hr.right hr'0

lemma one_mul (a : dReal) : dReal.one.mul a = a := by
  have h2 := pos_neg_exclusion dReal.one ispos_one
  by_cases h : ispos a
  simp [dReal.mul, h, ispos_one]
  apply one_posmul a h
  have h3 : isneg a ∨ a = dReal.zero:= by
    have h4 := pos_or_neg_or_zero a
    simp [h] at h4
    apply h4
  cases h3 with
    | inr h4 =>
      have h5 : ¬ ispos dReal.zero := by
        apply zero_not_pos
        rfl
      have h6 : ¬ isneg dReal.zero := by
        apply zero_not_neg
        rfl
      simp [dReal.mul, h, ispos_one, h2, h4, h5, h6]
    | inl h4 =>
      simp [dReal.mul, h, ispos_one, h2, h4]
      have h5 : dReal.one.posmul a.neg ispos_one (isneg_neg a h4)= a.neg := one_posmul a.neg (isneg_neg a h4)
      rw [h5]
      apply negneg

lemma mul_one (a : dReal) : a.mul dReal.one = a := by
  have h2 := pos_neg_exclusion dReal.one ispos_one
  by_cases h : ispos a
  simp [dReal.mul, h, ispos_one]
  apply posmul_one a h
  have h3 : isneg a ∨ a = dReal.zero := by
    have h4 := pos_or_neg_or_zero a
    simp [h] at h4
    apply h4
  cases h3 with
    | inr h4 =>
      have h5 : ¬ ispos dReal.zero := by
        apply zero_not_pos
        rfl
      have h6 : ¬ isneg dReal.zero := by
        apply zero_not_neg
        rfl
      simp [dReal.mul, h, ispos_one, h2, h4, h5, h6]
    | inl h4 =>
      simp [dReal.mul, h, ispos_one, h2, h4, negneg]
      have h4 := posmul_one a.neg (isneg_neg a h4)
      rw [h4]
      apply negneg

noncomputable instance dReal_ring : Ring dReal :=
  {
  dReal_addcommgroup with
  mul := dReal.mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one := dReal.one
  one_mul := one_mul
  mul_one := mul_one
  }

noncomputable instance : CommRing dReal :=
  {
  dReal_ring with
  mul_comm := mul_comm
  }

end Dedekind
