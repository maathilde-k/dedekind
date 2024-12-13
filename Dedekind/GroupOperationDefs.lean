import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.Cut_Defs
import Dedekind.CutLemmas
open Dedekind.lemmas
open Classical

def dReal.zero : dReal := Rat.todReal 0

def dReal.add (a b: dReal) : dReal :=
  {
    cut := dReal.addCut a b
    nontrivial := by
      simp [dReal.addCut]
      obtain ⟨pa1, hpa1⟩ := a.nontrivial.left
      obtain ⟨qa1, hqa1⟩ := a.nontrivial.right
      obtain ⟨pb1, hpb1⟩ := b.nontrivial.left
      obtain ⟨qb1, hqb1⟩ :=  b.nontrivial.right
      apply And.intro
      use pa1 + pb1
      use pa1
      apply And.intro
      apply hpa1
      use pb1
      use qa1 + qb1
      intro x hx y hy
      apply Classical.byContradiction
      intro h
      simp at h
      have h1 := dedekind_lemma1 a x qa1 hx hqa1
      have h2 := dedekind_lemma1 b y qb1 hy hqb1
      linarith
    closedDownwards := by
      simp [dReal.addCut]
      intro r p hp q hq eq
      intro r2 hr2
      have h1 : r2 - r < 0 := by linarith
      have h2 : p + r2 - r < p := by linarith
      have h3 := a.closedDownwards p hp (p + r2 - r) h2
      use p + r2 - r
      apply And.intro
      apply h3
      use q
      apply And.intro
      apply hq
      linarith
    openUpwards := by
      simp [dReal.addCut]
      intro r p hp q hq eq
      obtain ⟨r1, hr1⟩ := a.openUpwards p hp
      obtain ⟨r2, hr2⟩ := b.openUpwards q hq
      use r1
      apply And.intro
      apply hr1.left
      use r2
      apply And.intro
      apply hr2.left
      rw [←eq]
      linarith
  }

instance : Add dReal := ⟨dReal.add⟩

def dReal.neg (a : dReal) : dReal := {
  cut := dReal.negCut a
  nontrivial := by
    simp [dReal.negCut]
    apply And.intro
    obtain ⟨r, hr⟩ := dedekind_sup a
    have h2 : r ∉ a.cut := by
      apply Classical.byContradiction
      intro h
      simp at h
      have h3 : r ≥ r := by linarith
      have h4 : r < r := hr r h
      linarith
    use - (r + 1)
    use 1
    apply And.intro
    linarith
    have h3 : - - (r + 1) - 1 = r := by ring
    rw [h3]
    apply h2
    obtain ⟨p, hp⟩ := a.nontrivial.left
    use -p
    simp
    intro x hx
    have h3 : p-x < p := by linarith
    apply a.closedDownwards p hp (p-x) h3
  closedDownwards := by
    simp [dReal.negCut]
    intros r r' hr' hrr' q hq
    use r + r' - q
    apply And.intro
    linarith
    have h1 : - q -(r + r' - q) = -r - r'  := by ring
    rw [h1]
    apply hrr'
  openUpwards := by
    simp [dReal.negCut]
    intros r r' hr hrr'
    use r + r'/2
    apply And.intro
    use r'/2
    apply And.intro
    linarith
    have h1 : -(r + r' / 2) - r' / 2 = -r - r' := by ring
    rw [h1]
    apply hrr'
    linarith
}

instance : Neg dReal := ⟨dReal.neg⟩
