import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
open Classical

namespace Dedekind

structure dReal :=
  (cut : Set ℚ)
  (nontrivial : (∃ p : ℚ, p ∈ cut) ∧ (∃ q : ℚ, q ∉ cut))
  (closedDownwards : ∀ p ∈ cut, ∀ q : ℚ, q < p → q ∈ cut)
  (openUpwards : ∀ p ∈ cut, ∃ r ∈ cut, r > p)

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

--instance : Coe ℚ dReal := ⟨Rat.todReal⟩

def dReal.zero : dReal := Rat.todReal 0

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
      apply Classical.byContradiction
      intro hs'
      simp at hs'
      have h1 : r ∈ cut := by
        apply hcd s hs'
        apply hs
      contradiction

def dReal.add (a b: dReal) : dReal :=
  {
    cut := { r : ℚ | ∃ p q : ℚ, (p ∈ a.cut ∧ q ∈ b.cut ∧ p + q = r)}
    nontrivial := by
      simp
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
      simp
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
      simp
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

def dReal.negCut (a : dReal) : Set ℚ := {r : ℚ | ∃ e : ℚ, (e > 0) ∧ (- r - e ∉ a.cut)}

-- we prove that every dedekind cut has an upper bound
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

-- we define the additive opposite of a dedekind cut
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

def ispos (a : dReal) : Prop := ∃ p : ℚ, p ∈ a.cut ∧ p > 0

def isneg (a : dReal) : Prop := (∀ p ∈ a.cut, p < 0) ∧ ∃ p : ℚ, p ∉ a.cut ∧ p < 0

/-lemma ispos_ngnotpos (a : dReal) : ispos a → ¬ ispos a.neg := by
  simp [ispos]
  intro p hp hppos
  intro x hx
  simp [dReal.neg, dReal.negCut] at hx
  obtain ⟨e, he⟩ := hx
  have h1 : -x -e > p := dedekind_lemma1 a p (-x-e) hp he.right
  have h2 : -p-e > x := by linarith
  have h3 : -p -e ≤ 0 := by linarith
  linarith-/

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

def dReal.posmulCut (a b : dReal) (ha : ∃ p : ℚ, p ∈ a.cut ∧ p > 0) (hb : ∃ p : ℚ, p ∈ b.cut ∧ p > 0): Set ℚ := {r : ℚ | ∃ p q : ℚ, (p > 0) ∧ (p ∈ a.cut) ∧ (q > 0) ∧ (q ∈ b.cut) ∧ (r < p*q)}

lemma pos_lt_mul (x y x' y' : ℚ) (hx : 0 < x) (hy : 0 < y) (hxx' : x < x') (hyy' : y < y') : x*y < x'*y' := by
  apply lt_trans (mul_lt_mul_of_pos_right hxx' hy)
  apply mul_lt_mul_of_pos_left hyy' (lt_trans hx hxx')

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

lemma pos_add (a b : dReal ) (ha : ispos a) (hb : ispos b) : ispos (a.add b) := by
  simp [ispos, dReal.add]
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
  simp [isneg, dReal.add]
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
  simp [dReal.posmul, dReal.posmulCut, dReal.add]
  simp_all [ispos]
  /-obtain ⟨pa, hpaz⟩ := ha
  obtain ⟨pb, hpbz⟩ := hb
  obtain ⟨pc, hpcz⟩ := hc
  obtain ⟨pbc, hpbcz⟩ := hbc -/
  ext x
  apply Iff.intro
  simp
  intro p hp0 hpa q hq0 r hrb s hsc hrsq hxpq
  have hqbc : q ∈ (b.add c).cut := by
    simp [dReal.add]
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
  simp [dReal.posmul, dReal.posmulCut, dReal.add, pos_left_distrib]
  sorry

lemma pos_left_distrib_cneg (a b c : dReal) (ha : ispos a) (hb : ispos b) (hc : ispos c.neg) (hbc : ispos (b.add c)):  a.posmul (b.add c) ha hbc = (a.posmul b ha hb).add (a.posmul c.neg ha hc).neg := by
  simp [dReal.posmul, dReal.posmulCut, dReal.add]
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
        apply add_zero b
      have hbcpos : ispos (b.add c) := by
        rw [hbc]
        exact hb
      simp [hbcpos, hc, hanotneg, hcnotneg]
      simp [hcz]
      simp [add_zero]
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
          simp [add_left_neg, add_comm]
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
        apply zero_add c
      simp [hbc, hb, hanotneg, hbnotneg]
      by_cases hc : ispos c
      simp [hc]
      simp [zero_add]
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
          simp [zero_add]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, hanotneg, hcneg, hcnotz, zero_add]
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
          rw [add_comm] at hbcz
          have h3 := sum_zero_inverse c b hbcz
          simp [h3]
          simp [add_left_neg, add_comm]
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
          simp [zero_add, add_comm, add_zero, hb, hbneg]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, hanotneg, hcneg, hcnotz, zero_add, add_comm, add_zero, hb, hbneg]
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
      simp [haz, zero_not_pos, zero_not_neg, add_zero]
    |inl haneg =>
      have hanotz : ¬ a = dReal.zero := by
        apply Classical.by_contradiction
        intro h
        simp at h
        apply zero_not_neg a h
        exact haneg
      simp [haneg, hanotz, zero_add, add_zero]
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
          simp_all [zero_add, add_zero, neg_pos_exclusion, pos_neg_exclusion]
        | inl hcneg =>
          have hcnotz : ¬ c = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg c h
            exact hcneg
          simp [hc, haneg, hcneg, hcnotz, zero_add, pos_neg_exclusion, neg_pos_exclusion, zero_not_neg, zero_not_pos]
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
                simp [add_comm]
                apply hbcz
              simp [add_comm] at hbcz
              have h3 := sum_zero_inverse c b hint
              simp [h3]
              simp [add_left_neg, add_comm, negneg]
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
          simp [zero_add, add_zero, negneg]
        | inl hbneg =>
          have hbnotz : ¬ b = dReal.zero := by
            apply Classical.by_contradiction
            intro h
            simp at h
            apply zero_not_neg b h
            apply hbneg
          simp [hb, haneg, hbneg, hbnotz, zero_add, add_zero, negneg]
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
                simp [add_comm]
                apply hbcz
              have h3 := sum_zero_inverse c b hint
              simp [h3]
              have h4 := isneg_neg b hbneg
              have h5 := pos_neg_exclusion b.neg h4
              simp [negneg, ispos_neg, isneg_neg, h5]
              rw [add_comm (a.neg.posmul b.neg _ _) (a.neg.posmul b.neg _ _).neg]
              apply (add_left_neg (a.neg.posmul b.neg _ _) ).symm
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
              simp [h1,h2,zero_add, add_zero, negneg, ispos_neg, isneg_neg, hbneg]
            | inl hcneg =>
              have hcnotz : ¬ c = dReal.zero := by
                apply Classical.by_contradiction
                intro h
                simp at h
                apply zero_not_neg c h
                apply hcneg
              simp [hc, haneg, hcneg, hcnotz, zero_add, add_zero, negneg, ispos_neg, isneg_neg, hbneg]
              have h0 : isneg (b.add c) := by sorry
              have h1 := neg_pos_exclusion (b.add c) h0
              simp [h0, h1]
              sorry -- new lemma?

lemma right_distrib (a b c : dReal) : (a.add b).mul c = (a.mul c).add (b.mul c) := by
  /-rw [mul_comm]
  rw [left_distrib]
  rw [mul_comm b a]
  rw [mul_comm c a]-/
  sorry



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

def dReal.one : dReal := Rat.todReal 1

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
