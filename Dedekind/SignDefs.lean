import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean
import Dedekind.LoVelib
import Dedekind.CutDefs
import Dedekind.CutLemmas
import Dedekind.GroupOperationDefs
open Dedekind.lemmas
open Classical

def ispos (a : dReal) : Prop := ∃ p : ℚ, p ∈ a.cut ∧ p > 0

def isneg (a : dReal) : Prop := (∀ p ∈ a.cut, p < 0) ∧ ∃ p : ℚ, p ∉ a.cut ∧ p < 0
