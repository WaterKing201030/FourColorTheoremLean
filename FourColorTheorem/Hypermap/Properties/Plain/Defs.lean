import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def plainSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.edge x = 2}}

structure Plain (H : Hypermap α) where
  univ_plain : Set.univ ∈ H.plainSubset
theorem plain_def' : H.Plain ↔ Set.univ ∈ H.plainSubset := by{
  constructor
  · apply Plain.univ_plain
  · apply Plain.mk
}
theorem plain_def : H.Plain ↔ ∀x, minimalPeriod H.edge x = 2 := by{
  rw[plain_def']
  unfold plainSubset
  simp[Set.eq_univ_iff_forall]
}
theorem plain_iff_edge_edge : H.Plain ↔ ∀x, H.edge (H.edge x) = x ∧ H.edge x ≠ x:=by{
  rw[plain_def']
  unfold plainSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_two_iff]
}

end Hypermap
