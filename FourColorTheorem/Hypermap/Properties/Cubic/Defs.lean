import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def cubicSubset (H : Hypermap α) : Set (Set α) := { s | s ⊆ {x | minimalPeriod H.node x = 3}}
def precubicSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.node x ≤ 3}}
theorem cubicSubset_subset_precubicSubset : H.cubicSubset ⊆ H.precubicSubset := by{
  intro x h
  unfold cubicSubset at h
  unfold precubicSubset
  simp only [Set.mem_setOf] at h
  simp only [Set.mem_setOf]
  intro a ha
  simp only [Set.mem_setOf]
  have h':=h ha
  simp only [Set.mem_setOf] at h'
  rw[h']
}

structure Cubic (H : Hypermap α) where
  univ_cubic : Set.univ ∈ H.cubicSubset
structure Precubic (H : Hypermap α) where
  univ_precubic : Set.univ ∈ H.precubicSubset
theorem cubic_def' : H.Cubic ↔ Set.univ ∈ H.cubicSubset := by{
  constructor
  · apply Cubic.univ_cubic
  · apply Cubic.mk
}
theorem precubic_def' : H.Precubic ↔ Set.univ ∈ H.precubicSubset := by{
  constructor
  · apply Precubic.univ_precubic
  · apply Precubic.mk
}
theorem cubic_def : H.Cubic ↔ ∀x, minimalPeriod H.node x = 3 := by{
  simp[cubic_def', cubicSubset, Set.eq_univ_iff_forall]
}
theorem precubic_def : H.Precubic ↔ ∀x, minimalPeriod H.node x ≤ 3 := by{
  simp[precubic_def', precubicSubset, Set.eq_univ_iff_forall]
}
theorem Cubic.precubic (Hc : H.Cubic) : H.Precubic := by{
  rw[cubic_def'] at Hc
  rw[precubic_def']
  apply cubicSubset_subset_precubicSubset
  assumption
}

end Hypermap
