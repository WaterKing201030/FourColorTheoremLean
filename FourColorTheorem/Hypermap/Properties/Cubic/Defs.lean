import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def cubicSubset (H : Hypermap α) : Set (Set α) := { s | s ⊆ {x | minimalPeriod H.node x = 3}}
def cubic (H : Hypermap α) := Set.univ ∈ H.cubicSubset
def precubicSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.node x ≤ 3}}
def precubic (H : Hypermap α) := Set.univ ∈ H.precubicSubset
theorem cubic_def : H.cubic ↔ ∀x, minimalPeriod H.node x = 3 := by{
  simp[cubic, cubicSubset, Set.eq_univ_iff_forall]
}
theorem precubic_def : H.precubic ↔ ∀x, minimalPeriod H.node x ≤ 3 := by{
  simp[precubic, precubicSubset, Set.eq_univ_iff_forall]
}
theorem cubic_iff_node_node_node : H.cubic ↔ ∀x, H.node (H.node (H.node x)) = x ∧ H.node x ≠ x:=by{
  unfold cubic cubicSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_three_iff]
}
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
theorem cubic.precubic (Hc : H.cubic) : H.precubic := by{
  unfold cubic at Hc
  change Set.univ ∈ _
  unfold precubicSubset
  unfold cubicSubset at Hc
  simp only [Set.mem_setOf, Set.univ_subset_iff, Set.eq_univ_iff_forall] at *
  intro x
  simp[Hc]
}

end Hypermap
