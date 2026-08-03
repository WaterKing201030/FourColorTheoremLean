import FourColorTheorem.Hypermap.Properties.Cubic.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem cubic_iff_period_three : H.cubic ↔ ∀x, H.node (H.node (H.node x)) = x ∧ H.node x ≠ x := by{
  unfold cubic cubicSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_three_iff]
}
theorem cubic.node_ne (hc : H.cubic) {x : α} : H.node x ≠ x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).right
}
theorem cubic.node_3 (hc : H.cubic) {x : α} : H.node (H.node (H.node x)) = x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).left
}
theorem cubic.node_2_ne (hc : H.cubic) {x : α} : H.node (H.node x) ≠ x := by{
  rw[cubic_iff_period_three] at hc
  intro h
  have h' := (hc x).left
  rw[h] at h'
  exact (hc x).right h'
}

end Hypermap
