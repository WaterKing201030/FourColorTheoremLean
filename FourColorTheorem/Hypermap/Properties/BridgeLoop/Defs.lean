import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

structure Bridgeless (H : Hypermap α) where
  not_cface_edge : ∀x, ¬H.cface x (H.edge x)
structure Loopless (H : Hypermap α) where
  not_cnode_edge : ∀x, ¬H.cnode x (H.edge x)

theorem bridgeless_def : H.Bridgeless ↔ ∀x, ¬H.cface x (H.edge x) := by{
  constructor
  · apply Bridgeless.not_cface_edge
  · apply Bridgeless.mk
}
theorem loopless_def : H.Loopless ↔ ∀x, ¬H.cnode x (H.edge x) := by{
  constructor
  · apply Loopless.not_cnode_edge
  · apply Loopless.mk
}

end Hypermap
