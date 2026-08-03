import FourColorTheorem.Hypermap.Properties.BridgeLoop.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

section bridgeless
theorem bridgeless.node_period_ge_two (Hb : H.bridgeless)
  : ∀x, minimalPeriod H.node x ≥ 2 := by{
  intro x
  by_contra
  rw[not_le] at this
  match hmpnx : minimalPeriod node x with
  | 0 => {
    have hmpnx' := H.node_injective.minimalPeriod_pos (x:=x)
    simp[hmpnx] at hmpnx'
  }
  | 1 => {
    simp only [minimalPeriod_eq_one_iff_isFixedPt] at hmpnx
    change node x = x at hmpnx
    specialize Hb (node x)
    apply Hb
    apply cface_equivalence.symm
    apply ReflTransGen.single
    change _ = _
    rw[fen_cancel, hmpnx]
  }
  | _ + 2 => simp[hmpnx] at this; omega
}
theorem bridgeless.edge_ne (Hb : H.bridgeless)
  : ∀x, H.edge x ≠ x := by{
    intro x
    specialize Hb x
    contrapose Hb
    rw[Hb]
    apply ReflTransGen.refl
  }
theorem bridgeless.not_cface_of_cface_edge (HB : H.bridgeless) (x y : α)
  : H.cface (edge x) y → ¬H.cface x y := by{
  intro hexy hxy
  apply HB x
  exact hxy.trans (cface_equivalence.symm hexy)
}
end bridgeless

end Hypermap
