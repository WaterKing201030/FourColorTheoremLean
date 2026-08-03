import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem dual_bridgeless : H.dual.bridgeless = H.loopless := by{
  unfold bridgeless loopless
  rw[dual_cface, dual_edge]
  ext
  constructor
  · {
    intro h x hn
    apply H.cnode_Symm.symm at hn
    apply h (H.edge x)
    rw[edgeinv_eq, comp_apply, nfe_cancel]
    exact hn
  }
  · {
    intro h x hn
    apply H.cnode_Symm.symm at hn
    apply h (H.edgeinv x)
    rw[edgeinv_eq, comp_apply, enf_cancel]
    rw[edgeinv_eq] at hn
    exact hn
  }
}
theorem dual_loopless : H.dual.loopless = H.bridgeless := by{
  rw[←dual_bridgeless, dual_dual]
}

end Hypermap
