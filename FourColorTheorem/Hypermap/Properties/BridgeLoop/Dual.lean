import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem dual_bridgeless_iff : H.dual.Bridgeless = H.Loopless := by{
  simp only [bridgeless_def, loopless_def]
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
theorem dual_loopless_iff : H.dual.Loopless = H.Bridgeless := by{
  rw[←dual_bridgeless_iff, dual_dual]
}

theorem Bridgeless.dual_loopless (Hb : H.Bridgeless) : H.dual.Loopless := by{
  rwa[dual_loopless_iff]
}
theorem Loopless.dual_bridgeless (Hb : H.Loopless) : H.dual.Bridgeless := by{
  rwa[dual_bridgeless_iff]
}

end Hypermap
