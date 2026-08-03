import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Dual

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem mirror_bridgeless : H.mirror.bridgeless = H.bridgeless := by{
  unfold bridgeless
  rw[mirror_cface, mirror_edge]
  ext
  constructor
  · {
    intro h x hx
    apply h (H.face (H.edge x))
    rw[comp_apply, nfe_cancel]
    apply H.cface_Symm.symm
    apply (H.cface_equivalence.symm (funReflTransGen.single H.face x)).trans
    apply hx.trans
    exact funReflTransGen.single H.face (H.edge x)
  }
  · {
    intro h x hx
    apply h (H.node x)
    apply H.cface_equivalence.symm
    apply (funReflTransGen.single H.face _).trans
    rw[fen_cancel]
    apply hx.trans
    apply H.cface_equivalence.symm
    rw[comp_apply]
    apply funReflTransGen.single
  }
}
theorem mirror_loopless : H.mirror.loopless = H.loopless := by{
  rw[←dual_bridgeless, ←dual_bridgeless]
  rw[mirror_dual]
  apply mirror_bridgeless
}

end Hypermap
