import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Dual

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem mirror_bridgeless_iff : H.mirror.Bridgeless = H.Bridgeless := by{
  simp only [bridgeless_def]
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
theorem mirror_loopless_iff : H.mirror.Loopless = H.Loopless := by{
  rw[←dual_bridgeless_iff, ←dual_bridgeless_iff]
  rw[mirror_dual]
  apply mirror_bridgeless_iff
}
theorem Bridgeless.mirror (Hb : H.Bridgeless) : H.mirror.Bridgeless := by{
  rwa[mirror_bridgeless_iff]
}
theorem Loopless.mirror (Hb : H.Loopless) : H.mirror.Loopless := by{
  rwa[mirror_loopless_iff]
}

end Hypermap
