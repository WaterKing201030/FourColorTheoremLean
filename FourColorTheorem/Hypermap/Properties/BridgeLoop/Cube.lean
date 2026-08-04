import FourColorTheorem.Hypermap.Actions.Cube
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

open CubeTag

theorem cube_bridgeless : H.cube.bridgeless ↔ H.bridgeless := by{
  constructor
  · {
    intro ih x hfxe
    apply ih (CTen, x)
    simp only [cube_edge, CubeDart.edge]
    rwa[cube_cface_iff_cface (by trivial) (by trivial)]
  }
  · {
    intro ih ⟨t, x⟩ hftxe
    match t with
    | CTe => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      have ih := H.cube_cte_of_cface_cte hftxe
      contradiction
    }
    | CTfe => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      have ih := H.cube_ctfe_of_cface_ctfe hftxe
      contradiction
    }
    | CTn => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      apply H.cube.cface_equivalence.symm at hftxe
      have ih := H.cube_ctfe_of_cface_ctfe hftxe
      contradiction
    }
    | CTen => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      rw[H.cube_cface_ctnf_pred_eq (by trivial), H.cube_cface_ctnf_pred_eq' (by trivial)] at hftxe
      rw[cube_cface_iff_cface (by trivial) (by trivial)] at hftxe
      exact ih _ hftxe
    }
    | CTf => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      apply H.cube.cface_equivalence.symm at hftxe
      have ih := H.cube_cte_of_cface_cte hftxe
      contradiction
    }
    | CTnf => {
      simp only [cube_edge, CubeDart.edge] at hftxe
      rw[H.cube_cface_ctnf_pred_eq (by trivial), H.cube_cface_ctnf_pred_eq' (by trivial)] at hftxe
      rw[cube_cface_iff_cface (by trivial) (by trivial)] at hftxe
      apply H.cface_equivalence.symm at hftxe
      specialize ih (node (face x))
      rw[enf_cancel] at ih
      exact ih hftxe
    }
  }
}

end Hypermap
