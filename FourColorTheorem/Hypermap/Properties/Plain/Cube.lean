import FourColorTheorem.Hypermap.Actions.Cube
import FourColorTheorem.Hypermap.Properties.Plain.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

open CubeTag

theorem cube_plain : H.cube.plain := by{
  rw[plain_iff_edge_edge]
  intro ⟨t, x⟩
  match t with | CTn | CTen | CTf | CTnf | CTe | CTfe => {
    simp[CubeDart.edge, nfe_cancel, enf_cancel]
  }
}

theorem cube_ecomp : H.cube.ecomp = Fintype.card α * 3 := by{
  have h := H.cube_plain.ecomp_double
  rw[H.cube_card] at h
  omega
}

end Hypermap
