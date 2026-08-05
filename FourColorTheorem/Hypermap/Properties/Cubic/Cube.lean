import FourColorTheorem.Hypermap.Actions.Cube
import FourColorTheorem.Hypermap.Properties.Cubic.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

open CubeTag

theorem cube_cubic : H.cube.Cubic := by{
  rw[cubic_iff_period_three]
  intro ⟨t, x⟩
  match t with | CTn | CTen | CTf | CTnf | CTe | CTfe => {
    simp[CubeDart.node, nfe_cancel, enf_cancel, fen_cancel]
  }
}

theorem cube_ncomp : H.cube.ncomp = Fintype.card α * 2 := by{
  have h : Fintype.card H.CubeDart = H.cube.ncomp * 3 := H.cube_cubic.ncomp_triple
  rw[H.cube_card] at h
  omega
}

end Hypermap
