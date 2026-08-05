import FourColorTheorem.Hypermap.Actions.Cube
import FourColorTheorem.Hypermap.Properties.Planar.Euler
import FourColorTheorem.Hypermap.Properties.Plain.Cube
import FourColorTheorem.Hypermap.Properties.Cubic.Cube

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem cube_genus : H.cube.genus = H.genus := by{
  unfold genus
  congr 1
  unfold euler_lhs euler_rhs
  rw[cube_ecomp, cube_ncomp, cube_fcomp, cube_card, cube_gcomp]
  omega
}

theorem cube_planar : H.cube.Planar ↔ H.Planar := by{
  simp[planar_def,cube_genus]
}

open CubeTag

end Hypermap
