import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Properties.Planar.Euler.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem mirror_euler_lhs : H.mirror.euler_lhs = H.euler_lhs := by{
  unfold euler_lhs
  simp[mirror_gcomp]
}

theorem mirror_euler_rhs : H.mirror.euler_rhs = H.euler_rhs := by{
  unfold euler_rhs
  simp[mirror_ecomp, mirror_ncomp, mirror_fcomp]
}
theorem mirror_genus : H.mirror.genus = H.genus := by{
  unfold genus
  simp[mirror_euler_lhs, mirror_euler_rhs]
}
theorem mirror_planar : H.mirror.planar ↔ H.planar := by{
  unfold planar
  simp[mirror_genus]
}

end Hypermap
