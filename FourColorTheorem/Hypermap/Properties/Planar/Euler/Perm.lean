import FourColorTheorem.Hypermap.Actions.Perm
import FourColorTheorem.Hypermap.Properties.Planar.Euler.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem permN_euler_lhs : H.permN.euler_lhs = H.euler_lhs := by{
  unfold euler_lhs
  simp[permN_gcomp]
}
theorem permN_euler_rhs : H.permN.euler_rhs = H.euler_rhs := by{
  unfold euler_rhs
  simp[permN_ecomp, permN_ncomp, permN_fcomp]
  simp[Nat.add_assoc, Nat.add_comm]
}
theorem permN_genus : H.permN.genus = H.genus := by{
  unfold genus
  simp[H.permN_euler_rhs, H.permN_euler_lhs]
}
theorem permN_planar : H.permN.planar ↔ H.planar := by{
  unfold planar
  simp[H.permN_genus]
}

theorem permF_euler_lhs : H.permF.euler_lhs = H.euler_lhs := by{
  unfold euler_lhs
  simp[permF_gcomp]
}
theorem permF_euler_rhs : H.permF.euler_rhs = H.euler_rhs := by{
  unfold euler_rhs
  simp[permF_ecomp, permF_ncomp, permF_fcomp]
  simp[Nat.add_comm H.fcomp, Nat.add_assoc]
}
theorem permF_genus : H.permF.genus = H.genus := by{
  unfold genus
  simp[H.permF_euler_rhs, H.permF_euler_lhs]
}
theorem permF_planar : H.permF.planar ↔ H.planar := by{
  unfold planar
  simp[H.permF_genus]
}

end Hypermap
