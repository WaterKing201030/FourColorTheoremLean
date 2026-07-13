import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

@[reducible] def permN (H : Hypermap α) : Hypermap α := ⟨H.node, H.face, H.edge, H.nfe_cancel⟩
@[reducible] def permF (H : Hypermap α) : Hypermap α := ⟨H.face, H.edge, H.node, H.fen_cancel⟩

theorem permF_eq_permN_permN : H.permF = H.permN.permN := rfl
theorem permN_eq_permF_permF : H.permN = H.permF.permF := rfl
theorem permN_triple : H.permN.permN.permN = H := rfl
theorem permF_triple : H.permF.permF.permF = H := rfl

theorem permN_edge : H.permN.edge = H.node := rfl
theorem permN_node : H.permN.node = H.face := rfl
theorem permN_face : H.permN.face = H.edge := rfl
theorem permN_edgeinv : H.permN.edgeinv = H.nodeinv := by{
  rw[edgeinv_eq, nodeinv_eq, permN_node, permN_face]
}
theorem permN_nodeinv : H.permN.nodeinv = H.faceinv := by{
  rw[nodeinv_eq, faceinv_eq, permN_face, permN_edge]
}
theorem permN_faceinv : H.permN.faceinv = H.edgeinv := by{
  rw[faceinv_eq, edgeinv_eq, permN_edge, permN_node]
}
theorem permN_cedge : H.permN.cedge = H.cnode := rfl
theorem permN_cnode : H.permN.cnode = H.cface := rfl
theorem permN_cface : H.permN.cface = H.cedge := rfl
theorem permN_ecomp : H.permN.ecomp = H.ncomp := rfl
theorem permN_ncomp : H.permN.ncomp = H.fcomp := rfl
theorem permN_fcomp : H.permN.fcomp = H.ecomp := rfl
theorem permN_glink : H.permN.glink = H.glink:=by{
  ext a b
  unfold glink
  unfold permN
  simp only
  rw[union_comm, union_comm (r1:=fromFun face), union_assoc, union_comm (r1:=fromFun face)]
}
theorem permN_cglink : H.permN.cglink = H.cglink := congrArg ReflTransGen H.permN_glink
theorem permN_gcomp : H.permN.gcomp = H.gcomp
  := by{
  unfold gcomp gsetoid
  simp[permN_cglink]
}
theorem permN_connected : H.permN.connected ↔ H.connected := by{
  unfold connected
  simp[permN_gcomp]
}
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

theorem permF_edge : H.permF.edge = H.face := rfl
theorem permF_node : H.permF.node = H.edge := rfl
theorem permF_face : H.permF.face = H.node := rfl
theorem permF_edgeinv : H.permF.edgeinv = H.faceinv := by{
  rw[edgeinv_eq, faceinv_eq, permF_node, permF_face]
}
theorem permF_nodeinv : H.permF.nodeinv = H.edgeinv := by{
  rw[nodeinv_eq, edgeinv_eq, permF_face, permF_edge]
}
theorem permF_faceinv : H.permF.faceinv = H.nodeinv := by{
  rw[faceinv_eq, nodeinv_eq, permF_edge, permF_node]
}
theorem permF_cedge : H.permF.cedge = H.cface := rfl
theorem permF_cnode : H.permF.cnode = H.cedge := rfl
theorem permF_cface : H.permF.cface = H.cnode := rfl
theorem permF_ecomp : H.permF.ecomp = H.fcomp := rfl
theorem permF_ncomp : H.permF.ncomp = H.ecomp := rfl
theorem permF_fcomp : H.permF.fcomp = H.ncomp := rfl
theorem permF_glink : H.permF.glink = H.glink:=by{
  rw[permF_eq_permN_permN]
  rw[permN_glink, permN_glink]
}
theorem permF_cglink : H.permF.cglink = H.cglink := congrArg ReflTransGen H.permF_glink
theorem permF_gcomp : H.permF.gcomp = H.gcomp
  := by{
  unfold gcomp gsetoid
  simp[permF_cglink]
}
theorem permF_connected : H.permF.connected ↔ H.connected := by{
  unfold connected
  simp[permF_gcomp]
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
