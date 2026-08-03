import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

lemma dual_enf_cancel : ∀ x, H.edgeinv (H.faceinv (H.nodeinv x)) = x := by{
  intro x
  rw[edgeinv_eq, faceinv_eq, nodeinv_eq]
  simp[nfe_cancel]
}
@[reducible] def dual (H : Hypermap α) : Hypermap α :=
  ⟨H.edgeinv, H.faceinv, H.nodeinv, dual_enf_cancel⟩

theorem dual_edge : H.dual.edge = H.edgeinv := rfl
theorem dual_node : H.dual.node = H.faceinv := rfl
theorem dual_face : H.dual.face = H.nodeinv := rfl
theorem dual_cedge : H.dual.cedge = H.cedge := by{
  unfold cedge
  rw[dual_edge]
  exact funReflTransGen_bijInv_iff H.edge_bijective
}
theorem dual_cnode : H.dual.cnode = H.cface := by{
  unfold cnode cface
  rw[dual_node]
  exact funReflTransGen_bijInv_iff H.face_bijective
}
theorem dual_cface : H.dual.cface = H.cnode := by{
  unfold cnode cface
  rw[dual_face]
  exact funReflTransGen_bijInv_iff H.node_bijective
}
theorem dual_ecomp : H.dual.ecomp = H.ecomp := by{unfold ecomp esetoid; simp[dual_cedge]}
theorem dual_ncomp : H.dual.ncomp = H.fcomp := by{unfold ncomp fcomp nsetoid; simp[dual_cnode]}
theorem dual_fcomp : H.dual.fcomp = H.ncomp := by{unfold fcomp ncomp fsetoid; simp[dual_cface]}
theorem dual_edgeinv : H.dual.edgeinv = H.edge := by{
  unfold edgeinv
  simp only [dual_edge]
  exact Fintype.bijInv_bijInv H.edge_bijective
}
theorem dual_nodeinv : H.dual.nodeinv = H.face := by{
  unfold nodeinv
  simp only [dual_node]
  exact Fintype.bijInv_bijInv H.face_bijective
}
theorem dual_faceinv : H.dual.faceinv = H.node := by{
  unfold faceinv
  simp only [dual_face]
  exact Fintype.bijInv_bijInv H.node_bijective
}
theorem dual_clink : H.dual.clink = H.clink := by{
  unfold clink
  simp[dual_nodeinv, dual_face, union_comm]
}
theorem dual_cclink : H.dual.cclink = H.cclink := congrArg ReflTransGen H.dual_clink
theorem dual_cglink : H.dual.cglink = H.cglink := by{
  rw[←cclink_iff_cglink, ←cclink_iff_cglink]
  exact dual_cclink
}
theorem dual_gcomp : H.dual.gcomp = H.gcomp := by{unfold gcomp gsetoid;simp[dual_cglink]}
theorem dual_connected : H.dual.connected = H.connected := by{unfold connected;simp[dual_gcomp]}

theorem dual_dual : H.dual.dual = H := by{
  unfold dual
  simp[dual_edgeinv, dual_nodeinv, dual_faceinv]
}

end Hypermap
