import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Planarity

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

lemma mirror_enf_cancel : ∀x, (H.face ∘ H.node) (H.nodeinv (H.faceinv x)) = x:=by{
  rw[nodeinv_eq, faceinv_eq]
  intro _
  simp only [comp_apply, nfe_cancel, fen_cancel]
}
@[reducible] def mirror (H : Hypermap α) : Hypermap α :=
  ⟨H.face ∘ H.node, H.nodeinv, H.faceinv, H.mirror_enf_cancel⟩
theorem mirror_edge : H.mirror.edge = H.face ∘ H.node := rfl
theorem mirror_node : H.mirror.node = H.nodeinv := rfl
theorem mirror_face : H.mirror.face = H.faceinv := rfl

theorem mirror_cnode : H.mirror.cnode = H.cnode := by{
  unfold cnode
  rw[mirror_node]
  exact funReflTransGen_bijInv_iff H.node_bijective
}
theorem mirror_cface : H.mirror.cface = H.cface := by{
  unfold cface
  rw[mirror_face]
  exact funReflTransGen_bijInv_iff H.face_bijective
}

theorem mirror_ncomp : H.mirror.ncomp = H.ncomp := by{unfold ncomp nsetoid; simp[mirror_cnode]}
theorem mirror_fcomp : H.mirror.fcomp = H.fcomp := by{unfold fcomp fsetoid; simp[mirror_cface]}
theorem mirror_edgeinv : H.mirror.edgeinv = H.face ∘ H.edge ∘ H.edge ∘ H.node := by{
  unfold edgeinv
  simp only [mirror_edge]
  rw[Fintype.comp_bijInv H.face_bijective H.node_bijective]
  rw[←H.faceinv_eq, ←Function.comp_assoc, ←H.nodeinv_eq]
  rfl
}
theorem mirror_nodeinv : H.mirror.nodeinv = H.node := by{
  unfold nodeinv
  simp only [mirror_node]
  exact Fintype.bijInv_bijInv H.node_bijective
}
theorem mirror_faceinv : H.mirror.faceinv = H.face := by{
  unfold faceinv
  simp only [mirror_face]
  exact Fintype.bijInv_bijInv H.face_bijective
}

theorem mirror_cclink : H.mirror.cclink = H.cclink := by{
  rw[cclink_iff_refltransgen_union_refltransgen]
  rw[mirror_cnode, mirror_cface]
  rw[cclink_iff_refltransgen_union_refltransgen]
}
theorem mirror_cglink : H.mirror.cglink = H.cglink := by{
  rw[←cclink_iff_cglink, ←cclink_iff_cglink, mirror_cclink]
}
theorem mirror_gcomp : H.mirror.gcomp = H.gcomp := by{
  unfold gcomp gsetoid
  simp[mirror_cglink]
}
theorem mirror_euler_lhs : H.mirror.euler_lhs = H.euler_lhs := by{
  unfold euler_lhs
  simp[mirror_gcomp]
}
theorem mirror_edge_adj_edgeinv : H.mirror.edge = H.nodeinv ∘ H.edgeinv ∘ H.node :=by{
  rw[mirror_edge, nodeinv_eq, edgeinv_eq]
  ext x
  simp[enf_cancel]
}
theorem mirror_cedge : H.mirror.cedge = InvImage H.cedge H.node := by{
  ext a b
  unfold cedge
  rw[mirror_edge_adj_edgeinv]
  have h:=ReflTransGen_InvImage_Equiv (r:=fromFun H.edgeinv)
    (f:=Equiv.ofBijective _ H.node_bijective)
  unfold funReflTransGen
  rw[Equiv.ofBijective_coe] at h
  have h':ReflTransGen (fromFun H.edgeinv) = ReflTransGen (fromFun H.edge):=by{
    unfold edgeinv
    exact funReflTransGen_bijInv_iff H.edge_bijective
  }
  rw[←h', ←h]
  rw[←funReflTransGen_conj H.node_bijective]
  rfl
}

theorem mirror_esetoid : H.mirror.esetoid = Setoid.mk (InvImage H.esetoid H.node)
  (InvImage.equivalence _ _ H.esetoid.iseqv) := by{
  unfold esetoid
  ext a b
  simp only
  rw[mirror_cedge]
}
theorem mirror_ecomp : H.mirror.ecomp = H.ecomp := by{
  unfold ecomp
  let nconjs := Setoid.mk _ (InvImage.equivalence H.esetoid H.node H.esetoid.iseqv)
  have h1:Fintype.nComp H.mirror.esetoid = @Fintype.nComp α inferInstance
    nconjs (InvImage.instDecidableRel H.node)
    :=by {
      congr 1
      exact mirror_esetoid
    }
  rw[h1]
  let neqv := (Equiv.ofBijective _ H.node_bijective)
  have h':=@Fintype.nComp_equiv _ _ _ nconjs H.esetoid (by{
    unfold nconjs
    simp only
    apply InvImage.instDecidableRel
  }) neqv (by{unfold nconjs neqv; simp[InvImage]})
  apply h'.trans
  congr
  · apply Subsingleton.elim
  · apply Subsingleton.elim
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
theorem mirror_jordan : H.mirror.jordan ↔ H.jordan := by{
  simp only [←planar_iff_jordan, mirror_planar]
}

theorem mirror_mirror : H.mirror.mirror = H := by{
  unfold mirror
  simp[faceinv_eq, nodeinv_eq, Function.comp_assoc, nfe_id]
  simp[←Function.comp_assoc (h:=H.node), enf_id]
}
theorem mirror_dual : H.mirror.dual = H.dual.mirror := by{
  unfold dual
  unfold mirror
  simp [faceinv_eq, nodeinv_eq, edgeinv_eq]
  simp [Function.comp_assoc, fen_id, enf_id, nfe_id]
  simp[←Function.comp_assoc (h:=H.node), enf_id]
}

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

theorem mirror_arity : H.mirror.arity = H.arity :=by{
  unfold arity
  rw[mirror_face]
  unfold faceinv
  rw[Fintype.bijInv_minimalPeriod' H.face_bijective]
}

end Hypermap
