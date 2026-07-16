import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import FourColorTheorem.Utils.Finite

class Hypermap (α : Type _) [Fintype α] [DecidableEq α] where
  edge : α → α
  node : α → α
  face : α → α
  enf_cancel : ∀ x, edge (node (face x)) = x

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem enf_id : H.edge ∘ H.node ∘ H.face = id := funext H.enf_cancel
theorem edge_leftInverse : LeftInverse H.edge (H.node ∘ H.face) := H.enf_cancel
theorem edge_surjective : Surjective H.edge := LeftInverse.surjective edge_leftInverse
theorem edge_injective : Injective H.edge := Finite.injective_iff_surjective.mpr edge_surjective
theorem edge_inj {x y : α} : H.edge x = H.edge y ↔ x = y := ⟨(H.edge_injective ·), congrArg H.edge⟩
theorem edge_bijective : Bijective H.edge := ⟨H.edge_injective, H.edge_surjective⟩
theorem edge_rightInverse : RightInverse H.edge (H.node ∘ H.face) :=
  rightInverse_of_injective_of_leftInverse edge_injective edge_leftInverse

theorem nfe_cancel : ∀ x, H.node (face (edge x)) = x := edge_rightInverse
theorem nfe_id : H.node ∘ H.face ∘ H.edge = id := funext nfe_cancel
theorem node_leftInverse : LeftInverse H.node (H.face ∘ H.edge) := nfe_cancel
theorem node_surjective : Surjective H.node := LeftInverse.surjective node_leftInverse
theorem node_injective : Injective H.node := Finite.injective_iff_surjective.mpr node_surjective
theorem node_inj {x y : α} : H.node x = H.node y ↔ x = y := ⟨(H.node_injective ·), congrArg H.node⟩
theorem node_bijective : Bijective H.node := ⟨H.node_injective, H.node_surjective⟩
theorem node_rightInverse : RightInverse H.node (H.face ∘ H.edge) :=
  rightInverse_of_injective_of_leftInverse node_injective node_leftInverse

theorem fen_cancel : ∀ x, H.face (edge (node x)) = x := node_rightInverse
theorem fen_id : H.face ∘ H.edge ∘ H.node = id := funext fen_cancel
theorem face_leftInverse : LeftInverse H.face (H.edge ∘ H.node) := fen_cancel
theorem face_surjective : Surjective H.face := LeftInverse.surjective face_leftInverse
theorem face_injective : Injective H.face := Finite.injective_iff_surjective.mpr face_surjective
theorem face_inj {x y : α} : H.face x = H.face y ↔ x = y := ⟨(H.face_injective ·), congrArg H.face⟩
theorem face_bijective : Bijective H.face := ⟨H.face_injective, H.face_surjective⟩
theorem face_rightInverse : RightInverse H.face (H.edge ∘ H.node) := H.enf_cancel

def cedge (H : Hypermap α) := funReflTransGen H.edge
def cnode (H : Hypermap α) := funReflTransGen H.node
def cface (H : Hypermap α) := funReflTransGen H.face

@[inline] instance cedge.dec : DecidableRel H.cedge := ReflTransGen.finDec
@[inline] instance cnode.dec : DecidableRel H.cnode := ReflTransGen.finDec
@[inline] instance cface.dec : DecidableRel H.cface := ReflTransGen.finDec

theorem cedge_Symm : Std.Symm H.cedge := Relation.funReflTransGen_Symm_of_injective H.edge_injective
theorem cnode_Symm : Std.Symm H.cnode := Relation.funReflTransGen_Symm_of_injective H.node_injective
theorem cface_Symm : Std.Symm H.cface := Relation.funReflTransGen_Symm_of_injective H.face_injective

theorem cedge_equivalence : Equivalence H.cedge where
  refl := fun _ => ReflTransGen.refl
  symm := cedge_Symm.symm _ _
  trans := ReflTransGen.trans
theorem cnode_equivalence : Equivalence H.cnode where
  refl := fun _ => ReflTransGen.refl
  symm := cnode_Symm.symm _ _
  trans := ReflTransGen.trans
theorem cface_equivalence : Equivalence H.cface where
  refl := fun _ => ReflTransGen.refl
  symm := cface_Symm.symm _ _
  trans := ReflTransGen.trans
theorem cedge_pred_eq_of_cedge {x y : α} (hxy : H.cedge x y)
  : H.cedge x = H.cedge y := cedge_equivalence.pred_eq_iff.mpr hxy
theorem cnode_pred_eq_of_cnode {x y : α} (hxy : H.cnode x y)
  : H.cnode x = H.cnode y := cnode_equivalence.pred_eq_iff.mpr hxy
theorem cface_pred_eq_of_cface {x y : α} (hxy : H.cface x y)
  : H.cface x = H.cface y := cface_equivalence.pred_eq_iff.mpr hxy

def glink (H : Hypermap α) : α → α → Prop := fromFun H.edge ∪ (fromFun H.node ∪ fromFun H.face)
theorem glink_iff {x y : α} : H.glink x y ↔ H.edge x = y ∨ H.node x = y ∨ H.face x = y := by rfl
def cglink (H : Hypermap α) := ReflTransGen H.glink
theorem cglink_iff {x y : α} : H.cglink x y ↔ ReflTransGen H.glink x y := by rfl
theorem cglink_iff_refltransgen_union_refltransgen
  : H.cglink = ReflTransGen (H.cedge ∪ (H.cnode ∪ H.cface)) := by{
  ext x y
  unfold cglink
  unfold glink
  unfold cedge cnode cface funReflTransGen
  symm
  rw[ReflTransGen_union_eq_ReflTransGen_union_ReflTransGen]
  rw[reflTransGen_idem]
  rw[←ReflTransGen_union_eq_ReflTransGen_union_ReflTransGen (r1:=fromFun node)]
  rw[←ReflTransGen_union_eq_ReflTransGen_union_ReflTransGen]
}
theorem cglink_Symm : Std.Symm H.cglink := by{
  rw[cglink_iff_refltransgen_union_refltransgen]
  apply Relation.ReflTransGen_Symm_of_Symm
  apply union_Symm_of_Symm cedge_Symm
  apply union_Symm_of_Symm cnode_Symm
  exact cface_Symm
}
theorem cglink_equivalence : Equivalence H.cglink where
  refl:=fun _ => ReflTransGen.refl
  symm:=cglink_Symm.symm _ _
  trans:=ReflTransGen.trans
@[inline] instance glink.dec:DecidableRel H.glink := fun _ _ => instDecidableOr
@[inline] instance cglink.dec:DecidableRel H.cglink := ReflTransGen.finDec
theorem cglink_of_cedge : H.cedge ⊆ H.cglink := by{
  unfold cedge cglink glink
  apply ReflTransGen_subset
  apply union_left_sub
}
theorem cglink_of_cnode : H.cnode ⊆ H.cglink := by{
  unfold cnode cglink glink
  apply ReflTransGen_subset
  intro x y h
  simp only [union_iff]
  right; left; assumption
}
theorem cglink_of_cface : H.cface ⊆ H.cglink := by{
  unfold cface cglink glink
  apply ReflTransGen_subset
  intro x y h
  simp only [union_iff]
  right; right; assumption
}

@[reducible] def esetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cedge_equivalence
@[reducible] def nsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cnode_equivalence
@[reducible] def fsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cface_equivalence
@[reducible] def gsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cglink_equivalence
@[inline] instance esetoid.instDecidable : DecidableRel H.esetoid := ReflTransGen.finDec
@[inline] instance nsetoid.instDecidable : DecidableRel H.nsetoid := ReflTransGen.finDec
@[inline] instance fsetoid.instDecidable : DecidableRel H.fsetoid := ReflTransGen.finDec
@[inline] instance gsetoid.instDecidable : DecidableRel H.gsetoid := ReflTransGen.finDec

def ecomp (H : Hypermap α) := Fintype.nComp H.esetoid
def ncomp (H : Hypermap α) := Fintype.nComp H.nsetoid
def fcomp (H : Hypermap α) := Fintype.nComp H.fsetoid
def gcomp (H : Hypermap α) := Fintype.nComp H.gsetoid
def connected (H : Hypermap α) : Prop := H.gcomp = 1
theorem ecomp_pos_intro (x : α) : H.ecomp > 0 := by{
  unfold ecomp Fintype.nComp
  simp only [gt_iff_lt]
  rw[Fintype.card_pos_iff]
  rw[nonempty_quotient_iff]
  apply Nonempty.intro x
}
theorem ncomp_pos_intro (x : α) : H.ncomp > 0 := by{
  unfold ncomp Fintype.nComp
  simp only [gt_iff_lt]
  rw[Fintype.card_pos_iff]
  rw[nonempty_quotient_iff]
  apply Nonempty.intro x
}
theorem fcomp_pos_intro (x : α) : H.fcomp > 0 := by{
  unfold fcomp Fintype.nComp
  simp only [gt_iff_lt]
  rw[Fintype.card_pos_iff]
  rw[nonempty_quotient_iff]
  apply Nonempty.intro x
}
theorem gcomp_pos_intro (x : α) : H.gcomp > 0 := by{
  unfold gcomp Fintype.nComp
  simp only [gt_iff_lt]
  rw[Fintype.card_pos_iff]
  rw[nonempty_quotient_iff]
  apply Nonempty.intro x
}
theorem ecomp_bound_card : H.ecomp ≤ Fintype.card α := by{
  apply Fintype.card_quotient_le
}
theorem ncomp_bound_card : H.ncomp ≤ Fintype.card α := by{
  apply Fintype.card_quotient_le
}
theorem fcomp_bound_card : H.fcomp ≤ Fintype.card α := by{
  apply Fintype.card_quotient_le
}
theorem gcomp_bound_card : H.gcomp ≤ Fintype.card α := by{
  apply Fintype.card_quotient_le
}


def euler_lhs (H : Hypermap α) := H.gcomp * 2 + Fintype.card α
def euler_rhs (H : Hypermap α) := H.ecomp + (H.ncomp + H.fcomp)
def genus (H : Hypermap α) := (H.euler_lhs - H.euler_rhs) / 2
def planar (H : Hypermap α) : Prop := H.genus = 0

def edgeinv (H : Hypermap α) :=Fintype.bijInv H.edge_bijective
def nodeinv (H : Hypermap α) :=Fintype.bijInv H.node_bijective
def faceinv (H : Hypermap α) :=Fintype.bijInv H.face_bijective

theorem edgeinv_eq:H.edgeinv = H.node ∘ H.face:=by{
  ext x
  apply H.edge_injective
  unfold edgeinv
  rw[Fintype.rightInverse_bijInv H.edge_bijective x]
  simp[enf_cancel]
}
theorem nodeinv_eq:H.nodeinv = H.face ∘ H.edge:=by{
  ext x
  apply H.node_injective
  unfold nodeinv
  rw[Fintype.rightInverse_bijInv H.node_bijective x]
  simp[nfe_cancel]
}
theorem faceinv_eq:H.faceinv = H.edge ∘ H.node:=by{
  ext x
  apply H.face_injective
  unfold faceinv
  rw[Fintype.rightInverse_bijInv H.face_bijective x]
  simp[fen_cancel]
}

theorem edgeinv_eq_iff_eq_edge {x y : α}
  : H.edgeinv x = y ↔ x = H.edge y:=by{
  rw[edgeinv_eq, comp_apply, ←H.edge_inj, enf_cancel]
}
theorem nodeinv_eq_iff_eq_node {x y : α}
  : H.nodeinv x = y ↔ x = H.node y:=by{
  rw[nodeinv_eq, comp_apply, ←H.node_inj, nfe_cancel]
}
theorem faceinv_eq_iff_eq_face {x y : α}
  : H.faceinv x = y ↔ x = H.face y:=by{
  rw[faceinv_eq, comp_apply, ←H.face_inj, fen_cancel]
}
theorem eq_edgeinv_iff_edge_eq {x y : α}
  : x = H.edgeinv y ↔ H.edge x = y:=by{
  rw[edgeinv_eq, comp_apply, ←H.edge_inj, enf_cancel]
}
theorem eq_nodeinv_iff_node_eq {x y : α}
  : x = H.nodeinv y ↔ H.node x = y:=by{
  rw[nodeinv_eq, comp_apply, ←H.node_inj, nfe_cancel]
}
theorem eq_faceinv_iff_face_eq {x y : α}
  : x = H.faceinv y ↔ H.face x = y:=by{
  rw[faceinv_eq, comp_apply, ←H.face_inj, fen_cancel]
}
theorem edgeinv_bijective : Bijective H.edgeinv := Fintype.bijective_bijInv H.edge_bijective
theorem nodeinv_bijective : Bijective H.nodeinv := Fintype.bijective_bijInv H.node_bijective
theorem faceinv_bijective : Bijective H.faceinv := Fintype.bijective_bijInv H.face_bijective
theorem edgeinv_injective : Injective H.edgeinv := H.edgeinv_bijective.injective
theorem nodeinv_injective : Injective H.nodeinv := H.nodeinv_bijective.injective
theorem faceinv_injective : Injective H.faceinv := H.faceinv_bijective.injective

theorem edgeinv_leftinv (x : α) : H.edgeinv (H.edge x) = x:=
  Fintype.leftInverse_bijInv H.edge_bijective x
theorem nodeinv_leftinv (x : α) : H.nodeinv (H.node x) = x:=
  Fintype.leftInverse_bijInv H.node_bijective x
theorem faceinv_leftinv (x : α) : H.faceinv (H.face x) = x:=
  Fintype.leftInverse_bijInv H.face_bijective x
theorem edgeinv_rightinv (x : α) : H.edge (H.edgeinv x) = x:=
  Fintype.rightInverse_bijInv H.edge_bijective x
theorem nodeinv_rightinv (x : α) : H.node (H.nodeinv x) = x:=
  Fintype.rightInverse_bijInv H.node_bijective x
theorem faceinv_rightinv (x : α) : H.face (H.faceinv x) = x:=
  Fintype.rightInverse_bijInv H.face_bijective x

theorem edge_eq_self_iff_edgeinv_eq_self {x : α}
  : H.edge x = x ↔ H.edgeinv x = x:=by{
    nth_rw 2 [←H.edge_inj]
    rw[edgeinv_eq, comp_apply, enf_cancel, Eq.comm]
  }
theorem node_eq_self_iff_nodeinv_eq_self {x : α}
  : H.node x = x ↔ H.nodeinv x = x:=by{
    nth_rw 2 [←H.node_inj]
    rw[nodeinv_eq, comp_apply, nfe_cancel, Eq.comm]
  }
theorem face_eq_self_iff_faceinv_eq_self {x : α}
  : H.face x = x ↔ H.faceinv x = x:=by{
    nth_rw 2 [←H.face_inj]
    rw[faceinv_eq, comp_apply, fen_cancel, Eq.comm]
  }
theorem not_edge_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.edge x ≠ x:=by{
  simp [glink_iff] at hgx
  simp [hgx]
}
theorem not_node_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.node x ≠ x:=by{
  simp [glink_iff] at hgx
  simp [hgx]
}
theorem not_face_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.face x ≠ x:=by{
  simp [glink_iff] at hgx
  simp [hgx]
}
theorem not_edgeinv_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.edgeinv x ≠ x:=
  not_edge_self_of_glink hgx ∘ edge_eq_self_iff_edgeinv_eq_self.mpr
theorem not_nodeinv_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.nodeinv x ≠ x:=
  not_node_self_of_glink hgx ∘ node_eq_self_iff_nodeinv_eq_self.mpr
theorem not_faceinv_self_of_glink {x : α} (hgx : ¬H.glink x x) : H.faceinv x ≠ x:=
  not_face_self_of_glink hgx ∘ face_eq_self_iff_faceinv_eq_self.mpr

theorem edge_self_cedge_iff {x y : α} (he : H.edge x = x) : H.cedge x y ↔ x = y:=by{
  simp[cedge, funReflTransGen_iff_iterate, iterate_fixed he]
}
theorem node_self_cnode_iff {x y : α} (hn : H.node x = x) : H.cnode x y ↔ x = y:=by{
  simp[cnode, funReflTransGen_iff_iterate, iterate_fixed hn]
}
theorem face_self_cface_iff {x y : α} (hf : H.face x = x) : H.cface x y ↔ x = y:=by{
  simp[cface, funReflTransGen_iff_iterate, iterate_fixed hf]
}


def clink (H : Hypermap α) := fromFun H.nodeinv ∪ fromFun H.face
def cclink (H : Hypermap α) := ReflTransGen H.clink
@[inline] instance clink.dec:DecidableRel H.clink := fun _ _ => instDecidableOr
@[inline] instance cclink.dec:DecidableRel H.cclink := ReflTransGen.finDec
theorem cclink_iff_refltransgen_union_refltransgen
  : H.cclink = ReflTransGen (H.cnode ∪ H.cface) := by{
    unfold cclink clink
    unfold cnode cface
    rw[ReflTransGen_union_eq_ReflTransGen_union_ReflTransGen]
    unfold funReflTransGen
    rw[←funReflTransGen]
    unfold nodeinv
    rw[funReflTransGen_bijInv_iff node_bijective]
    rfl
  }
theorem cnf_eq_cenf:ReflTransGen (H.cnode ∪ H.cface)
  = ReflTransGen (H.cedge ∪ (H.cnode ∪ H.cface)):=by{
  ext a b
  constructor
  · exact ReflTransGen_subset union_right_sub
  · {
    intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail c b hac hcb ih => {
      apply ih.trans
      repeat rw[union_iff] at hcb
      cases hcb with
      | inl hcb => {
        unfold cedge at hcb
        unfold funReflTransGen at hcb
        apply funReflTransGen_symm_of_injective H.edge_injective at hcb
        rw[←funReflTransGen_bijInv_iff H.edge_bijective] at hcb
        have hcb':=funReflTransGen_symm_of_injective
          (Fintype.bijective_bijInv H.edge_bijective).left hcb
        rw[←edgeinv, edgeinv_eq] at hcb'
        rw[←reflTransGen_idem]
        apply (ReflTransGen_subset (r2:=ReflTransGen (H.cnode ∪ H.cface)) · hcb')
        intro x y hxy
        simp only [fromFun, comp_apply] at hxy
        have h0:ReflTransGen (H.cnode ∪ H.cface) x (H.face x):=by{
          apply ReflTransGen.single
          apply union_right_sub
          apply ReflTransGen.single
          rfl
        }
        have h1:ReflTransGen (H.cnode ∪ H.cface) (H.face x) (H.node (H.face x)):=by{
          apply ReflTransGen.single
          apply union_left_sub
          apply ReflTransGen.single
          rfl
        }
        rw[hxy] at h1
        exact h0.trans h1
      }
      | inr hcb => rw[←union_iff] at hcb; exact ReflTransGen.single hcb
    }
  }
}
theorem cclink_iff_cglink : H.cclink = H.cglink := by{
  rw[cclink_iff_refltransgen_union_refltransgen]
  rw[cglink_iff_refltransgen_union_refltransgen]
  rw[cnf_eq_cenf]
}
theorem cclink_of_cedge : H.cedge ⊆ H.cclink := by{
  simp[cclink_iff_cglink, cglink_of_cedge]
}
theorem cclink_of_cnode : H.cnode ⊆ H.cclink := by{
  simp[cclink_iff_cglink, cglink_of_cnode]
}
theorem cclink_of_cface : H.cface ⊆ H.cclink := by{
  simp[cclink_iff_cglink, cglink_of_cface]
}
theorem cglink_iff_cef : H.cglink = ReflTransGen (H.cedge ∪ H.cface) := by{
  ext x y
  constructor
  · {
    intro h
    induction h with
    | refl => rfl
    | @tail _ c hh ht ih => {
      apply ih.trans
      rcases ht with ht | ht | ht
      · exact ReflTransGen.single (Or.inl (ReflTransGen.single ht))
      · {
        rw[fromFun, ← eq_nodeinv_iff_node_eq, nodeinv_eq, comp_apply] at ht
        rw[ht]
        apply ReflTransGen.trans (b:=edge c)
        · {
          apply ReflTransGen.single
          right
          apply H.cface_equivalence.symm
          apply funReflTransGen.single
        }
        · {
          apply ReflTransGen.single
          left
          apply H.cedge_equivalence.symm
          apply funReflTransGen.single
        }
      }
      · exact ReflTransGen.single (Or.inr (ReflTransGen.single ht))
    }
  }
  · {
    intro h
    induction h with
    | refl => unfold cglink; rfl
    | tail hh ht ih => {
      apply ih.trans
      rcases ht with ht | ht
      · exact H.cglink_of_cedge ht
      · exact H.cglink_of_cface ht
    }
  }
}
theorem cclink_equivalence : Equivalence H.cclink := by{
  rw[cclink_iff_cglink]
  exact cglink_equivalence
}
@[reducible] def csetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cclink_equivalence
@[inline] instance csetoid.instDecidable : DecidableRel H.csetoid := ReflTransGen.finDec
theorem csetoid_eq_gsetoid {H : Hypermap α} : H.csetoid = H.gsetoid := by{
  ext
  unfold csetoid gsetoid
  simp[cclink_iff_cglink]
}
def moebius_path (H : Hypermap α) (p : List α) : Prop :=
  if hp: p = [] then False
  else p.Nodup ∧ p.IsChain H.clink
  ∧ H.node (p.head hp) ∈ p.tail.drop (p.tail.idxOf (H.nodeinv (p.getLast hp)))
def jordan (H : Hypermap α) := ∀q, ¬H.moebius_path q
theorem nil_not_moebius_path:¬H.moebius_path []:=by{unfold moebius_path;simp}
theorem moebius_path_ne_nil {p : List α} (hp : H.moebius_path p) : p ≠ [] :=
  fun h => nil_not_moebius_path (h ▸ hp)
theorem head_node_mem_moebius_path_tail {p : List α} (hp : H.moebius_path p) :
  H.node (p.head (moebius_path_ne_nil hp)) ∈ p.tail := by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.tail_cons, List.head_cons]
      unfold moebius_path at hp
      simp only [reduceCtorEq, ↓reduceDIte, List.nodup_cons, List.head_cons] at hp
      exact List.mem_of_mem_drop hp.right.right
    }
  }
theorem head_node_mem_moebius_path_tail_cons {x : α} {p : List α} (hp : H.moebius_path (x :: p))
  : H.node x ∈ p :=  by{
    have h:=head_node_mem_moebius_path_tail hp
    simp at h
    simp[h]
  }
theorem last_nodeinv_mem_moebius_path_tail {p : List α} (hp : H.moebius_path p) :
  H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.tail := by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.tail_cons]
      rw[List.getLast_cons_eq_getLastD]
      unfold moebius_path at hp
      rw[←List.idxOf_lt_length_iff]
      have hp'':=List.length_pos_of_mem hp.right.right
      simp only [List.length_drop, tsub_pos_iff_lt, List.tail_cons
      , List.getLast_cons_eq_getLastD] at hp''
      exact hp''
    }
  }
theorem last_nodeinv_mem_moebius_path_tail_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  H.nodeinv (p.getLastD x) ∈ p := by{
    have h:=last_nodeinv_mem_moebius_path_tail hp
    simp only [List.tail_cons] at h
    rw[List.getLast_cons_eq_getLastD] at h
    exact h
  }
theorem moebius_path_not_eq {p : List α} (hp : H.moebius_path p) :
  p.head (moebius_path_ne_nil hp) ≠ H.nodeinv (p.getLast (moebius_path_ne_nil hp)) :=by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.head_cons, ne_eq]
      rw[List.getLast_cons_eq_getLastD]
      have hy := last_nodeinv_mem_moebius_path_tail_cons hp
      unfold moebius_path at hp
      rw[List.nodup_cons] at hp
      intro hn
      apply hp.left.left
      rw[hn]
      exact hy
    }
  }
theorem moebius_path_not_eq_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  x ≠ H.nodeinv (p.getLastD x) := by{
    rw[←List.getLast_cons_eq_getLastD]
    have hp:=moebius_path_not_eq hp
    simp at hp
    simp[hp]
  }
theorem moebius_path_not_eq' {p : List α} (hp : H.moebius_path p) :
  H.node (p.head (moebius_path_ne_nil hp)) ≠ p.getLast (moebius_path_ne_nil hp) := by{
    intro hn
    apply moebius_path_not_eq hp
    apply H.node_injective
    rw[nodeinv_eq]
    simp[nfe_cancel, hn]
  }
theorem moebius_path_not_eq'_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  H.node x ≠ p.getLastD x := by{
    rw[←List.getLast_cons_eq_getLastD]
    have hp:=moebius_path_not_eq' hp
    simp at hp
    simp[hp]
  }
theorem moebius_path_tail_ne_nil {p : List α} (hp : H.moebius_path p) :
  p.tail ≠ []:=by{
    match p with
    | x::p' => {
      simp only [List.tail_cons, ne_eq]
      simp only [moebius_path, reduceCtorEq, ↓reduceDIte, List.nodup_cons, List.tail_cons,
        List.head_cons] at hp
      have hp':=List.mem_of_mem_drop hp.right.right
      apply List.ne_nil_of_mem hp'
    }
  }
theorem moebius_path_head_ne_last {p : List α} (hp : H.moebius_path p) :
  p.head (moebius_path_ne_nil hp) ≠ p.getLast (moebius_path_ne_nil hp) := by{
    have hpn:=moebius_path_ne_nil hp
    have hp'n:=moebius_path_tail_ne_nil hp
    unfold moebius_path at hp
    rw[dite_cond_eq_false (by{simp[hpn]})] at hp
    have hpd:=hp.left
    rw[←List.cons_head_tail hpn] at hpd
    rw[List.nodup_cons] at hpd
    intro h
    apply hpd.left
    rw[h]
    rw[←List.getLast_tail hp'n]
    apply List.getLast_mem
  }
theorem moebius_path_node_head_mem_tail {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p.tail :=by{
    have hpn:=moebius_path_ne_nil hp
    unfold moebius_path at hp
    simp only [hpn, ↓reduceDIte] at hp
    exact List.mem_of_mem_drop hp.right.right
  }
theorem moebius_path_node_head_mem_dropLast_tail {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p.dropLast.tail :=by{
    have ih:=moebius_path_node_head_mem_tail hp
    have hpn:=moebius_path_ne_nil hp
    nth_rw 1 [←List.concat_dropLast_getLast hpn] at ih
    have h:p.dropLast ≠ []:=by{
      intro h
      simp[h] at ih
    }
    rw[List.tail_append_of_ne_nil h, List.mem_append] at ih
    apply ih.resolve_right
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    apply moebius_path_not_eq'
    exact hp
  }
theorem moebius_path_node_head_mem {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p :=by{
    apply List.mem_of_mem_tail
    apply moebius_path_node_head_mem_tail
    exact hp
  }
theorem moebius_path_head_ne_node {p : List α} (hp : H.moebius_path p)
: p.head (moebius_path_ne_nil hp) ≠ H.node (p.head (moebius_path_ne_nil hp)) := by{
  have hpn:=moebius_path_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn, ↓reduceDIte] at hp
  have hpd:=hp.left
  rw[←List.cons_head_tail hpn, List.nodup_cons] at hpd
  intro h
  apply hpd.left
  rw[h]
  apply moebius_path_node_head_mem_tail
  exact hp_backup
}
theorem moebius_path_nodeinv_getLast_mem_tail {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.tail := by{
  have hpn:=moebius_path_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn, ↓reduceDIte] at hp
  have hpm:=hp.right.right
  have hpm':=List.ne_nil_of_mem hpm
  simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
  rw[List.idxOf_lt_length_iff] at hpm'
  exact hpm'
}
theorem moebius_path_nodeinv_ne_getLast {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ≠ p.getLast (moebius_path_ne_nil hp) := by{
  have hpn:=moebius_path_ne_nil hp
  have hp'n:=moebius_path_tail_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn] at hp
  have hpm:=hp.right.right
  intro h
  rw[h] at hpm
  rw[←List.getLast_tail hp'n] at hpm
  rw[List.idxOf_getLast hp'n (by{
    have hpd:=hp.left
    rw[←List.cons_head_tail hpn, ←List.concat_dropLast_getLast hp'n] at hpd
    rw[←List.concat_eq_append, List.nodup_cons, List.nodup_concat] at hpd
    exact hpd.right.left
  })] at hpm
  rw[List.drop_length_sub_one hp'n] at hpm
  simp only [List.getLast_tail, List.mem_cons, List.not_mem_nil, or_false] at hpm
  apply moebius_path_not_eq' hp_backup
  exact hpm
}
theorem moebius_path_nodeinv_getLast_mem_dropLast_tail {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.dropLast.tail := by{
  have ih:=moebius_path_nodeinv_getLast_mem_tail hp
  have hpn:=moebius_path_ne_nil hp
  nth_rw 1 [←List.concat_dropLast_getLast hpn] at ih
  have h:p.dropLast ≠ []:=by{
    intro h
    simp[h] at ih
  }
  rw[List.tail_append_of_ne_nil h, List.mem_append] at ih
  apply ih.resolve_right
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  apply moebius_path_nodeinv_ne_getLast
  exact hp
}
theorem moebius_path_nodeinv_getLast_mem_dropLast {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.dropLast := by{
  apply List.mem_of_mem_tail
  apply moebius_path_nodeinv_getLast_mem_dropLast_tail
  exact hp
}
theorem moebius_path_nodeinv_getLast_mem {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p := by{
  apply List.mem_of_mem_tail
  apply moebius_path_nodeinv_getLast_mem_tail
  exact hp
}
theorem card_ge_three_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : Fintype.card α ≥ 3:=by{
    apply Nat.le_of_not_gt
    simp only [Nat.lt_succ_iff]
    rw[Fintype.card_le_two_iff]
    rw[not_or, not_exists]
    simp only [not_exists, not_forall, not_or]
    have hpn:=moebius_path_ne_nil hp
    rw[not_isEmpty_iff]
    apply And.intro (Nonempty.intro (p.head hpn))
    intro a b
    have h0:=moebius_path_not_eq hp
    have h1:=moebius_path_head_ne_last hp
    have h2:=moebius_path_nodeinv_ne_getLast hp
    cases em (H.nodeinv (p.getLast hpn) = a) with
    | inl ha => {
      rw[←ha]
      cases em (p.getLast hpn = b) with
      | inl hb => {
        use p.head hpn
        rw[←hb]
        exact ⟨h0, h1⟩
      }
      | inr hb => {
        use p.getLast hpn
        exact ⟨h2.symm, hb⟩
      }
    }
    | inr ha => {
      cases em (p.getLast hpn = b) with
      | inl hb => {
        use H.nodeinv (p.getLast hpn)
        rw[←hb]
        exact ⟨ha, h2⟩
      }
      | inr hb => {
        cases em (H.nodeinv (p.getLast hpn) = b) with
        | inl hb' => {
          cases em (p.getLast hpn = a) with
          | inl ha' => {
            rw[←ha', ←hb']
            use p.head hpn
          }
          | inr ha' => {
            use p.getLast hpn
          }
        }
        | inr hb' => {
          use H.nodeinv (p.getLast hpn)
        }
      }
    }
  }
theorem length_ge_three_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : p.length ≥ 3 := by{
    have h0:=moebius_path_node_head_mem_dropLast_tail hp
    have hn:=moebius_path_ne_nil hp
    have hn':=moebius_path_tail_ne_nil hp
    rw[←List.cons_head_tail hn, ←List.concat_dropLast_getLast hn']
    simp only [List.getLast_tail, List.length_cons]
    apply Nat.succ_le_succ
    rw[List.length_append, List.length_singleton]
    apply Nat.succ_le_succ
    rw[←List.tail_dropLast]
    apply List.length_pos_of_mem h0
  }
theorem moebius_path_tail_tail_ne_nil {p : List α} (hp : H.moebius_path p)
  : p.tail.tail ≠ [] := by{
    have h:=length_ge_three_of_moebius_path hp
    match p with
    | [] | [_] | [_, _] => simp at h
    | _::_::_::_ => simp
  }
theorem card_pos_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : Fintype.card α > 0:=by{
    apply (Nat.lt_of_lt_of_le · (card_ge_three_of_moebius_path hp))
    simp
  }
theorem moebius_path_nodup {p : List α} (hp : H.moebius_path p)
  : p.Nodup := by{
    simp[moebius_path] at hp
    simp[hp]
  }
theorem moebius_path_isChain_clink {p : List α} (hp : H.moebius_path p)
  : p.IsChain H.clink := by{
    simp[moebius_path] at hp
    simp[hp]
  }
theorem moebius_path_cross_nlink {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈
  p.tail.drop (p.tail.idxOf (H.nodeinv (p.getLast (moebius_path_ne_nil hp)))) := by{
    simp[moebius_path, moebius_path_ne_nil hp] at hp
    simp[hp]
  }

def bridgeless (H : Hypermap α) := ∀x, ¬H.cface x (H.edge x)
def loopless (H : Hypermap α) := ∀x, ¬H.cnode x (H.edge x)

theorem node_period_ge_two_of_bridgeless (Hb : H.bridgeless)
  : ∀x, minimalPeriod H.node x ≥ 2 := by{
  intro x
  by_contra
  rw[not_le] at this
  match hmpnx : minimalPeriod node x with
  | 0 => {
    have hmpnx' := H.node_injective.minimalPeriod_pos (x:=x)
    simp[hmpnx] at hmpnx'
  }
  | 1 => {
    simp only [minimalPeriod_eq_one_iff_isFixedPt] at hmpnx
    change node x = x at hmpnx
    specialize Hb (node x)
    apply Hb
    apply cface_equivalence.symm
    apply ReflTransGen.single
    change _ = _
    rw[fen_cancel, hmpnx]
  }
  | _ + 2 => simp[hmpnx] at this; omega
}

def arity (H : Hypermap α) (x : α) := minimalPeriod' H.face x
def pentagonal (H : Hypermap α) := ∀x, 4 < H.arity x
theorem cface_arity {x y : α} (hxy : H.cface x y) : H.arity x = H.arity y := by{
  unfold cface at hxy
  rw[funReflTransGen_iff_iterate_bounded] at hxy
  have ⟨n, hn, hxy'⟩:=hxy
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
  rw[←hxy']
  rw[minimalPeriod_eq_minimalPeriod_iff]
  intro n'
  unfold IsPeriodicPt IsFixedPt
  rw[←iterate_add_apply, add_comm, iterate_add_apply]
  symm
  apply Injective.eq_iff
  apply Injective.iterate
  exact H.face_injective
}
theorem iter_face_arity {x : α} : H.face^[H.arity x] x = x:=by{
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
  exact isPeriodicPt_minimalPeriod H.face x
}

def fband (H : Hypermap α) (p : List α) : Set α :=
  /- x is in the face closure of p -/
  /- can be used for configuration -/
  {x | p.any (H.cface x) }
@[inline] instance instMemFbandDecidable {p : List α} : DecidablePred (· ∈ H.fband p) :=
  fun x => by{
    simp only [fband, Set.mem_setOf]
    infer_instance
  }
theorem mem_fband_iff {p : List α} {x : α} : x ∈ H.fband p ↔ ∃y ∈ p, H.cface x y := by{
  simp[fband]
}
theorem subset_fband {p : List α} {x : α} : x ∈ p → x ∈ H.fband p :=by{
  intro h
  unfold fband
  simp only [List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq]
  use x
  simp only [h, true_and]
  apply ReflTransGen.refl
}
theorem fband_closure {p : List α} {x : α} (hx : x ∈ H.fband p) : H.face x ∈ H.fband p:=by{
  unfold fband at *
  simp only [List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at *
  have ⟨k, hk⟩:=hx
  use k
  apply hk.imp_right
  intro hk'
  apply (ReflTransGen.trans · hk')
  apply cface_Symm.symm
  apply ReflTransGen.single
  simp[fromFun]
}
def kernel (H : Hypermap α) (p : List α) : Set α := Set.compl (H.fband p)
noncomputable def fproj (H : Hypermap α) (p : List α) (x : α) : α :=
  /- first y in intersection of p and the face x lies in -/
  /- usually p is simple, so y is unique -/
  /- if intersection is empty, return  -/
  match p.find? (H.cface x) with
  | some y => y
  | none => Quotient.out (Quotient.mk H.fsetoid x)
theorem fproj_cface {p : List α} {x : α} :
  H.cface x (H.fproj p x) := by{
    match hf : p.find? (H.cface x) with
    | some y => {
      unfold fproj
      simp only [hf]
      rw[List.find?_eq_some_iff_append] at hf
      simp at hf
      exact hf.left
    }
    | none => {
      unfold fproj
      simp only [hf]
      apply H.cface_equivalence.symm
      have h:=Quotient.mk_out (s:=H.fsetoid) x
      unfold fsetoid at h
      simp only at h
      exact h
    }
  }
theorem fproj_spec_of_mem_hband {p : List α} {x : α} (hx : x ∈ H.fband p)
  : H.fproj p x ∈ p := by{
    have h:(p.find? (H.cface x)).isSome:=by{
      simp only [List.find?_isSome, decide_eq_true_eq]
      unfold fband at hx
      simp only [List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at hx
      exact hx
    }
    have ⟨y, hy⟩:∃y, p.find? (H.cface x) = some y:=Option.isSome_iff_exists.mp h
    unfold fproj
    simp only [hy]
    rw[List.find?_eq_some_iff_append] at hy
    simp at hy
    have ⟨_, ⟨_, hy'⟩, _⟩:=hy.right
    rw[hy']
    simp
  }
def simpleList (H : Hypermap α) (p : List α) := (p.map (Quotient.mk H.fsetoid)).Nodup
theorem nodup_of_simpleList {p : List α} (hp : H.simpleList p) : p.Nodup := by{
  unfold simpleList at hp
  exact List.Nodup.of_map _ hp
}
def simpleList.rec_def (H : Hypermap α) : List α → Prop
| [] => True
| x :: p => x ∉ H.fband p ∧ Hypermap.simpleList.rec_def H p
theorem simpleList.rec_def_iff {p : List α}
  : Hypermap.simpleList.rec_def H p ↔ H.simpleList p := by{
    induction p with
    | nil => simp[rec_def, simpleList]
    | cons x p' ih => {
      simp only [rec_def, ih, simpleList, List.map_cons, List.nodup_cons, List.mem_map, not_exists,
        not_and, and_congr_left_iff, fband, Set.mem_setOf, List.any_eq_true, decide_eq_true_eq,
        not_exists, not_and, Quotient.eq_iff_equiv, H.cface_equivalence.comm (a:=x)]
      intro _
      rfl
    }
  }
theorem simpleList_nil : H.simpleList [] := by{simp[simpleList]}
theorem simpleList_cons {x : α} {p : List α} : H.simpleList (x :: p) ↔
  x ∉ H.fband p ∧ H.simpleList p := by{
    rw[← simpleList.rec_def_iff]
    unfold simpleList.rec_def
    rw[simpleList.rec_def_iff]
  }
def simpleCycle (H : Hypermap α) (e : α → α → Prop) (p : List α) :=
  p.IsCycleChain e ∧ H.simpleList p
theorem simpleCycle.cycle {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.IsCycleChain e := h.left
theorem simpleCycle.simple {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  H.simpleList p := h.right
theorem simpleCycle.chain {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.IsChain e := h.cycle.isChain
theorem simpleCycle.nodup {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.Nodup := nodup_of_simpleList h.simple

def rlink (H : Hypermap α) : α → α → Prop := fun x y => H.cface (edge x) y
theorem rlink_edge {x : α} : H.rlink x (edge x) := by{
  simp[rlink, cface, funReflTransGen.refl]
}
theorem rlink_right_congr_of_cface {y1 y2 : α} (h12 : H.cface y1 y2) {x : α}
  : H.rlink x y1 ↔ H.rlink x y2 := by{
    simp[rlink, H.cface_equivalence.comm (a:=edge x), H.cface_pred_eq_of_cface h12]
  }

def adj (H : Hypermap α) := fun x y => ∃z, H.cface x z ∧ H.rlink z y
theorem adj_of_rlink {x y : α} (hxy : H.rlink x y) : H.adj x y :=
  ⟨x, ReflTransGen.refl, hxy⟩
theorem adj_edge {x : α} : H.adj x (edge x) :=
  H.adj_of_rlink H.rlink_edge
theorem adj_left_congr_of_cface {x y : α} (hxy : H.cface x y) : H.adj x = H.adj y := by{
  ext z
  simp only [adj]
  constructor
  all_goals
  intro ⟨z, hz0, hz1⟩
  refine ⟨z, ?_, hz1⟩
  try exact (H.cface_equivalence.symm hxy).trans hz0
  try exact hxy.trans hz0
}
theorem adj_right_congr_of_cface {x y : α} (hxy : H.cface x y) {z : α} : H.adj z x = H.adj z y
:= by{
  simp only [adj]
  ext
  constructor
  all_goals
  intro ⟨z, hz0, hz1⟩
  refine ⟨z, hz0, ?_⟩
  try rw[H.rlink_right_congr_of_cface hxy]; exact hz1
  try rw[H.rlink_right_congr_of_cface (H.cface_equivalence.symm hxy)]; exact hz1
}
theorem face_adj_iff {x y : α} : H.adj (face x) y ↔ H.adj x y := by{
  symm
  rw[adj_left_congr_of_cface]
  apply funReflTransGen.single
}
theorem adj_face_iff {x y : α} : H.adj x (face y) ↔ H.adj x y := by{
  symm
  rw[adj_right_congr_of_cface]
  apply funReflTransGen.single
}
theorem node_adj {x : α} : H.adj (node x) x := by{
  nth_rw 2 [← H.fen_cancel x]
  rw[H.adj_face_iff]
  apply adj_edge
}

def chordless (H : Hypermap α) (r : List α) :=
  let non_adj_r := fun x y => ∃(h : x ∈ r), y ≠ r.prev x h ∧ y ≠ r.next x h
  ∀x ∈ r, Disjoint {y | H.adj x y} {y | non_adj_r x y}
@[simp] theorem chordless_nil : H.chordless [] := by{simp[chordless]}
theorem chordless_rotate {r : List α} {n : ℕ} (hr : r.Nodup)
: H.chordless (r.rotate n) ↔ H.chordless r := by{
  suffices H : ∀r n, r.Nodup → H.chordless (r.rotate n) → H.chordless r by{
    constructor
    · apply H; exact hr
    nth_rw 1 [← List.rotate_length r]
    rw[← List.rotate_mod r n]
    rcases eq_or_ne r [] with hrn | hrn
    · simp[hrn]
    nth_rw 1 [← Nat.sub_add_cancel (le_of_lt (Nat.mod_lt n (List.length_pos_of_ne_nil hrn)))]
    rw[Nat.add_comm, ← List.rotate_rotate]
    apply H
    rw[List.nodup_rotate]
    exact hr
  }
  intro r n hr hrc
  unfold chordless at *
  simp only [Set.disjoint_iff, Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem,
  Set.mem_inter_iff, Set.mem_setOf]; push_neg
  simp only[Set.disjoint_iff, Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem,
  Set.mem_inter_iff, Set.mem_setOf] at hrc; push_neg at hrc
  intro x hx
  have ihp := List.isRotated_prev_eq (l := r) (l' := r.rotate n)
    (List.IsRotated.symm (List.IsRotated.forall _ _)) hr hx
  have ihn := List.isRotated_next_eq (l := r) (l' := r.rotate n)
    (List.IsRotated.symm (List.IsRotated.forall _ _)) hr hx
  simp only [List.mem_rotate] at hrc
  specialize hrc x hx
  simp only [hx, ne_eq, forall_true_left, ← ihp, ← ihn] at hrc
  simp only [hx, forall_true_left]
  exact hrc
}
theorem chordless_def {r : List α} :
  H.chordless r ↔
  ∀x, (h: x ∈ r) → ∀y, H.adj x y → y ≠ r.prev x h → y = r.next x h
  := by{
  unfold chordless
  simp only [Set.disjoint_iff, Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem,
  Set.mem_inter_iff, Set.mem_setOf]; push_neg
  constructor
  · intro ih x h y hxy; exact ih x h y hxy h
  · intro ih x h y hxy _; exact ih x h y hxy
}

def plainSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.edge x = 2}}
def plain (H : Hypermap α) := Set.univ ∈ H.plainSubset
theorem plain_iff_edge_edge : H.plain ↔ ∀x, H.edge (H.edge x) = x ∧ H.edge x ≠ x:=by{
  unfold plain plainSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_two_iff]
}
def cubicSubset (H : Hypermap α) : Set (Set α) := { s | s ⊆ {x | minimalPeriod H.node x = 3}}
def cubic (H : Hypermap α) := Set.univ ∈ H.cubicSubset
def precubicSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.node x ≤ 3}}
def precubic (H : Hypermap α) := Set.univ ∈ H.precubicSubset
theorem cubic_iff_node_node_node : H.cubic ↔ ∀x, H.node (H.node (H.node x)) = x ∧ H.node x ≠ x:=by{
  unfold cubic cubicSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_three_iff]
}
theorem cubicSubset_subset_precubicSubset : H.cubicSubset ⊆ H.precubicSubset := by{
  intro x h
  unfold cubicSubset at h
  unfold precubicSubset
  simp only [Set.mem_setOf] at h
  simp only [Set.mem_setOf]
  intro a ha
  simp only [Set.mem_setOf]
  have h':=h ha
  simp only [Set.mem_setOf] at h'
  rw[h']
}

structure PlanarBridgeless : Prop where
  planar : H.planar
  bridgeless : H.bridgeless
structure PlainCubic : Prop where
  plain : H.plain
  cubic : H.cubic
structure PlainCubicConnected : Prop extends H.PlainCubic where
  connected : H.connected
structure PlanarPlainCubicConnected : Prop extends H.PlainCubicConnected where
  planar : H.planar
structure PlainCubicPentagonal : Prop extends H.PlainCubic where
  pentagonal : H.pentagonal
structure PlanarBridgelessPlain : Prop extends H.PlanarBridgeless where
  plain : H.plain
structure PlanarBridgelessPlainConnected : Prop extends H.PlanarBridgelessPlain where
  connected : H.connected
structure PlanarBridgelessPlainPrecubic : Prop extends H.PlanarBridgelessPlain where
  precubic : H.precubic


section plain

theorem plain.cedge_cases (hp : H.plain) {x y : α} (hxy : H.cedge x y)
  : x = y ∨ edge x = y := by{
    rw[cedge, funReflTransGen_iff_iterate] at hxy
    have ⟨n, hn⟩:=hxy
    clear hxy
    rw[plain_iff_edge_edge] at hp
    induction n generalizing x with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      specialize ih hn
      rw[(hp x).left] at ih
      exact Or.symm ih
    }
  }
theorem plain.cedge_cases_iff (hp : H.plain) {x y : α}
  : H.cedge x y ↔ x = y ∨ edge x = y := by{
    apply Iff.intro hp.cedge_cases
    intro h
    rcases h with h | h
    · rw[h]; apply ReflTransGen.refl
    · rw[← h]; apply funReflTransGen.single
  }
theorem plain.cedge_cases'_iff (hp : H.plain) {x y : α}
  : H.cedge x y ↔ x = y ∨ x = edge y := by{
    rw[hp.cedge_cases_iff]
    apply or_congr_right
    nth_rw 1 [← edge_inj]
    rw[plain_iff_edge_edge] at hp
    rw[(hp x).left]
  }
theorem plain.cedge_cases' (hp : H.plain) {x y : α} (hxy : H.cedge x y)
  : x = y ∨ x = edge y := hp.cedge_cases'_iff.mp hxy

theorem plain.equotient_lemma (hP : H.plain) (x : α) : (∃q : Quotient H.esetoid, q.out = x)
↔ ¬∃q : Quotient H.esetoid, edge (q.out) = x := by{
  have hP' := hP
  rw[plain_iff_edge_edge] at hP
  constructor
  · {
    intro ⟨q0, hq0⟩ ⟨q1, hq1⟩
    have hQ : q0 = q1 := by{
      rw[← Quotient.out_equiv_out]
      change H.cedge q0.out q1.out
      rw[← edge_inj, (hP q1.out).left] at hq1
      rw[hq0, hq1]
      apply funReflTransGen.single
    }
    rw[← hQ, ← hq0] at hq1
    exact (hP q0.out).right hq1
  }
  · {
    intro h
    rw[not_exists] at h
    specialize h ⟦edge x⟧
    use ⟦edge x⟧
    have h0 : H.cedge ⟦edge x⟧.out x := by{
      have h0 : H.cedge ⟦edge x⟧.out (edge x) := by{
        have h0 := Quotient.mk_out (s := H.esetoid) (edge x)
        exact h0
      }
      apply H.cedge_equivalence.trans h0
      apply H.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    rw[hP'.cedge_cases_iff] at h0
    exact h0.resolve_right h
  }
}

theorem plain.ecomp_double (hP : H.plain) : Fintype.card α = H.ecomp * 2 := by{
  have hP' := hP
  rw[plain_iff_edge_edge] at hP
  let q1 := {x // ∃q : Quotient H.esetoid, q.out = x}
  let q2 := {x // ∃q : Quotient H.esetoid, edge (q.out) = x}
  let q1fin : Fintype q1 := inferInstance
  let q2fin : Fintype q2 := inferInstance
  let q12e : q1 ≃ q2 := by{
    let f : q1 → q2 := fun ⟨x, hx⟩ => ⟨edge x, by{
      have ⟨q, hq⟩:=hx; use q; rw[hq]
    }⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro ⟨x0, hx0⟩ ⟨x1, hx1⟩ hx01
      rw[Subtype.ext_iff] at hx01
      rw[Subtype.ext_iff]
      simp only [f, edge_inj] at hx01
      simp[hx01]
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use ⟨edge x, ⟨q, by{rw[←hq, (hP q.out).left]}⟩⟩
      simp[f, hP x]
    }
  }
  have hq1e : H.ecomp = Fintype.card q1 := by{
    apply Fintype.card_congr
    let f : Quotient H.esetoid → q1 := fun q => ⟨q.out, ⟨q, rfl⟩⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro Q0 Q1 hQ
      simp only [f] at hQ
      rw[Subtype.ext_iff] at hQ
      simp only [Quotient.out_inj] at hQ
      exact hQ
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use q
      simp only [f, hq]
    }
  }
  have hq12e := Fintype.card_congr q12e
  rw[hq1e, mul_two]
  nth_rw 2 [hq12e]
  rw[← Fintype.card_sum]
  apply Fintype.card_congr
  let f : α → q1 ⊕ q2 := fun x => by{
    let inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
    match inst with
    | isTrue hq => exact Sum.inl ⟨x, hq⟩
    | isFalse hq => {
      have hq' : ∃q : Quotient H.esetoid, edge (q.out) = x := by{
        rw[hP'.equotient_lemma, not_not] at hq
        exact hq
      }
      exact Sum.inr ⟨x, hq'⟩
    }
  }
  apply Equiv.ofBijective f
  constructor
  · {
    intro x0 x1 hx01
    unfold f at hx01
    set inst0 : Decidable (∃q : Quotient H.esetoid, q.out = x0) := inferInstance
    set inst1 : Decidable (∃q : Quotient H.esetoid, q.out = x1) := inferInstance
    match inst0, inst1 with
    | isFalse _, isTrue _ | isTrue _, isFalse _ => simp at hx01
    | isTrue _, isTrue _ | isFalse _, isFalse _ => {
      simp only [Sum.inl.injEq, Sum.inr.injEq] at hx01; rw[Subtype.ext_iff] at hx01; exact hx01
    }
  }
  · {
    intro x'
    match x' with
    | Sum.inl ⟨x, hx⟩ => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
      simp only
      match inst with
      | isTrue hp => simp
      | isFalse hp => contradiction
    }
    | Sum.inr ⟨x, hx⟩ => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
      simp only
      match inst with
      | isTrue hp => {
        rw[hP'.equotient_lemma] at hp
        contradiction
      }
      | isFalse hp => simp only
    }
  }
}
theorem plain.edge_edge (hp : H.plain) {p : α} : H.edge (H.edge p) = p := by{
  rw[plain_iff_edge_edge] at hp
  rw[(hp p).left]
}
theorem plain.edgeinv_eq_edge (hp : H.plain) : H.edgeinv = H.edge := by{
  ext x
  rw[← edge_inj, edgeinv_rightinv, hp.edge_edge]
}
end plain

section cubic
theorem cubic_iff_period_three : H.cubic ↔ ∀x, H.node (H.node (H.node x)) = x ∧ H.node x ≠ x := by{
  unfold cubic cubicSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_three_iff]
}
theorem not_idemp_of_cubic (hc : H.cubic) {x : α} : H.node x ≠ x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).right
}
theorem period_three_of_cubic (hc : H.cubic) {x : α} : H.node (H.node (H.node x)) = x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).left
}
theorem not_invol_of_cubic (hc : H.cubic) {x : α} : H.node (H.node x) ≠ x := by{
  rw[cubic_iff_period_three] at hc
  intro h
  have h' := (hc x).left
  rw[h] at h'
  exact (hc x).right h'
}
end cubic
end Hypermap
