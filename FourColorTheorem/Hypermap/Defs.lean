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
theorem cedge_edge {x : α} : H.cedge (edge x) = H.cedge x := by{
  apply H.cedge_pred_eq_of_cedge
  apply cedge_equivalence.symm
  apply funReflTransGen.single
}
theorem cnode_node {x : α} : H.cnode (node x) = H.cnode x := by{
  apply H.cnode_pred_eq_of_cnode
  apply cnode_equivalence.symm
  apply funReflTransGen.single
}
theorem cface_face {x : α} : H.cface (face x) = H.cface x := by{
  apply H.cface_pred_eq_of_cface
  apply cface_equivalence.symm
  apply funReflTransGen.single
}

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
theorem cglink_pred_eq_of_cglink {x y : α} (hxy : H.cglink x y)
  : H.cglink x = H.cglink y := cglink_equivalence.pred_eq_iff.mpr hxy

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
theorem edgeinv_apply {x : α}:H.edgeinv x = node (face x):=by{
  simp[edgeinv_eq]
}
theorem nodeinv_apply {x : α}:H.nodeinv x = face (edge x):=by{
  simp[nodeinv_eq]
}
theorem faceinv_apply {x : α}:H.faceinv x = edge (node x):=by{
  simp[faceinv_eq]
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
lemma cnf_eq_cenf:ReflTransGen (H.cnode ∪ H.cface)
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
theorem cclink_equivalence : Equivalence H.cclink := by{
  rw[cclink_iff_cglink]
  exact cglink_equivalence
}

@[reducible] def esetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cedge_equivalence
@[reducible] def nsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cnode_equivalence
@[reducible] def fsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cface_equivalence
@[reducible] def gsetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cglink_equivalence
@[reducible] def csetoid (H : Hypermap α) : Setoid α := Setoid.mk _ H.cclink_equivalence
@[inline] instance esetoid.instDecidable : DecidableRel H.esetoid := ReflTransGen.finDec
@[inline] instance nsetoid.instDecidable : DecidableRel H.nsetoid := ReflTransGen.finDec
@[inline] instance fsetoid.instDecidable : DecidableRel H.fsetoid := ReflTransGen.finDec
@[inline] instance gsetoid.instDecidable : DecidableRel H.gsetoid := ReflTransGen.finDec
@[inline] instance csetoid.instDecidable : DecidableRel H.csetoid := ReflTransGen.finDec
theorem csetoid_eq_gsetoid {H : Hypermap α} : H.csetoid = H.gsetoid := by{
  ext
  unfold csetoid gsetoid
  simp[cclink_iff_cglink]
}

def ecomp (H : Hypermap α) := Fintype.nComp H.esetoid
def ncomp (H : Hypermap α) := Fintype.nComp H.nsetoid
def fcomp (H : Hypermap α) := Fintype.nComp H.fsetoid
def gcomp (H : Hypermap α) := Fintype.nComp H.gsetoid
def connected (H : Hypermap α) : Prop := H.gcomp = 1

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

def kernel (H : Hypermap α) (p : List α) : Set α := Set.compl (H.fband p)
noncomputable def fproj (H : Hypermap α) (p : List α) (x : α) : α :=
  /- first y in intersection of p and the face x lies in -/
  /- usually p is simple, so y is unique -/
  /- if intersection is empty, return  -/
  match p.find? (H.cface x) with
  | some y => y
  | none => Quotient.out (Quotient.mk H.fsetoid x)

def simpleList (H : Hypermap α) (p : List α) := (p.map (Quotient.mk H.fsetoid)).Nodup
theorem simpleList.nodup {p : List α} (hp : H.simpleList p) : p.Nodup := by{
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
def simpleCycle (H : Hypermap α) (e : α → α → Prop) (p : List α) :=
  p.IsCycleChain e ∧ H.simpleList p
theorem simpleCycle.cycle {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.IsCycleChain e := h.left
theorem simpleCycle.simple {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  H.simpleList p := h.right
theorem simpleCycle.chain {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.IsChain e := h.cycle.isChain
theorem simpleCycle.nodup {e : α → α → Prop} {p : List α} (h : H.simpleCycle e p) :
  p.Nodup := h.simple.nodup

def rlink (H : Hypermap α) : α → α → Prop := fun x y => H.cface (edge x) y
def adj (H : Hypermap α) := fun x y => ∃z, H.cface x z ∧ H.rlink z y
theorem adj_of_rlink {x y : α} (hxy : H.rlink x y) : H.adj x y :=
  ⟨x, ReflTransGen.refl, hxy⟩

def chordless (H : Hypermap α) (r : List α) :=
  let non_adj_r := fun x y => ∃(h : x ∈ r), y ≠ r.prev x h ∧ y ≠ r.next x h
  ∀x ∈ r, Disjoint {y | H.adj x y} {y | non_adj_r x y}
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

end Hypermap
