import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Hypermap.Actions.Perm

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def skip_edge'' (H : Hypermap α) (x : α) : α → α :=
  fun z =>
    if H.edge x = x then H.edge z else
    if H.face (H.edge z) = x then H.edge x else
    if H.edge z = x then H.edge (H.node x) else H.edge z
lemma skip_edge''_subproof {x : α} {u : {a // a ≠ x}}
  : H.skip_edge'' x u ≠ x:=by{
    unfold skip_edge''
    cases em (edge x = x) with
    | inl hx => {
      simp only [hx, ↓reduceIte, ne_eq]
      nth_rw 2 [←hx]
      rw[H.edge_injective.eq_iff]
      exact u.prop
    }
    | inr hx => {
      simp only [hx, ↓reduceIte, ne_eq]
      cases em (H.face (H.edge u.val) = x) with
      | inl hfeu => simp[hfeu, hx]
      | inr hfeu => {
        simp only [hfeu, ↓reduceIte]
        cases em (H.edge u = x) with
        | inl heu => {
          simp only [heu, ↓reduceIte]
          intro hen
          apply hfeu
          rw[heu]
          have hen':=congrArg H.face hen
          rw[fen_cancel] at hen'
          exact hen'.symm
        }
        | inr heu => simp[heu]
      }
    }
  }
def skip_edge' (H : Hypermap α) (x : α) : {a // a ≠ x} → {a // a ≠ x} :=
  fun u => ⟨H.skip_edge'' x u, H.skip_edge''_subproof⟩
lemma skip_edge'_cancel {x : α} : ∀z:{a // a ≠ x}, H.skip_edge' x
  (skip H.node_injective x (skip H.face_injective x z)) = z:=by{
    intro ⟨z, hz⟩
    cases em (H.face z = x) with
    | inl hfz => {
      rw[skip_eq_of_apply_eq H.face_injective hfz]
      simp only
      cases em (H.node (H.face (H.face z)) = x) with
      | inl hnffz => {
        rw[skip_eq_of_apply_eq H.node_injective hnffz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hnffz':H.face z = H.edge x:=by{
          have hnffz':=congrArg H.edge hnffz
          rw[enf_cancel] at hnffz'
          exact hnffz'
        }
        have hex:=hnffz'.symm.trans hfz
        unfold skip_edge''
        simp[hex]
        simp[hnffz', nfe_cancel]
        simp[←hfz, enf_cancel]
      }
      | inr hnffz => {
        rw[skip_eq_of_apply_ne H.node_injective hnffz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hnffz':H.face z ≠ H.edge x:=by{
          intro hnffz'
          apply hnffz
          apply H.edge_injective
          rw[enf_cancel]
          exact hnffz'
        }
        have hex:=Ne.symm (hfz ▸ hnffz')
        unfold skip_edge''
        have hfx:H.face x ≠ x:=by{
          intro h
          apply hz
          have h':=hfz.trans h.symm
          exact H.face_injective h'
        }
        simp only [hex, ↓reduceIte, hfz, enf_cancel, hfx]
        rw[←hfz, enf_cancel]
      }
    }
    | inr hfz => {
      rw[skip_eq_of_apply_ne H.face_injective hfz]
      simp only
      cases em (H.node (H.face z) = x) with
      | inl hnfz => {
        rw[skip_eq_of_apply_eq H.node_injective hnfz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hex:H.edge x ≠ x:=by{
          have hnfz':=congrArg H.edge hnfz
          rw[enf_cancel] at hnfz'
          rw[←hnfz']
          exact hz
        }
        unfold skip_edge''
        simp only [hex, ↓reduceIte, hnfz, fen_cancel]
        rw[←hnfz, enf_cancel]
      }
      | inr hnfz => {
        rw[skip_eq_of_apply_ne H.node_injective hnfz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        unfold skip_edge''
        rw[enf_cancel]
        simp[hfz, hz]
      }
    }
}
theorem skip_edge'_eq_of_glink {x : α} (hx : H.glink x x) : H.skip_edge' x =
  skip H.edge_injective x:=by{
  unfold glink at hx
  repeat rw[union_iff] at hx
  unfold fromFun at hx
  ext ⟨z, hz⟩
  unfold skip_edge' skip_edge''
  simp only [ne_eq]
  cases em (H.edge z = x) with
  | inl hzx => {
    rw[skip_eq_of_apply_eq H.edge_injective hzx]
    simp only [hzx, ↓reduceIte]
    cases hx with
    | inl hx => simp[hx]
    | inr hx => cases hx with
      | inl hx => simp only [hx, ite_self, ite_eq_right_iff]; exact Eq.symm
      | inr hx => simp only [hx, ite_eq_right_iff, ite_true]; exact Eq.symm
  }
  | inr hzx => {
    rw[skip_eq_of_apply_ne H.edge_injective hzx]
    simp only [hzx, ↓reduceIte, ite_eq_left_iff, ite_eq_right_iff]
    intro hex
    simp only [hex, false_or] at hx
    simp only [H.edge_injective.eq_iff, hz.symm, imp_false]
    intro hfez
    cases hx with
    | inl hx => {
      have hfez':=congrArg H.node hfez
      rw[nfe_cancel] at hfez'
      exact hz (hfez'.trans hx)
    }
    | inr hx => {
      have hfez':=hfez.trans hx.symm
      rw[H.face_inj] at hfez'
      contradiction
    }
  }
}
theorem skip_edge'_val {x : α} {u : {a // a ≠ x}}
  : (H.skip_edge' x u).val = H.skip_edge'' x u:=by{
    unfold skip_edge'
    simp
}
@[reducible] def WalkupE (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  ⟨H.skip_edge' x, skip H.node_injective x, skip H.face_injective x, skip_edge'_cancel⟩

theorem walkupe_edge {x : α} : (H.WalkupE x).edge = H.skip_edge' x:=rfl
theorem walkupe_node {x : α} : (H.WalkupE x).node = skip H.node_injective x:=rfl
theorem walkupe_face {x : α} : (H.WalkupE x).face = skip H.face_injective x:=rfl

theorem walkupe_nodeinv {x : α} : (H.WalkupE x).nodeinv = skip H.nodeinv_injective x:=by{
  rw[nodeinv, ←Fintype.skip_bijInv_comm H.node_bijective]
  congr
}
theorem walkupe_faceinv {x : α} : (H.WalkupE x).faceinv = skip H.faceinv_injective x:=by{
  rw[faceinv, ←Fintype.skip_bijInv_comm H.face_bijective]
  congr
}

def cross_edge (H : Hypermap α) (x : α) := H.cedge x (H.node x)
@[inline] instance cross_edge.decidable : DecidablePred H.cross_edge := fun x =>
  (inferInstance : DecidableRel H.cedge) x (H.node x)

def isbarb (H : Hypermap α) (x : α) := {y | H.clink x y} ⊆ {x}
theorem isbarb_iff_all_perm_self {x : α}
  : H.isbarb x ↔ H.edge x = x ∧ H.node x = x ∧ H.face x = x:=by{
    unfold isbarb
    rw[Set.subset_singleton_iff]
    simp only [Set.mem_setOf_eq]
    unfold clink
    simp only [union_iff]
    unfold fromFun
    rw[nodeinv_eq, comp_apply]
    constructor
    · {
      intro hy
      have hy':=hy _ (Or.inl rfl)
      have hy'':=hy _ (Or.inr rfl)
      simp only [hy'', and_true]
      nth_rw 3 [←hy']
      rw[nfe_cancel]
      simp only [and_true]
      have hy''':=hy'.trans hy''.symm
      rw[H.face_inj] at hy'''
      exact hy'''
    }
    · {
      intro ⟨he, hn, hf⟩ y
      simp only [hf, Eq.comm (a:=y)]
      nth_rw 1 [←hn]
      rw[fen_cancel, or_self]
      exact id
    }
  }
@[inline] instance isbarb.instDecidable : DecidablePred H.isbarb := by{
  intro x
  simp only [isbarb_iff_all_perm_self]
  infer_instance
}

@[reducible] def WalkupN (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  (H.permN.WalkupE x).permF
@[reducible] def WalkupF (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  (H.permF.WalkupE x).permN
end Hypermap
