import FourColorTheorem.Hypermap.Actions.Walkup.Skip

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def edge_affect_set (H : Hypermap α) (x : α) := {y : α | H.cedge x y ∨ H.cedge (H.node x) y}
@[inline] instance edge_affect_set.instDecidableMem {x y : α}
  : Decidable (y ∈ H.edge_affect_set x) := by{
    unfold edge_affect_set
    rw[Set.mem_setOf]
    infer_instance
  }
theorem mem_edge_affect_set_iff {x y : α}
: y ∈ H.edge_affect_set x ↔ H.cedge x y ∨ H.cedge (H.node x) y
:= by{
  unfold edge_affect_set
  rw[Set.mem_setOf]
}
theorem self_mem_edge_affect_set {x : α}
  : x ∈ H.edge_affect_set x := by{
    simp[mem_edge_affect_set_iff, cedge_equivalence.refl]
  }
theorem node_mem_edge_affect_set {x : α}
  : H.node x ∈ H.edge_affect_set x := by{
    simp[mem_edge_affect_set_iff, cedge_equivalence.refl]
  }
theorem edge_mem_edge_affect_set {x : α}
  : H.edge x ∈ H.edge_affect_set x := by{
    simp only [mem_edge_affect_set_iff, cedge, funReflTransGen]
    left
    exact ReflTransGen.single rfl
  }
theorem edgeinv_mem_edge_affect_set {x : α}
  : H.edgeinv x ∈ H.edge_affect_set x := by{
    simp only [mem_edge_affect_set_iff]
    rw[cedge_equivalence.symmetric.iff]
    left
    apply ReflTransGen.single
    simp[fromFun, edgeinv_eq, enf_cancel]
  }
def edge_affect_subtype (H : Hypermap α) (x : α) :=
  {a // a ∈ H.edge_affect_set x}
def edge_affect_compl_subtype (H : Hypermap α) (x : α) :=
  {a // a ∉ H.edge_affect_set x}
def edge_affect_walkupe_subtype (H : Hypermap α) (x : α) :=
  {a : {a // a ≠ x} // a.val ∈ H.edge_affect_set x}
def edge_affect_walkupe_compl_subtype (H : Hypermap α) (x : α) :=
  {a : {a // a ≠ x} // a.val ∉ H.edge_affect_set x}
@[inline] instance edge_affect_subtype.fintype : Fintype (H.edge_affect_subtype x) := by{
  unfold edge_affect_subtype
  apply Subtype.fintype
}
@[inline] instance edge_affect_compl_subtype.fintype
: Fintype (H.edge_affect_compl_subtype x) := by{
  unfold edge_affect_compl_subtype
  apply Subtype.fintype
}
@[inline] instance edge_affect_walkupe_subtype.fintype
: Fintype (H.edge_affect_walkupe_subtype x) := by{
  unfold edge_affect_walkupe_subtype
  apply Subtype.fintype
}
@[inline] instance edge_affect_walkupe_compl_subtype.fintype
: Fintype (H.edge_affect_walkupe_compl_subtype x) := by{
  unfold edge_affect_walkupe_compl_subtype
  apply Subtype.fintype
}
@[inline] instance edge_affect_subtype.decEq {x : α}
: DecidableEq (H.edge_affect_subtype x) := by{
  unfold edge_affect_subtype
  infer_instance
}
@[inline] instance edge_affect_compl_subtype.decEq {x : α}
: DecidableEq (H.edge_affect_compl_subtype x) := by{
  unfold edge_affect_compl_subtype
  infer_instance
}
@[inline] instance edge_affect_walkupe_subtype.decEq {x : α}
: DecidableEq (H.edge_affect_walkupe_subtype x) := by{
  unfold edge_affect_walkupe_subtype
  infer_instance
}
@[inline] instance edge_affect_walkupe_compl_subtype.decEq {x : α}
: DecidableEq (H.edge_affect_walkupe_compl_subtype x) := by{
  unfold edge_affect_walkupe_compl_subtype
  infer_instance
}

def edge_affect_esetoid (H : Hypermap α) (x : α) : Setoid (H.edge_affect_subtype x)
  := H.esetoid.ofSubtype (· ∈ H.edge_affect_set x)
@[inline] instance edge_affect_esetoid.decidable
: DecidableRel (H.edge_affect_esetoid x) := by{
  unfold edge_affect_esetoid
  apply Setoid.ofSubtype.decidable
}
theorem edge_affect_esetoid_iff_cedge {x : α} {u v : H.edge_affect_subtype x}
  : H.edge_affect_esetoid x u v ↔ H.cedge u.val v.val:=by{
    unfold edge_affect_esetoid
    have h:=@Setoid.ofSubtype_iff α (· ∈ H.edge_affect_set x) H.esetoid u v
    nth_rw 2 [esetoid] at h
    simp only at h
    exact h
  }
def edge_affect_compl_esetoid (H : Hypermap α) (x : α) : Setoid (H.edge_affect_compl_subtype x)
  := H.esetoid.ofSubtype (· ∉ H.edge_affect_set x)
@[inline] instance edge_affect_compl_esetoid.decidable
: DecidableRel (H.edge_affect_compl_esetoid x) := by{
  unfold edge_affect_compl_esetoid
  apply Setoid.ofSubtype.decidable
}
theorem edge_affect_compl_esetoid_iff_cedge {x : α} {u v : H.edge_affect_compl_subtype x}
  : H.edge_affect_compl_esetoid x u v ↔ H.cedge u.val v.val:=by{
    unfold edge_affect_compl_esetoid
    have h:=@Setoid.ofSubtype_iff α (· ∉ H.edge_affect_set x) H.esetoid u v
    nth_rw 2 [esetoid] at h
    simp only at h
    exact h
  }
def edge_affect_walkupe_esetoid (H : Hypermap α) (x : α) : Setoid (H.edge_affect_walkupe_subtype x)
  := (H.WalkupE x).esetoid.ofSubtype (Subtype.val · ∈ H.edge_affect_set x)
@[inline] instance edge_affect_walkupe_esetoid.decidable
: DecidableRel (H.edge_affect_walkupe_esetoid x) := by{
  unfold edge_affect_walkupe_esetoid
  apply Setoid.ofSubtype.decidable
}
theorem edge_affect_walkupe_esetoid_iff_cedge {x : α} {u v : H.edge_affect_walkupe_subtype x}
  : H.edge_affect_walkupe_esetoid x u v ↔ (H.WalkupE x).cedge u.val v.val:=by{
    unfold edge_affect_walkupe_esetoid
    have h:=@Setoid.ofSubtype_iff _ (Subtype.val · ∈ H.edge_affect_set x) (H.WalkupE x).esetoid u v
    nth_rw 2 [esetoid] at h
    simp only at h
    exact h
  }
def edge_affect_walkupe_compl_esetoid (H : Hypermap α) (x : α)
: Setoid (H.edge_affect_walkupe_compl_subtype x)
  := (H.WalkupE x).esetoid.ofSubtype (Subtype.val · ∉ H.edge_affect_set x)
@[inline] instance edge_affect_walkupe_compl_esetoid.decidable
: DecidableRel (H.edge_affect_walkupe_compl_esetoid x) := by{
  unfold edge_affect_walkupe_compl_esetoid
  apply Setoid.ofSubtype.decidable
}
theorem edge_affect_walkupe_compl_esetoid_iff_cedge {x : α}
{u v : H.edge_affect_walkupe_compl_subtype x}
  : H.edge_affect_walkupe_compl_esetoid x u v ↔ (H.WalkupE x).cedge u.val v.val:=by{
    unfold edge_affect_walkupe_compl_esetoid
    have h:=@Setoid.ofSubtype_iff _ (Subtype.val · ∉ H.edge_affect_set x) (H.WalkupE x).esetoid u v
    nth_rw 2 [esetoid] at h
    simp only at h
    exact h
  }
def edge_affect_ecomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.edge_affect_esetoid x)
def edge_affect_compl_ecomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.edge_affect_compl_esetoid x)
def edge_affect_walkupe_ecomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.edge_affect_walkupe_esetoid x)
def edge_affect_walkupe_compl_ecomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.edge_affect_walkupe_compl_esetoid x)
theorem walkupe_cedge_node_of_mem_edge_affect_set_of_not_crossedge {x : α}
  {u : {a // a ≠ x}} (hux : u.val ∈ H.edge_affect_set x) (hx : ¬H.cross_edge x)
  : (H.WalkupE x).cedge u ⟨H.node x, not_node_self_of_not_cross_edge hx⟩
  := by{
    simp[mem_edge_affect_set_iff] at hux
    exact hux.elim ((walkupe_cedge_node_of_cedge_of_not_crossedge · hx)
    ∘ cedge_equivalence.symm)
      ((walkupe_cedge_node_of_cedge_node_of_not_crossedge · hx)
    ∘ cedge_equivalence.symm)
  }
theorem edge_affect_walkupe_subtype_walkupe_cedge_node_of_not_crossedge {x : α}
  {u : H.edge_affect_walkupe_subtype x} (hx : ¬H.cross_edge x)
  : (H.WalkupE x).cedge u.val ⟨H.node x, not_node_self_of_not_cross_edge hx⟩
  :=
    walkupe_cedge_node_of_mem_edge_affect_set_of_not_crossedge u.prop hx
theorem walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_mem_edge_affect_set {x : α}
  {u : {a // a ≠ x}} (hex : H.edge x ≠ x) (hux : u.val ∈ H.edge_affect_set x) :
  (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ := by{
    simp only [mem_edge_affect_set_iff] at hux
    apply hux.elim
    · exact walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_cedge hex ∘ cedge_equivalence.symm
    · exact walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_cedge_node hex
      ∘ cedge_equivalence.symm
  }
theorem edge_affect_walkupe_subtype_walkupe_cedge_edge_or_edgeinv_of_not_edge_self {x : α}
  {u : H.edge_affect_walkupe_subtype x} (hex : H.edge x ≠ x) :
  (H.WalkupE x).cedge u.val ⟨H.edge x, hex⟩ ∨
  (H.WalkupE x).cedge u.val ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ := by{
    have hu:=u.prop
    exact walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_mem_edge_affect_set hex hu
  }
theorem walkupe_mem_edge_affect_of_mem_edge_affect_set {x : α} {u : {a // a ≠ x}}
  (hux : u.val ∈ H.edge_affect_set x) : ((H.WalkupE x).edge u).val ∈ H.edge_affect_set x:=by{
    simp only [mem_edge_affect_set_iff] at *
    rw[walkupe_edge, skip_edge'_val]
    cases em (H.edge x = x) with
    | inl hx => {
      unfold skip_edge''
      simp only [hx, ↓reduceIte]
      apply hux.imp
      all_goals
      intro h
      apply cedge_equivalence.trans h
      apply ReflTransGen.single
      rfl
    }
    | inr hx => {
      cases em (H.face (H.edge u) = x) with
      | inl hnx' => {
        unfold skip_edge''
        simp only [hx, hnx', ↓reduceIte]
        left
        apply ReflTransGen.single
        rfl
      }
      | inr hnx' => {
        cases em (H.edge u = x) with
        | inl hux => {
          unfold skip_edge''
          simp only [hx, hnx', ↓reduceIte]
          simp only [hux, ↓reduceIte]
          right
          apply ReflTransGen.single
          rfl
        }
        | inr hux' => {
          unfold skip_edge''
          simp only [hx, hnx', ↓reduceIte]
          simp only [hux', ↓reduceIte]
          apply hux.imp
          all_goals
          intro h
          apply cedge_equivalence.trans h
          apply ReflTransGen.single
          rfl
        }
      }
    }
  }
theorem edge_affect_set_walkupe_cedge_closure {x : α} {u v : {a // a ≠ x}}
  (huv : (H.WalkupE x).cedge u v) (hux : u.val ∈ H.edge_affect_set x)
  : v.val ∈ H.edge_affect_set x:=by{
    rw[cedge, funReflTransGen_iff_iterate] at huv
    have ⟨n, hn⟩:=huv
    induction n generalizing v with
    | zero => {
      simp at hn
      simp[←hn, hux]
    }
    | succ n' ih => {
      rw[←hn, iterate_succ_apply']
      apply walkupe_mem_edge_affect_of_mem_edge_affect_set
      apply (ih · rfl)
      use n'
    }
  }
theorem edge_affect_set_walkupe_cedge_closure_iff {x : α} {u v : {a // a ≠ x}}
  (huv : (H.WalkupE x).cedge u v)
  : u.val ∈ H.edge_affect_set x ↔ v.val ∈ H.edge_affect_set x:=by{
    constructor
    · apply edge_affect_set_walkupe_cedge_closure huv
    · apply edge_affect_set_walkupe_cedge_closure (cedge_equivalence.symm huv)
  }
theorem mem_edge_affect_set_iff_of_not_edge_self {x : α} {u : {a // a ≠ x}} (hex : H.edge x ≠ x)
  : u.val ∈ H.edge_affect_set x ↔ (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ :=by{
    constructor
    · exact walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_mem_edge_affect_set hex
    intro h
    have h':=h.imp edge_affect_set_walkupe_cedge_closure_iff
      edge_affect_set_walkupe_cedge_closure_iff
    simp[edge_mem_edge_affect_set, edgeinv_mem_edge_affect_set] at h'
    simp[h']
  }
theorem edge_affect_ecomp_iff {x : α} :
  H.edge_affect_ecomp x = if H.cross_edge x then 1 else 2 := by{
    unfold edge_affect_ecomp
    unfold Fintype.nComp
    rw[apply_ite (_ = ·)]
    simp only[Fintype.card_eq_one_iff]
    simp only[Fintype.card_eq_nat_card, Nat.card_eq_two_iff]
    cases em (H.cross_edge x) with
    | inl hcex => {
      simp only [hcex, ↓reduceIte]
      unfold cross_edge at hcex
      use ⟦⟨x, by{simp[mem_edge_affect_set_iff, H.cedge_equivalence.refl]}⟩⟧
      intro y
      rw[Quotient.eq_mk_iff_out]
      simp only [H.edge_affect_esetoid_iff_cedge]
      have hy:=y.out.prop
      simp only[mem_edge_affect_set_iff] at hy
      apply H.cedge_equivalence.symm
      cases hy with
      | inl hy => exact hy
      | inr hy => exact hcex.trans hy
    }
    | inr hcex => {
      simp only [hcex, ↓reduceIte]
      unfold cross_edge at hcex
      use ⟦⟨x, by{simp[mem_edge_affect_set_iff, H.cedge_equivalence.refl]}⟩⟧
      use ⟦⟨H.node x, by{simp[mem_edge_affect_set_iff, H.cedge_equivalence.refl]}⟩⟧
      rw[ne_eq, Quotient.eq_iff_equiv]
      simp only [H.edge_affect_esetoid_iff_cedge, hcex, not_false_eq_true, true_and]
      rw[Set.eq_univ_iff_forall]
      intro y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      simp only [Quotient.eq_mk_iff_out]
      simp only [H.edge_affect_esetoid_iff_cedge]
      have hy:=y.out.prop
      simp only [mem_edge_affect_set_iff] at hy
      simp only [cedge_equivalence.symmetric.iff (y:=y.out.val)] at hy
      exact hy
    }
  }
theorem edge_affect_ecomp_add_compl_ecomp {x : α} :
  H.edge_affect_ecomp x + H.edge_affect_compl_ecomp x = H.ecomp := by{
    unfold edge_affect_compl_ecomp edge_affect_ecomp ecomp
    unfold Fintype.nComp
    rw[←Fintype.card_sum]
    let e:Quotient H.esetoid ≃
      Quotient (H.edge_affect_esetoid x) ⊕ Quotient (H.edge_affect_compl_esetoid x)
    := by{
      let toFun : Quotient H.esetoid →
        Quotient (H.edge_affect_esetoid x) ⊕ Quotient (H.edge_affect_compl_esetoid x)
      := fun q => if hq : q.out ∈ H.edge_affect_set x then Sum.inl ⟦⟨q.out, hq⟩⟧
      else Sum.inr ⟦⟨q.out, hq⟩⟧
      let invFun : Quotient (H.edge_affect_esetoid x) ⊕ Quotient (H.edge_affect_compl_esetoid x)
        → Quotient H.esetoid := fun q => match q with
          | Sum.inl q' | Sum.inr q' => ⟦q'.out.val⟧
      have left_inv : LeftInverse invFun toFun := by{
        intro q
        unfold toFun
        cases em (q.out ∈ H.edge_affect_set x) with
        | inl hqx => {
          simp only [hqx, ↓reduceDIte]
          unfold invFun
          simp only [Quotient.mk_eq_iff_out]
          have h:=Quotient.mk_out (s:=H.edge_affect_esetoid x) ⟨q.out, hqx⟩
          rw[edge_affect_esetoid_iff_cedge] at h
          apply h.trans
          simp only
          apply ReflTransGen.refl
        }
        | inr hqx => {
          simp only [hqx, ↓reduceDIte]
          unfold invFun
          simp only [Quotient.mk_eq_iff_out]
          have h:=Quotient.mk_out (s:=H.edge_affect_compl_esetoid x) ⟨q.out, hqx⟩
          rw[edge_affect_compl_esetoid_iff_cedge] at h
          apply h.trans
          simp only
          apply ReflTransGen.refl
        }
      }
      have right_inv : RightInverse invFun toFun := by{
        intro q
        match q with
        | Sum.inl q' => {
          unfold invFun
          simp only
          have hq0:=q'.out.prop
          simp only [mem_edge_affect_set_iff] at hq0
          have hq1:=Quotient.mk_out (s:=H.esetoid) q'.out.val
          unfold esetoid at hq1
          simp only at hq1
          apply cedge_equivalence.symm at hq1
          have hq:(Quotient.mk H.esetoid q'.out.val).out ∈ H.edge_affect_set x:=by{
            simp only [mem_edge_affect_set_iff]
            exact hq0.imp (cedge_equivalence.trans · hq1) (cedge_equivalence.trans · hq1)
          }
          unfold toFun
          simp only [hq, ↓reduceDIte, Sum.inl.inj_iff]
          simp only [Quotient.mk_eq_iff_out]
          simp only [edge_affect_esetoid_iff_cedge]
          exact cedge_equivalence.symm hq1
        }
        | Sum.inr q' => {
          unfold invFun
          simp only
          have hq0:=q'.out.prop
          simp only [mem_edge_affect_set_iff, not_or] at hq0
          have hq1:=Quotient.mk_out (s:=H.esetoid) q'.out.val
          unfold esetoid at hq1
          simp only at hq1
          apply cedge_equivalence.symm at hq1
          have hq:(Quotient.mk H.esetoid q'.out.val).out ∉ H.edge_affect_set x:=by{
            simp only [mem_edge_affect_set_iff, not_or]
            apply cedge_equivalence.symm at hq1
            apply hq0.imp
            all_goals
            rw[not_imp_not]
            intro h
            exact h.trans hq1
          }
          unfold toFun
          simp only [hq, ↓reduceDIte, Sum.inr.inj_iff]
          simp only [Quotient.mk_eq_iff_out]
          simp only [edge_affect_compl_esetoid_iff_cedge]
          exact cedge_equivalence.symm hq1
        }
      }
      exact ⟨toFun, invFun, left_inv, right_inv⟩
    }
    simp only
    have he:=Fintype.ofEquiv_card e
    apply (Eq.mp · he)
    congr
    apply Subsingleton.elim
  }
theorem edge_affect_compl_closure_edge {x : α}
  {u : H.edge_affect_compl_subtype x}
  : H.edge u.val ∉ H.edge_affect_set x := by{
    have hu:=u.prop
    simp only [mem_edge_affect_set_iff, not_or] at *
    apply hu.imp
    all_goals
    rw[not_imp_not]
    intro h
    apply cedge_equivalence.trans h
    apply cedge_equivalence.symm
    apply ReflTransGen.single
    rfl
  }
theorem edge_affect_walkupe_compl_edge_ne {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} :
  H.edge u.val.val ≠ x:=by{
    have h1:=u.prop
    have h2:=u.val.prop
    intro h3
    simp[mem_edge_affect_set_iff] at h1
    simp only [←h3] at h1
    apply h1.left
    apply cedge_equivalence.symm
    apply ReflTransGen.single
    rfl
  }
theorem edge_affect_walkupe_compl_walkupe_edge_eq {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} :
  (H.WalkupE x).edge u.val = ⟨H.edge u.val.val, edge_affect_walkupe_compl_edge_ne⟩
  :=by{
    rw[walkupe_edge]
    ext
    rw[skip_edge'_val]
    simp only
    unfold skip_edge''
    repeat rw [apply_ite (· = _)]
    simp only [ne_eq, if_true_right, if_true_left]
    intro hex
    simp only [edge_affect_walkupe_compl_edge_ne, edge_inj]
    simp only [IsEmpty.forall_iff, if_true_right]
    intro hfu
    exfalso
    have hu:=u.prop
    simp only [mem_edge_affect_set_iff] at hu
    have hnu:u.val.val ≠ H.node x:=by{
      intro hnu
      simp[hnu, cedge_equivalence.refl] at hu
    }
    apply hnu
    rw[←node_inj, nfe_cancel] at hfu
    exact hfu
  }
theorem edge_affect_walkupe_compl_closure_edge {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x}
  : H.edge u.val.val ∉ H.edge_affect_set x := by{
    simp only [mem_edge_affect_set_iff, not_or]
    have hu:=u.prop
    simp only [mem_edge_affect_set_iff, not_or] at hu
    apply hu.imp
    all_goals
    rw[not_imp_not]
    intro h
    apply cedge_equivalence.trans h
    apply cedge_equivalence.symm
    apply ReflTransGen.single
    rfl
  }
theorem edge_affect_walkupe_compl_closure_walkupe_edge {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x}
  : ((H.WalkupE x).edge u.val).val ∉ H.edge_affect_set x := by{
    rw[edge_affect_walkupe_compl_walkupe_edge_eq]
    simp only
    apply edge_affect_walkupe_compl_closure_edge
  }
theorem edge_affect_walkupe_compl_closure_cedge {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {y : α}
  (huy : H.cedge u.val.val y) : y ∉ H.edge_affect_set x := by{
    have hu:=u.prop
    intro hy
    apply hu
    simp only [mem_edge_affect_set_iff] at *
    apply cedge_equivalence.symm at huy
    apply hy.imp
    all_goals
    intro h
    exact h.trans huy
  }
theorem edge_affect_walkupe_compl_cedge_ne {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {y : α}
  (huy : H.cedge u.val.val y) : y ≠ x := by{
    have h:=edge_affect_walkupe_compl_closure_cedge huy
    intro h'
    apply h
    rw[h']
    exact self_mem_edge_affect_set
  }
theorem edge_affect_walkupe_compl_cedge_ne_node {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {y : α}
  (huy : H.cedge u.val.val y) : y ≠ H.node x := by{
    have h:=edge_affect_walkupe_compl_closure_cedge huy
    intro h'
    apply h
    rw[h']
    exact node_mem_edge_affect_set
  }
theorem edge_affect_walkupe_compl_edge_iterate_ne {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {n : ℕ}
  : H.edge^[n] u.val.val ≠ x := by{
    apply edge_affect_walkupe_compl_cedge_ne (u:=u)
    apply funReflTransGen.iterate
  }
theorem edge_affect_walkupe_compl_edge_iterate_ne_node {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {n : ℕ}
  : H.edge^[n] u.val.val ≠ H.node x := by{
    apply edge_affect_walkupe_compl_cedge_ne_node (u:=u)
    apply funReflTransGen.iterate
  }
theorem edge_affect_walkupe_compl_edge_iterate {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {n : ℕ} :
  (H.WalkupE x).edge^[n] u.val =
  ⟨H.edge^[n] u.val.val, edge_affect_walkupe_compl_edge_iterate_ne⟩ := by{
    induction n with
    | zero => simp
    | succ n' ih => {
      ext
      simp only [iterate_succ_apply']
      simp only [Subtype.ext_iff] at ih
      rw[walkupe_edge]
      nth_rw 1 [skip_edge']
      simp only
      unfold skip_edge''
      repeat rw[apply_ite (· = _)]
      simp only [edge_inj]
      rw[walkupe_edge] at ih
      simp only [ne_eq, ih, if_true_right, if_true_left]
      intro hex
      repeat rw[←iterate_succ_apply' H.edge]
      simp only [edge_affect_walkupe_compl_edge_iterate_ne
      , IsEmpty.forall_iff, if_true_right]
      intro h
      exfalso
      rw[←node_inj, iterate_succ_apply', nfe_cancel] at h
      exact edge_affect_walkupe_compl_edge_iterate_ne_node h
    }
  }
theorem edge_affect_walkupe_compl_closure_walkupe_cedge {x : α}
  {u : H.edge_affect_walkupe_compl_subtype x} {y : {a // a ≠ x}}
  (huy : (H.WalkupE x).cedge u.val y) : y.val ∉ H.edge_affect_set x := by{
    have hu:=u.prop
    have hu':=u.val.prop
    intro hy
    apply hu
    simp only [mem_edge_affect_set_iff] at *
    apply hy.imp
    all_goals
    intro hxy
    apply cedge_equivalence.trans hxy
    apply cedge_equivalence.symm
    unfold cedge at huy
    unfold cedge
    rw[funReflTransGen_iff_iterate] at huy
    have ⟨k, hk⟩:=huy
    rw[funReflTransGen_iff_iterate]
    rw[edge_affect_walkupe_compl_edge_iterate] at hk
    use k
    exact Subtype.ext_iff.mp hk
  }
theorem edge_affect_walkupe_compl_cedge_iff_cedge {x : α}
  {u v : H.edge_affect_walkupe_compl_subtype x}
  : (H.WalkupE x).cedge u.val v.val ↔ H.cedge u.val v.val:=by{
    unfold cedge funReflTransGen
    constructor
    · {
      generalize hu : u.val = u'
      generalize hv : v.val = v'
      intro h
      induction h generalizing u v with
      | refl => rfl
      | @tail b c huw hwv ih => {
        let w:H.edge_affect_walkupe_compl_subtype x:=⟨b,
        edge_affect_walkupe_compl_closure_walkupe_cedge (hu ▸ huw)⟩
        have ih':=ih (v:=w) hu rfl
        apply ih'.tail
        simp only [fromFun] at *
        have hwv':=edge_affect_walkupe_compl_walkupe_edge_eq (u:=w)
        unfold w at hwv'
        simp only at hwv'
        rw[hwv'] at hwv
        rw[←hwv]
      }
    }
    · {
      generalize hu : u.val.val = u'
      generalize hv : v.val.val = v'
      intro h
      induction h generalizing u v with
      | refl => {
        have huv:=Subtype.ext (hu.trans hv.symm)
        rw[huv]
      }
      | @tail b c huw hwv ih => {
        let w:H.edge_affect_walkupe_compl_subtype x:=
          ⟨⟨b, edge_affect_walkupe_compl_cedge_ne (hu ▸ huw)⟩,
          edge_affect_walkupe_compl_closure_cedge (hu ▸ huw)⟩
        have ih':=ih (v:=w) hu rfl
        apply ih'.tail
        simp only [fromFun] at *
        simp only [edge_affect_walkupe_compl_walkupe_edge_eq]
        unfold w
        ext
        simp[hwv, hv]
      }
    }
  }
theorem edge_affect_walkupe_compl_ecomp_eq_edge_affect_compl_ecomp {x : α}
  : H.edge_affect_walkupe_compl_ecomp x = H.edge_affect_compl_ecomp x := by{
    unfold edge_affect_compl_ecomp edge_affect_walkupe_compl_ecomp
    unfold Fintype.nComp
    simp only
    let e:Quotient (H.edge_affect_compl_esetoid x) ≃
    Quotient (H.edge_affect_walkupe_compl_esetoid x) := by{
      let toFun : Quotient (H.edge_affect_compl_esetoid x)
      → Quotient (H.edge_affect_walkupe_compl_esetoid x)
        := fun q => ⟦⟨⟨q.out.val, by{
          have hq:=q.out.prop
          intro hqx
          simp[mem_edge_affect_set_iff] at hq
          simp[hqx, cedge_equivalence.refl] at hq
        }⟩, q.out.prop⟩⟧
      let invFun : Quotient (H.edge_affect_walkupe_compl_esetoid x)
      → Quotient (H.edge_affect_compl_esetoid x)
        := fun q => ⟦⟨q.out.val.val, q.out.prop⟩⟧
      have left_inv : LeftInverse invFun toFun := by{
        intro q
        unfold toFun invFun
        simp only [Quotient.mk_eq_iff_out, edge_affect_compl_esetoid_iff_cedge]
        have hq0:q.out.val ≠ x:=by{
          have hq:=q.out.prop
          intro hqx
          simp[mem_edge_affect_set_iff] at hq
          simp[hqx, cedge_equivalence.refl] at hq
        }
        have hq1:=Quotient.mk_out (s:=H.edge_affect_walkupe_compl_esetoid x)
          ⟨⟨q.out.val, hq0⟩, q.out.prop⟩
        rw[edge_affect_walkupe_compl_esetoid_iff_cedge] at hq1
        rw[edge_affect_walkupe_compl_cedge_iff_cedge] at hq1
        exact hq1
      }
      have right_inv : RightInverse invFun toFun := by{
        intro q
        unfold toFun invFun
        simp only [Quotient.mk_eq_iff_out]
        simp only [ne_eq, edge_affect_walkupe_compl_esetoid_iff_cedge]
        have hq0:=Quotient.mk_out (s:=H.edge_affect_compl_esetoid x)
          ⟨q.out.val.val, q.out.prop⟩
        simp only [edge_affect_compl_esetoid_iff_cedge] at hq0
        have hq1:q.out.val.val ≠ x:=by{
          have hq:=q.out.prop
          revert hq
          rw[not_imp_not]
          intro hq
          simp[hq, self_mem_edge_affect_set]
        }
        have hq2:(Quotient.mk (H.edge_affect_compl_esetoid x)
          ⟨q.out.val.val, q.out.prop⟩).out.val ∉ H.edge_affect_set x:=by{
            have hq:=q.out.prop
            revert hq
            rw[not_imp_not]
            intro hq
            simp only [mem_edge_affect_set_iff] at *
            apply hq.imp
            all_goals
            intro h
            exact h.trans hq0
        }
        have hq3:(Quotient.mk (H.edge_affect_compl_esetoid x)
          ⟨q.out.val.val, q.out.prop⟩).out.val ≠ x:=by{
            revert hq2
            rw[not_imp_not]
            intro hq2
            simp[hq2, self_mem_edge_affect_set]
        }
        let w:H.edge_affect_walkupe_compl_subtype x:=
          ⟨⟨(Quotient.mk (H.edge_affect_compl_esetoid x) ⟨q.out.val.val, q.out.prop⟩).out.val,
          hq3⟩, hq2⟩
        change (H.WalkupE x).cedge w.val _
        rw[edge_affect_walkupe_compl_cedge_iff_cedge]
        unfold w
        simp only
        exact hq0
      }
      exact ⟨toFun, invFun, left_inv, right_inv⟩
    }
    have he:=Fintype.ofEquiv_card e
    apply (Eq.mp · he)
    congr
    apply Subsingleton.elim
  }

theorem edge_affect_walkupe_ecomp_eq {x : α}
  : H.edge_affect_walkupe_ecomp x = if H.isbarb x then 0 else if H.glink x x then 1 else
  if H.cross_edge x then 2 else 1 := by{
    unfold edge_affect_walkupe_ecomp Fintype.nComp
    simp only
    repeat rw[apply_ite (_ = ·)]
    rw[Fintype.card_eq_zero_iff, isEmpty_quotient_iff]
    rw[Fintype.card_eq_one_iff, Fintype.card_eq_nat_card, Nat.card_eq_two_iff]
    cases em (H.isbarb x) with
    | inl hbx => {
      simp only [hbx, ↓reduceIte]
      apply Subtype.isEmpty_of_false
      intro a ha
      have hbx':=isbarb_cedge_iff hbx (y:=a.val)
      simp[isbarb_iff_all_perm_self] at hbx
      simp[mem_edge_affect_set_iff, hbx, hbx', Eq.comm (a:=x), a.prop] at ha
    }
    | inr hbx => {
      simp only [hbx, ↓reduceIte]
      simp only [isbarb_iff_all_perm_self, not_and] at hbx
      cases em (H.glink x x) with
      | inl hgx => {
        simp only [hgx, ↓reduceIte]
        cases em (H.edge x = x) with
        | inl hex => {
          have hnx:H.node x ≠ x:=by{
            intro hnx
            apply hbx hex hnx
            nth_rw 1 [←hex, ←hnx, fen_cancel]
          }
          have hfx:H.face x ≠ x:=by{
            intro hfx
            apply (hbx hex · hfx)
            nth_rw 1 [←hfx, ←hex, nfe_cancel]
          }
          use ⟦⟨⟨H.node x, hnx⟩, node_mem_edge_affect_set⟩⟧
          intro y
          rw[Quotient.eq_mk_iff_out]
          simp only [edge_affect_walkupe_esetoid_iff_cedge]
          have hcex:¬H.cross_edge x:=by{
            unfold cross_edge
            simp only [cedge, funReflTransGen_iff_iterate,
            iterate_fixed hex, exists_const]
            exact Ne.symm hnx
          }
          exact edge_affect_walkupe_subtype_walkupe_cedge_node_of_not_crossedge hcex
        }
        | inr hex => {
          use ⟦⟨⟨H.edge x, hex⟩, edge_mem_edge_affect_set⟩⟧
          intro y
          rw[Quotient.eq_mk_iff_out]
          simp only [edge_affect_walkupe_esetoid_iff_cedge]
          have hgx':=hgx.resolve_left hex
          simp only [union_iff, fromFun] at hgx'
          have hy:=y.out.prop
          simp only [mem_edge_affect_set_iff] at hy
          have hy':H.cedge x y.out.val.val → (H.WalkupE x).cedge y.out.val ⟨H.edge x, hex⟩:=by{
            intro hy'
            apply cedge_equivalence.symm at hy'
            rw[cedge, funReflTransGen_iff_iterate_minimal] at hy'
            have ⟨n, hn⟩:=hy'
            apply ReflTransGen.tail (b:=⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩)
            · {
              have hnz:n ≠ 0:=by{
                intro hnz
                simp[hnz, y.out.val.prop] at hn
              }
              match n with
              | n' + 1 => {
                apply funReflTransGen_iff_iterate.mpr
                use n'
                have hn':H.edge^[n'] y.out.val.val = H.edgeinv x
                  ∧ ∀m < n', H.edge^[m] y.out.val.val ≠ H.edgeinv x:=by{
                  simp only [ne_eq]
                  rw[←edge_inj, ←iterate_succ_apply' H.edge]
                  nth_rw 1 [edgeinv_eq, comp_apply, enf_cancel]
                  apply hn.imp_right
                  intro hn' m hmn
                  rw[←edge_inj, ←iterate_succ_apply' H.edge]
                  rw[edgeinv_eq, comp_apply, enf_cancel]
                  apply hn'
                  exact Nat.succ_lt_succ hmn
                }
                have h:∀m ≤ n', ((H.WalkupE x).edge^[m] y.out.val).val
                = H.edge^[m] y.out.val.val:=by{
                  intro m hmn
                  induction m with
                  | zero => simp
                  | succ m' ih => {
                    rw[iterate_succ_apply']
                    nth_rw 1 [walkupe_edge]
                    rw[skip_edge'_eq_of_glink hgx]
                    rw[skip_val]
                    rw[ih (Nat.le_of_succ_le hmn)]
                    unfold skip'
                    rw[ite_cond_eq_false]
                    · rw[←iterate_succ_apply' H.edge]
                    · {
                      simp only [ne_eq, eq_iff_iff, iff_false]
                      rw[Nat.succ_le_iff] at hmn
                      rw[←iterate_succ_apply' H.edge]
                      exact hn.right _ (Nat.succ_lt_succ hmn)
                    }
                  }
                }
                ext
                rw[h n' (by rfl)]
                exact hn'.left
              }
            }
            · {
              simp only [walkupe_edge]
              ext
              simp only [skip_edge'_eq_of_glink hgx, skip_val]
              unfold skip'
              simp[edgeinv_eq, enf_cancel]
            }
          }
          cases hgx' with
          | inl hnx => {
            rw[hnx, or_self] at hy
            exact hy' hy
          }
          | inr hfx => {
            have hnx':H.node x = H.edgeinv x:=by{
              rw[edgeinv_eq, comp_apply, hfx]
            }
            rw[hnx'] at hy
            have hy'':H.cedge x y.out.val.val:=by{
              apply hy.elim id
              intro h
              apply (cedge_equivalence.trans · h)
              apply cedge_equivalence.symm
              apply ReflTransGen.single
              simp[fromFun, edgeinv_eq, enf_cancel]
            }
            exact hy' hy''
          }
        }
      }
      | inr hgx => {
        simp only [hgx, ↓reduceIte]
        simp only [glink_iff, not_or] at hgx
        cases em (H.cross_edge x) with
        | inl hcex => {
          simp only [hcex, ↓reduceIte]
          use ⟦⟨⟨H.edge x, hgx.left⟩, edge_mem_edge_affect_set⟩⟧
          use ⟦⟨⟨H.edgeinv x, hgx.left ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩
          , edgeinv_mem_edge_affect_set⟩⟧
          rw[ne_eq, Quotient.eq_iff_equiv]
          constructor
          · {
            simp only [edge_affect_walkupe_esetoid_iff_cedge]
            apply edge_not_cedge_inv_of_not_glink_of_cross_edge
            · simp [glink_iff, hgx]
            · exact hcex
          }
          · {
            rw[Set.eq_univ_iff_forall]
            intro q
            simp only [ne_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
            simp only [Quotient.eq_mk_iff_out]
            simp only [edge_affect_walkupe_esetoid_iff_cedge]
            apply edge_affect_walkupe_subtype_walkupe_cedge_edge_or_edgeinv_of_not_edge_self
          }
        }
        | inr hcex => {
          simp only [hcex, ↓reduceIte]
          have hnx:H.node x ≠ x:=not_node_self_of_not_cross_edge hcex
          use ⟦⟨⟨H.node x, hnx⟩, node_mem_edge_affect_set⟩⟧
          intro y
          rw[Quotient.eq_mk_iff_out]
          simp only [ne_eq, edge_affect_walkupe_esetoid_iff_cedge]
          apply edge_affect_walkupe_subtype_walkupe_cedge_node_of_not_crossedge
          exact hcex
        }
      }
    }
  }
theorem edge_affect_walkupe_ecomp_add_compl_ecomp {x : α} :
  H.edge_affect_walkupe_ecomp x + H.edge_affect_walkupe_compl_ecomp x =
  (H.WalkupE x).ecomp := by{
    unfold edge_affect_walkupe_compl_ecomp edge_affect_walkupe_ecomp ecomp
    unfold Fintype.nComp
    rw[←Fintype.card_sum]
    let e:Quotient (H.WalkupE x).esetoid ≃
      Quotient (H.edge_affect_walkupe_esetoid x) ⊕ Quotient (H.edge_affect_walkupe_compl_esetoid x)
    := by{
      let toFun : Quotient (H.WalkupE x).esetoid →
        Quotient (H.edge_affect_walkupe_esetoid x)
        ⊕ Quotient (H.edge_affect_walkupe_compl_esetoid x)
      := fun q => if hq : q.out.val ∈ H.edge_affect_set x then Sum.inl ⟦⟨q.out, hq⟩⟧
      else Sum.inr ⟦⟨q.out, hq⟩⟧
      let invFun : Quotient (H.edge_affect_walkupe_esetoid x)
      ⊕ Quotient (H.edge_affect_walkupe_compl_esetoid x)
        → Quotient (H.WalkupE x).esetoid := fun q => match q with
          | Sum.inl q' | Sum.inr q' => ⟦q'.out.val⟧
      have left_inv : LeftInverse invFun toFun := by{
        intro q
        unfold toFun
        cases em (q.out.val ∈ H.edge_affect_set x) with
        | inl hqx => {
          simp only [hqx, ↓reduceDIte]
          unfold invFun
          simp only [Quotient.mk_eq_iff_out]
          have h:=Quotient.mk_out (s:=H.edge_affect_walkupe_esetoid x) ⟨q.out, hqx⟩
          rw[edge_affect_walkupe_esetoid_iff_cedge ] at h
          apply h.trans
          simp only
          apply ReflTransGen.refl
        }
        | inr hqx => {
          simp only [hqx, ↓reduceDIte]
          unfold invFun
          simp only [Quotient.mk_eq_iff_out]
          have h:=Quotient.mk_out (s:=H.edge_affect_walkupe_compl_esetoid x) ⟨q.out, hqx⟩
          rw[edge_affect_walkupe_compl_esetoid_iff_cedge] at h
          apply h.trans
          simp only
          apply ReflTransGen.refl
        }
      }
      have right_inv : RightInverse invFun toFun := by{
        intro q
        match q with
        | Sum.inl q' => {
          unfold invFun
          simp only
          have hq0:=q'.out.prop
          simp only [mem_edge_affect_set_iff] at hq0
          have hq1:=Quotient.mk_out (s:=(H.WalkupE x).esetoid) q'.out.val
          unfold esetoid at hq1
          simp only at hq1
          apply cedge_equivalence.symm at hq1
          have hq:(Quotient.mk (H.WalkupE x).esetoid q'.out.val).out.val ∈ H.edge_affect_set x:=by{
            have hq2:=edge_affect_set_walkupe_cedge_closure_iff hq1
            rw[←hq2]
            exact q'.out.prop
          }
          unfold toFun
          simp only [hq, ↓reduceDIte, Sum.inl.inj_iff]
          simp only [Quotient.mk_eq_iff_out]
          simp only [edge_affect_walkupe_esetoid_iff_cedge]
          exact cedge_equivalence.symm hq1
        }
        | Sum.inr q' => {
          unfold invFun
          simp only
          have hq0:=q'.out.prop
          simp only [mem_edge_affect_set_iff, not_or] at hq0
          have hq1:=Quotient.mk_out (s:=(H.WalkupE x).esetoid) q'.out.val
          unfold esetoid at hq1
          simp only at hq1
          apply cedge_equivalence.symm at hq1
          have hq:(Quotient.mk (H.WalkupE x).esetoid q'.out.val).out.val ∉ H.edge_affect_set x:=by{
            have hq2:=edge_affect_set_walkupe_cedge_closure_iff hq1
            rw[←hq2]
            exact q'.out.prop
          }
          unfold toFun
          simp only [hq, ↓reduceDIte, Sum.inr.inj_iff]
          simp only [Quotient.mk_eq_iff_out]
          simp only [edge_affect_walkupe_compl_esetoid_iff_cedge]
          exact cedge_equivalence.symm hq1
        }
      }
      exact ⟨toFun, invFun, left_inv, right_inv⟩
    }
    simp only
    have he:=Fintype.ofEquiv_card e
    apply (Eq.mp · he)
    congr
    apply Subsingleton.elim
  }

theorem walkupe_ecomp' {x : α} :
  (H.WalkupE x).ecomp +
  (if H.isbarb x then 2
  else if H.cross_edge x then
    if H.glink x x then 1 else 0
  else 2
  ) = H.ecomp + 1 := by{
    rw[←edge_affect_walkupe_ecomp_add_compl_ecomp]
    rw[←edge_affect_ecomp_add_compl_ecomp (x:=x)]
    rw[add_assoc, add_left_comm]
    symm
    rw[add_assoc, add_left_comm]
    symm
    rw[edge_affect_walkupe_compl_ecomp_eq_edge_affect_compl_ecomp]
    apply congrArg
    rw[edge_affect_ecomp_iff]
    rw[edge_affect_walkupe_ecomp_eq]
    cases em (H.isbarb x) with
    | inl hbx => {
      simp[hbx]
      simp[cross_edge_of_isbarb hbx]
    }
    | inr hbx => {
      cases em (H.cross_edge x) with
      | inl hcex => {
        cases em (H.glink x x) with
        | inl hgx | inr hgx => simp[hbx, hcex, hgx]
      }
      | inr hcex => {
        simp[hcex, hbx]
      }
    }
  }

theorem walkupe_ecomp {x : α} :
  (H.WalkupE x).ecomp  = H.ecomp + 1 - (if H.isbarb x then 2
  else if H.cross_edge x then
    if H.glink x x then 1 else 0
  else 2) := by{
    apply Nat.eq_sub_of_add_eq
    exact walkupe_ecomp'
  }
-- e + n + f
theorem walkupe_euler_rhs {x : α} :
  (H.WalkupE x).euler_rhs = H.euler_rhs + 1 - if H.isbarb x then 4
  else if H.glink x x then 2 else if H.cross_edge x then 0 else 2 := by{
    unfold euler_rhs
    rw[walkupe_ecomp, walkupe_ncomp, walkupe_fcomp]
    have hep:=H.ecomp_pos_intro x
    have hnp:=H.ncomp_pos_intro x
    have hfp:=H.fcomp_pos_intro x
    cases em (H.isbarb x) with
    | inl hbx => {
      simp only [hbx, ↓reduceIte, Nat.reduceSubDiff]
      simp[isbarb_iff_all_perm_self] at hbx
      simp only [hbx, ↓reduceIte]
      rw[←Nat.sub_add_comm hep]
      rw[←Nat.sub_add_comm hnp]
      rw[←Nat.add_sub_assoc hfp]
      rw[Nat.sub_sub]
      rw[←Nat.add_sub_assoc
        (Nat.add_le_add hnp hfp)]
      rw[Nat.sub_sub]
    }
    | inr hbx => {
      cases em (H.cross_edge x) with
      | inl hcex => {
        cases em (H.glink x x) with
        | inl hgx => {
          have hex:=(cross_edge_iff_not_edge_self_of_not_isbarb_of_glink
          hbx hgx).mp hcex
          simp only [hgx, hcex, hbx, ↓reduceIte]
          simp only [add_tsub_cancel_right, Nat.reduceSubDiff]
          have hn:H.face x = x ↔ H.node x ≠ x:=by{
            constructor
            · {
              intro hfx hnx
              apply hex
              nth_rw 1 [←hnx, ←hfx, enf_cancel]
            }
            · {
              intro hnx
              exact (hgx.resolve_left hex).resolve_left hnx
            }
          }
          simp only [hn, ne_eq, ite_not]
          cases em (H.node x = x) with
          | inl hnx => {
            simp only [hnx, ↓reduceIte, tsub_zero]
            rw[←Nat.sub_add_comm hnp]
            rw[←Nat.add_sub_assoc]
            apply Nat.le_add_left_of_le
            exact hfp
          }
          | inr hnx => {
            simp only [hnx, ↓reduceIte, tsub_zero]
            rw[←Nat.add_sub_assoc hfp]
            rw[←Nat.add_sub_assoc]
            apply Nat.le_add_left_of_le
            exact hfp
          }
        }
        | inr hgx => {
          simp [hgx]
          simp [glink_iff] at hgx
          simp [hgx, hbx, hcex, Nat.succ_add]
        }
      }
      | inr hcex => {
        have hnx:=not_node_self_of_not_cross_edge hcex
        have hfx:=not_face_self_of_not_cross_edge hcex
        simp[hfx, hnx, hcex, hbx]
        simp[←Nat.sub_add_comm hep]
      }
    }
}

end Hypermap
