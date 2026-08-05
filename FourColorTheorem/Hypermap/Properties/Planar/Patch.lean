import FourColorTheorem.Hypermap.Actions.Patch
import FourColorTheorem.Hypermap.Properties.Planar.Euler

open Function
open Relation

namespace Hypermap

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]

namespace Patch

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]
variable {G : Hypermap α} {Gd : Hypermap αd} {Gr : Hypermap αr}
variable {hd : αd → α} {hr : αr → α} {bGd : List αd} {bGr : List αr}
variable (patchG : Patch G Gd Gr hd hr bGd bGr)
include patchG

theorem card_inex : Fintype.card αd + Fintype.card αr = Fintype.card α + patchG.diskBorder.length
:= by{
  rw[← Fintype.card_sum, ← List.Subtype.fintype_card_eq_length_of_nodup patchG.diskBorder_nodup,
  ← Fintype.card_sum]
  apply Fintype.card_congr
  let f : αd ⊕ αr → α ⊕ { x // x ∈ patchG.diskBorder } := fun x =>
    match x with
    | Sum.inl x => if hxd : x ∈ bGd then Sum.inr ⟨hd x, by{
      rw[List.mem_map_of_injective patchG.disk_hom_injective]
      exact hxd
    }⟩ else Sum.inl (hd x)
    | Sum.inr x => Sum.inl (hr x)
  apply Equiv.ofBijective f
  constructor
  · {
    intro x1 x2 hx12
    match x1 with
    | Sum.inl x1 => match x2 with
      | Sum.inl x2 => {
        simp only [f] at hx12
        rw[apply_dite (· = _), apply_dite (_ = ·)] at hx12
        simp only [reduceCtorEq, Sum.inl.injEq, dite_eq_ite, if_false_left,
        patchG.disk_hom_injective.eq_iff] at hx12
        rcases em (x1 ∈ bGd) with hx1d | hx1d
        · {
          simp only [hx1d, ↓reduceDIte] at hx12
          rcases em (x2 ∈ bGd) with hx2d | hx2d
          · {
            simp[hx2d, patchG.disk_hom_injective.eq_iff] at hx12
            simp[hx12]
          }
          · simp[hx2d] at hx12
        }
        · simp[hx1d] at hx12; simp[hx12]
      }
      | Sum.inr x2 => {
        rcases em (x1 ∈ bGd) with hx1d | hx1d
        all_goals
        simp only [hx1d, ↓reduceDIte, Sum.inl.injEq, f, reduceCtorEq] at hx12
        try exfalso; apply hx1d; rw[← patchG.border_antisymm_disk]; exact ⟨x2, hx12.symm⟩
      }
    | Sum.inr x1 => match x2 with
      | Sum.inl x2 => {
        simp only [f] at hx12
        rw[apply_dite (_ = ·)] at hx12
        simp only [reduceCtorEq, Sum.inl.injEq, dite_eq_ite, if_false_left] at hx12
        exfalso
        apply hx12.left
        rw[← patchG.border_antisymm_disk]
        exact ⟨x1, hx12.right⟩
      }
      | Sum.inr x2 => {
        simp[f] at hx12
        simp[patchG.rem_hom_injective hx12]
      }
  }
  · {
    intro x
    match x with
    | Sum.inl x => {
      rcases em (x ∈ patchG.rem) with hxr | hxr
      · {
        have ⟨x, hx⟩:=hxr
        use Sum.inr x
        simp[f, hx]
      }
      · {
        rw[mem_rem_iff, not_or, not_not, mem_border_iff_disk] at hxr
        have ⟨x, hx⟩:=hxr.left
        rw[← hx, List.mem_map_of_injective patchG.disk_hom_injective] at hxr
        use Sum.inl x
        simp[f, hxr, hx]
      }
    }
    | Sum.inr ⟨x, hx⟩ => {
      rw[List.mem_map] at hx
      have ⟨x, hx', hx⟩:=hx
      use Sum.inl x
      simp[f, hx', hx]
    }
  }
}
theorem rem_gcomp' : Gr.gcomp =
  @Fintype.nComp _ _ patchG.rem_glink_adjunctionOn_remGClosure.subtype_setoid_e (by{
    classical
    infer_instance
  }) := by{
  let inst : Fintype patchG.rem_glink_adjunctionOn_remGClosure.subtype_quotient := by{
    unfold AdjunctionOn.subtype_quotient
    classical
    infer_instance
  }
  let e := patchG.rem_glink_adjunctionOn_remGClosure.subtype_quotient_equiv
  unfold gcomp Fintype.nComp
  simp only
  change _ = Fintype.card patchG.rem_glink_adjunctionOn_remGClosure.subtype_quotient
  have he := Fintype.ofEquiv_card e
  apply Eq.trans ?_ he
  let e' : Quotient Gr.gsetoid ≃ patchG.rem_glink_adjunctionOn_remGClosure.subtype_quotient' := by{
    let f : Quotient Gr.gsetoid → patchG.rem_glink_adjunctionOn_remGClosure.subtype_quotient' :=
      fun q => ⟦⟨q.out, patchG.rem_subset_remGClosure (by{simp})⟩⟧
    apply Equiv.ofBijective f
    constructor
    · {
      intro qx qy hqxy
      unfold f at hqxy
      apply Quotient.eq.mp at hqxy
      unfold AdjunctionOn.subtype_setoid_e' at hqxy
      simp only[InvImage] at hqxy
      rw[← Quotient.out_eq qx, ← Quotient.out_eq qy]
      apply Quotient.eq.mpr
      change Gr.cglink qx.out qy.out
      exact hqxy
    }
    · {
      intro qy
      use ⟦qy.out.val⟧
      unfold f
      nth_rw 5 [← Quotient.out_eq qy]
      apply Quotient.eq.mpr
      unfold AdjunctionOn.subtype_setoid_e'
      simp only[InvImage]
      have hqyp' := Quotient.mk_out (s := Gr.gsetoid) qy.out.val
      exact hqyp'
    }
  }
  have he' := Fintype.ofEquiv_card e'
  apply he'.symm.trans
  congr
  apply Subsingleton.elim
}
theorem rem_gcomp : Gr.gcomp = Fintype.nCompSet G.gsetoid patchG.remGClosure := by{
  rw[patchG.rem_gcomp']
  unfold Fintype.nCompSet Fintype.nComp
  simp only
  congr 1
  congr 1
  apply Subsingleton.elim
}
theorem rem_fcomp : Gr.fcomp = Fintype.nCompSet G.fsetoid patchG.outer := by{
  unfold Fintype.nCompSet fcomp Fintype.nComp
  simp only
  let e : Quotient Gr.fsetoid
    ≃ Quotient ⟨_, LiftOn_equivalence_of_equivalence patchG.outer G.fsetoid.iseqv⟩ := by{
    let f : Quotient Gr.fsetoid →
      Quotient ⟨_, LiftOn_equivalence_of_equivalence patchG.outer G.fsetoid.iseqv⟩ := fun q =>
        ⟦⟨hr q.out, patchG.rem_subset_outer (by{simp})⟩⟧
    apply Equiv.ofBijective f; constructor
    · {
      intro qx qy h
      unfold f at h
      rw[Quotient.eq] at h
      simp only[LiftOn] at h
      change G.cface _ _ at h
      rw[← patchG.rem_cface_iff] at h
      rw[← Quotient.out_equiv_out]
      exact h
    }
    · {
      intro qy
      have hqy := qy.out.prop
      have ⟨qx, hqx0, hqx1⟩:=hqy
      have ⟨qx', hqx'⟩:=hqx0
      use ⟦qx'⟧
      unfold f
      rw[Quotient.mk_eq_iff_out]
      change G.cface _ _
      simp only
      apply G.cface_equivalence.trans ?_ hqx1
      rw[← hqx', ← patchG.rem_cface_iff]
      exact Quotient.mk_out qx' (s:=Gr.fsetoid)
    }
  }
  have he := Fintype.ofEquiv_card e
  rw[← he]
  congr
  apply Subsingleton.elim
}
theorem rem_ecomp : Gr.ecomp = Fintype.nCompSet G.esetoid patchG.rem := by{
  apply Fintype.nComp_adjunctionOn_partial_of_full (h:=hr) ?_ (by{simp})
  apply adjunctionOn_of_strict
  · apply patchG.rem_cedge_close
  · exact ⟨fun _ _ => G.cedge_equivalence.symm⟩
  · exact ⟨fun _ _ => Gr.cedge_equivalence.symm⟩
  · exact patchG.rem_hom_injective
  · exact fun _ => id
  intro x y _
  simp [fromFun, ← patchG.rem_edge_morph, patchG.rem_hom_injective.eq_iff]
}
theorem rem_ncomp : Gr.ncomp = Fintype.nCompSet G.nsetoid patchG.diskᶜ + if bGr = [] then 0 else 1
:= by{
  have hClo : Closure (fromFun Gr.node) {x | x ∈ bGr} := by{
    intro x (hx : _ ∈ _)
    exact fun _ => (patchG.rem_border_cnode_close hx).mp
  }
  have hCloR : Closure Gr.nsetoid {x | x ∈ bGr} := by{
    rw[← reflTransGen_closure_iff] at hClo
    exact hClo
  }
  have ih := Fintype.nCompSet_inex_of_closure (D:={x | x ∈ bGr}) hCloR
  unfold ncomp
  rw[ih]
  rw[add_comm]
  congr
  · {
    have hset : {x | x ∈ bGr}ᶜ = {x | hr x ∈ patchG.diskᶜ} := by{
      ext x
      rw[Set.mem_compl_iff]
      simp only [Set.mem_compl_iff, patchG.mem_disk_iff, not_or, not_not]
      simp only [Set.mem_setOf]
      have h : ∃xr, hr xr = hr x := ⟨x, rfl⟩
      rw[eq_true h, true_and, not_iff_not, ← patchG.mem_border_iff_disk, patchG.rem_mem_border_iff]
    }
    simp only [hset]
    apply Fintype.nComp_adjunctionOn_partial
    rw[← adjunctionOn_reflTransGen_left_iff, ← adjunctionOn_reflTransGen_right_iff]
    change AdjunctionOn hr G.cnode Gr.cnode patchG.diskᶜ
    apply adjunctionOn_of_strict
    · {
      rw[compl_closure_of_equivalence G.cnode_equivalence]
      unfold Closure cnode funReflTransGen
      simp only [reflTransGen_idem]
      apply patchG.disk_cnode_close
    }
    · unfold cnode funReflTransGen
      simp only [reflTransGen_idem]
      exact ⟨fun _ _ => G.cnode_equivalence.symm⟩
    · unfold cnode funReflTransGen
      simp only [reflTransGen_idem]
      exact ⟨fun _ _ => Gr.cnode_equivalence.symm⟩
    · exact patchG.rem_hom_injective
    · {
      intro y hy
      rw[Set.mem_compl_iff, patchG.mem_disk_iff, not_or, not_not] at hy
      exact hy.left
    }
    intro x y hxr
    rw[Set.mem_compl_iff, patchG.mem_disk_iff, not_or, not_not, patchG.rem_mem_border_iff] at hxr
    rw[patchG.rem_cnode_iff hxr.right]
  }
  · {
    rcases eq_or_ne bGr [] with hbn | hbn
    · simp[hbn]
    simp only [hbn, ↓ reduceIte]
    unfold Fintype.nCompSet
    simp only [Fintype.nComp_eq_one_iff_exists_all]
    simp only [Set.mem_setOf_eq, Subtype.forall, Subtype.exists]
    have ⟨a, l, ha⟩:=List.exists_cons_of_ne_nil hbn
    refine ⟨a, (by{simp[ha]}), ?_⟩
    simp only [LiftOn]
    intro b hb
    have ih' := (patchG.rem_border_cnode_close (xr:=a) (by{simp[ha]})).mpr hb
    exact ih'
  }
}
theorem disk_ecomp : Gd.ecomp = Fintype.nCompSet G.esetoid patchG.remᶜ + if bGd = [] then 0 else 1
:= by{
  have hClo : Closure (fromFun Gd.edge) {x | x ∈ bGd} := by{
    intro x (hx : _ ∈ _)
    exact fun _ => (patchG.disk_border_cedge_close hx).mp
  }
  have hCloR : Closure Gd.esetoid {x | x ∈ bGd} := by{
    rw[← reflTransGen_closure_iff] at hClo
    exact hClo
  }
  have ih := Fintype.nCompSet_inex_of_closure (D:={x | x ∈ bGd}) hCloR
  unfold ecomp
  rw[ih]
  rw[add_comm]
  congr
  · {
    have hset : {x | x ∈ bGd}ᶜ = {x | hd x ∈ patchG.remᶜ} := by{
      ext x
      rw[Set.mem_compl_iff]
      simp only [Set.mem_compl_iff, patchG.mem_rem_iff, not_or, not_not]
      simp only [Set.mem_setOf]
      have h : ∃xd, hd xd = hd x := ⟨x, rfl⟩
      rw[eq_true h, true_and, not_iff_not, ← patchG.mem_border_iff_disk, patchG.disk_mem_border_iff]
    }
    simp only [hset]
    apply Fintype.nComp_adjunctionOn_partial
    rw[← adjunctionOn_reflTransGen_left_iff, ← adjunctionOn_reflTransGen_right_iff]
    change AdjunctionOn hd G.cedge Gd.cedge patchG.remᶜ
    apply adjunctionOn_of_strict
    · {
      rw[compl_closure_of_equivalence G.cedge_equivalence]
      unfold Closure cedge funReflTransGen
      simp only [reflTransGen_idem]
      apply patchG.rem_cedge_close
    }
    · unfold cedge funReflTransGen
      simp only [reflTransGen_idem]
      exact ⟨fun _ _ => G.cedge_equivalence.symm⟩
    · unfold cedge funReflTransGen
      simp only [reflTransGen_idem]
      exact ⟨fun _ _ => Gd.cedge_equivalence.symm⟩
    · exact patchG.disk_hom_injective
    · {
      intro y hy
      rw[Set.mem_compl_iff, patchG.mem_rem_iff, not_or, not_not] at hy
      exact hy.left
    }
    intro x y hxr
    rw[Set.mem_compl_iff, patchG.mem_rem_iff, not_or, not_not, patchG.disk_mem_border_iff] at hxr
    rw[patchG.disk_cedge_iff hxr.right]
  }
  · {
    rcases eq_or_ne bGd [] with hbn | hbn
    · simp[hbn]
    simp only [hbn, ↓ reduceIte]
    unfold Fintype.nCompSet
    simp only [Fintype.nComp_eq_one_iff_exists_all]
    simp only [Set.mem_setOf_eq, Subtype.forall, Subtype.exists]
    have ⟨a, l, ha⟩:=List.exists_cons_of_ne_nil hbn
    refine ⟨a, (by{simp[ha]}), ?_⟩
    simp only [LiftOn]
    intro b hb
    have ih' := (patchG.disk_border_cedge_close (xd:=a) (by{simp[ha]})).mpr hb
    exact ih'
  }
}
theorem disk_ncomp : Gd.ncomp = Fintype.nCompSet G.nsetoid patchG.disk := by{
  apply Fintype.nComp_adjunctionOn_partial_of_full (h:=hd) ?_ (by{simp})
  apply adjunctionOn_of_strict
  · apply patchG.disk_cnode_close
  · exact ⟨fun _ _ => G.cnode_equivalence.symm⟩
  · exact ⟨fun _ _ => Gd.cnode_equivalence.symm⟩
  · exact patchG.disk_hom_injective
  · exact fun _ => id
  intro x y _
  simp [fromFun, ← patchG.disk_node_morph, patchG.disk_hom_injective.eq_iff]
}
theorem disk_fcomp : Gd.fcomp = Fintype.nCompSet G.fsetoid patchG.outerᶜ + bGd.length := by{
  have hClo := patchG.disk_outerC_face_closure
  have hCloR : Closure Gd.fsetoid _ := reflTransGen_closure_iff.mpr hClo
  have ih := Fintype.nCompSet_inex_of_closure (D:={x | hd x ∈ patchG.outerᶜ}) hCloR
  unfold fcomp
  rw[ih]
  congr
  · {
    apply Fintype.nComp_adjunctionOn_partial
    apply adjunctionOn_of_strict
    · exact patchG.outerC_face_closure
    · exact ⟨fun _ _ => G.cface_equivalence.symm⟩
    · exact ⟨fun _ _ => Gd.cface_equivalence.symm⟩
    · exact patchG.disk_hom_injective
    · intro y hy; exact patchG.outerC_subset_disk hy
    intro x y (hx : _ ∉ _)
    unfold fromFun
    have hx' : x ∉ bGd := by{
      contrapose hx
      apply patchG.border_subset_outer
      exact patchG.disk_mem_border_iff.mpr hx
    }
    rw[← patchG.disk_face_morph _ hx', patchG.disk_hom_injective.eq_iff]
  }
  · {
    have hset : {x | hd x ∈ patchG.outerᶜ}ᶜ = {x | hd x ∈ patchG.outer} := by{
      ext x
      simp
    }
    simp only [hset, ← patchG.mem_borderFband_iff, mem_fband_iff]
    rw[← List.Subtype.fintype_card_eq_length_of_nodup patchG.disk_border_cycle.nodup]
    unfold Fintype.nCompSet Fintype.nComp
    simp only
    let e : {x // x ∈ bGd} ≃
      Quotient ⟨_, LiftOn_equivalence_of_equivalence {x | ∃y ∈ bGd, Gd.cface x y} Gd.fsetoid.iseqv⟩
    := by{
      let f : {x // x ∈ bGd} →
        Quotient ⟨_, LiftOn_equivalence_of_equivalence
        {x | ∃y ∈ bGd, Gd.cface x y} Gd.fsetoid.iseqv⟩
      :=
        fun x => ⟦⟨x.val, ⟨x.val, x.prop, ReflTransGen.refl⟩⟩⟧
      apply Equiv.ofBijective f; constructor
      · {
        intro x y hxy
        unfold f at hxy
        rw[Quotient.eq] at hxy
        simp only [LiftOn] at hxy
        change Gd.cface _ _ at hxy
        have hxy' := (patchG.disk_border_cface_unique x.prop hxy).mp y.prop
        exact Subtype.ext hxy'.symm
      }
      · {
        intro y
        have ⟨x, hx, hxy⟩:=y.out.prop
        use ⟨x, hx⟩
        unfold f
        simp only
        rw[Quotient.mk_eq_iff_out]
        change LiftOn _ _ _ _
        simp only [LiftOn]
        change Gd.cface _ _
        exact Gd.cface_equivalence.symm hxy
      }
    }
    have he := Fintype.ofEquiv_card e
    rw[← he]
    congr
    apply Subsingleton.elim
  }
}

theorem disk_gcomp : Gd.gcomp = Fintype.nCompSet G.gsetoid patchG.remGClosureᶜ
  + if bGr = [] then 0 else 1 := by{
  have hClo := patchG.disk_remGClosureC_glink_closure
  have hCloR : Closure Gd.gsetoid _ := reflTransGen_closure_iff.mpr hClo
  have ih := Fintype.nCompSet_inex_of_closure (D:={x | hd x ∈ patchG.remGClosureᶜ}) hCloR
  unfold gcomp
  rw[ih]
  congr
  · {
    apply Fintype.nComp_adjunctionOn_partial
    rw[← adjunctionOn_reflTransGen_left_iff, ← adjunctionOn_reflTransGen_right_iff]
    apply adjunctionOn_of_strict
    · rw[reflTransGen_closure_iff]; exact patchG.remGClosureC_glink_closure
    · simp only [reflTransGen_idem]
      exact ⟨fun _ _ => G.cglink_equivalence.symm⟩
    · simp only [reflTransGen_idem]
      exact ⟨fun _ _ => Gd.cglink_equivalence.symm⟩
    · exact patchG.disk_hom_injective
    · intro y hy; exact patchG.remGClosureC_subset_disk hy
    intro x y (hx : _ ∉ _)
    apply patchG.disk_remGClosureC_cglink_iff hx
  }
  · {
    have hset : {x | hd x ∈ patchG.remGClosureᶜ}ᶜ = {x | hd x ∈ patchG.remGClosure} := by{
      ext x
      simp
    }
    simp only [hset, remGClosure, Set.mem_setOf]
    rcases eq_or_ne bGr [] with bGrn | bGrn
    · {
      simp only [bGrn, ↓reduceIte]
      unfold Fintype.nCompSet
      simp only
      rw[Fintype.nComp_eq_zero_iff]
      simp only [Set.mem_setOf_eq]
      rw[isEmpty_iff]
      intro ⟨a, b, hb⟩
      have ⟨c, hc, _⟩ := patchG.exists_border_of_cglink_rem_disk (by{simp}) (by{simp}) hb
      rw[patchG.mem_border_iff_rem] at hc
      unfold remBorder at hc
      simp[bGrn] at hc
    }
    simp only [bGrn, ↓reduceIte]
    unfold Fintype.nCompSet
    simp only
    rw[Fintype.nComp_eq_one_iff_nonempty_all]
    simp only [Set.mem_setOf_eq, nonempty_subtype, LiftOn, Subtype.forall, forall_exists_index]
    constructor
    · {
      have ⟨a, l, hal⟩:=List.exists_cons_of_ne_nil bGrn
      have ha : a ∈ bGr := by{simp[hal]}
      have ⟨b, hbe, hbn⟩ := patchG.exists_galois_en_of_mem_bGr ha
      use (edge b), a
      rw[hbe]
      apply ReflTransGen.refl
    }
    intro xd yr hyrxd zd wr hwrzd
    change Gd.cglink xd zd
    have ⟨ar, ad, ha0, ha1, ha2⟩ := patchG.exists_border_of_cglink_rem_disk' hyrxd
    have ⟨br, bd, hb0, hb1, hb2⟩ := patchG.exists_border_of_cglink_rem_disk' hwrzd
    apply Gd.cglink_equivalence.trans (cglink_equivalence.symm ha2)
    apply cglink_equivalence.trans ?_ hb2
    apply cglink_of_cedge
    apply patchG.disk_cedge_of_mem_border
    · exact patchG.border_antisymm_disk.mp ⟨_, ha0⟩
    · exact patchG.border_antisymm_disk.mp ⟨_, hb0⟩
  }
}

theorem genus_eq_add : G.genus = Gd.genus + Gr.genus := by{
  unfold genus
  apply Nat.mul_left_cancel (n:=2) (by{simp})
  rw[mul_add, Nat.mul_div_cancel' G.always_even_genus]
  rw[Nat.mul_div_cancel' Gd.always_even_genus]
  rw[Nat.mul_div_cancel' Gr.always_even_genus]
  rw[Nat.sub_eq_iff_eq_add G.always_nneg_genus]
  rw[add_right_comm, ← Nat.add_sub_assoc Gr.always_nneg_genus]
  apply Nat.eq_sub_of_add_eq
  rw[add_assoc, add_comm (_ - _), ← Nat.add_sub_assoc Gd.always_nneg_genus]
  apply Nat.eq_sub_of_add_eq
  unfold euler_lhs euler_rhs
  rw[patchG.disk_fcomp]
  rw[Nat.add_comm _ bGd.length, Nat.add_left_comm _ bGd.length]
  rw[Nat.add_left_comm _ bGd.length, ← add_assoc]
  rw[Nat.add_right_comm _ _ bGd.length]
  rw[Nat.add_assoc _ (Fintype.card α)]
  have h0 : bGd.length = patchG.diskBorder.length := by{simp}
  rw[h0, ← patchG.card_inex]
  simp only [Nat.add_assoc, Nat.add_left_comm _ (Fintype.card αd), Nat.add_comm _ (Fintype.card αd)]
  simp only [Nat.add_left_comm _ (Fintype.card αr)]
  congr 2
  rw[patchG.rem_ecomp, patchG.disk_ecomp]
  simp only [Nat.add_left_comm _ (Fintype.nCompSet G.esetoid patchG.rem)]
  simp only [Nat.add_assoc, Nat.add_left_comm _ (Fintype.nCompSet G.esetoid patchG.remᶜ)]
  rw[← Nat.add_assoc, Nat.add_comm (Fintype.nCompSet _ _)]
  rw[← Fintype.nCompSet_inex_of_closure (by{
    change Closure G.cedge _
    unfold Closure
    have ih := patchG.rem_cedge_close
    unfold cedge funReflTransGen
    simp only [reflTransGen_idem]
    exact ih
  })]
  congr 1
  rw[patchG.rem_ncomp, patchG.disk_ncomp]
  simp only [Nat.add_assoc, Nat.add_left_comm _ (Fintype.nCompSet G.nsetoid patchG.disk)]
  simp only [Nat.add_left_comm _ (Fintype.nCompSet G.nsetoid patchG.diskᶜ)]
  rw[← Nat.add_assoc, Nat.add_comm (Fintype.nCompSet _ _)]
  rw[← Fintype.nCompSet_inex_of_closure (by{
    change Closure G.cnode _
    unfold Closure
    have ih := patchG.disk_cnode_close
    unfold cnode funReflTransGen
    simp only [reflTransGen_idem]
    exact ih
  })]
  congr 1
  rw[patchG.rem_fcomp]
  simp only [Nat.add_left_comm _ (Fintype.nCompSet G.fsetoid patchG.outer)]
  simp only [Nat.add_comm _ (Fintype.nCompSet G.fsetoid patchG.outerᶜ),
    Nat.add_left_comm _ (Fintype.nCompSet G.fsetoid patchG.outerᶜ)]
  rw[← Nat.add_assoc, Nat.add_comm (Fintype.nCompSet _ _)]
  rw[← Fintype.nCompSet_inex_of_closure (by{
      change Closure G.cface _
      unfold Closure
      have ih := patchG.outer_cface_close
      unfold cface funReflTransGen
      simp only [reflTransGen_idem]
      exact ih
    })]
  congr 1
  rw[patchG.rem_gcomp, patchG.disk_gcomp]
  rw[Nat.add_mul, ← Nat.add_assoc (Fintype.nCompSet _ _ * _), ← Nat.add_mul]
  rw[← Fintype.nCompSet_inex_of_closure (by{
      change Closure G.cglink _
      unfold Closure
      have ih := patchG.remGClosure_glink_close
      unfold cglink
      simp only [reflTransGen_idem]
      exact ih
    })]
  congr 1
  rw[Nat.mul_two]
  congr
  simp only [eq_iff_iff]
  simp only [List.eq_nil_iff_length_eq_zero, patchG.disk_rem_border_length_eq']
}
theorem planar_patch_iff : G.Planar ↔ Gd.Planar ∧ Gr.Planar := by{
  simp only [planar_def]
  rw[patchG.genus_eq_add, Nat.add_eq_zero_iff]
}

end Patch
end Hypermap
