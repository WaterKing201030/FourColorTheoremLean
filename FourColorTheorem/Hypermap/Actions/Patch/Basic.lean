import FourColorTheorem.Hypermap.Actions.Patch.Defs

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

theorem disk_face_eq_face_rem_iff {xd : αd} {xr : αr} :
  (hd (face xd) = face (hr xr)) ↔ hd xd = hr (face xr) := by{
    nth_rw 2 [← enf_cancel xd]
    rw[patchG.galois_connect_edge_node, patchG.disk_node_morph]
    nth_rw 2 [← edge_inj]
    rw[← patchG.rem_edge_morph, enf_cancel]
    nth_rw 2 [← face_inj]
    rw[fen_cancel]
  }

theorem disk_border_cface_unique {xd yd : αd} (hxd : xd ∈ bGd) (hxdyd : Gd.cface xd yd)
  : yd ∈ bGd ↔ yd = xd := by{
    have ih := patchG.disk_border_cycle.simple
    unfold simpleList at ih
    rw[List.nodup_map_iff_inj_on patchG.disk_border_cycle.nodup] at ih
    constructor
    · {
      intro hyd
      specialize ih _ hxd _ hyd
      symm; apply ih
      rw[Quotient.eq_iff_equiv]
      exact hxdyd
    }
    · intro h; exact h ▸ hxd
  }
theorem cface_of_disk_cface {xd yd : αd} (hxdyd : Gd.cface xd yd) : G.cface (hd xd) (hd yd) := by{
  have hwlog {xd yd : αd} :
  (∃n, Gd.face^[n] xd = yd ∧ ∀m < n, Gd.face^[m] xd ∉ bGd) → G.cface (hd xd) (hd yd) := by{
    intro ⟨n, hn0, hn1⟩
    rw[cface, funReflTransGen_iff_iterate]
    use n
    induction n generalizing yd with
    | zero => simp at hn0; simp[hn0]
    | succ n' ih => {
      specialize ih rfl (fun m hmn' => hn1 m (Nat.lt_succ_of_lt hmn'))
      rw[iterate_succ_apply'] at hn0
      rw[iterate_succ_apply', ih, ← patchG.disk_face_morph, hn0]
      apply hn1; simp
    }
  }
  have hydxd := Gd.cface_equivalence.symm hxdyd
  rw[cface, funReflTransGen_iff_iterate_minimal] at hxdyd hydxd
  have ⟨nx, hnxy, hnxm⟩ := hxdyd
  have ⟨ny, hnyx, hnym⟩ := hydxd
  rcases em (∀m < nx, Gd.face^[m] xd ∉ bGd) with himpx | himpx
  · {
    apply hwlog
    use nx
  }
  rcases em (∀m < ny, Gd.face^[m] yd ∉ bGd) with himpy | himpy
  · {
    apply G.cface_equivalence.symm
    apply hwlog
    use ny
  }
  have hxy : xd = yd := by{
    simp only [not_forall, Decidable.not_not] at himpx himpy
    simp only [exists_prop] at himpx himpy
    have ⟨mx, hmxn, hmxb⟩:=himpx
    have ⟨my, hmyn, hmyb⟩:=himpy
    have hcxm : Gd.cface xd (face^[mx] xd) := by apply funReflTransGen.iterate
    have hcym : Gd.cface yd (face^[my] yd) := by apply funReflTransGen.iterate
    have hcxy : Gd.cface xd yd := by rw[← hnxy]; apply funReflTransGen.iterate
    have ih0 : Gd.cface (face^[mx] xd) (face^[my] yd) :=
      (Gd.cface_equivalence.symm hcxm).trans (hcxy.trans hcym)
    have ih := (patchG.disk_border_cface_unique hmxb ih0).mp hmyb
    rcases lt_trichotomy (nx - mx) (ny - my) with hnmxy | hnmxy | hnmxy
    · {
      exfalso
      apply hnym ((ny - my) - (nx - mx)) (by omega)
      rw[← hnxy, ← iterate_add_apply, ← Nat.sub_add_comm (Nat.le_of_lt hnmxy)]
      rw[Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self (Nat.le_of_lt hmxn)]
      rw[iterate_add_apply, ← ih, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmyn), hnyx]
    }
    · rw[← hnyx, ← Nat.sub_add_cancel (Nat.le_of_lt hmyn), iterate_add_apply, ← hnmxy, ih,
      ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmxn), hnxy]
    · {
      exfalso
      apply hnxm ((nx - mx) - (ny - my)) (by omega)
      rw[← hnyx, ← iterate_add_apply, ← Nat.sub_add_comm (Nat.le_of_lt hnmxy)]
      rw[Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self (Nat.le_of_lt hmyn)]
      rw[iterate_add_apply, ih, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmxn), hnxy]
    }
  }
  rw[hxy]
  apply ReflTransGen.refl
}

theorem cface_of_rem_cface {xr yr : αr} (hxryr : Gr.cface xr yr) : G.cface (hr xr) (hr yr) := by{
  rw[cface, funReflTransGen_iff_iterate] at hxryr
  have ⟨n, hnxy⟩:=hxryr; clear hxryr
  induction n generalizing xr with
  | zero => simp at hnxy; simp[hnxy, cface, funReflTransGen]; rfl
  | succ n' ih => {
    specialize ih (xr := face xr) (by{rw[← iterate_succ_apply, hnxy]})
    apply funReflTransGen.trans ?_ ih
    rcases em' (face xr ∈ bGr) with b_xr | b_xr
    · {
      have ih' := patchG.rem_face_morph xr (by{
        simp only [List.mem_map]
        intro ⟨xr', hxr'b, hxr'r⟩
        rw[faceinv_eq_iff_eq_face] at hxr'r
        rw[hxr'r] at hxr'b
        contradiction
      })
      rw[ih']
      apply funReflTransGen.single
    }
    have ⟨xd, hxde, hxrn⟩ := patchG.exists_galois_en_of_mem_bGr b_xr
    rw[← G.edge_inj, ← patchG.rem_edge_morph, enf_cancel] at hxrn
    rw[← hxrn, ← hxde]
    apply funReflTransGen.trans (funReflTransGen.single _ _)
    rw[← comp_apply (f:=G.face) (g:=G.edge), ← G.nodeinv_eq, ← patchG.disk_nodeinv_morph,
    Gd.nodeinv_eq, comp_apply]
    apply G.cface_equivalence.symm
    apply patchG.cface_of_disk_cface
    apply funReflTransGen.single
  }
}
theorem rem_cface_of_cface {xr yr : αr} (hxryr : G.cface (hr xr) (hr yr)) : Gr.cface xr yr := by{
  -- 我们泛化hr xr为x
  -- 若x在rem中，则只需证x对应的xr得到Gr.cface xr yr
  -- 考虑x的下一步，若
  -- 否则，不存在这样的xr，但是有xd。引入新谓词cFdr，假设存在一个边界点，这个边界点在Gd.cface上和该点连接。
  let cFdr : α → αr → Prop := fun x xr =>
    ∃xd, hd xd = x ∧ ∃yd, hd yd = hr xr ∧ Gd.cface yd xd
  generalize hrxrx : hr xr = x
  have ind_tmp : if x ∈ patchG.rem then x = hr xr else cFdr x xr := by{simp[← hrxrx]}
  rw[hrxrx] at hxryr
  clear hrxrx
  rw[cface, funReflTransGen_iff_iterate] at hxryr
  have ⟨n, hn⟩:=hxryr
  clear hxryr
  induction n generalizing x xr with
  | zero => {
    simp at hn
    simp[hn, patchG.rem_hom_injective.eq_iff] at ind_tmp
    simp[ind_tmp, cface, funReflTransGen]
    rfl
  }
  | succ n' ih => {
    have ih' := fun xr h => ih (xr := xr) (face x) h (by{rw[← iterate_succ_apply, hn]})
    cases em (x ∈ patchG.rem) with
    | inl hxr => {
      simp only [hxr, ↓reduceIte] at ind_tmp
      suffices H : Gr.cface (face xr) yr by apply funReflTransGen.head rfl H
      apply ih'
      cases em (face xr ∈ bGr) with
      | inl hfxb => {
        have ⟨xd, hxde, hxdn⟩ := patchG.exists_galois_en_of_mem_bGr hfxb
        have hxde' := hxde
        rw[← patchG.disk_face_eq_face_rem_iff] at hxde'
        rw[← hxde]
        unfold cFdr
        rw[ind_tmp, ← hxde', ← hxde]
        simp only [patchG.disk_hom_injective.eq_iff, ↓existsAndEq, true_and]
        have lem : Gd.cface _ _ := funReflTransGen.single Gd.face (edge xd)
        simp only [lem, if_true_right]
        intro hdd
        rw[mem_rem_iff_disk] at hdd
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply, not_true_eq_false, List.mem_map,
          false_or, patchG.disk_hom_injective.eq_iff, ↓ existsAndEq, and_true] at hdd
        have hxde' := patchG.border_antisymm_disk.mp ⟨_, hxde.symm⟩
        refine (patchG.disk_border_cface_unique hxde' ?_).mp hdd
        exact funReflTransGen.single _ _
      }
      | inr hfxb => {
        have hfi := patchG.rem_face_morph' _ hfxb
        rw[hfi, ind_tmp, ← hfi]
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply, ↓reduceIte]
      }
    }
    | inr hxr => {
      have ⟨hxd, hxb⟩ := not_or.mp (hxr ∘ patchG.mem_rem_iff.mpr)
      rw[not_not] at hxd
      simp only [hxr, ↓reduceIte] at ind_tmp
      have ⟨xd, Dxd, yd, Dyd, ydFxd⟩:=ind_tmp
      have hxdb : xd ∉ bGd := (Dxd ▸ hxb) ∘ patchG.disk_mem_border_iff.mpr
      have hfi := patchG.disk_face_morph _ hxdb
      have hfxd : face x ∈ patchG.disk := by{
        rw[← Dxd, ← hfi]
        simp
      }
      cases em (face x ∈ patchG.rem) with
      | inl hfxr => {
        simp only [hfxr, ↓reduceIte] at ih'
        have ydFxd' : Gd.cface _ _ := ydFxd.tail rfl
        have hfxb : face x ∈ patchG.border := by{simp[← patchG.disk_inter_rem, hfxd, hfxr]}
        rw[← Dxd, ← hfi, disk_mem_border_iff] at hfxb
        apply ih'
        rw[← Dxd, ← hfi, ← Dyd]
        congr
        apply (patchG.disk_border_cface_unique ?_ ydFxd').mp hfxb
        exact patchG.border_antisymm_disk.mp ⟨_, Dyd.symm⟩
      }
      | inr hfxr => {
        simp only [hfxr, ↓reduceIte] at ih'
        apply ih'
        unfold cFdr
        rw[← Dxd, ← hfi, ← Dyd]
        simp only [patchG.disk_hom_injective.eq_iff, exists_eq_left]
        apply ydFxd.tail rfl
      }
    }
  }
}
theorem rem_cface_iff {xr yr : αr} : Gr.cface xr yr ↔ G.cface (hr xr) (hr yr) :=
  ⟨patchG.cface_of_rem_cface, patchG.rem_cface_of_cface⟩

theorem rem_cedge_close : ∀x ∈ patchG.rem, ∀y, G.cedge x y → y ∈ patchG.rem := by{
  intro x hx y hxy
  rw[cedge, funReflTransGen_iff_iterate] at hxy
  have ⟨n, hnxy⟩ := hxy; clear hxy
  rw[rem, Set.mem_setOf] at hx
  rw[rem, Set.mem_setOf]
  have ⟨xr, hxr⟩:=hx
  clear hx
  rw[← hnxy, ← hxr]
  use edge^[n] xr
  induction n generalizing y with
  | zero => simp
  | succ n' ih => {
    specialize ih (edge^[n'] x) rfl
    rw[iterate_succ_apply', patchG.rem_edge_morph, ih, iterate_succ_apply']
  }
}
theorem disk_cnode_close : ∀x ∈ patchG.disk, ∀y, G.cnode x y → y ∈ patchG.disk := by{
  intro x hx y hxy
  rw[cnode, funReflTransGen_iff_iterate] at hxy
  have ⟨n, hnxy⟩ := hxy; clear hxy
  rw[disk, Set.mem_setOf] at hx
  rw[disk, Set.mem_setOf]
  have ⟨xd, hxd⟩:=hx
  clear hx
  rw[← hnxy, ← hxd]
  use node^[n] xd
  induction n generalizing y with
  | zero => simp
  | succ n' ih => {
    specialize ih (node^[n'] x) rfl
    rw[iterate_succ_apply', patchG.disk_node_morph, ih, iterate_succ_apply']
  }
}

theorem rem_cedge_iff {xr yr : αr} : Gr.cedge xr yr ↔ G.cedge (hr xr) (hr yr) := by{
  have h : AdjunctionOn hr (fromFun edge) (fromFun edge) patchG.rem := by{
    apply adjunctionOn_of_strict
    · apply patchG.rem_cedge_close
    · exact ⟨fun _ _ => G.cedge_equivalence.symm⟩
    · exact ⟨fun _ _ => Gr.cedge_equivalence.symm⟩
    · exact patchG.rem_hom_injective
    · intro y hy; exact hy
    simp[fromFun, ← patchG.rem_edge_morph, patchG.rem_hom_injective.eq_iff]
  }
  have h' := h.functor xr yr
  simp only [Set.mem_setOf_eq, exists_apply_eq_apply, forall_const] at h'
  exact h'
}

theorem rem_border_node_closure : Closure (fromFun Gr.node) {x | x ∈ bGr} := by{
  unfold Closure
  intro x (hx : _ ∈ bGr) y
  have ih := patchG.rem_border_cnode_close hx (yr:=y)
  exact ih.mp
}
theorem rem_node_closure : Closure (fromFun Gr.node) {x | x ∉ bGr} := by{
  have hset : {x | x ∉ bGr} = {x | x ∈ bGr}ᶜ :=by{
    ext x
    simp
  }
  rw[hset, compl_closure_of_equivalence']
  · exact patchG.rem_border_node_closure
  · exact Gr.cnode_equivalence
}
theorem disk_border_edge_closure : Closure (fromFun Gd.edge) {x | x ∈ bGd} := by{
  unfold Closure
  intro x (hx : _ ∈ bGd) y
  have ih := patchG.disk_border_cedge_close hx (yd:=y)
  exact ih.mp
}
theorem disk_edge_closure : Closure (fromFun Gd.edge) {x | x ∉ bGd} := by{
  have hset : {x | x ∉ bGd} = {x | x ∈ bGd}ᶜ :=by{
    ext x
    simp
  }
  rw[hset, compl_closure_of_equivalence']
  · exact patchG.disk_border_edge_closure
  · exact Gd.cedge_equivalence
}

theorem rem_cnode_iff {xr yr : αr} (hxr : xr ∉ bGr) : Gr.cnode xr yr ↔ G.cnode (hr xr) (hr yr)
:= by{
  constructor
  · {
    intro h
    induction h with
    | refl => change ReflTransGen _ _ _; rfl
    | tail hh ht ih => {
      have ih' : _ ∉ _ := patchG.rem_node_closure _ hxr _ hh
      rw[fromFun] at ht
      rw[← ht, patchG.rem_node_morph _ ih']
      apply ih.tail rfl
    }
  }
  · {
    intro h
    rw[cnode, funReflTransGen_iff_iterate] at h
    have IH : ∀n, node^[n] (hr xr) = hr (node^[n] xr) := by{
      suffices IH : ∀n, node^[n] (hr xr) = hr (node^[n] xr) ∧ node^[n] xr ∉ bGr by{
        intro n; exact (IH n).left
      }
      intro n
      induction n with
      | zero => simp[hxr]
      | succ n' ih => {
        rw[iterate_succ_apply', ih.left, ← patchG.rem_node_morph _ ih.right,
          ← iterate_succ_apply' node]
        apply And.intro rfl
        have ihr := ih.right
        contrapose ihr
        have ihr' := patchG.rem_border_node_closure _ ihr
        apply ihr'
        apply Gr.cnode_equivalence.symm
        rw[iterate_succ_apply']
        apply funReflTransGen.single
      }
    }
    simp only [IH, patchG.rem_hom_injective.eq_iff] at h
    exact funReflTransGen_iff_iterate.mpr h
  }
}

theorem disk_cedge_iff {xd yd : αd} (hxd : xd ∉ bGd) : Gd.cedge xd yd ↔ G.cedge (hd xd) (hd yd)
:= by{
  constructor
  · {
    intro h
    induction h with
    | refl => change ReflTransGen _ _ _; rfl
    | tail hh ht ih => {
      have ih' : _ ∉ _ := patchG.disk_edge_closure _ hxd _ hh
      rw[fromFun] at ht
      rw[← ht, patchG.disk_edge_morph _ ih']
      apply ih.tail rfl
    }
  }
  · {
    intro h
    rw[cedge, funReflTransGen_iff_iterate] at h
    have IH : ∀n, edge^[n] (hd xd) = hd (edge^[n] xd) := by{
      suffices IH : ∀n, edge^[n] (hd xd) = hd (edge^[n] xd) ∧ edge^[n] xd ∉ bGd by{
        intro n; exact (IH n).left
      }
      intro n
      induction n with
      | zero => simp[hxd]
      | succ n' ih => {
        rw[iterate_succ_apply', ih.left, ← patchG.disk_edge_morph _ ih.right,
          ← iterate_succ_apply' edge]
        apply And.intro rfl
        have ihr := ih.right
        contrapose ihr
        have ihr' := patchG.disk_border_edge_closure _ ihr
        apply ihr'
        apply Gd.cedge_equivalence.symm
        rw[iterate_succ_apply']
        apply funReflTransGen.single
      }
    }
    simp only [IH, patchG.disk_hom_injective.eq_iff] at h
    exact funReflTransGen_iff_iterate.mpr h
  }
}


theorem outer_cface_close : ∀x ∈ patchG.outer, ∀y, G.cface x y → y ∈ patchG.outer := by{
  intro x ⟨z, hz, hzx⟩ y hxy
  exact ⟨z, hz, hzx.trans hxy⟩
}
theorem outerC_cface_close : ∀x ∉ patchG.outer, ∀y, G.cface x y → y ∉ patchG.outer := by{
  intro x hx y hxy
  revert hx
  rw[not_imp_not]
  intro hy
  apply patchG.outer_cface_close _ hy
  apply G.cface_equivalence.symm
  exact hxy
}
theorem outer_face_closure : Closure (fromFun G.face) patchG.outer :=
  patchG.outer_cface_close
theorem outerC_face_closure : Closure (fromFun G.face) patchG.outerᶜ :=
  patchG.outerC_cface_close
theorem rem_subset_outer : patchG.rem ⊆ patchG.outer := by{
  intro x hx
  rw[rem, Set.mem_setOf] at hx
  have ⟨xr, hxr⟩:=hx
  use x
  constructor
  · use xr
  · apply funReflTransGen.refl
}
theorem outerC_subset_disk : patchG.outerᶜ ⊆ patchG.disk := by{
  intro x hx
  rw[Set.mem_compl_iff] at hx
  rw[mem_disk_iff_rem]
  left
  intro hx'
  have hx'' := patchG.rem_subset_outer hx'
  contradiction
}
theorem border_subset_outer : patchG.border ⊆ patchG.outer :=
  patchG.border_subset_rem.trans patchG.rem_subset_outer
theorem outerC_subset_disk_diff_border : patchG.outerᶜ ⊆ patchG.disk \ patchG.border := by{
  intro x hx
  rw[Set.mem_diff]
  apply And.intro (patchG.outerC_subset_disk hx)
  revert hx; rw[Set.mem_compl_iff, not_imp_not]
  apply border_subset_outer
}
theorem disk_outerC_face_closure : Closure (fromFun Gd.face) {x | hd x ∈ patchG.outerᶜ} := by{
  intro x (hx : _ ∉ _) y (hxy : Gd.cface _ _)
  rw[Set.mem_setOf, Set.mem_compl_iff]
  have hxy' := patchG.cface_of_disk_cface hxy
  contrapose hx
  have ih := patchG.outer_cface_close _ hx _ (G.cface_equivalence.symm hxy')
  exact ih
}
theorem disk_outerC_cface_iff {xd yd : αd} (hxd : hd xd ∉ patchG.outer)
  : Gd.cface xd yd ↔ G.cface (hd xd) (hd yd) := by{
  constructor
  · {
    intro h
    induction h with
    | refl => change ReflTransGen _ _ _; rfl
    | tail hh ht ih => {
      have ih' : _ ∉ _ := patchG.disk_outerC_face_closure _ hxd _ hh
      rw[fromFun] at ht
      apply ih.tail
      rw[← ht, patchG.disk_face_morph]
      contrapose ih'
      apply patchG.border_subset_outer
      exact patchG.disk_mem_border_iff.mpr ih'
    }
  }
  · {
    intro h
    rw[cface, funReflTransGen_iff_iterate] at h
    have IH : ∀n, face^[n] (hd xd) = hd (face^[n] xd) := by{
      suffices IH : ∀n, face^[n] (hd xd) = hd (face^[n] xd) ∧ hd (face^[n] xd) ∉ patchG.outer by{
        intro n; exact (IH n).left
      }
      intro n
      induction n with
      | zero => simp[hxd]
      | succ n' ih => {
        have ihr := ih.right
        have ihr' : face^[n'] xd ∉ bGd := by{
          contrapose ihr
          apply patchG.border_subset_outer
          exact patchG.disk_mem_border_iff.mpr ihr
        }
        rw[iterate_succ_apply', ih.left, ← patchG.disk_face_morph _ ihr',
          ← iterate_succ_apply' face]
        apply And.intro rfl
        apply patchG.disk_outerC_face_closure _ ihr
        rw[iterate_succ_apply']
        apply funReflTransGen.single
      }
    }
    simp only [IH, patchG.disk_hom_injective.eq_iff] at h
    exact funReflTransGen_iff_iterate.mpr h
  }
}

theorem mem_borderFband_iff {xd : αd} : xd ∈ patchG.borderFband ↔ hd xd ∈ patchG.outer := by{
  constructor
  · -- 正向：xd ∈ borderFband ⇒ hd xd ∈ outer
    rw[mem_fband_iff]
    intro ⟨zd, hzd, hxdzd⟩
    have h := patchG.cface_of_disk_cface hxdzd
    have hzdb := patchG.disk_mem_border_iff.mpr hzd
    rw [mem_border_iff_rem] at hzdb
    rw [outer, Set.mem_setOf]
    use hd zd
    constructor
    · exact patchG.border_subset_rem (patchG.mem_border_iff_rem.mpr hzdb)
    · exact G.cface_equivalence.symm h
  · -- 反向：hd xd ∈ outer ⇒ xd ∈ borderFband
    intro hxd_outer
    rw [outer, Set.mem_setOf] at hxd_outer
    rcases hxd_outer with ⟨y, hyr, hyxd⟩
    rw [rem, Set.mem_setOf] at hyr
    rcases hyr with ⟨yr, hyr⟩
    rw [← hyr] at hyxd
    -- 现在有 G.cface (hd xd) (hr yr)，对称得 cface (hd xd) y
    have h := G.cface_equivalence.symm hyxd
    rw [cface, funReflTransGen_iff_iterate] at h
    rcases h with ⟨n, hn⟩
    rw[mem_fband_iff, cface]
    simp only [funReflTransGen_iff_iterate]
    simp only [↓existsAndEq, and_true]
    -- 反证法：假设对任意 k ≤ n，face^k xd ∉ bGd
    by_contra h_not
    -- 具体否定：存在某个 k≤n 使 face^k xd ∈ bGd
    push_neg at h_not
    have h_not' : ∀ k, k ≤ n → Gd.face^[k] xd ∉ bGd := fun k hk => h_not k
    -- 归纳证明：对任意 k ≤ n，G.face^k (hd xd) = hd (Gd.face^k xd)
    have H : ∀ k, k ≤ n → G.face^[k] (hd xd) = hd (Gd.face^[k] xd) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' := Nat.le_of_succ_le hk
        specialize ih hk'
        rw [iterate_succ_apply', ih, ← patchG.disk_face_morph]
        · rw[← iterate_succ_apply' Gd.face]
        · exact h_not' k hk'  -- 确保 face^k xd 不在边界，才能使用 disk_face_morph
    -- 取 k = n
    specialize H n (le_refl n)
    rw [hn] at H
    -- 现在有 hr yr = hd (Gd.face^n xd)，所以 hr yr 同时在 disk 和 rem 中
    have h_disk : hd (Gd.face^[n] xd) ∈ patchG.disk := by use Gd.face^[n] xd
    rw [← H] at h_disk
    have h_rem := hyr
    -- hr yr ∈ disk ∩ rem = border
    have h_border := patchG.disk_inter_rem' h_disk (by{simp})
    rw [H, mem_border_iff_disk, List.mem_map_of_injective patchG.disk_hom_injective] at h_border
    -- 于是 face^n xd ∈ bGd，与假设矛盾
    exact h_not' n (le_refl n) h_border
}

theorem outerC_face_morph : ∀xd, hd xd ∉ patchG.outer → hd (face xd) = face (hd xd) := by{
  intro xd hxd
  have ⟨hxd', hxb⟩ := patchG.outerC_subset_disk_diff_border hxd
  rw[disk_mem_border_iff] at hxb
  apply patchG.disk_face_morph _ hxb
}

theorem disk_cface_adjunctionOn_outerC
: AdjunctionOn hd (fromFun face) (fromFun face) patchG.outerᶜ
:= by{
  apply adjunctionOn_of_strict
  · exact patchG.outerC_cface_close
  · exact ⟨fun _ _ => G.cface_equivalence.symm⟩
  · exact ⟨fun _ _ => Gd.cface_equivalence.symm⟩
  · exact patchG.disk_hom_injective
  · intro y; apply patchG.outerC_subset_disk
  · {
    intro x y hx
    simp only [fromFun, ← patchG.outerC_face_morph _ hx, patchG.disk_hom_injective.eq_iff]
  }
}

theorem disk_cface_iff_of_mem_outerC {xd yd : αd} (hxdoc : hd xd ∉ patchG.outer)
  : Gd.cface xd yd ↔ G.cface (hd xd) (hd yd) := by{
    have ih : AdjunctionOn hd (fromFun face) (fromFun face) patchG.outerᶜ :=
      patchG.disk_cface_adjunctionOn_outerC
    exact ih.functor xd yd hxdoc
  }

theorem borderFband_face_close
: ∀x ∈ patchG.borderFband, ∀y, Gd.cface x y → y ∈ patchG.borderFband
:= by{
  intro x hx y hxy
  simp only [borderFband, fband, List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq]
  simp only [borderFband, fband, List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at hx
  have ⟨x', hx', hxx'⟩:=hx
  exact ⟨x', hx', (Gd.cface_equivalence.symm hxy).trans hxx'⟩
}
theorem borderFbandCompl_face_close
: ∀x ∉ patchG.borderFband, ∀y, Gd.cface x y → y ∉ patchG.borderFband
:= by{
  intro x hx y hxy
  revert hx; rw[not_imp_not]; intro hy
  apply patchG.borderFband_face_close _ hy
  apply Gd.cface_equivalence.symm
  exact hxy
}

theorem remGClosure_glink_close
: ∀x ∈ patchG.remGClosure, ∀y, G.cglink x y → y ∈ patchG.remGClosure
:= by{
  intro x hx y hy
  have ⟨zr, hzr⟩:=hx
  use zr
  exact hzr.trans hy
}
theorem remGClosure_glink_closure : Closure G.glink patchG.remGClosure :=
  patchG.remGClosure_glink_close
theorem remGClosureC_glink_closure : Closure G.glink patchG.remGClosureᶜ := by{
  rw[compl_closure_of_equivalence']
  · exact patchG.remGClosure_glink_closure
  exact G.cglink_equivalence
}
theorem rem_subset_remGClosure : patchG.rem ⊆ patchG.remGClosure := by{
  intro x hx
  change ∃_, _
  have ⟨xr, hxr⟩:=hx
  use xr
  rw[hxr]
  apply ReflTransGen.refl
}
theorem remGClosureC_subset_disk : patchG.remGClosureᶜ ⊆ patchG.disk := by{
  intro x hx
  rw[mem_disk_iff]
  left
  contrapose hx
  rw[Set.mem_compl_iff, not_not]
  exact patchG.rem_subset_remGClosure hx
}
theorem cglink_of_disk_cglink {xd yd : αd} (hxyd : Gd.cglink xd yd) : G.cglink (hd xd) (hd yd)
:= by{
  rw[← Gd.cclink_iff_cglink] at hxyd
  induction hxyd with
  | refl => change ReflTransGen _ _ _; rfl
  | @tail b c hh ht ih => {
    apply G.cglink_equivalence.trans ih
    rcases ht with ht | ht
    · {
      unfold fromFun at ht
      rw[nodeinv_eq_iff_eq_node] at ht
      rw[ht, patchG.disk_node_morph]
      apply G.cglink_of_cnode
      apply G.cnode_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      unfold fromFun at ht
      rw[← ht]
      apply cglink_of_cface
      apply patchG.cface_of_disk_cface
      apply funReflTransGen.single
    }
  }
}

theorem glink_of_not_mem_bGd {xd yd : αd} (hxd : xd ∉ bGd)
: Gd.glink xd yd ↔ G.glink (hd xd) (hd yd):= by{
  change _ = _ ∨ _ = _ ∨ _ = _ ↔ _ = _ ∨ _ = _ ∨ _ = _
  rw[← patchG.disk_edge_morph _ hxd, ← patchG.disk_node_morph, ← patchG.disk_face_morph _ hxd]
  simp[patchG.disk_hom_injective.eq_iff]
}

theorem disk_remGClosureC_glink_closure : Closure Gd.glink {x | hd x ∈ patchG.remGClosureᶜ} := by{
  intro x (hx : _ ∉ _) y (hy : Gd.cglink _ _)
  change hd y ∉ _
  contrapose hx
  have ih := patchG.remGClosure_glink_closure _ hx _
    (G.cglink_equivalence.symm (patchG.cglink_of_disk_cglink hy))
  exact ih
}
theorem disk_remGClosureC_cglink_iff {xd yd : αd} (hxd : hd xd ∉ patchG.remGClosure) :
  Gd.cglink xd yd ↔ G.cglink (hd xd) (hd yd) := by{
  constructor
  · apply patchG.cglink_of_disk_cglink
  intro hxyd
  have hyd : hd yd ∉ patchG.remGClosure :=
    patchG.remGClosureC_glink_closure _ hxd _ hxyd
  generalize hdyd : hd yd = y at *
  have hy : y ∈ patchG.disk := by{simp[← hdyd]}
  have hCho : Classical.choose hy = yd := by{
    have ih := Classical.choose_spec hy
    exact patchG.disk_hom_injective (ih.trans hdyd.symm)
  }
  clear hdyd
  rw[← hCho]
  clear! yd
  rw[← G.cclink_iff_cglink] at hxyd
  induction hxyd with
  | refl => {
    have hcho := Classical.choose_spec hy
    rw[patchG.disk_hom_injective hcho]
    apply ReflTransGen.refl
  }
  | @tail b c hh ht ih => {
    change G.cclink _ _ at hh
    rw[G.cclink_iff_cglink] at hh
    have hh' := patchG.remGClosureC_glink_closure _ hxd _ hh
    specialize ih hh' (patchG.remGClosureC_subset_disk hh')
    apply ih.trans
    have h0 := Classical.choose_spec (patchG.remGClosureC_subset_disk hh')
    have h1 := Classical.choose_spec hy
    rcases ht with (ht : _ = _) | (ht : _ = _)
    · {
      nth_rw 2 [← ht] at h1
      rw[eq_nodeinv_iff_node_eq, ← h0, ← patchG.disk_node_morph,
        patchG.disk_hom_injective.eq_iff] at h1
      rw[←h1]
      apply Gd.cglink_of_cnode
      apply Gd.cnode_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      rw[← h1, ← h0] at ht
      rw[← patchG.disk_face_morph _ (by{
        rw[Set.mem_compl_iff] at hh'
        contrapose hh'
        rw[← h0]
        apply patchG.rem_subset_remGClosure
        apply patchG.border_subset_rem
        rw[patchG.disk_mem_border_iff]
        exact hh'
      }), patchG.disk_hom_injective.eq_iff] at ht
      rw[← ht]
      apply Gd.cglink_of_cface
      apply funReflTransGen.single
    }
  }
}

theorem rem_glink_adjunctionOn_remGClosure :
  AdjunctionOn hr G.glink Gr.glink patchG.remGClosure
:= by{
  have hsurj : ∀ x ∈ patchG.remGClosure, ∃ x', ReflTransGen G.glink x (hr x')
  := by{
    rintro x (hx : ∃_, _)
    simp only [G.cglink_equivalence.comm] at hx
    exact hx
  }
  apply AdjunctionOn.mk
  · exact hsurj
  · {
    intro xr yr hx
    change Gr.cglink _ _ ↔ G.cglink _ _
    constructor
    · {
      intro h
      induction h with
      | refl => apply ReflTransGen.refl
      | @tail b c hh ht ih => {
        apply ih.trans
        unfold glink at ht
        change _ = _ ∨ _ = _ ∨ _ = _ at ht
        rcases ht with ht | ht | ht
        · rw[← ht, patchG.rem_edge_morph]; apply ReflTransGen.single; simp[glink, union_iff]
        · {
          rw[← ht]
          rcases em' (b ∈ bGr) with hbB | hbB
          · {
            rw[patchG.rem_node_morph _ hbB]
            apply ReflTransGen.single
            simp[glink, union_iff]
          }
          have ⟨b', hb'e, hb'n⟩ := patchG.exists_galois_en_of_mem_bGr hbB
          rw[← hb'e, ← hb'n]
          have h0 : G.cglink (hd (Gd.nodeinv b')) (hd b') := by{
            rw[patchG.disk_nodeinv_morph]
            apply ReflTransGen.single
            unfold glink
            change _ ∨ _ = _ ∨ _
            simp[nodeinv_rightinv]
          }
          refine ReflTransGen.trans ?_ h0
          apply G.cglink_of_cface
          apply patchG.cface_of_disk_cface
          rw[nodeinv_eq, comp_apply]
          apply funReflTransGen.single
        }
        · {
          rw[← ht]
          apply G.cglink_of_cface
          rw[← patchG.rem_cface_iff]
          apply funReflTransGen.single
        }
      }
    }
    · {
      intro h
      generalize x_def : hr xr = x at *
      have hx_ind : if x ∈ patchG.rem then x = hr xr else xr ∈ bGr := by{simp[← x_def]}
      clear x_def
      rw[← cclink_iff_cglink] at h
      induction h using ReflTransGen.head_induction_on generalizing xr with
      | refl => {
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply, ↓reduceIte,
        patchG.rem_hom_injective.eq_iff] at hx_ind
        rw[hx_ind]
        apply ReflTransGen.refl
      }
      | @head x' z hh ht ih => {
        have hz : z ∈ patchG.remGClosure := by{
          apply patchG.remGClosure_glink_close _ hx
          rw[← cclink_iff_cglink]
          apply ReflTransGen.single hh
        }
        simp only [hz, forall_const] at ih
        change _ = _ ∨ _ = _ at hh
        rw[nodeinv_eq_iff_eq_node] at hh
        rcases em (z ∈ patchG.rem) with hzR | hzR
        · {
          obtain ⟨zr, hzr⟩:=hzR
          simp only [← hzr, Set.mem_setOf_eq, patchG.rem_hom_injective.eq_iff, exists_eq,
            ↓reduceIte, forall_eq'] at ih
          refine Gr.cglink_equivalence.trans ?_ ih
          rw[← hzr] at hh
          clear hz
          rcases em (x' ∈ patchG.rem) with hx'R | hx'R
          · {
            simp only [hx'R, ↓reduceIte] at hx_ind
            rw[hx_ind] at hh
            clear hx hx'R hx_ind
            rcases em' (zr ∈ bGr) with hzrB | hzrB
            · {
              rw[← patchG.rem_node_morph _ hzrB, patchG.rem_hom_injective.eq_iff] at hh
              rcases hh with hh | hh
              · {
                rw[hh]
                apply Gr.cglink_of_cnode
                apply Gr.cnode_equivalence.symm
                apply funReflTransGen.single
              }
              rw[← eq_faceinv_iff_face_eq, ← patchG.rem_faceinv_morph _ hzrB,
              patchG.rem_hom_injective.eq_iff, eq_faceinv_iff_face_eq] at hh
              rw[← hh]
              apply Gr.cglink_of_cface
              apply funReflTransGen.single
            }
            have ⟨zd, hzde, hzdn⟩ := patchG.exists_galois_en_of_mem_bGr hzrB
            rw[← hzde, ← patchG.disk_node_morph] at hh
            rcases hh with hh | hh
            · {
              have hxrB : xr ∈ bGr := patchG.border_antisymm_rem.mp ⟨_, hh.symm⟩
              apply Gr.cglink_of_cnode
              exact (patchG.rem_border_cnode_close hxrB).mpr hzrB
            }
            have hfxrB : face xr ∈ bGr := by{
              by_contra hfxrB
              rw[← patchG.rem_face_morph' _ hfxrB] at hh
              have hfxrB' := patchG.border_antisymm_rem.mp ⟨_, hh.symm⟩
              contradiction
            }
            apply Gr.cglink_equivalence.trans (y := face xr)
            · apply Gr.cglink_of_cface; apply funReflTransGen.single
            apply Gr.cglink_of_cnode
            exact (patchG.rem_border_cnode_close hfxrB).mpr hzrB
          }
          · {
            simp only [hx'R, ↓reduceIte] at hx_ind
            have hzrB : zr ∈ bGr := by{
              by_contra hzrB
              rw[← patchG.rem_node_morph _ hzrB, ← eq_faceinv_iff_face_eq,
              ← patchG.rem_faceinv_morph _ hzrB] at hh
              apply hx'R
              change ∃_, _
              simp only [Eq.comm (a:=x')] at hh
              exact hh.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
            }
            apply Gr.cglink_of_cnode
            exact (patchG.rem_border_cnode_close hx_ind).mpr hzrB
          }
        }
        · {
          simp only [hzR, ↓reduceIte] at ih
          rcases em (xr ∈ bGr) with hxrB | hxrB
          · exact ih _ hxrB
          simp only [hxrB, if_false_right] at hx_ind
          rcases hx_ind with ⟨tmp, hx_ind⟩; clear tmp
          rw[hx_ind] at hh
          have ⟨hzD, hzB⟩ := not_or.mp (hzR ∘ patchG.mem_rem_iff.mpr)
          rw[not_not] at hzD
          obtain ⟨zd, hzd⟩ := hzD
          rcases hh with hh | hh
          · {
            rw[← hzd, ← patchG.disk_node_morph] at hh
            have hh' := patchG.border_antisymm_rem.mp ⟨_, hh.symm⟩
            contradiction
          }
          rw[← hzd, ← Gd.faceinv_rightinv zd, Eq.comm, patchG.disk_face_eq_face_rem_iff] at hh
          have hh' := patchG.border_antisymm_rem.mp ⟨_, hh⟩
          apply ReflTransGen.head ?_ (ih _ hh')
          simp[glink, union_iff]
        }
      }
    }
  }
  · exact patchG.remGClosure_glink_close
  · exact ⟨fun _ _ => G.cglink_equivalence.symm⟩
  · exact ⟨fun _ _ => Gr.cglink_equivalence.symm⟩
}

theorem rem_cglink_iff {xr yr : αr} :
  Gr.cglink xr yr ↔ G.cglink (hr xr) (hr yr) := by{
    have ih := patchG.rem_glink_adjunctionOn_remGClosure.functor xr yr
      (patchG.rem_subset_remGClosure (by{simp}))
    exact ih
  }

theorem exists_border_of_cglink_rem_disk' {xr : αr} {yd : αd} (hxy : G.cglink (hr xr) (hd yd)) :
  ∃zr zd, hr zr = hd zd ∧ Gr.cglink xr zr ∧ Gd.cglink zd yd := by{
  rw[← cclink_iff_cglink] at hxy
  generalize hdyd : hd yd = y
  rw[hdyd] at hxy
  have hy : y ∈ patchG.disk := by{simp[← hdyd]}
  have hCho := (Classical.choose_spec hy).trans hdyd.symm
  rw[patchG.disk_hom_injective.eq_iff] at hCho
  rw[← hCho]
  clear! yd
  induction hxy with
  | refl => {
    have hCho := Classical.choose_spec hy
    refine ⟨xr, Classical.choose hy, hCho.symm, ReflTransGen.refl, ReflTransGen.refl⟩
  }
  | @tail b c hh ht ih => {
    rcases em (b ∈ patchG.disk) with hbD | hbD
    · {
      have ih' := ih hbD
      have ⟨bd, hbd⟩ := hbD
      have ⟨cd, hcd⟩ := hy
      have hChob := (Classical.choose_spec hbD).trans hbd.symm
      have hChoc := (Classical.choose_spec hy).trans hcd.symm
      apply patchG.disk_hom_injective at hChob
      apply patchG.disk_hom_injective at hChoc
      rw[hChoc]
      rw[hChob] at ih'
      have ⟨zr, zd, h0, h1, h2⟩ := ih'
      refine ⟨zr, zd, h0, h1, h2.trans ?_⟩
      rcases ht with (ht : _ = _) | (ht : _ = _)
      · {
        rw[← hbd, ← hcd, ← patchG.disk_nodeinv_morph, patchG.disk_hom_injective.eq_iff] at ht
        rw[← ht]
        apply cglink_of_cnode
        apply cnode_equivalence.symm
        apply ReflTransGen.single
        exact nodeinv_rightinv _
      }
      · {
        rw[← hbd, ← hcd] at ht
        rcases em' (bd ∈ bGd) with hbdB | hbdB
        · {
          rw[← patchG.disk_face_morph _ hbdB, patchG.disk_hom_injective.eq_iff] at ht
          rw[← ht]
          apply cglink_of_cface
          apply funReflTransGen.single
        }
        have ⟨br, hbrbd⟩ := patchG.border_subset_rem (patchG.disk_mem_border_iff.mpr hbdB)
        have hbrB : br ∈ bGr := by{
          rw[← patchG.rem_mem_border_iff, patchG.mem_border_iff_disk]
          unfold diskBorder
          rw[List.mem_map]
          refine ⟨bd, hbdB, hbrbd.symm⟩
        }
        rw[← hbrbd, ← Gd.faceinv_rightinv cd, Eq.comm, patchG.disk_face_eq_face_rem_iff] at ht
        have hf'cdB := patchG.border_antisymm_disk.mp ⟨_, ht.symm⟩
        have hbdf'cd := patchG.disk_cedge_of_mem_border hbdB hf'cdB
        apply (cglink_of_cedge hbdf'cd).trans
        apply cglink_of_cface
        apply ReflTransGen.single
        exact faceinv_rightinv _
      }
    }
    have ⟨cd, hcd⟩ := hy
    have hChoc := (Classical.choose_spec hy).trans hcd.symm
    apply patchG.disk_hom_injective at hChoc
    rw[hChoc]
    clear ih
    rw[patchG.mem_disk_iff, not_or, not_not] at hbD
    have ⟨br, hbr⟩ := hbD.left
    rw[← hbr, ← hcd] at ht
    rcases ht with (ht : _ = _) | (ht : _ = _)
    · {
      rw[G.nodeinv_eq_iff_eq_node, ← patchG.disk_node_morph] at ht
      exfalso
      apply hbD.right
      rw[← hbr, patchG.rem_mem_border_iff, ← patchG.border_antisymm_rem]
      exact ⟨_, ht.symm⟩
    }
    rw[← Gd.faceinv_rightinv cd, Eq.comm, patchG.disk_face_eq_face_rem_iff] at ht
    refine ⟨face br, Gd.faceinv cd, ht.symm, ?_⟩
    constructor
    · {
      change G.cclink _ _ at hh
      rw[cclink_iff_cglink, ← hbr, ← patchG.rem_cglink_iff] at hh
      apply hh.trans
      apply cglink_of_cface
      apply funReflTransGen.single
    }
    apply cglink_of_cface
    apply ReflTransGen.single
    exact faceinv_rightinv _
  }
}

theorem disk_cglink_iff {xd yd : αd} : Gd.cglink xd yd ↔ G.cglink (hd xd) (hd yd) := by{
  apply Iff.intro patchG.cglink_of_disk_cglink
  intro h
  rw[← cclink_iff_cglink] at h
  generalize hdyd : hd yd = y
  rw[hdyd] at h
  have hy : y ∈ patchG.disk := by{simp[← hdyd]}
  have hCho := Classical.choose_spec hy
  apply (Eq.trans · hdyd.symm) at hCho
  rw[patchG.disk_hom_injective.eq_iff] at hCho
  rw[← hCho]
  clear! yd
  induction h with
  | refl => {
    have hCho := Classical.choose_spec hy
    apply patchG.disk_hom_injective at hCho
    rw[hCho]
    apply ReflTransGen.refl
  }
  | @tail b c hh ht ih => {
    rcases em (b ∈ patchG.disk) with hbD | hbD
    · {
      have ih' := ih hbD
      have ⟨bd, hbd⟩ := hbD
      have ⟨cd, hcd⟩ := hy
      have hChob := (Classical.choose_spec hbD).trans hbd.symm
      have hChoc := (Classical.choose_spec hy).trans hcd.symm
      apply patchG.disk_hom_injective at hChob
      apply patchG.disk_hom_injective at hChoc
      rw[hChoc]
      rw[hChob] at ih'
      apply ih'.trans
      rcases ht with (ht : _ = _) | (ht : _ = _)
      · {
        rw[← hbd, ← hcd, ← patchG.disk_nodeinv_morph, patchG.disk_hom_injective.eq_iff] at ht
        rw[← ht]
        apply cglink_of_cnode
        apply cnode_equivalence.symm
        apply ReflTransGen.single
        exact nodeinv_rightinv _
      }
      · {
        rw[← hbd, ← hcd] at ht
        rcases em' (bd ∈ bGd) with hbdB | hbdB
        · {
          rw[← patchG.disk_face_morph _ hbdB, patchG.disk_hom_injective.eq_iff] at ht
          rw[← ht]
          apply cglink_of_cface
          apply funReflTransGen.single
        }
        have ⟨br, hbrbd⟩ := patchG.border_subset_rem (patchG.disk_mem_border_iff.mpr hbdB)
        have hbrB : br ∈ bGr := by{
          rw[← patchG.rem_mem_border_iff, patchG.mem_border_iff_disk]
          unfold diskBorder
          rw[List.mem_map]
          refine ⟨bd, hbdB, hbrbd.symm⟩
        }
        rw[← hbrbd, ← Gd.faceinv_rightinv cd, Eq.comm, patchG.disk_face_eq_face_rem_iff] at ht
        have hf'cdB := patchG.border_antisymm_disk.mp ⟨_, ht.symm⟩
        have hbdf'cd := patchG.disk_cedge_of_mem_border hbdB hf'cdB
        apply (cglink_of_cedge hbdf'cd).trans
        apply cglink_of_cface
        apply ReflTransGen.single
        exact faceinv_rightinv _
      }
    }
    have ⟨cd, hcd⟩ := hy
    have hChoc := (Classical.choose_spec hy).trans hcd.symm
    apply patchG.disk_hom_injective at hChoc
    rw[hChoc]
    clear ih
    rw[patchG.mem_disk_iff, not_or, not_not] at hbD
    have ⟨br, hbr⟩ := hbD.left
    rw[← hbr, ← hcd] at ht
    rw[← hbr] at hh
    rcases ht with (ht : _ = _) | (ht : _ = _)
    · {
      rw[G.nodeinv_eq_iff_eq_node, ← patchG.disk_node_morph] at ht
      exfalso
      apply hbD.right
      rw[← hbr, patchG.rem_mem_border_iff, ← patchG.border_antisymm_rem]
      exact ⟨_, ht.symm⟩
    }
    rw[← Gd.faceinv_rightinv cd, Eq.comm, patchG.disk_face_eq_face_rem_iff] at ht
    change G.cclink _ _ at hh
    rw[cclink_iff_cglink, G.cglink_equivalence.comm] at hh
    have ⟨zr, zd, h0, h1, h2⟩ := patchG.exists_border_of_cglink_rem_disk' hh
    apply Gd.cglink_equivalence.symm at h2
    apply Gd.cglink_equivalence.trans h2
    have hzdB : zd ∈ bGd := patchG.border_antisymm_disk.mp ⟨_, h0⟩
    have hf'cdB := patchG.border_antisymm_disk.mp ⟨_, ht.symm⟩
    apply Gd.cglink_equivalence.trans
      (cglink_of_cedge (patchG.disk_cedge_of_mem_border hzdB hf'cdB))
    apply Gd.cglink_of_cface
    apply ReflTransGen.single
    exact faceinv_rightinv _
  }
}

theorem exists_border_of_cglink_rem_disk {x y : α} (hx : x ∈ patchG.rem) (hy : y ∈ patchG.disk)
  (hxy : G.cglink x y) : ∃z ∈ patchG.border, G.cglink x z ∧ G.cglink z y := by{
    rw[← G.cclink_iff_cglink] at hxy
    induction hxy with
    | refl => {
      refine ⟨x, by{rw[← patchG.disk_inter_rem, Set.mem_inter_iff]; exact ⟨hy, hx⟩}, ?_⟩
      exact ⟨ReflTransGen.refl, ReflTransGen.refl⟩
    }
    | @tail b c hh ht ih => {
      rcases em (b ∈ patchG.disk) with hbD | hbD
      · {
        have ⟨z, hz0, hz1, hz2⟩:=ih hbD
        refine ⟨z, hz0, hz1, ?_⟩
        apply hz2.trans
        rcases ht with ht | ht
        · {
          rw[← ht]
          apply G.cglink_of_cnode
          apply G.cnode_equivalence.symm
          nth_rw 2 [← G.nodeinv_rightinv b]
          apply funReflTransGen.single
        }
        · {
          rw[← ht]
          apply G.cglink_of_cface
          apply funReflTransGen.single
        }
      }
      rcases ht with (ht : _ = _) | (ht : _ = _)
      · {
        have ⟨cd, hcd⟩:=hy
        rw[← hcd, nodeinv_eq_iff_eq_node, ← patchG.disk_node_morph] at ht
        simp[ht] at hbD
      }
      · {
        rw[patchG.mem_disk_iff, not_or, not_not] at hbD
        have ⟨br, hbr⟩:=hbD.left
        have ⟨cd, hcd⟩:=hy
        rw[← hcd, ← hbr, ← Gd.faceinv_rightinv cd] at ht
        symm at ht
        rw[patchG.disk_face_eq_face_rem_iff] at ht
        use hr (Gr.face br)
        constructor
        · {
          have h0 := patchG.border_antisymm_rem.mp ⟨_, ht⟩
          rw[patchG.rem_mem_border_iff]
          exact h0
        }
        constructor
        · {
          change G.cclink _ _ at hh
          rw[G.cclink_iff_cglink] at hh
          apply hh.trans
          rw[← hbr]
          apply G.cglink_of_cface
          apply patchG.cface_of_rem_cface
          apply funReflTransGen.single
        }
        · {
          rw[← ht, ← hcd]
          apply G.cglink_of_cface
          apply patchG.cface_of_disk_cface
          apply ReflTransGen.single
          exact Gd.faceinv_rightinv _
        }
      }
    }
  }

end Patch

end Hypermap
