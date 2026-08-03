import FourColorTheorem.Hypermap.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem glink_self_of_clink_self {x : α} (hcx : H.clink x x) : H.glink x x:=by{
  rw[glink_iff]
  right
  rw[clink, union_iff, fromFun, fromFun, nodeinv_eq_iff_eq_node] at hcx
  apply hcx.imp_left
  apply Eq.symm
}

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

section fband
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
end fband

section simple
@[simp] theorem simpleList_nil : H.simpleList [] := by{simp[simpleList]}
theorem simpleList_cons {x : α} {p : List α} : H.simpleList (x :: p) ↔
  x ∉ H.fband p ∧ H.simpleList p := by{
    rw[← simpleList.rec_def_iff]
    unfold simpleList.rec_def
    rw[simpleList.rec_def_iff]
  }
@[simp] theorem simpleCycle_nil {e : α → α → Prop} : H.simpleCycle e [] := by{
  unfold simpleCycle; simp
}
end simple

section adj
theorem rlink_edge {x : α} : H.rlink x (edge x) := by{
  simp[rlink, cface, funReflTransGen.refl]
}
theorem rlink_right_congr_of_cface {y1 y2 : α} (h12 : H.cface y1 y2) {x : α}
  : H.rlink x y1 ↔ H.rlink x y2 := by{
    simp[rlink, H.cface_equivalence.comm (a:=edge x), H.cface_pred_eq_of_cface h12]
  }
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
end adj

end Hypermap
