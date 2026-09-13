import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.GridPlane.Basic
open Function
open Relation

namespace GridPlane
namespace Matte
namespace Extend2

def ext2Hp (m : Matte) (d : GDart) : Prop :=
  (edge d).half ∈ m ∧ (edge (face d)).half ∈ m ∧ m.disk.Disjoint (GRectangle.equad d).enum

theorem ext2Hp.half_not_mem {m : Matte} {d : GDart} (h : ext2Hp m d)
  : d.half ∉ m := by{
    rw[ext2Hp] at h
    intro h'
    rw[mem_def] at h'
    have ih:=h.right.right h'
    apply ih
    rw[GRectangle.mem_enum_iff]
    apply GRectangle.half_mem_equad
  }
theorem ext2Hp.edge_face_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
  : edge (face d) ∈ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2, face_half]
    rw[ext2Hp] at h
    apply And.intro h.right.left
    apply half_not_mem h
  }
theorem ext2Hp.edge_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
  : edge d ∈ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2]
    rw[ext2Hp] at h
    apply And.intro h.left
    apply half_not_mem h
  }
theorem ext2Hp.face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: face d ∉ m.ring:= by{
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, not_and, face_half]
  have h:=half_not_mem h
  rw[mem_def] at h
  simp[h]
}
theorem ext2Hp.node_2_face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: node (node (face d)) ∉ m.ring:= by{
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, not_and]
  intro _
  rw[not_not]
  rw[←face_half, fen_cancel, ←edge_eq_node_face]
  exact h.left
}
theorem ext2Hp.node_3_face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: node (node (node (face d))) ∉ m.ring:= by{
  rw[node_3]
  intro h0
  have h1:end0 (face (edge (face d))) = end0 (edge d) := by{
    rw[face_end0, edge_end1, face_end0, edge_end0]
  }
  have h2:face (edge (face d)) ≠ edge d := fef_ne_edge
  have hs := m.ring_simple
  rw[List.nodup_map_iff_inj_on m.ring_nodup] at hs
  have hs':=hs _ h0 _ (edge_mem_ring h) h1
  exact h2 hs'
}
theorem ext2Hp.edge_face_next {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring[(m.ring.idxOf (edge (face d)) + 1) % m.ring.length]'(by{
    apply Nat.mod_lt
    apply List.length_pos_of_ne_nil
    exact m.ring_ne_nil
  }) = edge d := by{
    have hlc := m.ring_cycle
    rw[List.isCycleChain_iff_getElem m.ring_ne_nil] at hlc
    have hlc':=hlc (m.ring.idxOf (edge (face d)))
    have hef := edge_face_mem_ring h
    simp only [Nat.mod_eq_of_lt (List.idxOf_lt_length_of_mem hef)] at hlc'
    rw[List.getElem_idxOf] at hlc'
    rw[mrlink, edge_end1] at hlc'
    nth_rw 3 [edge_eq_node_face]
    symm at hlc'
    rw[end0_eq_cases_node] at hlc'
    have h0:=face_not_mem_ring h
    have h2:=node_2_face_not_mem_ring h
    have h3:=node_3_face_not_mem_ring h
    rcases hlc' with hlc' | hlc' | hlc' | hlc'
    · rw[←hlc'] at h0; simp at h0
    · rw[hlc']
    · rw[←hlc'] at h2; simp at h2
    · rw[←hlc'] at h3; simp at h3
  }
theorem ext2Hp.ring_length_ge_2 {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring.length ≥ 2 := by{
    have h0:=edge_face_mem_ring h
    have h1:=edge_mem_ring h
    have h2:=edge_face_ne_edge (d := d)
    have h3:=List.length_erase_add_one h0
    have h5:=(m.ring_nodup.mem_erase_iff).mpr ⟨h2.symm, h1⟩
    have h6:=List.length_erase_add_one h5
    rw[←h3, ←h6]
    simp
  }
theorem ext2Hp.ring_length_gt_2 {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring.length > 2 := by{
    have h0:=ring_length_ge_2 h
    have h1:=edge_face_mem_ring h
    have h2:=edge_mem_ring h
    have h3:=edge_face_ne_edge (d := d)
    apply lt_of_le_of_ne h0
    have hlc:=m.ring_cycle
    generalize hmr : m.ring = mr
    rw[hmr] at hlc h0 h1 h2
    match mr with
    | [a, b] => {
      exfalso
      simp only [List.IsCycleChain, reduceCtorEq, ↓reduceDIte, List.isChain_cons_cons,
        List.IsChain.singleton, and_true, ne_eq, List.cons_ne_self, not_false_eq_true,
        List.getLast_cons, List.getLast_singleton, List.head_cons] at hlc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
      cases h1 with
      | inl h1 => {
        have h2:=h2.resolve_left (by{intro h; simp[←h, h3] at h1})
        have hlc':=hlc.right
        rw[mrlink, ←h2, ←h1] at hlc'
        rw[edge_end0, edge_end1, end0, end1, face_half, face_mod2] at hlc'
        rw[add_left_cancel_iff] at hlc'
        symm at hlc'
        apply GPoint.ccw_2_ne hlc'
      }
      | inr h1 => {
        have h2:=h2.resolve_right (by{intro h; simp[←h, h3] at h1})
        have hlc':=hlc.left
        rw[mrlink, ←h2, ←h1] at hlc'
        rw[edge_end0, edge_end1, end0, end1, face_half, face_mod2] at hlc'
        rw[add_left_cancel_iff] at hlc'
        symm at hlc'
        apply GPoint.ccw_2_ne hlc'
      }
    }
    | _::_::_::_ => simp
  }
theorem ext2Hp.end0_face_3_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext2Hp m d)
: end0 (face (face (face d))) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext2Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  simp only [List.coe_toFinset, Set.mem_setOf_eq] at hx
  have hc':=hc.right.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply GRectangle.half_mem_equad_of_end0_eq_end0_face_3
  exact hxf
}

def ext2loop (d : GDart) := [face (face d), face (face (face d))]

theorem ext2loop_map_end0_nodup {d : GDart} : ((ext2loop d).map end0).Nodup := by{
  simp[ext2loop, face_end0_ne_end0.symm]
}
theorem ext2loop_nodup {d : GDart} : (ext2loop d).Nodup := by{
  apply List.Nodup.of_map end0
  exact ext2loop_map_end0_nodup
}
theorem ext2loop_ne_nil {d : GDart} : ext2loop d ≠ [] := by{simp[ext2loop]}
theorem head_ext2loop {d : GDart} : (ext2loop d).head ext2loop_ne_nil = face (face d) := rfl
theorem getLast_ext2loop {d : GDart} : (ext2loop d).getLast ext2loop_ne_nil = face (face (face d))
  := rfl
theorem ext2loop_isChain_mrlink {d : GDart} : (ext2loop d).IsChain mrlink := by{
  simp[ext2loop, mrlink_face]
}
theorem half_ext2loop_edge_mem_equad {d : GDart}
: ∀x ∈ ext2loop d, (edge x).half ∈ GRectangle.equad d := by{
  intro x hx
  simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx
  · {
    rw[hx]
    apply GRectangle.half_mem_equad_of_end0_eq_end0_face_3
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx, face_3, edge_2]
    apply GRectangle.half_node_mem_equad
  }
}

theorem ext2Hp.ext2loop_disjoint_ring {m : Matte} {d : GDart} (hc : ext2Hp m d)
  : (ext2loop d).Disjoint m.ring := by{
    intro x hx
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf]
    simp only [imp_false, not_and, Decidable.not_not]
    rw[ext2Hp] at hc
    intro hx'
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at hx'
    have hx'':=hc.right.right hx'
    simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at hx
    exfalso
    apply hx''
    rcases hx with hx | hx
    all_goals
    rw[GRectangle.mem_enum_iff, hx]
    simp[face_half, GRectangle.half_mem_equad]
  }
lemma ext2Hp.take_two {m : Matte} {d : GDart} (h : ext2Hp m d) :
List.take 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))
= [edge (face d), edge d] := by{
  rw[←List.cons_head_tail (by{simp[m.ring_ne_nil]}
  : m.ring.rotate (List.idxOf (edge (face d)) m.ring) ≠ [])]
  rw[List.take_succ_cons]
  simp only [List.cons.injEq]
  rw[←List.cons_head_tail (by{
    rw[ne_eq, List.eq_nil_iff_length_eq_zero]
    simp only [List.length_tail, List.length_rotate]
    intro h'
    apply Nat.le_of_sub_eq_zero at h'
    have h'':=ring_length_gt_2 h
    have h''':=lt_of_lt_of_le h'' h'
    simp at h'''
  } : (m.ring.rotate (List.idxOf (edge (face d)) m.ring)).tail ≠ [])]
  rw[List.take_succ_cons, List.take_zero]
  simp only [List.head_tail, List.getElem_rotate, List.cons.injEq, and_true]
  simp only [add_comm 1, edge_face_next h, and_true]
  have h0 := List.head_rotate_idxOf h.edge_face_mem_ring
  apply Eq.mp ?_ h0
  congr
  apply lawful_beq_subsingleton
}

def ext2Disk (m : Matte) (d : GDart) := d.half :: m.disk
def ext2Ring (m : Matte) (d : GDart) :=
  ext2loop d ++ (m.ring.rotate (m.ring.idxOf (edge (face d)))).drop 2

theorem ext2Disk_ne_nil {m : Matte} {d : GDart} : ext2Disk m d ≠ [] := by{simp[ext2Disk]}
theorem ext2Ring_ne_nil {m : Matte} {d : GDart} : ext2Ring m d ≠ [] := by{simp[ext2Ring, ext2loop]}

theorem ext2Ring_getLast {m : Matte} {d : GDart} (h : ext2Hp m d)
: (ext2Ring m d).getLast ext2Ring_ne_nil =
  (m.ring.rotate (m.ring.idxOf (edge (face d)))).getLast (by{simp[m.ring_ne_nil]}) := by{
    simp only [ext2Ring]
    have h':List.drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring)) ≠ [] := by{
      simp[ext2Hp.ring_length_gt_2 h]
    }
    rw[List.getLast_append_of_right_ne_nil _ _ h']
    rw[List.getLast_drop]
  }
theorem ext2Ring_head {m : Matte} {d : GDart}
: (ext2Ring m d).head ext2Ring_ne_nil = face (face d) := by{
    simp only [ext2Ring]
    rw[List.head_append_left ext2loop_ne_nil, head_ext2loop]
  }
theorem ext2Ring_chain {m : Matte} {d : GDart} (h : ext2Hp m d)
  : (ext2Ring m d).IsChain mrlink := by{
  rw[ext2Ring, List.isChain_append]
  apply And.intro ext2loop_isChain_mrlink
  have hc := m.ring_cycle
  have hc':=m.ring_cycle.rotate (m.ring.idxOf (edge (face d)))
  rw[List.IsCycleChain] at hc'
  rw[dite_cond_eq_false (by{simp[m.ring_ne_nil]})] at hc'
  apply And.intro (hc'.left.drop _)
  rw[List.getLast?_eq_some_getLast ext2loop_ne_nil]
  simp only [Option.mem_def, Option.some.injEq, List.head?_drop, forall_eq']
  rw[List.getElem?_eq_some_getElem (by{simp[ext2Hp.ring_length_gt_2 h]})]
  simp only [List.getElem_rotate, Option.some.injEq, forall_eq']
  rw[getLast_ext2loop]
  have h0:=ext2Hp.edge_face_next h
  have hc'':=(List.isCycleChain_iff_getElem m.ring_ne_nil).mp hc
    (m.ring.idxOf (edge (face d)) + 1)
  rw[h0] at hc''
  rw[mrlink]
  rw[mrlink] at hc''
  simp only [add_assoc, Nat.reduceAdd] at hc''
  simp only [add_comm (b:=2)] at hc''
  rw[←hc'', face_3, edge_end1, edge_end1, node_end0]
}
theorem ext2Ring_cycleChain {m : Matte} {d : GDart} (h : ext2Hp m d)
  : (ext2Ring m d).IsCycleChain mrlink := by{
    rw[List.IsCycleChain]
    rw[dite_cond_eq_false (by{simp[ext2Ring_ne_nil]})]
    apply And.intro (ext2Ring_chain h)
    rw[ext2Ring_getLast h, ext2Ring_head]
    have hc := m.ring_cycle
    have hc':=m.ring_cycle.rotate (m.ring.idxOf (edge (face d)))
    rw[List.IsCycleChain] at hc'
    rw[dite_cond_eq_false (by{simp[m.ring_ne_nil]})] at hc'
    have hc'':=hc'.right
    have h0 := List.head_rotate_idxOf (ext2Hp.edge_face_mem_ring h)
    rw[mrlink] at hc''
    rw[mrlink, hc'', face_end0, ← edge_end0, ← h0]
    congr
    apply lawful_beq_subsingleton
  }

theorem ext2Ring_simple {m : Matte} {d : GDart} (h : ext2Hp m d)
  : ((ext2Ring m d).map end0).Nodup := by{
    rw[List.nodup_map_iff_inj_on]
    · {
      have hls:=m.ring_simple
      have hld:=m.ring_nodup
      have he:=ext2Hp.edge_mem_ring h
      have hef:=ext2Hp.edge_face_mem_ring h
      intro x hx y hy hxy
      rw[ext2Ring, List.mem_append] at hx hy
      wlog hx': x ∈ ext2loop d generalizing x y with H
      · {
        apply (Or.resolve_left · hx') at hx
        cases hy with
        | inl hy => {
          have H':=H y (Or.inl hy) x (Or.inr hx) hxy.symm hy
          exact H'.symm
        }
        | inr hy => {
          have hx':=List.mem_of_mem_drop hx
          have hy':=List.mem_of_mem_drop hy
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hls
          rw[←List.map_rotate, List.nodup_map_iff_inj_on] at hls'
          · exact hls' _ hx' _ hy' hxy
          simp[hld]
        }
      }
      cases hy with
      | inl hy => {
        have hls':=ext2loop_map_end0_nodup (d:=d)
        rw[List.nodup_map_iff_inj_on] at hls'
        · exact hls' _ hx' _ hy hxy
        apply ext2loop_nodup
      }
      | inr hy => {
        rw[ext2Hp] at h
        have hy':=List.mem_rotate.mp (List.mem_of_mem_drop hy)
        have hy'':=hy'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hy'
        simp only [List.coe_toFinset, Set.mem_setOf_eq] at hy'
        have hc':=h.right.right hy'.left
        rw[GRectangle.mem_enum_iff] at hc'
        rw[ext2loop] at hx'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        exfalso
        rcases hx' with hx' | hx'
        · {
          have hyd : y = edge (face d) := by{
            have h0:end0 (edge (face d)) = end0 x:=by{
              rw[hx', edge_end0, face_end0]
            }
            rw[hxy] at h0
            rw[List.nodup_map_iff_inj_on hld] at hls
            have hls':=hls _ hef _ hy'' h0
            rw[hls']
          }
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hld
          rw[←List.take_append_drop 2
            (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at hld'
          have h_take := ext2Hp.take_two h
          rw[h_take, List.nodup_append'] at hld'
          apply (hld'.right.right · hy)
          simp[hyd]
        }
        · {
          apply hc'
          apply GRectangle.half_mem_equad_of_end0_eq_end0_face_3
          rw[←hx', hxy]
        }
      }
    }
    · {
      rw[ext2Ring, List.nodup_append']
      apply And.intro ext2loop_nodup
      apply And.intro (List.nodup_drop (List.nodup_rotate.mpr m.ring_nodup))
      apply List.disjoint_of_subset_right (List.drop_subset _ _)
      rw[List.disjoint_rotate_right]
      apply ext2Hp.ext2loop_disjoint_ring h
    }
  }

theorem mem_ext2Ring_iff {m : Matte} {d : GDart} (h : ext2Hp m d)
  : ∀x, x ∈ ext2Ring m d ↔ x ∈ border (ext2Disk m d).toFinset := by{
    intro x
    rw[ext2Ring, List.mem_append]
    rw[ext2Disk, border, Set.mem_setOf, List.coe_toFinset, Set.mem_setOf_eq, List.mem_cons]
    rw[Set.mem_setOf, List.mem_cons, not_or]
    constructor
    · {
      intro h'
      cases h' with
      | inl h' => {
        constructor
        · {
          left
          simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at h'
          rcases h' with h' | h'
          all_goals
          simp[h', face_half]
        }
        rw[ext2Hp, List.disjoint_comm] at h
        constructor
        · {
          rw[edge_half]
          simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at h'
          rcases h' with h' | h'
          all_goals
          simp only [h', face_half, face_mod2, add_sub_assoc, add_assoc, add_eq_left]
          simp only [←add_sub_assoc, sub_eq_zero]
          simp only [GPoint.ccw, GPoint.mod2]
          cases Int.emod_two_eq d.1 with | inl hx | inr hx =>
          cases Int.emod_two_eq d.2 with | inl hy | inr hy =>
            simp[hx, hy]
        }
        · {
          apply h.right.right
          rw[GRectangle.mem_enum_iff]
          apply half_ext2loop_edge_mem_equad
          exact h'
        }
      }
      | inr h' => {
        have h'':=List.mem_rotate.mp (List.mem_of_mem_drop h')
        have h''':=h''
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at h''
        simp only [List.coe_toFinset, Set.mem_setOf_eq] at h''
        refine ⟨Or.inr h''.left, ?_⟩
        rw[ext2Hp] at h
        constructor
        · {
          have hld:=m.ring_nodup
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hld
          rw[←List.take_append_drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at hld'
          rw[ext2Hp.take_two h, List.nodup_append'] at hld'
          rw[half_eq_cases_face, not_or, not_or, not_or]
          have hls'':=(hld'.right.right · h')
          simp only [List.mem_cons, List.not_mem_nil, or_false, imp_false, not_or] at hls''
          rw[←edge_inj (x:=x), ←edge_inj (x:=x), edge_2, edge_2] at hls''
          simp only [hls'', not_false_eq_true, true_and]
          constructor
          · {
            intro h0
            apply congrArg edge at h0
            rw[edge_2] at h0
            rw[h0] at h'''
            have hc':=h.right.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply GRectangle.half_mem_equad_of_end0_eq_end0_face_3
            rw[h0, edge_end0, face_end0]
          }
          · {
            intro h0
            apply congrArg edge at h0
            rw[edge_2, face_3, edge_2] at h0
            rw[h0] at h''
            have hc':=h.right.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply GRectangle.half_node_mem_equad
          }
        }
        · exact h''.right
      }
    }
    · {
      intro ⟨h0, h1, h2⟩
      cases h0 with
      | inl h0 => {
        left
        rw[half_eq_cases_face] at h0
        simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false]
        rw[←or_assoc] at h0
        apply h0.resolve_left
        rw[ext2Hp] at h
        intro h'
        apply h2
        rcases h' with h' | h'
        · rw[h']; rw[mem_def] at h; exact h.left
        · rw[h']; nth_rw 2 [mem_def] at h; exact h.right.left
      }
      | inr h0 => {
        right
        have h3 : x ∈ m.ring := by{
          rw[mem_ring_iff_mem_disk_border]
          rw[mem_border_iff, mem_def, mem_def]
          exact ⟨h0, h2⟩
        }
        have h3':=(List.mem_rotate (n:=m.ring.idxOf (edge (face d)))).mpr h3
        rw[←List.take_append_drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at h3'
        rw[List.mem_append] at h3'
        apply h3'.resolve_left
        rw[ext2Hp.take_two h]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor
        · {
          intro h
          apply h1
          rw[h, edge_2, face_half]
        }
        · {
          intro h
          apply h1
          rw[h, edge_2]
        }
      }
    }
  }

end Extend2

def extend2 {m : Matte} {d : GDart} (hd : Extend2.ext2Hp m d) : Matte where
  disk := Extend2.ext2Disk m d
  ring := Extend2.ext2Ring m d
  disk_ne_nil := Extend2.ext2Disk_ne_nil
  ring_cycle := Extend2.ext2Ring_cycleChain hd
  ring_simple := Extend2.ext2Ring_simple hd
  mem_ring_iff_mem_disk_border:=Extend2.mem_ext2Ring_iff hd
end Matte
end GridPlane
