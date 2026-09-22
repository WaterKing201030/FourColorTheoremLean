import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.GridPlane.Basic

/-! 扩展方式1：当一个像素是在一边时，可以扩展 -/

open Function
open Relation

namespace GridPlane
namespace Matte
namespace Extend1

def ext1Hp (m : Matte) (d : GDart) : Prop :=
  (edge d).half ∈ m ∧ m.disk.Disjoint (GRectangle.ehex d).enum

theorem ext1Hp.half_not_mem {m : Matte} {d : GDart} (h : ext1Hp m d)
: d.half ∉ m := by{
  rw[ext1Hp] at h
  intro h'
  rw[List.Disjoint] at h
  rw[mem_def] at h'
  have ih:=h.right h'
  apply ih
  rw[GRectangle.mem_enum_iff]
  apply GRectangle.half_mem_ehex
}
theorem ext1Hp.edge_mem_ring {m : Matte} {d : GDart} (h : ext1Hp m d)
: edge d ∈ m.ring := by{
  rw[mem_ring_iff_mem_disk_border, border]
  change _ ∧ _
  rw[Extend1.ext1Hp] at h
  apply And.intro h.left
  rw[edge_2]
  apply half_not_mem h
}

def ext1loop (d : GDart) := [face d, face (face d), face (face (face d))]
theorem ext1loop_map_end0_nodup {d : GDart} : ((ext1loop d).map end0).Nodup := by{
  simp[ext1loop, face_end0_ne_end0.symm, face_2_end0_ne_end0.symm]
}
theorem ext1loop_nodup {d : GDart} : (ext1loop d).Nodup := by{
  apply List.Nodup.of_map end0
  exact ext1loop_map_end0_nodup
}
theorem ext1loop_ne_nil {d : GDart} : ext1loop d ≠ [] := by{simp[ext1loop]}
theorem head_ext1loop {d : GDart} : (ext1loop d).head ext1loop_ne_nil = face d := rfl
theorem getLast_ext1loop {d : GDart} : (ext1loop d).getLast ext1loop_ne_nil = face (face (face d))
  := rfl
theorem ext1loop_isChain_mrlink {d : GDart} : (ext1loop d).IsChain mrlink := by{
  simp[ext1loop, mrlink_face]
}

def ext1Disk (m : Matte) (d : GDart) := d.half :: m.disk
def ext1Ring (m : Matte) (d : GDart) : List GDart :=
  ext1loop d ++ (m.ring.rotate (m.ring.idxOf (edge d))).tail

theorem ext1Disk_ne_nil {m : Matte} {d : GDart} : ext1Disk m d ≠ [] := by{simp[ext1Disk]}
theorem ext1Ring_ne_nil {m : Matte} {d : GDart} : ext1Ring m d ≠ [] := by{
  rw[ext1Ring]
  apply List.append_ne_nil_of_left_ne_nil
  exact ext1loop_ne_nil
}
theorem ext1Ring_chain {m : Matte} {d : GDart} (h : ext1Hp m d)
  : (ext1Ring m d).IsChain mrlink := by{
    have hln:=m.ring_ne_nil
    have hlc:=m.ring_cycle
    have he:=h.edge_mem_ring
    rw[ext1Ring, List.isChain_append]
    have hlc':=hlc.rotate (m.ring.idxOf (edge d))
    rw[List.IsCycleChain] at hlc'
    simp only [List.rotate_eq_nil_iff, dite_true_left] at hlc'
    have hlc'':=hlc' hln
    apply And.intro ext1loop_isChain_mrlink
    apply And.intro hlc''.left.tail
    rw[List.getLast?_eq_some_getLast ext1loop_ne_nil, getLast_ext1loop]
    simp only [Option.mem_def, Option.some.injEq, List.head?_tail, forall_eq']
    have h_lemma : 1 < m.ring.length := by{
      have hl:=List.ne_singleton_of_isCycleChain_mrlink hlc
      generalize hmr : m.ring = mr
      match mr with
      | _::_::_ => simp
      | [_] => simp[hmr] at hl
      | [] => contradiction
    }
    rw[List.getElem?_eq_some_getElem]
    · {
      simp only [Option.some.injEq, forall_eq']
      have hlc''':=List.isChain_iff_getElem.mp hlc''.left 0 (by{simp[h_lemma]})
      have h' : (m.ring.rotate (List.idxOf (edge d) m.ring)).head (by{simp[hln]}) = edge d := by{
        have h' := List.head_rotate_idxOf he
        apply Eq.mp ?_ h'
        congr
      }
      rw[List.getElem_zero_eq_head, h'] at hlc'''
      rw[mrlink] at hlc'''
      rw[mrlink, ←hlc''']
      rw[←face_end0, face_4, ←face_end0]
      nth_rw 1 [←nfe_cancel d]
      rw[node_end0]
    }
    · simp[h_lemma]
  }
theorem ext1Ring_cycleChain {m : Matte} {d : GDart} (h : ext1Hp m d)
: (ext1Ring m d).IsCycleChain mrlink := by{
  have hln:=m.ring_ne_nil
  have hlc:=m.ring_cycle
  have he:=h.edge_mem_ring
  rw[List.IsCycleChain]
  rw[dite_eq_right_of_eq_false (by{simp[ext1Ring_ne_nil]})]
  constructor
  · apply ext1Ring_chain h
  simp only [ext1Ring, List.head_append_of_ne_nil ext1loop_ne_nil, head_ext1loop]
  rw[List.getLast_append_of_right_ne_nil _ _ (by{
    have h':=List.ne_singleton_of_isCycleChain_mrlink hlc
    generalize hmr : m.ring = mr
    match mr with
    | _::_::_ => rw[ne_eq, List.eq_nil_iff_length_eq_zero]; simp
    | [_] => simp[hmr] at h'
    | [] => contradiction
  })]
  rw[List.getLast_tail]
  have hlc':=hlc.rotate (m.ring.idxOf (edge d))
  rw[List.IsCycleChain] at hlc'
  simp only [List.rotate_eq_nil_iff, dite_true_left] at hlc'
  have hlc'':=(hlc' hln).right
  rw[mrlink] at hlc''
  rw[mrlink]
  rw[hlc'']
  rw[face_end0, ← edge_end0]
  congr 1
  have h' := List.head_rotate_idxOf he
  apply Eq.mp ?_ h'
  congr
}

theorem end0_face_2_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext1Hp m d)
: end0 (face (face d)) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext1Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_ofPred] at hx
  simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hx
  have hc':=hc.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_face
  exact hxf
}
theorem end0_face_3_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext1Hp m d)
: end0 (face (face (face d))) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext1Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_ofPred] at hx
  simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hx
  have hc':=hc.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_3
  exact hxf
}
theorem ext1loop_disjoint_ring {m : Matte} {d : GDart} (hc : ext1Hp m d)
  : (ext1loop d).Disjoint m.ring := by{
    intro x hx
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_ofPred]
    simp only [imp_false, not_and, Decidable.not_not]
    rw[ext1Hp] at hc
    intro hx'
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hx'
    have hx'':=hc.right hx'
    simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at hx
    exfalso
    apply hx''
    rcases hx with hx | hx | hx
    all_goals
    rw[GRectangle.mem_enum_iff]
    simp[hx, face_half, GRectangle.half_mem_ehex]
  }
theorem half_ext1loop_edge_mem_ehex {d : GDart}
: ∀x ∈ ext1loop d, (edge x).half ∈ GRectangle.ehex d := by{
  intro x hx
  simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx
  · {
    rw[hx]
    apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_face
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx]
    apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_3
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx, face_3, edge_2]
    apply GRectangle.half_node_mem_ehex
  }
}

theorem ext1Ring_simple {m : Matte} {d : GDart} (hc : ext1Hp m d)
: ((ext1Ring m d).map end0).Nodup := by{
    have hls:=m.ring_simple
    have hld:=m.ring_nodup
    have he:=hc.edge_mem_ring
    rw[ext1Ring, List.nodup_map_iff_inj_on]
    · {
      intro x hx y hy hxy
      rw[List.mem_append] at hx hy
      wlog hx': x ∈ ext1loop d generalizing x y with H
      · {
        apply (Or.resolve_left · hx') at hx
        cases hy with
        | inl hy => {
          have H':=H y (Or.inl hy) x (Or.inr hx) hxy.symm hy
          exact H'.symm
        }
        | inr hy => {
          have hx':=List.mem_of_mem_tail hx
          have hy':=List.mem_of_mem_tail hy
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate, List.nodup_map_iff_inj_on] at hls'
          · exact hls' _ hx' _ hy' hxy
          simp[hld]
        }
      }
      cases hy with
      | inl hy => {
        have hls':=ext1loop_map_end0_nodup (d:=d)
        rw[List.nodup_map_iff_inj_on] at hls'
        · exact hls' _ hx' _ hy hxy
        apply ext1loop_nodup
      }
      | inr hy => {
        rw[ext1Hp] at hc
        have hy':=List.mem_rotate.mp (List.mem_of_mem_tail hy)
        have hy'':=hy'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_ofPred] at hy'
        simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hy'
        have hc':=hc.right hy'.left
        rw[GRectangle.mem_enum_iff] at hc'
        rw[ext1loop] at hx'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        rcases hx' with hx' | hx' | hx'
        · {
          exfalso
          have hyd : y = edge d := by{
            have h0:end0 (edge d) = end0 x:=by{
              rw[hx', edge_end0, face_end0]
            }
            rw[hxy] at h0
            rw[List.nodup_map_iff_inj_on hld] at hls
            have hls':=hls _ he _ hy'' h0
            rw[hls']
          }
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate] at hls'
          have ⟨a, l', hal'⟩:=List.exists_cons_of_ne_nil
            (l:=m.ring.rotate (List.idxOf (edge d) m.ring))
            (by{simp[m.ring_ne_nil]})
          rw[hal', List.map_cons] at hls'
          rw[List.nodup_cons] at hls'
          rw[hal', List.tail_cons] at hy
          apply hls'.left
          have h':=List.head_rotate_idxOf he
          rw[List.mem_map]
          use y, hy
          rw[hyd]
          congr 1
          rw[← h']
          change _ = (a :: l').head (by{simp})
          congr
        }
        · {
          exfalso
          apply hc'
          apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_face
          rw[←hx', hxy]
        }
        · {
          exfalso
          apply hc'
          apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_3
          rw[←hx', hxy]
        }
      }
    }
    · {
      rw[List.nodup_append']
      apply And.intro ext1loop_nodup
      constructor
      · {
        apply List.Nodup.tail
        rw[List.nodup_rotate]
        exact hld
      }
      apply List.disjoint_of_subset_right (List.tail_subset _)
      rw[List.disjoint_rotate_right]
      apply ext1loop_disjoint_ring hc
    }
  }

theorem mem_ext1Ring_iff {m : Matte} {d : GDart} (hc : ext1Hp m d) :
  ∀x, x ∈ ext1Ring m d ↔ x ∈ border (ext1Disk m d).toFinset := by{
    intro x
    rw[ext1Ring, List.mem_append]
    rw[ext1Disk, border, Set.mem_ofPred]
    simp only [List.toFinset_cons, Finset.coe_insert, List.coe_toFinset, Set.mem_insert_iff,
      Set.mem_ofPred_eq, not_or]
    constructor
    · {
      intro h
      cases h with
      | inl h => {
        constructor
        · {
          left
          simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          all_goals
          simp[h, face_half]
        }
        rw[ext1Hp, List.disjoint_comm] at hc
        constructor
        · {
          rw[edge_half]
          simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          all_goals
          simp only [h, face_half, face_mod2, add_sub_assoc, add_assoc, add_eq_left]
          simp only [←add_sub_assoc, sub_eq_zero]
          simp only [GPoint.ccw, GPoint.mod2]
          cases Int.emod_two_eq d.1 with | inl hx | inr hx =>
          cases Int.emod_two_eq d.2 with | inl hy | inr hy =>
            simp[hx, hy]
        }
        · {
          apply hc.right
          rw[GRectangle.mem_enum_iff]
          apply half_ext1loop_edge_mem_ehex
          exact h
        }
      }
      | inr h => {
        have h':=List.mem_rotate.mp (List.mem_of_mem_tail h)
        have h'':=h'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_ofPred] at h'
        simp only [List.coe_toFinset, Set.mem_ofPred_eq] at h'
        refine ⟨Or.inr h'.left, ?_⟩
        rw[ext1Hp] at hc
        constructor
        · {
          have hls:=m.ring_simple
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate] at hls'
          have h3'_lemma : m.ring.rotate (List.idxOf (edge d) m.ring) ≠ [] := by{
            rw[ne_eq, List.eq_nil_iff_length_eq_zero]
            simp[m.ring_ne_nil]
          }
          rw[←List.cons_head_tail h3'_lemma] at hls'
          have h0 : (m.ring.rotate (List.idxOf (edge d) m.ring)).head h3'_lemma = edge d
            := by{
            have h0 := List.head_rotate_idxOf (ext1Hp.edge_mem_ring hc)
            apply Eq.mp ?_ h0
            congr
          }
          rw[List.map_cons, List.nodup_cons, h0] at hls'
          have hls'':=hls'.left
          rw[List.mem_map, not_exists] at hls''
          simp only [not_and] at hls''
          have hls0:=hls'' _ h
          have hld:=m.ring_nodup
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hld
          rw[←List.cons_head_tail h3'_lemma, List.nodup_cons] at hld'
          have he:=ext1Hp.edge_mem_ring hc
          rw[h0] at hld'
          have hld'':=hld'.left
          rw[half_eq_cases_face, not_or, not_or, not_or]
          constructor
          · {
            intro h
            apply hls0
            rw[←h, edge_2]
          }
          rw[mem_ring_iff_mem_disk_border] at h''
          constructor
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2] at h
            rw[h] at h''
            unfold border at h''
            rw[Set.mem_ofPred, List.coe_toFinset, Set.mem_ofPred_eq] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_face
            rw[edge_end0, face_end0]
          }
          constructor
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2] at h
            rw[h] at h''
            unfold border at h''
            rw[Set.mem_ofPred, List.coe_toFinset, Set.mem_ofPred_eq] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply GRectangle.half_mem_ehex_of_end0_eq_end0_face_3
            rw[edge_end0, face_end0]
          }
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2, face_3, edge_2] at h
            rw[h] at h''
            unfold border at h''
            rw[Set.mem_ofPred, List.coe_toFinset, Set.mem_ofPred_eq] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply GRectangle.half_node_mem_ehex
          }
        }
        exact h'.right
      }
    }
    · {
      intro ⟨h0, h1, h2⟩
      cases h0 with
      | inl h0 => {
        left
        rw[half_eq_cases_face] at h0
        simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false]
        apply h0.resolve_left
        rw[ext1Hp] at hc
        intro h
        apply h2
        rw[h, ← mem_def]
        exact hc.left
      }
      | inr h0 => {
        right
        have h3 : x ∈ m.ring := by{
          rw[mem_ring_iff_mem_disk_border]
          refine ⟨by{simp[h0]}, by{simp[h2]}⟩
        }
        have h3':=(List.mem_rotate (n:=m.ring.idxOf (edge d))).mpr h3
        have h3'_lemma : m.ring.rotate (List.idxOf (edge d) m.ring) ≠ [] := by{
          rw[ne_eq, List.eq_nil_iff_length_eq_zero]
          simp[m.ring_ne_nil]
        }
        rw[←List.cons_head_tail h3'_lemma] at h3'
        rw[List.mem_cons] at h3'
        apply h3'.resolve_left
        have h4 : (m.ring.rotate (List.idxOf (edge d) m.ring)).head h3'_lemma = edge d := by{
          have h4 := List.head_rotate_idxOf (ext1Hp.edge_mem_ring hc)
          apply Eq.mp ?_ h4
          congr
        }
        rw[h4]
        intro h
        apply h1
        rw[h, edge_2]
      }
    }
  }

end Extend1

def extend1 {m : Matte} {d : GDart} (hd : Extend1.ext1Hp m d) : Matte where
  disk := Extend1.ext1Disk m d
  ring := Extend1.ext1Ring m d
  disk_ne_nil := Extend1.ext1Disk_ne_nil
  ring_cycle := Extend1.ext1Ring_cycleChain hd
  ring_simple := Extend1.ext1Ring_simple hd
  mem_ring_iff_mem_disk_border:=Extend1.mem_ext1Ring_iff hd
end Matte
end GridPlane
