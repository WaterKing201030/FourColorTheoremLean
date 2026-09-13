import FourColorTheorem.GridPlane.Matte.Constructors.Singleton

open Function
open Relation

namespace GridPlane
namespace Matte
namespace Refine
/- Lemmas and tools for Matte.zoom -/

def ringOf (l : List GDart) : List GDart :=
  l.flatMap (fun d => [d, face d].map (fun p => 2 • p + d.mod2))
def diskOf (l : List GPixel) : List GPixel :=
  l.flatMap Singleton.ringOf
theorem ringOf_eq_nil_iff {l : List GDart} : ringOf l = [] ↔ l = [] := by{
  simp[ringOf]
  simp[List.eq_nil_iff_forall_not_mem]
}
theorem diskOf_eq_nil_iff {l : List GPixel} : diskOf l = [] ↔ l = [] := by{
  simp[diskOf, Singleton.ringOf_eq_tuple_4]
  simp[List.eq_nil_iff_forall_not_mem]
}
@[simp] theorem ringOf_nil : ringOf [] = [] := rfl
@[simp] theorem diskOf_nil : diskOf [] = [] := rfl
@[simp] theorem ringOf_singleton {d : GDart} : ringOf [d] = [2 • d + d.mod2, 2 • face d + d.mod2] :=
  rfl
theorem diskOf_singleton_eq_ofPixel_ring {p : GPixel} : diskOf [p] = Singleton.ringOf p := rfl
@[simp] theorem diskOf_singleton {p : GPixel}
  : diskOf [p] = [2 • p, face (2 • p), face (face (2 • p)), face (face (face (2 • p)))] := by{
    rw[diskOf_singleton_eq_ofPixel_ring, Singleton.ringOf_eq_tuple_4]
  }

theorem ringOf_chain_of_chain {l : List GDart} (hl : l.IsChain mrlink)
  : (ringOf l).IsChain mrlink := by{
    match l with
    | [] => simp
    | [d] => {
      simp[ringOf, mrlink, end1, end0, GPoint.half_add_double', GPoint.half_mod2,
      GPoint.mod2_add_double', GPoint.mod2_mod2, face, GPoint.arc, add_assoc]
    }
    | d0::d1::l' => {
      rw[List.isChain_cons_cons] at hl
      have ih:=ringOf_chain_of_chain hl.right
      rw[ringOf] at ih
      rw[ringOf, List.flatMap_cons, List.map_cons, List.map_singleton]
      rw[List.cons_append, List.singleton_append, List.isChain_cons_cons]
      constructor
      · {
        simp[mrlink, end1, end0, GPoint.half_add_double', GPoint.mod2_add_double',
        GPoint.half_mod2, GPoint.mod2_mod2]
        simp[face, GPoint.arc, add_assoc]
      }
      rw[List.isChain_cons_iff_of_ne_nil (by{simp})]
      refine ⟨?_, ih⟩
      simp only [mrlink, end1, nsmul_eq_mul, Nat.cast_ofNat, GPoint.half_add_double',
        GPoint.mod2_add_double', end0, List.map_cons, List.map_nil, List.flatMap_cons,
        List.cons_append, List.nil_append, List.head_cons, GPoint.half_mod2,
        GPoint.mod2_mod2, add_zero]
      simp only [face, GPoint.arc]
      have hl' := hl.1
      simp only [mrlink, end1, end0] at hl'
      nth_rw 1 [← GPoint.double_half_add_mod2' d0]
      ring_nf
      rw[← add_mul, hl', add_mul]
      nth_rw 2 [mul_two]
      rw[← add_assoc, mul_comm, GPoint.double_half_add_mod2']
    }
  }

theorem ringOf_head {l : List GDart} (hln : l ≠ []) :
  (ringOf l).head (by{simp[ringOf_eq_nil_iff, hln]}) = 2 • (l.head hln) + (l.head hln).mod2
:= by{
  match l with | d :: _ => {
    simp[ringOf]
  }
}
theorem ringOf_getLast {l : List GDart} (hln : l ≠ []) :
  (ringOf l).getLast (by{simp[ringOf_eq_nil_iff, hln]})
  = 2 • (face (l.getLast hln)) + (l.getLast hln).mod2
:= by{
  have ⟨l', d, hl⟩:=List.ne_nil_iff_exists_concat.mp hln
  simp[ringOf, ←hl]
}

theorem ringOf_cycle_of_cycle {l : List GDart} (hl : l.IsCycleChain mrlink)
  : (ringOf l).IsCycleChain mrlink := by{
    cases em (l = []) with
    | inl hln => simp[hln]
    | inr hln => {
      rw[List.IsCycleChain, dite_cond_eq_false (by{simp[ringOf_eq_nil_iff, hln]})]
      rw[List.IsCycleChain, dite_cond_eq_false (by{simp[hln]})] at hl
      apply And.intro (ringOf_chain_of_chain hl.left)
      rw[ringOf_head hln, ringOf_getLast hln]
      rw[mrlink, end1_add_double, end0_add_double, end1_mod2, end0_mod2]
      rw[mrlink, end0, end1] at hl
      have hl':=hl.right
      rw[←eq_sub_iff_add_eq'] at hl'
      rw[hl']
      rw[←add_sub_assoc, sub_eq_iff_eq_add, add_right_comm, ←add_assoc]
      congr 1
      rw[face]
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=l.getLast hln)]
      rw[two_nsmul, add_assoc, add_assoc, add_assoc]
      symm
      rw[add_comm]
      congr 1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=l.head hln)]
      rw[two_nsmul, add_right_comm, ←add_assoc, ←add_assoc]
      congr 1
      rw[GPoint.arc, add_assoc, add_sub_cancel, hl.right]
    }
  }

theorem mem_ringOf_iff {l : List GDart} {d : GDart} : d ∈ ringOf l ↔
  ∃d0 ∈ l, d.mod2 = d0.mod2 ∧ (d.half = d0 ∨ d.half = face d0) := by{
    rw[ringOf, List.mem_flatMap]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · {
      intro ⟨d0, hd0l, hd0m⟩
      use d0
      apply And.intro hd0l
      rcases hd0m with hd0m | hd0m
      all_goals
      simp only [hd0m, GPoint.mod2_add_double, GPoint.mod2_mod2,
      GPoint.half_add_double, GPoint.half_mod2]
      simp
    }
    · {
      intro ⟨d0, hd0l, hd0m, hd0h⟩
      use d0
      apply And.intro hd0l
      rcases hd0h with hd0h | hd0h
      all_goals
      simp only [←hd0m]
      simp only [←hd0h, GPoint.double_half_add_mod2]
      simp
    }
  }

theorem ringOf_simple {l : List GDart} (hls : (l.map end0).Nodup)
  (hle : ∀ p ∈ l, edge p ∉ l) : ((ringOf l).map end0).Nodup := by{
    rw[ringOf, List.map_flatMap, List.nodup_flatMap]
    constructor
    · {
      intro x hxl
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_self, and_true]
      rw[end0, GPoint.half_add_double, GPoint.mod2_add_double,
      GPoint.half_mod2, GPoint.mod2_mod2, add_zero]
      rw[end0, GPoint.half_add_double, GPoint.mod2_add_double,
      GPoint.half_mod2, GPoint.mod2_mod2, add_zero, add_right_cancel_iff]
      exact Ne.symm face_ne
    }
    · {
      rw[List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.map_cons, List.map_nil, List.disjoint_cons_right,
        List.mem_cons, List.not_mem_nil, or_false, not_or, end0_add_double, end0_mod2]
      rw[List.nodup_iff_getElem_ne_getElem'] at hls
      simp only [List.length_map, List.getElem_map, ne_eq] at hls
      nth_rw 1 3 [←GPoint.double_half_add_mod2 (d:=l[j])]
      rw[two_nsmul]
      nth_rw 1 5 [←GPoint.double_half_add_mod2 (d:=l[i])]
      rw[two_nsmul, face, GPoint.arc, add_assoc (b:= _ - _), sub_add_cancel]
      rw[face, GPoint.arc, add_assoc (b:= _ - _), sub_add_cancel]
      nth_rw 9 11 [←GPoint.double_half_add_mod2 (d:=l[j])]
      rw[two_nsmul]
      nth_rw 5 11 [←GPoint.double_half_add_mod2 (d:=l[i])]
      rw[two_nsmul]
      rw[add_right_comm (b:=GPoint.half l[j]) (c:=GPoint.mod2 _)]
      rw[add_right_comm (b:=GPoint.half l[i]) (c:=GPoint.mod2 _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[←end0, ←end1]
      rw[←end0, ←end1]
      simp only [List.disjoint_nil_right, and_true]
      constructor
      · {
        constructor
        · {
          rw[←two_nsmul, ←two_nsmul]
          rw[smul_right_inj (by{simp})]
          apply hls
          · exact ne_of_gt hij
          · exact hj
          · exact hi
        }
        · {
          rw[←two_nsmul]
          intro h
          have ih:=GPoint.mod2_eq_zero_iff_exists_double.mpr ⟨end0 l[j], h.symm⟩
          exact end0_add_end1_mod2_ne_zero ih
        }
      }
      · {
        constructor
        · {
          rw[←two_nsmul]
          intro h
          have ih:=GPoint.mod2_eq_zero_iff_exists_double.mpr ⟨end0 l[i], h⟩
          exact end0_add_end1_mod2_ne_zero ih
        }
        · {
          rw[end0_add_end1_eq_iff_eq_or_edge_eq, not_or]
          constructor
          · {
            intro hij'
            have hls':=hls j i (ne_of_gt hij) hj hi
            apply hls'
            rw[hij']
          }
          · {
            intro hi
            apply hle l[i] (List.getElem_mem _)
            rw[←hi]
            apply List.getElem_mem
          }
        }
      }
    }
  }

theorem ringOf_def {lr : List GDart} {ld : List GPixel}
  (hld : ∀ x, x ∈ lr ↔ x ∈ border ld.toFinset) :
  ∀x, x ∈ ringOf lr ↔ x ∈ border (diskOf ld).toFinset
:= by{
  intro x
  rw[mem_ringOf_iff, border]
  have hle : ∀ p ∈ lr, edge p ∉ lr := by{
    intro p hlp
    rw[hld, border]
    rw[hld, border] at hlp
    change ¬(_ ∧ _)
    change _ ∧ _ at hlp
    simp at hlp
    simp[hlp]
  }
  change _ ↔ _ ∧ _
  simp only [List.coe_toFinset, Set.mem_setOf_eq]
  rw[diskOf, List.mem_flatMap, List.mem_flatMap, not_exists]
  simp only [Singleton.mem_ringOf_iff_half_eq]
  simp only [↓existsAndEq, and_true, not_and]
  simp only [border] at hld
  change ∀ x, x ∈ lr ↔ _ ∧ _ at hld
  have change_lemma {p : GPoint}: (∀x ∈ ld, p ≠ x) ↔ p ∉ ld := by{
    constructor
    · intro h; have h':=h p; simp at h'; simp[h']
    · intro h x hx hpx; apply h; exact hpx ▸ hx
  }
  rw[change_lemma]
  constructor
  · {
    intro ⟨d0, hd00, hd01, hd02⟩
    rw[hld] at hd00
    change _ ∧ _ at hd00
    constructor
    · {
      rcases hd02 with hd02 | hd02
      all_goals
      rw[hd02]
      simp only [List.coe_toFinset, Set.mem_setOf_eq] at hd00
      try rw[face_half]
      exact hd00.left
    }
    · {
      rw[edge_half]
      cases hd02 with
      | inl hd02 => {
        rw[hd02, hd01, add_right_comm]
        nth_rw 1 [←GPoint.double_half_add_mod2 (d:=d0)]
        rw[add_assoc (c:=d0.mod2), ←two_nsmul, ←nsmul_add, add_sub_assoc, GPoint.half_add_double]
        rw[GPoint.mod2_ccw, GPoint.half_mod2_sub_unit, ←add_sub_assoc, add_right_comm]
        rw[←GPoint.mod2_ccw, ←edge_half]
        simp only [List.coe_toFinset, Set.mem_setOf_eq] at hd00
        exact hd00.right
      }
      | inr hd02 => {
        rw[hd02, face, GPoint.arc, hd01, add_right_comm, add_assoc (b:=_ - _)]
        rw[sub_add_cancel, add_assoc, ←two_nsmul]
        nth_rw 1 [←GPoint.double_half_add_mod2 (d:=d0)]
        rw[add_right_comm, ←nsmul_add, add_sub_assoc, GPoint.half_add_double]
        rw[GPoint.half_mod2_sub_unit, ←add_sub_assoc, ←edge_half]
        simp only [List.coe_toFinset, Set.mem_setOf_eq] at hd00
        exact hd00.right
      }
    }
  }
  · {
    intro ⟨h0, h1⟩
    have h2 : x.half.half ≠ (edge x).half.half:=by{
      intro h
      apply h1
      exact h ▸ h0
    }
    rw[edge_half] at h2
    symm at h2
    nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h2
    rw[ne_eq, add_sub_assoc, add_assoc, add_assoc, GPoint.half_add_double, add_eq_left] at h2
    rw[←add_assoc, ←add_sub_assoc] at h2
    have h3:x.half.mod2 ≠ x.mod2.ccw.ccw := by{
      intro h3
      rw[h3, GPoint.ccw_2, add_right_comm, sub_add_cancel, add_sub_cancel_left] at h2
      simp[GPoint.mod2_ccw, GPoint.half_mod2] at h2
    }
    have h4:x.half.mod2 ≠ x.mod2.ccw.ccw.ccw := by{
      intro h3
      rw[h3, GPoint.ccw_2, sub_add_cancel, add_sub_cancel_left] at h2
      simp[GPoint.half_mod2] at h2
    }
    have h5:=GPoint.mod2_eq_mod2_cases (p:=x.half) (q:=x)
    simp only [h3, h4, or_self, or_false] at h5
    cases h5 with
    | inl h5 => {
      use x.half
      rw[h5]
      refine ⟨?_, rfl, Or.inl rfl⟩
      rw[hld]
      simp only [List.coe_toFinset, Set.mem_setOf_eq]
      refine ⟨h0, ?_⟩
      rw[edge, GPoint.arc, GPoint.arc, h5]
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)]
      rw[add_sub, add_assoc, h5, add_sub_cancel, ←sub_add, sub_add_eq_add_sub]
      rw[add_assoc, ←two_nsmul, ←nsmul_add, GPoint.ccw_2, ←sub_add, sub_add_eq_add_sub]
      rw[add_sub_assoc, GPoint.half_add_double, GPoint.half_mod2_sub_unit, ←add_sub_assoc]
      rw[edge_half] at h1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h1
      rw[h5, add_right_comm, add_assoc (c:=x.mod2), ←two_nsmul, ←nsmul_add] at h1
      rw[add_sub_assoc, GPoint.half_add_double, GPoint.mod2_ccw, GPoint.half_mod2_sub_unit] at h1
      rw[←GPoint.mod2_ccw, ←add_sub_assoc, add_right_comm] at h1
      exact h1
    }
    | inr h5 => {
      use edge (node x.half)
      rw[fen_cancel, edge_mod2, node_mod2, h5, GPoint.ccw_4]
      refine ⟨?_, rfl, Or.inr rfl⟩
      have h6 : (edge (node x.half)).half = x.half.half := by{
        nth_rw 2 [←fen_cancel x.half]
        rw[face_half]
      }
      rw[hld, h6]
      simp only [List.coe_toFinset, Set.mem_setOf_eq]
      refine ⟨h0, ?_⟩
      rw[edge_half, h6, edge_mod2, node_mod2, h5, GPoint.ccw_4, GPoint.ccw_4]
      rw[edge_half] at h1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h1
      rw[h5, add_assoc (c:=x.mod2.ccw), ←two_nsmul, ←nsmul_add, add_sub_assoc] at h1
      rw[GPoint.half_add_double, GPoint.half_mod2_sub_unit, ←add_sub_assoc] at h1
      exact h1
    }
  }
}

end Refine

def zoom (m : Matte) : Matte where
  disk := Refine.diskOf m.disk
  ring := Refine.ringOf m.ring
  disk_ne_nil := by{simp[Refine.diskOf_eq_nil_iff, m.disk_ne_nil]}
  ring_cycle := by{simp[Refine.ringOf_cycle_of_cycle m.ring_cycle]}
  ring_simple := by{
    apply Refine.ringOf_simple
    · exact m.ring_simple
    exact fun p => m.edge_not_mem_ring_of_mem_ring (p:=p)
  }
  mem_ring_iff_mem_disk_border := by{
    apply Refine.ringOf_def
    · exact m.mem_ring_iff_mem_disk_border
  }

theorem mem_zoom_iff {m : Matte} {p : GPixel} :
  p ∈ m.zoom ↔ p.half ∈ m := by{
    rw[mem_def, mem_def, zoom]
    simp only
    rw[Refine.diskOf, List.mem_flatMap]
    simp only [Singleton.ringOf_eq_tuple_4, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · {
      intro ⟨a, ha0, ha1⟩
      rcases ha1 with ha1 | ha1 | ha1 | ha1
      all_goals
      rw[ha1]
      simp[face_half, GPoint.half_double', ha0]
    }
    · {
      intro h
      use p.half
      apply And.intro h
      rw[←half_eq_cases_face, GPoint.half_double]
    }
  }

theorem zoom_coe {m : Matte} : (m.zoom : GRegion) = GRegion.zoom m := by{
  ext x
  simp only [List.coe_toFinset, Set.mem_setOf_eq]
  rw[GRegion.zoom, Set.mem_setOf, Set.mem_setOf, ← mem_def, mem_zoom_iff, mem_def]
}
end Matte
end GridPlane
