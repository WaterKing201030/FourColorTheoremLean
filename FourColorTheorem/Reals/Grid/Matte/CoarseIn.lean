import FourColorTheorem.Reals.Grid.Matte.Basic

open Function
open Relation

namespace GridPlane
def GPoint.nd (q : GPixel) : GDart := 2 • q + q.mod2.ccw.ccw.ccw
namespace GPoint
theorem nd_half {q : GPixel} : (GPoint.nd q).half = q := by{
  rw[nd, GPoint.half_add_double]
  repeat rw[GPoint.mod2_ccw]
  rw[GPoint.half_mod2, add_zero]
}
theorem nd_mod2 {q : GPixel} : (nd q).mod2 = q.mod2.ccw.ccw.ccw := by{
  rw[nd, GPoint.mod2_add_double]
  repeat rw[GPoint.mod2_ccw]
  rw[GPoint.mod2_mod2]
}
theorem hEnd {q : GPixel} : (edge (nd q)).half = node q := by{
  rw[edge_half, nd_half, node, GPoint.arc, nd_mod2, GPoint.ccw_4]
  rw[←sub_add, sub_add_eq_add_sub, add_sub_assoc, eq_sub_iff_add_eq]
  rw[add_assoc, add_eq_left, sub_add_eq_add_sub, GPoint.ccw_2]
  simp
}
theorem ndN {q : GPixel} : nd (node q) = edge (node (edge (nd q))) := by{
  rw[←GPoint.double_half_add_mod2 (d:=edge (nd q)), hEnd]
  nth_rw 2 [←nd_half (q:=node q)]
  rw[edge_mod2, nd_mod2, ←node_mod2, ←nd_mod2]
  rw[←add_sub_cancel_right (2 • _) (nd (node q)).mod2, GPoint.double_half_add_mod2]
  rw[sub_add_eq_add_sub, add_sub_assoc]
  change _ = edge (node (face _))
  rw[enf_cancel]
}
theorem ndFE {q : GPixel} : nd (face (edge q)) = edge (face (nd q)) := by{
  nth_rw 1 [←node_4 (d:=q)]
  rw[fen_cancel, ndN, ndN, edge_2, ndN, edge_2, edge_inj]
  apply node_injective
  apply edge_injective
  rw[node_4, edge_2, enf_cancel]
}
end GPoint
namespace Matte
section extend_matte

theorem ehex_shift_quad {q q' : GPixel} :
  q' ∈ ehex q ∨ q' ∈ ehex (face (edge (face q))) →
  q' ∈ equad q ∨ q' ∈ equad (edge (face q)) := by{
    have chop1idl {q1 q2 : GPixel} {P : Prop} :
      q2 ∈ chop1 q1 ∧ P ∧ q2 ∈ chop q1 ↔ q2 ∈ chop q1 ∧ P:=by{
        constructor
        · tauto
        · intro ⟨h0, h1⟩; simp[h0, h1, chop_subset_chop1 h0]
      }
    simp only [equad, ehex, Set.mem_inter_iff,
      chopRect_toRegion, GRectangle.mem_iff_toRegion]
    rw[fef_chop_eq, ←or_and_right, and_right_comm, ←or_and_right,
      face_half, mem_edge_chop_iff]
    nth_rw 1 [←face_half]
    apply And.imp_left
    match q, q' with
    | ⟨qx, qy⟩, ⟨q'x, q'y⟩ => {
      simp only [chop, face_toUnitSquareDart, ge_iff_le, Set.mem_setOf_eq]
      simp only [GRectangle.toRegion, GPoint.touch, face, GPoint.arc, GPoint.sub_def,
        GPoint.x_ccw, GPoint.y_mod2, GPoint.x_mod2, GPoint.y_ccw, GPoint.add_def,
        GPoint.x_half, GPoint.y_half, GInterval.mem_iff, tsub_le_iff_right,
        Set.mem_setOf_eq, GPoint.toUnitSquareDart, edge]
      cases Int.emod_two_eq qx with | inl hqx | inr hqx =>
      cases Int.emod_two_eq qy with | inl hqy | inr hqy => {
        simp only [hqy, sub_self, hqx, zero_sub, Int.reduceNeg, Int.add_neg_eq_sub,
          add_zero, Int.sub_one_emod_two, sub_zero, sub_add_eq_add_sub, Int.sub_sub,
          Int.reduceAdd,
          Int.sub_ediv_of_dvd (b := 2) (c := 2) _ (by {simp}),
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Int.ediv_self, tsub_le_iff_right,
          add_assoc, add_sub_assoc, Int.reduceSub, GPoint.UnitSquareDart.ccw, one_ne_zero,
          ↓reduceIte, not_le, Int.add_one_emod_two, Int.add_ediv, Int.natAbs, Int.sign]
        omega
      }
    }
  }

theorem ehex_shift_quad_iff {q q' : GPixel} :
  q' ∈ ehex q ∨ q' ∈ ehex (face (edge (face q))) ↔
  q' ∈ equad q ∨ q' ∈ equad (edge (face q)) := by{
    apply Iff.intro ehex_shift_quad
    have chop1idl {q1 q2 : GPixel} {P : Prop} :
      q2 ∈ chop1 q1 ∧ P ∧ q2 ∈ chop q1 ↔ q2 ∈ chop q1 ∧ P:=by{
        constructor
        · tauto
        · intro ⟨h0, h1⟩; simp[h0, h1, chop_subset_chop1 h0]
      }
    simp only [equad, ehex, Set.mem_inter_iff,
      chopRect_toRegion, GRectangle.mem_iff_toRegion]
    rw[fef_chop_eq, ←or_and_right, and_right_comm, ←or_and_right,
      face_half, mem_edge_chop_iff]
    nth_rw 1 [←face_half]
    apply And.imp_left
    match q, q' with
    | ⟨qx, qy⟩, ⟨q'x, q'y⟩ => {
      simp only [chop, face_toUnitSquareDart, ge_iff_le, Set.mem_setOf_eq]
      simp only [GRectangle.toRegion, GPoint.touch, face, GPoint.arc, GPoint.sub_def,
        GPoint.x_ccw, GPoint.y_mod2, GPoint.x_mod2, GPoint.y_ccw, GPoint.add_def,
        GPoint.x_half, GPoint.y_half, GInterval.mem_iff, tsub_le_iff_right,
        Set.mem_setOf_eq, GPoint.toUnitSquareDart, edge]
      cases Int.emod_two_eq qx with | inl hqx | inr hqx =>
      cases Int.emod_two_eq qy with | inl hqy | inr hqy => {
        simp only [hqy, sub_self, hqx, zero_sub, Int.reduceNeg, Int.add_neg_eq_sub,
          add_zero, Int.sub_one_emod_two, sub_zero, sub_add_eq_add_sub, Int.sub_sub,
          Int.reduceAdd,
          Int.sub_ediv_of_dvd (b := 2) (c := 2) _ (by {simp}),
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Int.ediv_self, tsub_le_iff_right,
          add_assoc, add_sub_assoc, Int.reduceSub, GPoint.UnitSquareDart.ccw, one_ne_zero,
          ↓reduceIte, not_le, Int.add_one_emod_two, Int.add_ediv, Int.natAbs, Int.sign]
        omega
      }
    }
  }

private lemma IHp {m : Matte} {r0 r : GRectangle} {n : ℕ} (r0Emh : coarseIn r0.toRegion m)
  (r_m0 : m.disk ∩ r0.enum ⊆ r.enum) (r0_r : r ⊆ r0) (le_r_n : r.area ≤ n) {d : GDart}
  (IHn : ∀ m_1 < n,
  ∀ {r0 r : GRectangle},
    coarseIn r0.toRegion m →
      (∃ p ∈ r, p ∈ m) →
        r ⊆ r0 →
          ∀ p ∈ r0.inner,
            p ∈ r →
              m.disk ∩ r0.enum ⊆ r.enum → r.area ≤ m_1 → m.extendsIn r p)
  {p : GPixel} (Dp : d.half = p) (m_r0d : ∃ q ∈ r0.toRegion \ chop1 d, q ∈ m)
  (r0p : p ∈ r0.inner) (r_p : p ∈ r) : extendsIn m r p := by{
    let r01 := chop1Rect r0 d
    have r01p : p ∈ r01.inner := by{
      rw[mem_chop1Rect_inner_iff_mem_inner_chopRect]
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
      rw[←GRectangle.mem_iff_toRegion]
      refine ⟨r0p, Dp ▸ half_mem_chop⟩
    }
    rcases em (∃x ∈ r01, x ∈ m) with m_r01 | r01'm
    · {
      let r1 := chop1Rect r d
      have r_r1 : r1 ⊆ r := chop1Rect_subset_rect
      have area_lt : r1.area < n := by{
        apply lt_of_lt_of_le ?_ le_r_n
        have area_le : r1.area ≤ r.area := chopRect_area_le_area
        apply lt_or_eq_of_le at area_le
        apply area_le.resolve_right
        intro hn
        rw[←GRectangle.enum_length, ←GRectangle.enum_length] at hn
        rw[GRectangle.subset_iff_enum] at r_r1
        have rect_perm := List.perm_of_nodup_subset_length_eq r1.enum_nodup r.enum_nodup
          r_r1 hn
        rw[List.perm_ext_iff_of_nodup r1.enum_nodup r.enum_nodup] at rect_perm
        have ⟨q, hq0, hq1⟩:=m_r0d
        rw[Set.mem_diff] at hq0
        apply hq0.right
        simp only [GRectangle.mem_enum_iff] at rect_perm
        apply chop1Rect_subset_chop1 (r:=r)
        rw[←GRectangle.mem_iff_toRegion, rect_perm, ←GRectangle.mem_enum_iff]
        apply r_m0
        rw[List.mem_inter_iff]
        refine ⟨hq1, GRectangle.mem_enum_iff.mpr (GRectangle.mem_iff_toRegion.mpr hq0.left)⟩
      }
      have coarse_r01 : coarseIn r01.toRegion m
        := coarseIn_of_subset
          (GRectangle.subset_iff_region_subset.mp chop1Rect_subset_rect) r0Emh
      have r01_r1 : r1 ⊆ r01 := by{
        rw[GRectangle.subset_iff_region_subset]
        rw[chop1Rect_toRegion, chop1Rect_toRegion]
        apply Set.inter_subset_inter_left
        apply r0_r
      }
      have r1_m0 : m.disk ∩ r01.enum ⊆ r1.enum := by{
        intro x hx
        rw[List.mem_inter_iff] at hx
        rw[GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion, chop1Rect_toRegion] at hx
        rw[GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion, chop1Rect_toRegion]
        rw[Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff] at hx
        rw[Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff]
        rw[←and_assoc, ←List.mem_inter_iff] at hx
        refine ⟨r_m0 hx.left, hx.right⟩
      }
      have m_r1 :∃p ∈ r1, p ∈ m:=by{
        have ⟨p, hp0, hp1⟩:=m_r01
        refine ⟨p, ?_, hp1⟩
        rw[GRectangle.mem_iff_toRegion, chop1Rect_toRegion, Set.mem_inter_iff]
        rw[GRectangle.mem_iff_toRegion, chop1Rect_toRegion, Set.mem_inter_iff] at hp0
        refine ⟨?_, hp0.right⟩
        rw[←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff]
        apply r_m0
        rw[List.mem_inter_iff]
        refine ⟨hp1, GRectangle.mem_enum_iff.mpr (GRectangle.mem_iff_toRegion.mpr hp0.left)⟩
      }
      have r1_p : p ∈ r1 := by{
        rw[GRectangle.mem_iff_toRegion, chop1Rect_toRegion]
        refine ⟨r_p, ?_⟩
        have r01p':=GRectangle.inner_subset r01p
        rw[GRectangle.mem_iff_toRegion, chop1Rect_toRegion] at r01p'
        exact r01p'.right
      }
      apply extendsIn_of_subset r_r1
      apply IHn _ area_lt (r:=r1) coarse_r01 m_r1 r01_r1 _ r01p r1_p r1_m0 (le_refl _)
    }
    · {
      apply extendsIn_ehex r_p (d:=d) Dp (by{
        have h1:(ehex d).enum ⊆ r01.enum := by{
          apply List.Subset.trans
            (GRectangle.subset_iff_enum.mp ehex_subset_touch)
          apply GRectangle.subset_iff_enum.mp
          apply GRectangle.mem_inner_iff.mp
          apply Dp ▸ r01p
        }
        apply List.disjoint_of_subset_right h1
        symm
        rw[List.Disjoint]
        simp only [GRectangle.mem_enum_iff]
        simp only [not_exists, not_and] at r01'm
        exact r01'm
      })
      set r1:=chopRect r (edge d)
      have r_r1 : r1 ⊆ r := chopRect_subset_rect
      have area_lt : r1.area < n := by{
        apply lt_of_lt_of_le ?_ le_r_n
        have area_le : r1.area ≤ r.area := chopRect_area_le_area
        apply lt_or_eq_of_le at area_le
        apply area_le.resolve_right
        intro hn
        rw[←GRectangle.enum_length, ←GRectangle.enum_length] at hn
        rw[GRectangle.subset_iff_enum] at r_r1
        have rect_perm := List.perm_of_nodup_subset_length_eq r1.enum_nodup r.enum_nodup
          r_r1 hn
        rw[List.perm_ext_iff_of_nodup r1.enum_nodup r.enum_nodup] at rect_perm
        have r1_p : p ∉ r1 := by{
          rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff, not_and]
          intro _
          rw[mem_edge_chop_iff, not_not, ←Dp]
          apply half_mem_chop
        }
        apply r1_p
        simp only [GRectangle.mem_enum_iff] at rect_perm
        rw[rect_perm]
        apply r_p
      }
      have m_r1 : ∃x ∈ r1, x ∈ m := by{
        have ⟨q,hq0,hq1⟩:=m_r0d
        refine ⟨q, ?_, hq1⟩
        rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
        rw[mem_edge_chop_iff, ←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff]
        rw[Set.mem_diff, ←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff] at hq0
        constructor
        · apply r_m0; rw[List.mem_inter_iff]; exact ⟨hq1, hq0.left⟩
        · apply Set.notMem_subset chop_subset_chop1 hq0.right
      }
      have r0_r1 : r1 ⊆ r0 :=by{
        apply GRectangle.subset.trans chopRect_subset_rect
        apply r0_r
      }
      have edi : (edge d).half ∈ r0.inner := by{
        apply of_not_not
        intro h
        have h0:r0.toRegion \ chop1 d = ∅:=by{
          rw[Set.diff_eq_empty]
          rw[←Dp] at r01p
          apply rectangle_subset_chop1_of_mem_inner_of_edge_not_mem_inner
          · apply GRectangle.inner_subset_inner_of_subset chop1Rect_subset_rect r01p
          · apply h
        }
        simp[h0] at m_r0d
      }
      have r1_ed : (edge d).half ∈ r1 := by{
        have ⟨q, hq1, _⟩:=m_r1
        apply half_mem_chopRect_of_edge_mem_of_mem_chopRect (p:=q)
        · rw[edge_2, Dp]; apply r_p
        · apply hq1
      }
      have r1_m0 : m.disk ∩ r0.enum ⊆ r1.enum := by{
        intro x
        rw[GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion, chopRect_toRegion]
        rw[Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion, ←GRectangle.mem_enum_iff]
        intro h
        refine ⟨r_m0 h, ?_⟩
        simp only [not_exists, not_and,
          GRectangle.mem_iff_toRegion, r01, chop1Rect_toRegion] at r01'm
        simp only [Set.mem_inter_iff, and_imp] at r01'm
        rw[List.mem_inter_iff, GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion] at h
        rw[mem_edge_chop_iff]
        have r01'm' := (r01'm _ h.right · h.left)
        intro h'
        apply r01'm'
        apply chop_subset_chop1
        exact h'
      }
      apply IHn _ area_lt r0Emh m_r1 r0_r1 _ edi r1_ed r1_m0 (le_refl _)
    }
  }
open GPoint
theorem m_nd4_of_coarseIn {r : GRectangle} {m : Matte}
 (r0Emh : coarseIn r.toRegion m)
 {q : GPixel} (r0q : q ∈ r) (hm : ∃ x ∈ equad (nd q), x ∈ m)
: q ∈ m := by{
  have ⟨q1, m_q1, q4q1⟩:=hm
  have r0Emh':=r0Emh q r0q q1
  rw[←r0Emh']
  · exact q4q1
  rw[equad_cases, nd_half] at m_q1
  rw[edge_half, face_half, face_half] at m_q1
  rw[face_mod2, face_mod2, nd_half, nd_mod2, GPoint.ccw_4, GPoint.ccw_4] at m_q1
  rw[GPoint.ccw_2, add_right_comm, ←add_sub_assoc, ←sub_add_eq_add_sub] at m_q1
  rw[add_sub_cancel_right, add_sub_assoc, ←GPoint.arc, ←face] at m_q1
  rw[edge_half, face_half, node_half, nd_half, nd_mod2, GPoint.ccw_4] at m_q1
  rw[face_mod2, node_mod2, nd_mod2, GPoint.ccw_4, GPoint.ccw_4] at m_q1
  rw[GPoint.ccw_2, GPoint.ccw_2] at m_q1
  rw[←add_sub_assoc, ←add_sub_assoc, sub_add_eq_add_sub (a:=q) (b:=q.mod2)] at m_q1
  rw[add_sub_assoc (a:=q) (c:=q.mod2), ←GPoint.ccw_2] at m_q1
  rw[add_sub_assoc (c:=q.mod2.ccw), ←GPoint.arc] at m_q1
  rw[sub_add_eq_add_sub, sub_right_comm, add_assoc, add_sub_assoc] at m_q1
  rw[add_sub_cancel_left, add_sub_assoc, ←GPoint.arc, add_right_comm, ←face] at m_q1
  rw[←face_mod2, ←face, face_mod2, ←face_3_eq_add_arc_ccw] at m_q1
  rw[half_eq_cases_face]
  exact m_q1
}

theorem coarse_extendsIn {m : Matte} {r : GRectangle} (r0Emh : coarseIn r.toRegion m)
  (m_r : ∃ p ∈ r, p ∈ m) : ∀p, p ∈ r.inner → extendsIn m r p := by{
    intro p rp
    apply coarse_extendsIn' r0Emh m_r List.inter_subset_right
      (GRectangle.subset.refl _) _ rp (GRectangle.inner_subset rp)
  }
where coarse_extendsIn' {m : Matte} {r0 r : GRectangle} (r0Emh : coarseIn r0.toRegion m)
  (m_r : ∃p ∈ r, p ∈ m) (r_m0 : m.disk ∩ r0.enum ⊆ r.enum) (r0_r : r ⊆ r0) (p : GPixel)
  (r0p : p ∈ r0.inner) (r_p : p ∈ r)
  : extendsIn m r p := by{
    set m0 := m.disk ∩ r0.enum
    have le_r_n:=Nat.lt_succ_self (r.area)
    generalize r.area.succ = n' at le_r_n
    match n' with
    | n + 1 => {
      rw[Nat.lt_succ_iff] at le_r_n
      induction n using Nat.strongRec generalizing r r0 p with
      | ind n IHn => {
        rcases em (p ∈ m) with m_p | m'p
        · apply extendsIn_of_mem _ m_p
        have IHp {d : GDart} (Dp : d.half = p) (m_r0d : ∃q ∈ r0.toRegion \ chop1 d, q ∈ m) :
          extendsIn m r p := by{
          apply IHp (r0:=r0) (r:=r) (n:=n) (d:=d) (p:=p)
          · apply r0Emh
          · apply r_m0
          · apply r0_r
          · apply le_r_n
          · apply IHn
          · apply Dp
          · apply m_r0d
          · apply r0p
          · apply r_p
        }
        have m_nd4 {q : GPixel} (r0q : q ∈ r0) (hm : ∃x ∈ equad (nd q), x ∈ m)
          : q ∈ m := by{
            apply m_nd4_of_coarseIn r0Emh r0q hm
          }
        have gchop1F3E {d : GDart} : chop1 (face (face (face (edge d)))) = chop1 (face d) := by{
          apply f3e_chop1_eq
        }
        have r0_np : node p ∈ r0 := by{
          rw[GRectangle.mem_inner_iff] at r0p
          apply r0p
          apply node_mem_touch
        }
        have r0_fep : (face (edge p)) ∈ r0 := by{
          rw[GRectangle.mem_inner_iff] at r0p
          apply r0p
          apply fe_mem_touch
        }
        have p4'm : m.disk.Disjoint (equad (nd p)).enum:=by{
          have m_nd4':=m'p ∘ m_nd4 (GRectangle.inner_subset r0p)
          rw[imp_false, not_exists] at m_nd4'
          simp only [not_and] at m_nd4'
          symm
          rw[List.Disjoint]
          simp only [GRectangle.mem_enum_iff]
          apply m_nd4'
        }
        rcases em (∃q ∈ ehex (nd p), q ∈ m) with m_p6 | p6'm
        · {
          have m_efp : (edge (face (nd p))).half ∈ m := by{
            have ⟨q, p6_q, m_q⟩:=m_p6
            apply m_nd4
            · {
              rw[←ndFE, nd_half]
              apply r0_fep
            }
            · {
              rw[←ndFE, nd_half, ndFE]
              have h:=ehex_shift_quad (Or.inl p6_q)
              use q
              refine ⟨h.resolve_left ?_, m_q⟩
              rw[←GRectangle.mem_enum_iff]
              apply p4'm m_q
            }
          }
          rcases em (∃q ∈ ehex (face (nd p)), q ∈ m) with m_fp6 | m'_fp6
          · {
            have m_ep : (edge (nd p)).half ∈ m := by{
              have ⟨q, p6_q, m_q⟩:=m_fp6
              apply m_nd4
              · rw[hEnd]; apply r0_np
              rw[hEnd]
              have h:=ehex_shift_quad (q:=nd (node p)) (q':=q)
              rw[←ndFE, fen_cancel] at h
              have h':=h (Or.inr p6_q)
              use q
              refine ⟨h'.resolve_right ?_, m_q⟩
              rw[←GRectangle.mem_enum_iff]
              apply p4'm m_q
            }
            have ext2p : Extend2.ext2Hp m (nd p) := ⟨m_ep, m_efp, p4'm⟩
            rw[←nd_half (q:=p)]
            apply extendsIn_of_extend2 ext2p
            rw[nd_half]
            apply r_p
          }
          · {
            simp only [not_exists, not_and, ←GRectangle.mem_enum_iff, mem_iff] at m'_fp6
            rw[←List.Disjoint] at m'_fp6
            symm at m'_fp6
            apply extendsIn_ehex r_p (d:=(face (nd p))) (by{rw[face_half, nd_half]})
              m'_fp6 (extendsIn_of_mem _ m_efp)
          }
        }
        simp only [not_exists, not_and, ←GRectangle.mem_enum_iff, mem_iff] at p6'm
        rw[←List.Disjoint] at p6'm
        symm at p6'm
        rcases em (∃q ∈ p.touch, q ∈ m) with m_p | m''p
        · {
          apply extendsIn_ehex r_p (nd_half (q:=p)) p6'm
          rcases em (node p ∈ m) with m_nd | m'nd
          · rw[hEnd]; apply extendsIn_of_mem _ m_nd
          have nd4'm : m.disk.Disjoint (equad (nd (node p))).enum := by{
            intro x h0 h1
            rw[GRectangle.mem_enum_iff] at h1
            exact m'nd (m_nd4 r0_np ⟨x, h1, h0⟩)
          }
          have nd6'm : m.disk.Disjoint (ehex (nd (node p))).enum := by{
            intro x h0 h1
            have h3:=nd4'm h0
            have h4:=p4'm h0
            rw[GRectangle.mem_enum_iff] at h1 h3 h4
            have h2:=ehex_shift_quad (Or.inl h1)
            rw[ndN, fen_cancel, edge_2, ←ndN] at h2
            exact h2.elim h3 h4
          }
          have r0_n2p : node (node p) ∈ r0 := by{
            rw[GRectangle.mem_inner_iff] at r0p
            apply r0p
            apply nn_mem_touch
          }
          have m_n2p : node (node p) ∈ m := by{
            have ⟨q, p9q, m_q⟩ := m_p
            apply m_nd4 r0_n2p
            refine ⟨q, ?_, m_q⟩
            have ep_q : q ∈ chop (edge (nd p)) := by{
              rw[mem_edge_chop_iff]
              have h0:=p6'm m_q
              rw[GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion,
              ehex, chopRect_toRegion, imp_false, Set.mem_inter_iff,
              ←GRectangle.mem_iff_toRegion, not_and, nd_half] at h0
              exact h0 p9q
            }
            have h:=ehex_shift_quad (q := nd (node (node p))) (q' := q)
            have h1 := nd4'm m_q
            nth_rw 2 4 [ndN] at h
            rw[fen_cancel, edge_2] at h
            rw[GRectangle.mem_enum_iff] at h1
            apply (Or.resolve_right · h1)
            apply h
            have h2:=nd6'm m_q
            rw[GRectangle.mem_enum_iff] at h2
            right
            rw[ndN, fen_cancel, ehex, GRectangle.mem_iff_toRegion, chopRect_toRegion]
            rw[Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion, hEnd]
            refine ⟨?_, ep_q⟩
            match p, q with
            | ⟨px, py⟩, ⟨qx, qy⟩ => {
              simp only [GPoint.touch, GRectangle.mem_iff, GInterval.mem_iff,
                tsub_le_iff_right] at p9q
              rw[mem_edge_chop_iff] at ep_q
              simp only [chop, nd, GPoint.toUnitSquareDart, GPoint.mod2_add_double] at ep_q
              simp only [GPoint.half_add_double, GPoint.mod2_ccw, GPoint.mod2_mod2] at ep_q
              simp only [GPoint.half_mod2, add_zero, Set.mem_setOf] at ep_q
              simp only [←GPoint.mod2_ccw, GPoint.x_ccw, GPoint.x_mod2, GPoint.y_ccw,
              GPoint.y_mod2] at ep_q
              simp only [sub_sub_cancel, ge_iff_le] at ep_q
              simp only [GPoint.touch, GRectangle.mem_iff, GInterval.mem_iff,
                tsub_le_iff_right, node, GPoint.arc, GPoint.sub_def, GPoint.x_ccw,
                GPoint.y_ccw, GPoint.x_mod2, GPoint.y_mod2]
              cases Int.emod_two_eq px with | inl hpx | inr hpx =>
              cases Int.emod_two_eq py with | inl hpy | inr hpy => {
                simp[hpx, hpy] at ep_q
                simp[hpx, hpy]
                omega
              }
            }
          }
          have r_n2p : node (node p) ∈ r := by{
            rw[←GRectangle.mem_enum_iff]
            apply r_m0
            rw[List.mem_inter_iff]
            refine ⟨m_n2p, GRectangle.mem_enum_iff.mpr r0_n2p⟩
          }
          have r_np : node p ∈ r := by{
            rw[node, node_mod2, GPoint.arc] at r_n2p
            match p, r with
            | ⟨px, py⟩, ⟨⟨rx0, rx1⟩, ⟨ry0, ry1⟩⟩ => {
              cases Int.emod_two_eq px with | inl hpx | inr hpx =>
              cases Int.emod_two_eq py with | inl hpy | inr hpy => {
                simp[node, GPoint.arc, GPoint.x_ccw, GPoint.y_ccw, GPoint.x_mod2, GPoint.y_mod2,
                GRectangle.mem_iff, GInterval.mem_iff, hpx, hpy] at r_n2p
                simp[GRectangle.mem_iff, GInterval.mem_iff] at r_p
                simp[node, GPoint.arc, GPoint.x_ccw, GPoint.y_ccw, GPoint.x_mod2, GPoint.y_mod2,
                GRectangle.mem_iff, GInterval.mem_iff, hpx, hpy]
                omega
              }
            }
          }
          have ext1nd : Extend1.ext1Hp m (nd (node p)) := ⟨hEnd.symm ▸ m_n2p, nd6'm⟩
          use extend1 ext1nd
          refine ⟨Extension.extend1 ext1nd, ?_, ?_⟩
          · {
            simp only [extend1, Extend1.ext1Disk, extDisk, List.cons_subset, List.mem_union_iff,
              List.subset_union_right, and_true]
            left
            simp only [nd_half, GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion,
              chopRect_toRegion, Set.mem_inter_iff]
            rw[←GRectangle.mem_iff_toRegion]
            refine ⟨r_np, ?_⟩
            rw[←hEnd]
            apply half_mem_chop
          }
          · {
            simp [extend1, Extend1.ext1Disk, extDisk, mem_iff,
            List.mem_cons, hEnd, nd_half]
          }
        }
        · {
          have ⟨d, hq0, hq1⟩ : ∃d, (∃q' ∈ r0.toRegion \ chop1 d, q' ∈ m)
            ∧ d.half = p
          := by{
            have ⟨q, r_q, m_q⟩:=m_r
            by_contra h
            simp only [and_comm, not_exists, not_and, Set.mem_diff, not_imp_not] at h
            have r0_q := r0_r r_q
            rw[GRectangle.mem_iff_toRegion] at r0_q
            simp only [not_exists, not_and] at m''p
            have h':=(m''p q · m_q)
            have h'':=(h · · q m_q r0_q)
            apply h'
            rw[←nd_half (q:=p), mem_touch_iff_mem_all_chop1_half_eq, nd_half]
            exact h''
          }
          apply IHp hq1 hq0
        }
      }
    }
  }

end extend_matte
end Matte
end GridPlane
