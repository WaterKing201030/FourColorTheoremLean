import FourColorTheorem.GridPlane.Defs
import FourColorTheorem.GridPlane.Lemmas.Hypermap
import FourColorTheorem.GridPlane.Lemmas.Rotation

open Function
open Relation

namespace GridPlane

open GPoint
open UnitSquareDart

theorem chop_subset_chop1 {d : GDart} : chop d ⊆ chop1 d := by{
  unfold chop1 chop
  intro p
  simp only [face_toUnitSquareDart, edge_toUnitSquareDart, ge_iff_le, face_half, edge_half']
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, opp, tsub_le_iff_right, Int.le_add_one_iff]
    intro hp
    left
    exact hp
  }
}
theorem chopRect_subset_chop1Rect {r : GRectangle} {d : GDart}
: chopRect r d ⊆ chop1Rect r d := by{
  rw[GRectangle.subset_def, chopRect_coe, chop1Rect_coe]
  apply Set.inter_subset_inter_right
  exact chop_subset_chop1
}

theorem touch_subset_chop1_iff_mem_chop {p : GPixel} {d : GDart} :
  (GRectangle.touch p : GRegion) ⊆ chop1 d ↔ p ∈ chop d:=by{
  revert p
  apply GPoint.recursion_ccw_00
    (motive := fun d => ∀p, (GRectangle.touch p : GRegion) ⊆ chop1 d ↔ p ∈ chop d)
  · {
    clear d
    intro d hd p
    unfold chop
    simp only [hd, Set.mem_setOf_eq]
    simp only [Set.subset_def, Set.mem_prod, Set.mem_Ico, and_imp, Prod.forall, chop1,
    GRectangle.touch, chop, face_toUnitSquareDart, edge_toUnitSquareDart, hd, opp,
    UnitSquareDart.ccw, Set.mem_setOf, face_half, Ico.touch]
    simp only [tsub_le_iff_right]
    rw[toUnitSquare_eq_gp00] at hd
    simp only [mod2, Prod.mk.injEq] at hd
    simp only [half, edge, arc, GPoint.ccw, mod2, hd, sub_zero, Prod.mk_sub_mk, sub_self, zero_sub,
      Int.reduceNeg, Prod.fst_add, Prod.snd_add]
    simp only [Int.reduceNeg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Int.add_ediv,
      Int.reduceDiv, Int.reduceAbs, Nat.cast_ofNat, hd, Int.neg_emod_two, Int.one_emod_two,
      zero_add, Nat.not_ofNat_le_one, ↓reduceIte, add_zero, add_neg_le_iff_le_add]
    constructor
    · {
      intro ih
      specialize ih p.1 (p.2 - 1) (by{simp}) (by{simp}) (by{simp}) (by{omega})
      simp only [sub_add_cancel] at ih
      exact ih
    }
    · intros; omega
  }
  · {
    clear d
    intro d ih p
    simp only [chop_ccw, chop1_ccw] at ih
    specialize ih p.rot
    rw[GRegion.rot_mem_rot_iff, GRectangle.touch_rot] at ih
    rw[GRectangle.rot_coe] at ih
    rw[GRegion.rot_subset_rot_iff] at ih
    exact ih
  }
}

theorem mem_chop1Rect_inner_iff_mem_inner_chopRect {r : GRectangle} {p : GPixel}
  {d : GDart} : p ∈ (chop1Rect r d).inner ↔ p ∈ chopRect r.inner d :=by{
    rw[GRectangle.mem_inner_iff_touch_subset]
    rw[GRectangle.mem_def, chopRect_coe, Set.mem_inter_iff]
    change _ ↔ p ∈ r.inner ∧ p ∈ chop d
    simp only [GRectangle.subset_iff]
    simp only [(chop1Rect r d).mem_def, chop1Rect_coe, Set.mem_inter_iff]
    change ((∀x ∈ GRectangle.touch p, x ∈ r ∧ _) ↔ _)
    simp only [← touch_subset_chop1_iff_mem_chop, forall_and, GRectangle.mem_inner_iff_touch_subset]
    apply and_congr
    · rfl
    · rfl
  }

theorem fn_chop_eq_ff_chop {d : GDart} : chop (face (node d)) = chop (face (face d)) := by{
  ext p
  simp only [chop, ge_iff_le, Set.mem_setOf_eq]
  simp only [face_toUnitSquareDart, node_toUnitSquareDart]
  match d with | ⟨dx, dy⟩ => {
    simp only [face_half, node_half, Prod.snd_add, Prod.snd_sub, Prod.fst_add, Prod.fst_sub]
    simp only [toUnitSquareDart, mod2, half]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx,hy,UnitSquareDart.ccw, GPoint.ccw]
  }
}

theorem fef_chop_eq_chop {d : GDart} : chop (face (edge (face d))) = chop d := by{
  ext p
  rw[edge_eq_node_face, fn_chop_eq_ff_chop, face_4]
}

theorem f3e_chop_eq_f_chop {d : GDart} : chop (face (face (face (edge d)))) = chop (face d) := by{
  have h0 : face d = face (edge (face (face (face (face (edge d)))))) := by{rw[face_4, edge_2]}
  rw[h0, fef_chop_eq_chop]
}

theorem node_half_mem_chop {d : GDart} : (node d).half ∈ chop d := by{
  have h0 : node d = edge (face (face (face d))) := by{rw[face_3, edge_2]}
  rw[h0]
  rw[← face_half, ← face_half, ← face_half]
  apply Eq.mp (congrArg (_ ∈ ·) ?_) half_mem_chop
  rw[f3e_chop_eq_f_chop, face_4]
}

theorem half_mem_chop_face {d : GDart} : d.half ∈ chop (face d) := by{
  induction d using recursion_ccw gp01 with
  | base d hd => {
    simp only [chop, face_toUnitSquareDart, UnitSquareDart.ccw, hd, face_half, Set.mem_setOf_eq,
      Std.le_refl]
  }
  | ind d ih => {
    rw[ccw_half,face_ccw, chop_ccw, GRegion.rot_mem_rot_iff] at ih
    exact ih
  }
}

theorem chopRect_disjoint_edge_chop {d : GDart} {R : GRectangle}
: ∀p ∈ chopRect R d, p ∉ chop (edge d) := by{
  simp[mem_edge_chop_iff, mem_chopRect_iff]
}
end GridPlane
