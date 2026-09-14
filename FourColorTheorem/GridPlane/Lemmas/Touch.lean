import FourColorTheorem.GridPlane.Defs
import FourColorTheorem.GridPlane.Lemmas.Hypermap
import FourColorTheorem.GridPlane.Lemmas.Rotation

open Function
open Relation

namespace GridPlane

open GPoint

namespace GRectangle

theorem end0_mem_touch {d : GDart} : end0 d ∈ touch d.half := by{
  rcases d with ⟨x, y⟩
  simp only [end0, GPoint.half_def, GPoint.mod2_def, touch, Ico.touch, mem_iff',
    Prod.mk_add_mk]
  rw [Ico.mem_iff, Ico.mem_iff]
  change (x / 2 - 1 ≤ x / 2 + x % 2 ∧ x / 2 + x % 2 < x / 2 + 2) ∧
    y / 2 - 1 ≤ y / 2 + y % 2 ∧ y / 2 + y % 2 < y / 2 + 2
  omega
}

theorem mem_touch_of_half_eq_half {p q : GPixel} (hpq : q.half = p.half) :
  q ∈ touch p := by{
  simp only [touch, Ico.touch, mem_iff, tsub_le_iff_right]
  simp only [half, Prod.mk.injEq] at hpq
  omega
}
theorem mem_touch_of_end0_eq_end0 {p q : GPixel} (hpq : end0 q = end0 p) :
  q ∈ touch p := by{
  simp only [touch, Ico.touch, mem_iff, tsub_le_iff_right]
  simp only [end0, half, mod2, Prod.mk_add_mk, Prod.mk.injEq] at hpq
  omega
}
theorem face_mem_touch {p : GPixel} : face p ∈ touch p := by{
  apply mem_touch_of_half_eq_half
  rw[face_half]
}
theorem node_mem_touch {p : GPixel} : node p ∈ touch p := by{
  apply mem_touch_of_end0_eq_end0
  rw[node_end0]
}
theorem edge_mem_touch {p : GPixel} : edge p ∈ touch p := by{
  simp[edge, touch, Ico.touch, arc, mod2, GPoint.ccw, mem_iff]
  omega
}
theorem fn_mem_touch {p : GPixel} : face (node p) ∈ touch p := by{
  simp[face, node, Ico.touch, touch, arc, mod2, GPoint.ccw, mem_iff]
  omega
}
theorem mem_touch_cases {p q : GPixel} (hpq : q ∈ touch p)
: q = p ∨ q = face p ∨ q = face (face p) ∨ q = edge (node p)
  ∨ q = node p ∨ q = node (node p) ∨ q = face (edge p)
  ∨ q = edge p ∨ q = face (node p) := by{
  induction p using recursion_ccw_00 generalizing q with
  | base d hd => {
    rw[toUnitSquare_eq_gp00] at hd
    simp only [mod2, Prod.mk.injEq] at hd
    simp only [face, arc, GPoint.ccw, mod2, hd, sub_zero, Prod.mk_sub_mk, sub_self, Prod.fst_add,
      Int.add_one_emod_two, Prod.snd_add, add_zero, edge, node, Prod.fst_sub, Int.sub_one_emod_two,
      Prod.snd_sub, zero_sub, Int.reduceNeg, sub_neg_eq_add, zero_add, Int.add_neg_eq_sub]
    match q, d with | ⟨qx, qy⟩, ⟨dx, dy⟩ => {
      simp only [Prod.mk.injEq, Prod.mk_add_mk, add_zero, Prod.mk_sub_mk, sub_zero, sub_add_cancel,
        Int.reduceNeg, add_neg_cancel_right]
      simp only at hd
      simp only [touch, Ico.touch, mem_iff, tsub_le_iff_right] at hpq
      omega
    }
  }
  | ind d ih => {
    specialize ih (q := q.ccw) (by{
      rwa[touch_ccw, GRectangle.ccw_mem_ccw_iff]
    })
    simp only [GPoint.ccw_injective.eq_iff, face_ccw, node_ccw, edge_ccw] at ih
    exact ih
  }
}
theorem mem_touch_cases_iff {p q : GPixel}
: q ∈ touch p ↔ q = p ∨ q = face p ∨ q = face (face p) ∨ q = edge (node p)
  ∨ q = node p ∨ q = node (node p) ∨ q = face (edge p)
  ∨ q = edge p ∨ q = face (node p) := by{
  apply Iff.intro mem_touch_cases
  intro h
  rw[← face_3, ← node_3] at h
  rw[← or_assoc, ← or_assoc, ← or_assoc] at h
  rcases h with h | h
  · {
    simp only [or_assoc] at h
    rcases h with h | h | h | h
    all_goals
    apply mem_touch_of_half_eq_half
    simp[h, face_half]
  }
  rw[← or_assoc, ← or_assoc] at h
  rcases h with h | h | h
  · {
    simp only [or_assoc] at h
    rcases h with h | h | h
    all_goals
    apply mem_touch_of_end0_eq_end0
    simp[h, node_end0]
  }
  · rw[h]; apply edge_mem_touch
  · rw[h]; apply fn_mem_touch
}

theorem node_node_mem_touch {p : GDart} : node (node p) ∈ touch p := by{
  rw[mem_touch_cases_iff]; simp
}

theorem half_mem_touch_half_of_mem_touch {p q : GDart} (hpq : q ∈ touch p) :
  q.half ∈ touch p.half := by{
  simp[touch, Ico.touch, mem_iff, half] at *
  omega
}

theorem half_mem_touch_of_end0_eq_end0 {p q : GDart} (hpq : end0 q = end0 p) :
  q.half ∈ touch p.half := by{
  apply half_mem_touch_half_of_mem_touch
  exact mem_touch_of_end0_eq_end0 hpq
}

theorem node_half_mem_touch_half {d : GDart} : (node d).half ∈ touch d.half := by{
  apply half_mem_touch_of_end0_eq_end0
  exact node_end0
}

theorem face_half_mem_touch_half {d : GDart} : (face d).half ∈ touch d.half := by{
  rw [face_half]
  exact mem_touch
}

theorem mem_touch_half_cases_iff {d : GDart} {p : GPixel} : p ∈ touch d.half
↔ p = d.half ∨ p = (edge (face d)).half ∨ p = (node (edge (face d))).half ∨
p = (edge (face (face d))).half ∨ p = (edge (face (node d))).half ∨ p = (node d).half
  ∨ p = (node (node d)).half ∨ p = (edge d).half ∨ p = (node (edge d)).half := by{
  induction d using recursion_ccw_00 generalizing p with
  | base d hd => {
    match p, d with | ⟨px, py⟩, ⟨dx, dy⟩ => {
      simp only [toUnitSquare_eq_gp00, mod2, Prod.mk.injEq] at hd
      simp[half, edge, face, node, arc, mod2, GPoint.ccw, hd, Int.add_one_emod_two,
      Int.sub_one_emod_two, add_assoc, Int.add_ediv_of_dvd_right, Int.add_one_ediv_two_of_mod_zero,
      Int.add_neg_eq_sub, Int.sub_one_ediv_two_of_mod_zero, touch, Ico.touch, mem_iff]
      omega
    }
  }
  | ind d ih => {
    specialize ih (p := p.rot)
    simp[touch_rot, face_ccw, edge_ccw, node_ccw, ccw_half, rot_mem_rot_iff,
      rot_injective.eq_iff] at ih
    assumption
  }
}

end GRectangle

end GridPlane
