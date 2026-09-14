import FourColorTheorem.GridPlane.Lemmas.Chop
import FourColorTheorem.GridPlane.Lemmas.Touch

open Function
open Relation

namespace GridPlane

open GPoint

namespace GRectangle

theorem mem_ehex_cases_iff {d : GDart} {p : GPixel} : p ∈ ehex d
↔ p = d.half ∨ p = (edge (face d)).half ∨ p = (node (edge (face d))).half ∨
p = (edge (face (face d))).half ∨ p = (edge (face (node d))).half ∨ p = (node d).half := by{
  induction d using recursion_ccw_00 generalizing p with
  | base d hd => {
    rw[ehex, mem_chopRect_iff]
    unfold chop
    simp only [hd, Set.mem_setOf]
    rw[mem_touch_half_cases_iff]
    simp only [toUnitSquare_eq_gp00, mod2, Prod.mk.injEq] at hd
    constructor
    · {
      intro ⟨hl, hr⟩
      suffices H : ¬(p = half (node (node d)) ∨ p = half (edge d) ∨ p = half (node (edge d))) by{
        push_neg at H
        simp only [H, or_self, or_false] at hl
        rcases hl with hl | hl | hl | hl | hl | hl <;> simp[hl]
      }
      match p, d with | ⟨px, py⟩, ⟨dx, dy⟩ => {
        push_neg
        split_ands <;> {
          contrapose hr
          simp[half, node, edge, hd, arc, mod2, GPoint.ccw, Int.sub_one_emod_two,
          Int.add_neg_eq_sub, Int.sub_one_ediv_two_of_mod_zero, Int.add_one_emod_two] at hr
          simp[hr, half]
        }
      }
    }
    · {
      intro h
      rcases h with h | h | h | h | h | h <;> {
        simp[h, half, edge, face, mod2, arc, GPoint.ccw, hd, Int.add_one_emod_two,
        node, Int.sub_one_emod_two, add_assoc, Int.add_ediv_of_dvd_right,
        Int.add_one_ediv_two_of_mod_zero]
      }
    }
  }
  | ind d ih => {
    specialize ih (p := p.rot)
    simp [ehex_ccw, rot_mem_rot_iff, ccw_half, face_ccw,
      edge_ccw, node_ccw, rot_injective.eq_iff] at ih
    assumption
  }
}
theorem mem_equad_cases_iff {d : GDart} {p : GPixel} : p ∈ equad d
↔ p = d.half ∨
p = (edge (face (face d))).half ∨ p = (edge (face (node d))).half ∨ p = (node d).half := by{
  induction d using recursion_ccw_00 generalizing p with
  | base d hd => {
    simp only [equad, mem_chopRect_iff, mem_ehex_cases_iff, chop, face_toUnitSquareDart,
      UnitSquareDart.ccw, hd, ge_iff_le, Set.mem_setOf_eq, face_half]
    constructor
    · {
      intro ⟨hl, hr⟩
      rw[or_left_comm, or_left_comm (a := p = d.half), ← or_assoc] at hl
      apply hl.resolve_left
      push_neg
      clear hl
      constructor <;> {
        match p with | ⟨px, py⟩ => {
          contrapose hr
          simp[toUnitSquare_eq_gp00, mod2] at hd
          simp[half, edge, face, arc, mod2, GPoint.ccw, hd, node, add_assoc, Int.add_one_emod_two,
          Int.add_one_ediv_two_of_mod_zero, Int.add_ediv_of_dvd_right] at hr
          simp[hr, half]
        }
      }
    }
    · {
      intro h
      rcases h with h | h | h | h <;> {
        constructor
        · simp[h]
        simp[toUnitSquare_eq_gp00, mod2] at hd
        simp[h, half, edge, face, node, arc, GPoint.ccw, mod2, hd, Int.add_one_emod_two,
          Int.sub_one_emod_two, Int.add_neg_eq_sub, Int.sub_one_ediv_two_of_mod_zero,
          sub_sub, Int.sub_ediv_of_dvd]
      }
    }
  }
  | ind d ih => {
    specialize ih (p := p.rot)
    simp [equad_ccw, rot_mem_rot_iff, ccw_half, face_ccw,
      edge_ccw, node_ccw, rot_injective.eq_iff] at ih
    assumption
  }
}

theorem half_mem_ehex {d : GDart} : d.half ∈ GRectangle.ehex d := by{
  rw[ehex, mem_chopRect_iff]
  apply And.intro mem_touch half_mem_chop
}
theorem half_mem_equad {d : GDart} : d.half ∈ GRectangle.equad d := by{
  rw[equad, mem_chopRect_iff]
  apply And.intro half_mem_ehex half_mem_chop_face
}

theorem half_mem_ehex_of_end0_eq_end0_face_face {d a : GDart} (hda : end0 a = end0 (face (face d)))
  : a.half ∈ ehex d :=by{
  rw[end0_eq_cases_node] at hda
  rw[mem_ehex_cases_iff]
  rcases hda with hda | hda | hda | hda
  · {
    left
    simp[hda, face_half]
  }
  · {
    right; left
    rw[hda, ← edge_eq_node_face]
  }
  · {
    right; right; left
    rw[hda, ← edge_eq_node_face]
  }
  · {
    right; right; right; left
    rw[hda, node_3, face_half]
  }
}
theorem half_mem_equad_of_end0_eq_end0_face_3 {d a : GDart}
(hda : end0 a = end0 (face (face (face d))))
  : a.half ∈ equad d := by{
  rw[end0_eq_cases_node] at hda
  rw[mem_equad_cases_iff]
  rcases hda with hda | hda | hda | hda
  · {
    left
    simp[hda, face_half]
  }
  · {
    right; left
    rw[hda, ← edge_eq_node_face]
  }
  · {
    right; right; left
    rw[hda, face_3, ← face_half (d := edge (face (node d))), ← node_3, ← edge_eq_node_face]
  }
  · {
    right; right; right
    rw[hda, node_3, face_3, edge_2, face_half]
  }
}
theorem half_mem_ehex_of_end0_eq_end0_face_3 {d a : GDart}
(hda : end0 a = end0 (face (face (face d))))
  : a.half ∈ ehex d :=
  chopRect_subset_rect (half_mem_equad_of_end0_eq_end0_face_3 hda)

theorem half_node_mem_equad {d : GDart} : (node d).half ∈ equad d := by{
  simp[mem_equad_cases_iff]
}
theorem half_node_mem_ehex {d : GDart} : (node d).half ∈ ehex d :=
  chopRect_subset_rect half_node_mem_equad

theorem ehex_disjoint_edge_chop {d : GDart} : ∀p ∈ ehex d, p ∉ chop (edge d)
:= by{
  apply chopRect_disjoint_edge_chop
}

theorem mem_ehex_shift_iff_mem_equad_shift {q : GDart} {q' : GPixel} :
  q' ∈ ehex q ∨ q' ∈ ehex (face (edge (face q)))
  ↔ q' ∈ equad q ∨ q' ∈ equad (edge (face q))
  := by{
  simp only [mem_ehex_cases_iff, mem_equad_cases_iff]
  simp only [face_3, edge_2, nfe_cancel]
  simp only [face_half]
  have h0 : half (node (edge (face (face (edge (face q))))))
    = half (edge (face (node (edge (face q))))) := by{
    nth_rw 1 [edge_eq_node_face]
    rw[face_3]
    nth_rw 1 [edge_eq_node_face]
    rw[node_3, face_half]
  }
  simp[h0]
  tauto
}

theorem equad_nodeinvDart_half_eq {p q : GPixel}
    (hq : q ∈ equad p.nodeinvDart) : q.half = p.half := by {
  rw [GRectangle.equad, mem_chopRect_iff, GRectangle.ehex, mem_chopRect_iff] at hq
  simp only [chop, Set.mem_setOf_eq] at hq
  simp only [face_toUnitSquareDart, face_half, GPoint.nodeinvDart_half] at hq
  simp only [GPoint.toUnitSquareDart, GPoint.nodeinvDart_mod2] at hq
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  simp [GPoint.half, GPoint.mod2,
    GPoint.ccw, UnitSquareDart.ccw, hx, hy, GRectangle.touch, GRectangle.mem_iff,
    Ico.touch] at hq ⊢ <;> omega
}

theorem touch_remaining_half {p q : GPixel}
    (ht : q ∈ touch p)
    (hh : q ∉ ehex p.nodeinvDart)
    (hq : q ∉ equad (node p).nodeinvDart) :
    q.half = (node (node p)).half := by {
  simp only [GRectangle.equad, GRectangle.ehex, mem_chopRect_iff] at hh hq
  simp only [chop, Set.mem_setOf_eq] at hh hq
  simp only [face_toUnitSquareDart, face_half, GPoint.nodeinvDart_half] at hh hq
  simp only [GPoint.toUnitSquareDart, GPoint.nodeinvDart_mod2, node_mod2] at hh hq
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  simp [node, GPoint.arc, GPoint.mod2, GPoint.half, GPoint.ccw,
    UnitSquareDart.ccw, GRectangle.mem_iff, GRectangle.touch, Ico.touch,
    Int.add_emod, Int.sub_emod, hx, hy] at ht hh hq ⊢ <;> omega
}

end GRectangle
end GridPlane
