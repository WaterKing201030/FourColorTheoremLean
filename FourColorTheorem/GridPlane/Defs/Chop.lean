import FourColorTheorem.GridPlane.Defs.Rectangle
import FourColorTheorem.GridPlane.Defs.Unitsquare

/-! 整平面上的半平面 -/

open Function
open Relation

namespace GridPlane

open GPoint
open UnitSquareDart

def chop (d : GDart) : GRegion :=
  {p |
    match d.toUnitSquareDart with
    | gp00 => d.half.2 ≤ p.2
    | gp01 => d.half.1 ≤ p.1
    | gp10 => d.half.1 ≥ p.1
    | gp11 => d.half.2 ≥ p.2
  }

theorem half_mem_chop {d : GDart} : d.half ∈ chop d := by{
  unfold chop
  rw[Set.mem_ofPred]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp only [ge_iff_le, le_refl]
}
theorem mem_edge_chop_iff {d : GDart} {p : GPixel} : p ∈ chop (edge d) ↔ p ∉ chop d := by{
  unfold chop
  simp only [Set.mem_ofPred, edge_toUnitSquareDart, edge_half']
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[opp, Int.add_one_le_iff, Int.le_sub_one_iff]
}
theorem edge_chop_disjoint {d : GDart} : Disjoint (chop (edge d)) (chop d) := by{
  rw[Set.disjoint_iff_inter_eq_empty,Set.eq_empty_iff_forall_notMem]
  intro p
  simp[mem_edge_chop_iff]
}
theorem edge_chop_eq_compl {d : GDart} : chop (edge d) = (chop d)ᶜ := by{
  ext p
  rw[mem_edge_chop_iff, Set.mem_compl_iff]
}

def chop1 (d : GDart) := chop (face (face (edge d)))

def chopRect (r : GRectangle) (d : GDart) : GRectangle :=
  match d.toUnitSquareDart with
  | gp00 => ⟨r.hspan, ⟨max r.vspan.inf d.half.2, r.vspan.sup⟩⟩
  | gp01 => ⟨⟨max r.hspan.inf d.half.1, r.hspan.sup⟩, r.vspan⟩
  | gp10 => ⟨⟨r.hspan.inf, min r.hspan.sup (d.half.1 + 1)⟩, r.vspan⟩
  | gp11 => ⟨r.hspan, ⟨r.vspan.inf, min r.vspan.sup (d.half.2 + 1)⟩⟩
theorem chopRect_coe {r : GRectangle} {d : GDart}
: (chopRect r d : GRegion) = (r : GRegion) ∩ chop d := by{
  ext p
  simp only [Set.mem_inter_iff]
  simp only [chopRect, chop, Set.mem_ofPred]
  simp only [Set.mem_prod, Set.mem_Ico, ge_iff_le]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [max_le_iff, lt_min_iff, Int.lt_add_one_iff]
    tauto
  }
}
theorem chopRect_subset_chop {r : GRectangle} {d : GDart}
: (chopRect r d : GRegion) ⊆ chop d := by{
  rw[chopRect_coe]
  apply Set.inter_subset_right
}
theorem chopRect_subset_rect {r : GRectangle} {d : GDart}
: chopRect r d ⊆ r := by{
  rw[GRectangle.subset_def, chopRect_coe]
  apply Set.inter_subset_left
}
theorem mem_chopRect_iff {r : GRectangle} {d : GDart} {p : GPixel} :
  p ∈ chopRect r d ↔ p ∈ r ∧ p ∈ chop d := by{
  rw[GRectangle.mem_def, chopRect_coe, Set.mem_inter_iff, ← GRectangle.mem_def]
}

def chop1Rect (r : GRectangle) (d : GDart) : GRectangle := chopRect r (face (face (edge d)))
theorem chop1Rect_coe {r : GRectangle} {d : GDart}
: (chop1Rect r d : GRegion) = (r : GRegion) ∩ chop1 d := by{
  rw[chop1Rect, chopRect_coe, chop1]
}
theorem chop1Rect_subset_chop1 {r : GRectangle} {d : GDart}
: (chop1Rect r d : GRegion) ⊆ chop1 d := by{
  rw[chop1Rect_coe]
  apply Set.inter_subset_right
}
theorem chop1Rect_subset_rect {r : GRectangle} {d : GDart}
: chop1Rect r d ⊆ r := by{
  rw[GRectangle.subset_def, chop1Rect_coe]
  apply Set.inter_subset_left
}

theorem mem_chop1Rect_iff {r : GRectangle} {d : GDart} {p : GPixel} :
  p ∈ chop1Rect r d ↔ p ∈ r ∧ p ∈ chop1 d := by{
  rw[chop1Rect, mem_chopRect_iff, chop1]
}

namespace GRectangle

def ehex (d : GDart) := chopRect (touch d.half) d
def equad (d : GDart) := chopRect (ehex d) (face d)

end GRectangle

end GridPlane
