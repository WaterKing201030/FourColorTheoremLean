import FourColorTheorem.GridPlane.Defs
import Mathlib.Data.ZMod.Basic

open Function
open Relation

namespace GridPlane
namespace GPoint

def rot : GPoint → GPoint
| ⟨x, y⟩ => ⟨- y, x⟩
theorem rot_def {p : GPoint} : p.rot = ⟨- p.2, p.1⟩ := rfl

theorem rot_4_periodic {p : GPoint} : IsPeriodicPt rot 4 p := by{
  match p with | ⟨x, y⟩ => simp[rot, IsPeriodicPt, IsFixedPt]
}
theorem rot_4 {p : GPoint} : p.rot.rot.rot.rot = p := by{
  exact rot_4_periodic
}
theorem rot_4_eq_id : rot^[4] = id := by{
  ext p <;> simp[rot_4]
}
theorem rot_injective : Injective rot := by{
  intro x y hxy
  have hxy':=congrArg (rot^[3] ·) hxy
  simp[rot_4] at hxy'
  simp[hxy']
}

theorem ccw_half {d : GPoint} : d.ccw.half = d.half.rot := by{
  simp[rot, half, ccw]
  omega
}

def recursion_ccw_00 {motive : GPoint → Prop}
  (base : ∀ d, d.toUnitSquareDart = UnitSquareDart.gp00 → motive d)
  (ind : ∀ d, motive d.ccw → motive d) (d : GPoint) : motive d := by{
  match hd : d.toUnitSquareDart with
  | UnitSquareDart.gp00 => exact base d hd
  | UnitSquareDart.gp01 => {
    exact ind _ (base d.ccw (by{simp[ccw_toUnitSquareDart, hd]; rfl}))
  }
  | UnitSquareDart.gp11 => {
    exact ind _ (ind _ (base d.ccw.ccw (by{simp[ccw_toUnitSquareDart, hd]; rfl})))
  }
  | UnitSquareDart.gp10 => {
    exact ind _ (ind _ (ind _ (base d.ccw.ccw.ccw (by{simp[ccw_toUnitSquareDart, hd]; rfl}))))
  }
}
def recursion_ccw {motive : GPoint → Prop} (u : UnitSquareDart)
  (base : ∀ d, d.toUnitSquareDart = u → motive d)
  (ind : ∀ d, motive d.ccw → motive d) (d : GPoint) : motive d := by{
    match u with
    | UnitSquareDart.gp00 => exact recursion_ccw_00 base ind d
    | UnitSquareDart.gp10 => {
      have base' : ∀d, d.toUnitSquareDart = UnitSquareDart.gp00 → motive d :=
        fun x hx => ind _ (base x.ccw (by{simp[ccw_toUnitSquareDart, hx]; rfl}))
      exact recursion_ccw_00 base' ind d
    }
    | UnitSquareDart.gp11 => {
      have base' : ∀d, d.toUnitSquareDart = UnitSquareDart.gp00 → motive d :=
        fun x hx => ind _ (ind _ (base x.ccw.ccw (by{simp[ccw_toUnitSquareDart, hx]; rfl})))
      exact recursion_ccw_00 base' ind d
    }
    | UnitSquareDart.gp01 => {
      have base' : ∀d, d.toUnitSquareDart = UnitSquareDart.gp00 → motive d :=
        fun x hx => ind _ (ind _
          (ind _ (base x.ccw.ccw.ccw (by{simp[ccw_toUnitSquareDart, hx]; rfl}))))
      exact recursion_ccw_00 base' ind d
    }
}

end GPoint

open GPoint

theorem end0_ccw {d : GPoint} : end0 d.ccw = (end0 d).ccw := by{
  simp[end0, ccw, mod2, half]; omega
}
theorem face_ccw {d : GPoint} : face d.ccw = (face d).ccw := by{
  simp[face, arc, ccw, mod2]; omega
}
theorem node_ccw {d : GPoint} : node d.ccw = (node d).ccw := by{
  simp[node, arc, ccw, mod2]; omega
}
theorem edge_ccw {d : GPoint} : edge d.ccw = (edge d).ccw := by{
  simp[edge, arc, ccw, mod2]; omega
}

def GRegion.ccw (R : GRegion) : GRegion := GPoint.ccw '' R
theorem GRegion.ccw_4 {R : GRegion} : R.ccw.ccw.ccw.ccw = R := by{
  ext p
  simp only [ccw, GPoint.ccw, Set.mem_image,
    sub_sub_cancel, exists_exists_and_eq_and]
  simp
}
theorem GRegion.ccw_mem_ccw_iff {R : GRegion} {p : GPoint} : p.ccw ∈ R.ccw ↔ p ∈ R := by{
  rw[GRegion.ccw, Set.mem_image]
  simp only [ccw_injective.eq_iff, exists_eq_right]
}
theorem GRegion.mem_ccw_iff {R : GRegion} {p : GPoint} : p ∈ R.ccw ↔ p.ccw.ccw.ccw ∈ R := by{
  nth_rw 1 [← GPoint.ccw_4 (p := p)]
  simp[GRegion.ccw_mem_ccw_iff]
}
theorem GRegion.ccw_subset_ccw_iff {R1 R2 : GRegion} : R1.ccw ⊆ R2.ccw ↔ R1 ⊆ R2 := by{
  constructor
  · {
    intro ih p hp
    specialize ih (ccw_mem_ccw_iff.mpr hp)
    rw[ccw_mem_ccw_iff] at ih
    exact ih
  }
  · {
    intro ih p hp
    rw[mem_ccw_iff] at *
    exact ih hp
  }
}
def GRegion.rot (R : GRegion) : GRegion := GPoint.rot '' R
theorem GRegion.rot_4 {R : GRegion} : R.rot.rot.rot.rot = R := by{
  ext p
  simp only [rot, GPoint.rot, Set.mem_image,
    exists_exists_and_eq_and]
  simp
}
theorem GRegion.rot_mem_rot_iff {R : GRegion} {p : GPoint} : p.rot ∈ R.rot ↔ p ∈ R := by{
  rw[GRegion.rot, Set.mem_image]
  simp only [rot_injective.eq_iff, exists_eq_right]
}
theorem GRegion.mem_rot_iff {R : GRegion} {p : GPoint} : p ∈ R.rot ↔ p.rot.rot.rot ∈ R := by{
  nth_rw 1 [← GPoint.rot_4 (p := p)]
  simp[GRegion.rot_mem_rot_iff]
}
theorem GRegion.rot_subset_rot_iff {R1 R2 : GRegion} : R1.rot ⊆ R2.rot ↔ R1 ⊆ R2 := by{
  constructor
  · {
    intro ih p hp
    specialize ih (rot_mem_rot_iff.mpr hp)
    rw[rot_mem_rot_iff] at ih
    exact ih
  }
  · {
    intro ih p hp
    rw[mem_rot_iff] at *
    exact ih hp
  }
}

open UnitSquareDart

theorem chop_ccw {d : GPoint} : chop d.ccw = (chop d).rot := by{
  ext p
  rw[GRegion.mem_rot_iff]
  simp only [chop, ccw_toUnitSquareDart, ge_iff_le, Set.mem_setOf_eq]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, ccw_half, rot]
    omega
  }
}
theorem chop1_ccw {d : GPoint} : chop1 d.ccw = (chop1 d).rot := by{
  unfold chop1
  rw[edge_ccw, face_ccw, face_ccw, chop_ccw]
}

def GRectangle.ccw (R : GRectangle) : GRectangle :=
  ⟨⟨2-R.vspan.sup, 2-R.vspan.inf⟩, ⟨R.hspan.inf, R.hspan.sup⟩⟩
theorem GRectangle.ccw_coe {R : GRectangle} : (R.ccw : GRegion) = GRegion.ccw (R : GRegion) := by{
  ext x
  simp[GRegion.mem_ccw_iff, GPoint.ccw, ccw]
  omega
}
theorem GRectangle.ccw_mem_ccw_iff {R : GRectangle} {p : GPoint} : p.ccw ∈ R.ccw ↔ p ∈ R := by{
  rw[mem_def, ccw_coe, GRegion.ccw_mem_ccw_iff, ← mem_def]
}
theorem GRectangle.mem_ccw_iff {R : GRectangle} {p : GPoint} : p ∈ R.ccw ↔ p.ccw.ccw.ccw ∈ R := by{
  nth_rw 1 [← ccw_4 (p := p)]
  simp[GRectangle.ccw_mem_ccw_iff]
}

def GRectangle.rot (R : GRectangle) : GRectangle :=
  ⟨⟨1-R.vspan.sup, 1-R.vspan.inf⟩, ⟨R.hspan.inf, R.hspan.sup⟩⟩
theorem GRectangle.rot_coe {R : GRectangle} : (R.rot : GRegion) = GRegion.rot (R : GRegion) := by{
  ext x
  simp[GRegion.mem_rot_iff, GPoint.rot, rot]
  omega
}
theorem GRectangle.rot_mem_rot_iff {R : GRectangle} {p : GPoint} : p.rot ∈ R.rot ↔ p ∈ R := by{
  rw[mem_def, rot_coe, GRegion.rot_mem_rot_iff, ← mem_def]
}
theorem GRectangle.mem_rot_iff {R : GRectangle} {p : GPoint} : p ∈ R.rot ↔ p.rot.rot.rot ∈ R := by{
  nth_rw 1 [← rot_4 (p := p)]
  simp[GRectangle.rot_mem_rot_iff]
}

theorem GRectangle.touch_ccw {p : GPoint} : touch p.ccw = (touch p).ccw := by{
  simp[touch, ccw, GPoint.ccw, Ico.touch]; omega
}
theorem GRectangle.touch_rot {p : GPoint} : touch p.rot = (touch p).rot := by{
  simp[touch, rot, GPoint.rot, Ico.touch]; omega
}

theorem chopRect_rot_ccw {R : GRectangle} {d : GDart}
: chopRect R.rot d.ccw = (chopRect R d).rot := by{
  simp only [chopRect, ccw_toUnitSquareDart, GRectangle.rot]
  simp only [GPoint.ccw]
  match hd : d.toUnitSquareDart with
  | gp00 | gp10 | gp11 | gp01 => {
    simp only [UnitSquareDart.ccw, GRectangle.mk.injEq, Ico.mk.injEq, true_and, and_true]
    simp only [half]
    try omega
  }
}
theorem chop1Rect_rot_ccw {R : GRectangle} {d : GDart}
: chop1Rect R.rot d.ccw = (chop1Rect R d).rot := by{
  simp only [chop1Rect, edge_ccw, face_ccw, chopRect_rot_ccw]
}

open GRectangle
theorem ehex_ccw {d : GDart} : ehex d.ccw = (ehex d).rot := by{
  simp only [ehex, ccw_half, touch_rot, chopRect_rot_ccw]
}
theorem equad_ccw {d : GDart} : equad d.ccw = (equad d).rot := by{
  simp only [equad, ehex_ccw, face_ccw, chopRect_rot_ccw]
}

end GridPlane
