import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Dynamics.PeriodicPts.Defs
import FourColorTheorem.Utils.Int
import FourColorTheorem.Utils.List

open Function
open Relation

namespace GridPlane

abbrev GPoint := ℤ × ℤ

abbrev GPixel := GPoint
abbrev GCorner := GPoint
abbrev GDart := GPoint
abbrev GVector := GPoint

namespace GPoint

instance : DecidableEq GPoint :=
  inferInstance

def half : GDart → GPixel
| ⟨x, y⟩ => ⟨x / 2, y / 2⟩
def mod2 : GDart → GCorner
| ⟨x, y⟩ => ⟨x % 2, y % 2⟩

theorem half_def (d : GPoint) : d.half = (d.1 / 2, d.2 / 2) := rfl
theorem mod2_def (d : GPoint) : d.mod2 = (d.1 % 2, d.2 % 2) := rfl

theorem half_add_double {p : GPixel} {d : GDart} : (2 • p + d).half = p + d.half := by{
  match p, d with
  | ⟨px, py⟩, ⟨dx, dy⟩ => {
    simp[half_def]; omega
  }
}
theorem half_double {p : GPixel} : (2 • p).half = p := by{
  match p with | ⟨dx, dy⟩ => simp[half_def]
}
theorem mod2_add_double {p : GPixel} {d : GDart} : (2 • p + d).mod2 = d.mod2 := by{
  match p, d with
  | ⟨px, py⟩, ⟨dx, dy⟩ => simp[mod2_def]
}
theorem mod2_double {p : GPixel} : (2 • p).mod2 = 0 := by{
  match p with
  | ⟨dx, dy⟩ => simp[mod2_def]
}
theorem double_half_add_mod2 (d : GDart) : 2 • d.half + d.mod2 = d := by{
  match d with
  | ⟨dx, dy⟩ => {
    simp[half_def, mod2_def]; omega
  }
}

theorem mod2_cases {p : GPoint}
  : p.mod2 = ⟨0, 0⟩ ∨ p.mod2 = ⟨1, 0⟩ ∨ p.mod2 = ⟨1, 1⟩ ∨ p.mod2 = ⟨0, 1⟩ := by{
    match p with | ⟨px, py⟩ => {
      simp[mod2_def]; omega
    }
  }

theorem zero_def : 0 = (⟨0, 0⟩ : GPoint) := rfl
theorem zero_half : GPoint.half 0 = 0 := rfl
theorem zero_mod2 : GPoint.mod2 0 = 0 := rfl
theorem half_mod2 {d : GDart} : d.mod2.half = 0 := by{
  match d with
  | ⟨dx, dy⟩ => simp[half_def, mod2_def]; omega
}
theorem mod2_mod2 {d : GDart} : d.mod2.mod2 = d.mod2 := by{
  simp[mod2_def]
}
theorem mod2_eq_zero_iff_exists_double {d : GPoint} : d.mod2 = 0 ↔ ∃p, d = 2 • p:= by{
  constructor
  · {
    intro h
    use d.half
    nth_rw 1 [←double_half_add_mod2 (d:=d)]
    rw[h, add_zero]
  }
  · {
    intro ⟨p, hp⟩
    rw[hp, mod2_double]
  }
}

def ccw : GPoint → GPoint
| ⟨x, y⟩ => ⟨1 - y, x⟩
theorem ccw_def {p : GPoint} : p.ccw = ⟨1 - p.2, p.1⟩ := rfl
theorem mod2_ccw {d : GDart} : d.mod2.ccw = d.ccw.mod2 := by{
  match d with
  | ⟨x, y⟩ => simp[mod2_def, ccw_def]; omega
}
theorem ccw_ne {p : GPoint} : p.ccw ≠ p := by{
  match p with
  | ⟨x, y⟩ => simp[ccw_def]; omega
}
theorem ccw2_ne {p : GPoint} : p.ccw.ccw ≠ p := by{
  match p with
  | ⟨x, y⟩ => simp[ccw_def]; omega
}
theorem ccw3_ne {p : GPoint} : p.ccw.ccw.ccw ≠ p := by{
  match p with
  | ⟨x, y⟩ => simp[ccw_def]; omega
}
theorem ccw_4_periodic {p : GPoint} : IsPeriodicPt ccw 4 p := by{
  match p with | ⟨x, y⟩ => simp[ccw, IsPeriodicPt, IsFixedPt]
}
theorem ccw_4 {p : GPoint} : p.ccw.ccw.ccw.ccw = p := by{
  exact ccw_4_periodic
}
theorem ccw_4_eq_id : ccw^[4] = id := by{
  ext p <;> simp[ccw_4]
}
theorem ccw_2 {p : GPoint} : p.ccw.ccw = ⟨1, 1⟩ - p := by{
  match p with
  | ⟨x, y⟩ => simp[ccw_def]
}
theorem ccw_injective : Injective ccw := by{
  intro x y hxy
  have hxy':=congrArg (ccw^[3] ·) hxy
  simp[ccw_4] at hxy'
  simp[hxy']
}
theorem add_ccw_mod2_ne_zero {p : GPoint} : (p + p.ccw).mod2 ≠ 0 := by{
  match p with | ⟨x, y⟩ => simp[ccw_def, mod2_def]; omega
}
theorem mod2_eq_mod2_cases {p q : GPoint}
  : p.mod2 = q.mod2 ∨ p.mod2 = q.mod2.ccw ∨ p.mod2 = q.mod2.ccw.ccw
  ∨ p.mod2 = q.mod2.ccw.ccw.ccw := by{
    match p, q with | ⟨px, py⟩, ⟨qx, qy⟩ => simp[mod2_def, ccw_def]; omega
  }

def arc (c : GCorner) : GVector := c.ccw - c
theorem arc_def {c : GCorner} : c.arc = c.ccw - c := rfl
theorem arc_def' {c : GCorner} : c.arc = (1 - c.2 - c.1, c.1 - c.2) := rfl
theorem arc_ne_zero {p : GPoint} : p.arc ≠ 0 := by{
  simp only [arc, ne_eq, sub_eq_zero]
  exact ccw_ne
}
theorem arc_ccw_2 {c : GCorner} : (ccw^[2] c).arc = - c.arc := by{
  match c with | ⟨x, y⟩ => simp[arc, ccw]; omega
}

end GPoint

abbrev GRegion := Set GPixel
def GRegion.zoom (r : GRegion) : GRegion :=
  {p | p.half ∈ r}
theorem GRegion.mem_zoom_iff {p : GPoint} {r : GRegion} : p ∈ r.zoom ↔ p.half ∈ r := Iff.rfl

end GridPlane
