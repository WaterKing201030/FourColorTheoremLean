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

@[ext] structure GPoint where
  x : ℤ
  y : ℤ
deriving DecidableEq
def GPoint.toProd : GPoint → ℤ × ℤ
| ⟨x, y⟩ => ⟨x, y⟩
def GPoint.ofProd : ℤ × ℤ → GPoint
| ⟨x, y⟩ => ⟨x, y⟩
def GPoint.equivProd : GPoint ≃ ℤ × ℤ where
  toFun:=toProd
  invFun:=ofProd
@[implicit_reducible] instance GPoint.instAddCommGroup : AddCommGroup GPoint
  := equivProd.addCommGroup

abbrev GPixel := GPoint
abbrev GCorner := GPoint
abbrev GDart := GPoint
abbrev GVector := GPoint

namespace GPoint

@[simp] theorem add_def {p q : GPoint} : p + q = {x := p.x + q.x, y := p.y + q.y}:=rfl
@[simp] theorem sub_def {p q : GPoint} : p - q = {x := p.x - q.x, y := p.y - q.y}:=rfl
@[simp] theorem neg_def {p : GPoint} : -p = {x := -p.x, y := -p.y}:=rfl

def half : GDart → GPixel
| ⟨x, y⟩ => ⟨x / 2, y / 2⟩
def mod2 : GDart → GCorner
| ⟨x, y⟩ => ⟨x % 2, y % 2⟩

theorem x_half {d : GDart} : d.half.x = d.x / 2 := rfl
theorem y_half {d : GDart} : d.half.y = d.y / 2 := rfl
theorem x_mod2 {d : GDart} : d.mod2.x = d.x % 2 := rfl
theorem y_mod2 {d : GDart} : d.mod2.y = d.y % 2 := rfl
theorem x_double {p : GPixel} : (2 • p).x = 2 * p.x := rfl
theorem y_double {p : GPixel} : (2 • p).y = 2 * p.y := rfl
theorem toProd_bijective : Bijective toProd := by{
  have h:=equivProd.bijective
  rw[←equivProd.toFun_as_coe] at h
  exact h
}
theorem ofProd_bijective : Bijective ofProd := by{
  have h:=equivProd.symm.bijective
  rw[←equivProd.invFun_as_coe] at h
  exact h
}
theorem toProd_injective : Injective toProd := toProd_bijective.injective
theorem ofProd_injective : Injective ofProd := ofProd_bijective.injective

theorem x_nsmul {n : ℕ} {p : GPoint} : (n • p).x = n * p.x := rfl
theorem y_nsmul {n : ℕ} {p : GPoint} : (n • p).y = n * p.y := rfl
theorem x_zsmul {n : ℤ} {p : GPoint} : (n • p).x = n * p.x := rfl
theorem y_zsmul {n : ℤ} {p : GPoint} : (n • p).y = n * p.y := rfl
theorem nsmul_cancel {n : ℕ} (hn : n ≠ 0) {p q : GPoint}
  (hpq : n • p = n • q) : p = q := by{
    simp[GPoint.ext_iff, x_nsmul, y_nsmul, hn] at hpq
    simp[GPoint.ext_iff, hpq]
  }
theorem nsmul_cancel_iff {n : ℕ} (hn : n ≠ 0) {p q : GPoint}
  : n • p = n • q ↔ p = q := ⟨nsmul_cancel hn, congrArg (_ • ·)⟩
theorem zsmul_cancel {n : ℤ} (hn : n ≠ 0) {p q : GPoint}
  (hpq : n • p = n • q) : p = q := by{
    simp[GPoint.ext_iff, x_zsmul, y_zsmul, hn] at hpq
    simp[GPoint.ext_iff, hpq]
  }
theorem zsmul_cancel_iff {n : ℤ} (hn : n ≠ 0) {p q : GPoint}
  : n • p = n • q ↔ p = q := ⟨zsmul_cancel hn, congrArg (_ • ·)⟩

theorem half_add_double {p : GPixel} {d : GDart} : (2 • p + d).half = p + d.half := by{
  match p, d with
  | ⟨px, py⟩, ⟨dx, dy⟩ => {
    rw[two_nsmul]
    simp only [Equiv.add_def, ←Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd, half]
    congr
    all_goals
    rw[←two_mul, Int.mul_add_ediv_left _ _ (by{simp})]
  }
}
theorem half_add_double' {p : GPixel} {d : GDart} : ((2 : ℤ) • p + d).half = p + d.half := by{
  rw[ofNat_zsmul, half_add_double]
}
theorem half_double {p : GPixel} : (2 • p).half = p := by{
  match p with
  | ⟨dx, dy⟩ => {
    rw[two_nsmul]
    simp only [Equiv.add_def, ←Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd, half]
    congr
    all_goals
    rw[←two_mul, Int.mul_ediv_cancel_left _ (by{simp})]
  }
}
theorem half_double' {p : GPixel} : ((2 : ℤ) • p).half = p := by{
  rw[ofNat_zsmul, half_double]
}
theorem mod2_add_double {p : GPixel} {d : GDart} : (2 • p + d).mod2 = d.mod2 := by{
  match p, d with
  | ⟨px, py⟩, ⟨dx, dy⟩ => {
    rw[two_nsmul]
    simp only [Equiv.add_def, ←Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd, mod2]
    congr 1
    all_goals
    rw[←two_mul, Int.mul_add_emod_self_left]
  }
}
theorem mod2_add_double' {p : GPixel} {d : GDart} : ((2 : ℤ) • p + d).mod2 = d.mod2 := by{
  rw[ofNat_zsmul, mod2_add_double]
}
theorem mod2_double {p : GPixel} : (2 • p).mod2 = 0 := by{
  match p with
  | ⟨dx, dy⟩ => {
    rw[two_nsmul]
    simp only [Equiv.add_def, ←Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd, mod2]
    congr 1
    all_goals
    rw[←two_mul, Int.mul_emod_right]
  }
}
theorem mod2_double' {p : GPixel} : ((2 : ℤ) • p).mod2 = 0 := by{
  rw[ofNat_zsmul, mod2_double]
}

theorem double_half_add_mod2 {d : GDart} : 2 • d.half + d.mod2 = d := by{
  match d with
  | ⟨dx, dy⟩ => {
    rw[two_nsmul]
    simp only [Equiv.add_def, ←Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd, half, mod2]
    congr 1
    all_goals
    rw[←two_mul, Int.mul_ediv_add_emod]
  }
}
theorem double'_half_add_mod2 {d : GDart} : (2 : ℤ) • d.half + d.mod2 = d := by{
  rw[ofNat_zsmul, double_half_add_mod2]
}

theorem zero_def : 0 = (⟨0, 0⟩ : GPoint) := rfl
theorem half_mod2 {d : GDart} : d.mod2.half = 0 := by{
  match d with
  | ⟨dx, dy⟩ => {simp[mod2, half, Int.emod_ediv_pos, zero_def]}
}
theorem mod2_mod2 {d : GDart} : d.mod2.mod2 = d.mod2 := by{
  simp[mod2]
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
inductive inUnitSquare : GPoint → Prop where
| gp00 : inUnitSquare ⟨0, 0⟩
| gp01 : inUnitSquare ⟨0, 1⟩
| gp10 : inUnitSquare ⟨1, 0⟩
| gp11 : inUnitSquare ⟨1, 1⟩

theorem x_eq_zero_or_one_of_inUnitSquare {d : GPoint} (h : d.inUnitSquare)
  : d.x = 0 ∨ d.x = 1 := by{
    cases h with
    | gp00 | gp01 | gp10 | gp11 => {
      simp
    }
  }
theorem y_eq_zero_or_one_of_inUnitSquare {d : GPoint} (h : d.inUnitSquare)
  : d.y = 0 ∨ d.y = 1 := by{
    cases h with
    | gp00 | gp01 | gp10 | gp11 => {
      simp
    }
  }
theorem inUnitSquare_iff {d : GPoint} :
  d.inUnitSquare ↔ (d.x = 0 ∨ d.x = 1) ∧ (d.y = 0 ∨ d.y = 1) := by{
    constructor
    · exact fun h => ⟨x_eq_zero_or_one_of_inUnitSquare h, y_eq_zero_or_one_of_inUnitSquare h⟩
    intro h
    match d with
    | ⟨x, y⟩ => {
      simp only at h
      cases h.left with
      | inl hx | inr hx => cases h.right with
        | inl hy | inr hy => simp[hx, hy, inUnitSquare.gp00, inUnitSquare.gp01,
        inUnitSquare.gp10, inUnitSquare.gp11]
    }
  }
inductive UnitSquareDart where
| gp00 | gp01 | gp10 | gp11
deriving DecidableEq
namespace UnitSquareDart
@[inline] instance instFintype : Fintype UnitSquareDart :=
  Fintype.mk [gp00, gp01, gp10, gp11].toFinset
    (by{intro x; match x with | gp00 | gp01 | gp10 | gp11 => simp})
def toGCorner : UnitSquareDart → GCorner
| gp00 => ⟨0, 0⟩ | gp01 => ⟨0, 1⟩ | gp10 => ⟨1, 0⟩ | gp11 => ⟨1, 1⟩
def cw : UnitSquareDart → UnitSquareDart
| gp00 => gp01 | gp01 => gp11 | gp11 => gp10 | gp10 => gp00
def ccw : UnitSquareDart → UnitSquareDart
| gp00 => gp10 | gp10 => gp11 | gp11 => gp01 | gp01 => gp00
def opp : UnitSquareDart → UnitSquareDart
| gp00 => gp11 | gp11 => gp00 | gp10 => gp01 | gp01 => gp10

theorem opp_eq_cw_2 : opp = cw^[2] := by{
  ext u
  match u with | gp00 | gp01 | gp11 | gp10 => simp[opp, cw]
}
theorem ccw_eq_cw_3 : ccw = cw^[3] := by{
  ext u
  match u with | gp00 | gp01 | gp11 | gp10 => simp[ccw, cw]
}
theorem cw_4 {u : UnitSquareDart} : cw (cw (cw (cw u))) = u := by{
  match u with | gp00 | gp01 | gp11 | gp10 => simp[cw]
}
theorem opp_2 {u : UnitSquareDart} : opp (opp u) = u := by{
  simp[opp_eq_cw_2, cw_4]
}
theorem ccw_4 {u : UnitSquareDart} : ccw (ccw (ccw (ccw u))) = u := by{
  simp[ccw_eq_cw_3, cw_4]
}
theorem cw_4_periodic {u : UnitSquareDart} : IsPeriodicPt cw 4 u := by{
  exact cw_4
}
theorem opp_2_periodic {u : UnitSquareDart} : IsPeriodicPt opp 2 u := by{
  exact opp_2
}
theorem ccw_4_periodic {u : UnitSquareDart} : IsPeriodicPt ccw 4 u := by{
  exact ccw_4
}
theorem opp_eq_ccw_2 : opp = ccw^[2] := by{
  ext u
  simp[opp_eq_cw_2, ccw_eq_cw_3, cw_4]
}
theorem cw_eq_ccw_3 : cw = ccw^[3] := by{
  ext u
  simp[ccw_eq_cw_3, cw_4]
}
theorem left_inv_cw : LeftInverse cw ccw := by{
  intro u
  simp[ccw_eq_cw_3, cw_4]
}
theorem right_inv_cw : RightInverse cw ccw := by{
  intro u
  simp[ccw_eq_cw_3, cw_4]
}
end UnitSquareDart
open UnitSquareDart

def toUnitSquareDart (d : GDart) : UnitSquareDart :=
  let ⟨x, y⟩ := d.mod2
  if x = 0 then
    if y = 0 then gp00 else gp01
  else
    if y = 0 then gp10 else gp11
theorem toUnitSquareDart_toGCorner {d : GDart} : d.toUnitSquareDart.toGCorner = d.mod2 := by{
  match d with
  | ⟨x, y⟩ => cases Int.emod_two_eq x with | inl hx | inr hx =>
    cases Int.emod_two_eq y with | inl hy | inr hy =>
      simp[mod2, hx, hy, toUnitSquareDart, toGCorner]
}
theorem UnitSquareDart.toGCorner_toUnitSquareDart {c : UnitSquareDart}
  : c.toGCorner.toUnitSquareDart = c := by{
    match c with | gp00 | gp01 | gp10 | gp11 => simp[toGCorner, toUnitSquareDart, mod2]
  }

theorem mod2_inUnitSquare {d : GPoint} :
  d.mod2.inUnitSquare := by{
    rw[inUnitSquare_iff, x_mod2, y_mod2]
    exact ⟨Int.emod_two_eq_zero_or_one _, Int.emod_two_eq_zero_or_one _⟩
  }
theorem mod2_eq_of_inUnitSquare {d : GPoint} (hd : d.inUnitSquare)
  : d.mod2 = d := by{
    cases hd with | gp00 | gp01 | gp10 | gp11 => simp[mod2]
  }
theorem half_eq_zero_of_inUnitSquare {d : GPoint} (hd : d.inUnitSquare)
  : d.half = 0 := by{
    cases hd with | gp00 | gp01 | gp10 | gp11 => simp[half, zero_def]
  }

theorem half_mod2_sub_unit {d : GPoint} : (d.mod2 - ⟨1, 1⟩).half = d.mod2 - ⟨1, 1⟩ := by{
  simp only [sub_def, x_mod2, y_mod2, GPoint.ext_iff, x_half, y_half]
  cases Int.emod_two_eq d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq d.y with | inl hy | inr hy =>
    simp[hx, hy]
}

theorem half_neg_mod2 {d : GDart} : (-d.mod2).half = -d.mod2 := by{
  simp only [neg_def, x_mod2, y_mod2, GPoint.ext_iff, x_half, y_half]
  cases Int.emod_two_eq d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq d.y with | inl hy | inr hy =>
    simp[hx, hy]
}

def ccw : GPoint → GPoint
| ⟨x, y⟩ => ⟨1 - y, x⟩
theorem x_ccw {p : GPoint} : p.ccw.x = 1 - p.y := rfl
theorem y_ccw {p : GPoint} : p.ccw.y = p.x := rfl

theorem mod2_ccw {d : GDart} : d.mod2.ccw = d.ccw.mod2 := by{
  match d with
  | ⟨x, y⟩ => {
    simp only [mod2, ccw]
    congr
    rw[sub_eq_iff_eq_add]
    symm
    cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      rw[Int.sub_emod]
      simp only [hy]
      simp
    }
  }
}
theorem ccw_ne {p : GPoint} : p.ccw ≠ p := by{
  match p with
  | ⟨x, y⟩ => {
    intro hxy
    simp only [ccw, mk.injEq] at hxy
    have ⟨hl, hr⟩:=hxy
    rw[hr] at hl
    rw[sub_eq_iff_eq_add] at hl
    have hl':=congrArg Even hl
    simp at hl'
  }
}
theorem ccw_4_periodic {p : GPoint} : IsPeriodicPt ccw 4 p := by{
  match p with | ⟨x, y⟩ => simp[ccw, IsPeriodicPt, IsFixedPt]
}
theorem ccw_4 {p : GPoint} : p.ccw.ccw.ccw.ccw = p := by{
  exact ccw_4_periodic
}
theorem ccw_2 {p : GPoint} : p.ccw.ccw = ⟨1, 1⟩ - p := by{
  match p with
  | ⟨x, y⟩ => {
    simp only [ccw, Equiv.sub_def, ← Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd]
  }
}
theorem ccw_2_ne {p : GPoint} : p.ccw.ccw ≠ p := by{
  rw[ccw_2]
  match p with
  | ⟨x, y⟩ => {
    simp
    omega
  }
}

theorem neg_toUnitSquareDart {p : GPoint} : (-p).toUnitSquareDart = p.toUnitSquareDart := by{
  match p with
  | ⟨x, y⟩ => {
    simp only [toUnitSquareDart, mod2, Equiv.toFun_as_coe, ← Equiv.invFun_as_coe]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd]
    simp only [Int.neg_emod_two]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy]
  }
}

theorem ccw_toUnitSquareDart {p : GPoint} : p.ccw.toUnitSquareDart = p.toUnitSquareDart.ccw := by{
  match p with
  | ⟨x, y⟩ => {
    simp only [toUnitSquareDart, ccw, mod2]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.sub_emod, UnitSquareDart.ccw]
  }
}

theorem ccw_injective : Injective ccw := by{
  intro x y hxy
  have hxy':=congrArg (ccw^[3] ·) hxy
  simp[ccw_4] at hxy'
  simp[hxy']
}
theorem ccw_3_ne {p : GPoint} : p.ccw.ccw.ccw ≠ p := by{
  apply ccw_injective.ne_iff.mp
  rw[ccw_4]
  symm
  exact ccw_ne
}

def arc (c : GCorner) : GVector := c.ccw - c
theorem arc_ccw_2 {c : GCorner} : (ccw^[2] c).arc = - c.arc := by{
  match c with
  | ⟨x, y⟩ => {
    simp only [iterate_succ, comp_apply, ccw, iterate_zero_apply, arc, Equiv.sub_def]
    simp only [←Equiv.invFun_as_coe, Equiv.neg_def]
    simp only [←Equiv.toFun_as_coe, equivProd, ofProd, toProd]
    abel_nf
  }
}
theorem x_arc {p : GPoint} : p.arc.x = 1 - p.y - p.x := rfl
theorem y_arc {p : GPoint} : p.arc.y = p.x - p.y := rfl
theorem arc_ne_zero {p : GPoint} : p.arc ≠ 0 := by{
  simp only [arc, ne_eq, sub_eq_zero]
  exact ccw_ne
}
theorem add_ccw_mod2_ne_zero {p : GPoint} : (p + p.ccw).mod2 ≠ 0 := by{
  simp only [ccw, add_def, zero_def, ne_eq]
  rw[GPoint.ext_iff, x_mod2, y_mod2]
  simp only
  rcases Int.emod_two_eq p.x with hx | hx
  all_goals
  rcases Int.emod_two_eq p.y with hy | hy
  all_goals
  rw[Int.add_emod, Int.sub_emod]
  rw[and_comm, Int.add_emod]
  simp[hx, hy]
}
theorem mod2_eq_mod2_cases {p q : GPoint}
  : p.mod2 = q.mod2 ∨ p.mod2 = q.mod2.ccw ∨ p.mod2 = q.mod2.ccw.ccw
  ∨ p.mod2 = q.mod2.ccw.ccw.ccw := by{
    simp only [mod2, mk.injEq, ccw, sub_sub_cancel]
    cases Int.emod_two_eq p.x with | inl hpx | inr hpx =>
    cases Int.emod_two_eq p.y with | inl hpy | inr hpy =>
    cases Int.emod_two_eq q.x with | inl hqx | inr hqx =>
    cases Int.emod_two_eq q.y with | inl hqy | inr hqy =>
      simp[hpx, hpy, hqx, hqy]
  }

theorem mod2_cases {p : GPoint}
  : p.mod2 = ⟨0, 0⟩ ∨ p.mod2 = ⟨1, 0⟩ ∨ p.mod2 = ⟨1, 1⟩ ∨ p.mod2 = ⟨0, 1⟩ := by{
    match p with | ⟨px, py⟩ => {
      cases Int.emod_two_eq px with | inl hpx | inr hpx =>
      cases Int.emod_two_eq py with | inl hpy | inr hpy =>
        simp[GPoint.ext_iff, x_mod2, y_mod2, hpx, hpy]
    }
  }

end GPoint

open GPoint

def end0 (d : GDart) : GPixel := d.half + d.mod2
def end1 (d : GDart) : GPixel := d.half + d.mod2.ccw

theorem end0_mod2 {d : GDart} : end0 d.mod2 = d.mod2 := by{
  simp[end0, half_mod2, mod2_mod2]
}
theorem end1_mod2 {d : GDart} : end1 d.mod2 = d.mod2.ccw := by{
  simp[end1, half_mod2, mod2_mod2]
}

theorem end0_add_double {p : GPixel} {d : GDart} : end0 (2 • p + d) = p + end0 d := by{
  rw[end0, half_add_double, mod2_add_double, end0, add_assoc]
}
theorem end1_add_double {p : GPixel} {d : GDart} : end1 (2 • p + d) = p + end1 d := by{
  rw[end1, half_add_double, mod2_add_double, end1, add_assoc]
}

theorem GPoint.mod2_arc {d : GDart} : d.mod2.arc = end1 d - end0 d := by{
  simp[arc, end1, end0]
}

def edge (d : GDart) : GDart := d + (d.mod2.arc - d.mod2.ccw.arc)
def node (d : GDart) : GDart := d - d.mod2.arc
def face (d : GDart) : GDart := d + d.mod2.arc

theorem enf_cancel : ∀d, edge (node (face d)) = d:=by{
  intro d
  match d with
  | ⟨x, y⟩ => {
    simp only [edge, node, face, arc, ccw, mod2, sub_def, add_def, sub_sub_sub_cancel_left,
      sub_sub_sub_cancel_right, mk.injEq]
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, Int.add_emod, Int.sub_emod]
  }
}
theorem nfe_cancel : ∀d, (node (face (edge d))) = d:=by{
  intro d
  match d with
  | ⟨x, y⟩ => {
    simp only [edge, node, face, arc, ccw, mod2, sub_def, add_def, sub_sub_sub_cancel_left,
      sub_sub_sub_cancel_right, mk.injEq]
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, Int.add_emod]
  }
}
theorem fen_cancel : ∀d, (face (edge (node d))) = d:=by{
  intro d
  match d with
  | ⟨x, y⟩ => {
    simp only [edge, node, face, arc, ccw, mod2, sub_def, add_def, sub_sub_sub_cancel_left,
      sub_sub_sub_cancel_right, mk.injEq]
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, Int.add_emod, Int.sub_emod]
  }
}
theorem enf_id : edge ∘ node ∘ face = id := funext enf_cancel
theorem nfe_id : node ∘ face ∘ edge = id := funext nfe_cancel
theorem fen_id : face ∘ edge ∘ node = id := funext fen_cancel

theorem edge_leftInverse : LeftInverse edge (node ∘ face) := enf_cancel
theorem node_leftInverse : LeftInverse node (face ∘ edge) := nfe_cancel
theorem face_leftInverse : LeftInverse face (edge ∘ node) := fen_cancel

theorem edge_rightInverse : RightInverse edge (node ∘ face) := nfe_cancel
theorem node_rightInverse : RightInverse node (face ∘ edge) := fen_cancel
theorem face_rightInverse : RightInverse face (edge ∘ node) := enf_cancel

theorem edge_surjective : Surjective edge := LeftInverse.surjective edge_leftInverse
theorem edge_injective : Injective edge := RightInverse.injective edge_rightInverse
theorem edge_inj {x y : GDart} : edge x = edge y ↔ x = y := edge_injective.eq_iff
theorem edge_bijective : Bijective edge := ⟨edge_injective, edge_surjective⟩

theorem node_surjective : Surjective node := LeftInverse.surjective node_leftInverse
theorem node_injective : Injective node := RightInverse.injective node_rightInverse
theorem node_inj {x y : GDart} : node x = node y ↔ x = y := node_injective.eq_iff
theorem node_bijective : Bijective node := ⟨node_injective, node_surjective⟩

theorem face_surjective : Surjective face := LeftInverse.surjective face_leftInverse
theorem face_injective : Injective face := RightInverse.injective face_rightInverse
theorem face_inj {x y : GDart} : face x = face y ↔ x = y := face_injective.eq_iff
theorem face_bijective : Bijective face := ⟨face_injective, face_surjective⟩

theorem face_4_periodic {d : GDart} : IsPeriodicPt face 4 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [IsPeriodicPt, IsFixedPt, iterate_succ, comp_apply, face, arc, ccw, mod2,
      sub_def, add_def]
    cases Int.emod_two_eq x with | inl hx | inr hx => cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      simp[hx, hy, Int.add_emod]
    }
  }
}
theorem node_4_periodic {d : GDart} : IsPeriodicPt node 4 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [IsPeriodicPt, IsFixedPt, iterate_succ, comp_apply, node, arc, ccw, mod2,
      sub_def]
    cases Int.emod_two_eq x with | inl hx | inr hx => cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      simp[hx, hy, Int.add_emod, Int.sub_emod]
    }
  }
}
theorem edge_2_periodic {d : GDart} : IsPeriodicPt edge 2 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [IsPeriodicPt, IsFixedPt, iterate_succ, comp_apply, edge, arc, ccw, mod2,
      sub_def, add_def]
    cases Int.emod_two_eq x with | inl hx | inr hx => cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      simp[hx, hy, Int.add_emod]
    }
  }
}

theorem face_4 {d : GDart} : face (face (face (face d))) = d := face_4_periodic
theorem node_4 {d : GDart} : node (node (node (node d))) = d := node_4_periodic
theorem edge_2 {d : GDart} : edge (edge d) = d := edge_2_periodic

theorem face_3 {d : GDart} : face (face (face d)) = edge (node d) := by{
  apply face_injective
  rw[face_4, fen_cancel]
}
theorem face_3_eq_add_arc_ccw {d : GDart} : face (face (face d)) = d + d.mod2.ccw.arc := by{
  apply face_injective
  rw[face_4, face]
  match d with | ⟨dx, dy⟩ => {
    simp only [arc, sub_def, x_ccw, y_ccw, x_mod2, y_mod2, sub_sub_sub_cancel_left, add_def,
      mk.injEq]
    cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
    cases Int.emod_two_eq dy with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      omega
    }
  }
}
theorem node_3 {d : GDart} : node (node (node d)) = face (edge d) := by{
  apply node_injective
  rw[node_4, nfe_cancel]
}
theorem edge_eq_node_face {d : GDart} : edge d = node (face d) := by{
  apply edge_injective
  rw[edge_2, enf_cancel]
}

theorem face_ne_node {d : GDart} : face d ≠ node d :=by{
  simp only [face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, add_def, node, ne_eq, mk.injEq,
    not_and]
  cases Int.emod_two_eq_zero_or_one d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq_zero_or_one d.y with | inl hy | inr hy =>
    simp[hx, hy]; try omega
}
theorem face_ne_edge {d : GDart} : face d ≠ edge d :=by{
  simp only [face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, add_def, edge, ne_eq, mk.injEq,
    not_and]
  cases Int.emod_two_eq_zero_or_one d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq_zero_or_one d.y with | inl hy | inr hy =>
    simp[hx, hy]; try omega
}
theorem node_ne_edge {d : GDart} : node d ≠ edge d :=by{
  simp only [node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, add_def, edge, ne_eq, mk.injEq,
    not_and]
  cases Int.emod_two_eq_zero_or_one d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq_zero_or_one d.y with | inl hy | inr hy =>
    simp[hx, hy]; try omega
}
theorem node_ne_face {d : GDart} : node d ≠ face d := face_ne_node.symm
theorem edge_ne_face {d : GDart} : edge d ≠ face d := face_ne_edge.symm
theorem edge_ne_node {d : GDart} : edge d ≠ node d := node_ne_edge.symm

theorem edge_end0 {d : GDart} : end0 (edge d) = end1 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [end0, half, edge, arc, ccw, mod2, sub_def, sub_sub_sub_cancel_left,
      sub_sub_sub_cancel_right, add_def, end1, mk.injEq]
    cases Int.emod_two_eq x with | inl hx | inr hx => cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      simp[hx, hy, Int.add_emod]
      simp[Int.add_ediv, hx, hy, Int.sign]
    }
  }
}

theorem edge_end1 {d : GDart} : end1 (edge d) = end0 d := by{
  nth_rw 2 [←edge_2 (d:=d)]
  rw[edge_end0]
}

theorem face_toUnitSquareDart {d : GDart} : (face d).toUnitSquareDart = d.toUnitSquareDart.ccw
:= by{
  match d with | ⟨x, y⟩ => {
    simp only [toUnitSquareDart, mod2, face, arc, ccw, sub_def, add_def]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_emod, UnitSquareDart.ccw]
  }
}
theorem node_toUnitSquareDart {d : GDart} : (node d).toUnitSquareDart = d.toUnitSquareDart.ccw
:= by{
  match d with | ⟨x, y⟩ => {
    simp only [toUnitSquareDart, mod2, node, arc, ccw, sub_def]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_emod, Int.sub_emod, UnitSquareDart.ccw]
  }
}
theorem edge_toUnitSquareDart {d : GDart} : (edge d).toUnitSquareDart = d.toUnitSquareDart.opp
:= by{
  nth_rw 2 [←nfe_cancel d]
  rw[node_toUnitSquareDart, face_toUnitSquareDart]
  rw[UnitSquareDart.opp_eq_ccw_2]
  simp[UnitSquareDart.ccw_4]
}

theorem face_half {d : GDart} : (face d).half = d.half := by{
  match d with | ⟨x, y⟩ => {
    simp only [half, face, arc, ccw, mod2, sub_def, add_def, mk.injEq]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign]
  }
}
open GPoint.UnitSquareDart
theorem node_half' {d : GDart} : (node d).half = match d.toUnitSquareDart with
  | gp00 => {x := d.half.x - 1, y:=d.half.y}
  | gp01 => {x := d.half.x, y:=d.half.y + 1}
  | gp10 => {x := d.half.x, y:=d.half.y - 1}
  | gp11 => {x := d.half.x + 1, y:=d.half.y}
:= by{
  match d with | ⟨x, y⟩ => {
    have h {k : ℤ} : (k - 1) / 2 = k / 2 - 1 + k % 2:=by{
      cases Int.emod_two_eq_zero_or_one k with
      | inl hk => {
        simp only [hk, add_zero]
        nth_rw 1 [←Int.ediv_mul_cancel_of_emod_eq_zero hk]
        rw[Int.mul_sub_ediv_right _ _ (by{simp})]
        rfl
      }
      | inr hk => {
        simp only [hk, sub_add_cancel]
        nth_rw 1 [←Int.ediv_mul_add_emod k 2]
        rw[hk]
        simp
      }
    }
    simp only [half, node, arc, GPoint.ccw, mod2, sub_def, toUnitSquareDart]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign, h]
  }
}

theorem edge_half' {d : GDart} : (edge d).half = match d.toUnitSquareDart with
  | gp00 => {x := d.half.x, y:=d.half.y - 1}
  | gp01 => {x := d.half.x - 1, y:=d.half.y}
  | gp10 => {x := d.half.x + 1, y:=d.half.y}
  | gp11 => {x := d.half.x, y:=d.half.y + 1}
:= by{
  match d with | ⟨x, y⟩ => {
    simp only [half, edge, arc, GPoint.ccw, mod2, sub_def, toUnitSquareDart]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign]
      try simp[Int.add_neg_eq_sub]
  }
}
theorem edge_half_ne {d : GDart} : (edge d).half ≠ d.half := by{
  simp only [edge_half', ne_eq]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[GPoint.ext_iff]
}
theorem edge_half {d : GDart} : (edge d).half = d.half + d.mod2.ccw + d.mod2 - ⟨1, 1⟩ := by{
  rw[edge, arc, arc, sub_sub, ←add_sub_assoc, ←add_sub_assoc, ←sub_add]
  rw[sub_add_eq_add_sub, add_assoc, ←two_nsmul]
  nth_rw 1 [←GPoint.double_half_add_mod2 (d:=d)]
  rw[add_right_comm, ←nsmul_add, add_sub_assoc, half_add_double]
  rw[add_sub_assoc, add_left_cancel_iff]
  rw[sub_add_cancel_left, ccw_2, neg_sub]
  exact half_mod2_sub_unit
}
theorem edge_half_eq_edge0_add {d : GDart} : (edge d).half = end0 d + d.mod2.ccw - ⟨1, 1⟩:=by{
  rw[edge_half, add_right_comm, ←end0]
}
theorem node_half_eq_end0_sub {d : GDart} : (node d).half = end0 d - d.mod2.ccw := by{
  rw[node, arc, ←sub_add, sub_add_eq_add_sub]
  nth_rw 1 [←double_half_add_mod2 (d:=d)]
  rw[add_assoc, ←two_nsmul, ←nsmul_add, ←end0, sub_eq_add_neg, half_add_double]
  rw[mod2_ccw, half_neg_mod2, ←sub_eq_add_neg]
}
theorem node_half {d : GDart} : (node d).half = d.half - d.mod2.ccw + d.mod2 := by{
  rw[node_half_eq_end0_sub, end0, sub_add_eq_add_sub]
}
theorem end0_double {p : GPixel} : end0 (2 • p) = p := by{
  rw[end0, half_double, mod2_double, add_zero]
}
theorem face_end0 {d : GDart} : end0 (face d) = end1 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [end0, end1, half, face, arc, GPoint.ccw, mod2, sub_def]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign, Int.add_emod]
  }
}
theorem node_end0 {d : GDart} : end0 (node d) = end0 d :=by{
  nth_rw 2 [←fen_cancel d]
  rw[face_end0, edge_end1]
}

theorem face_mod2 {d : GDart} : (face d).mod2 = d.mod2.ccw := by{
  match d with | ⟨x, y⟩ => {
    simp only [mod2, face, arc, GPoint.ccw, sub_def, add_def, mk.injEq]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_emod]
  }
}
theorem node_mod2 {d : GDart} : (node d).mod2 = d.mod2.ccw := by{
  match d with | ⟨x, y⟩ => {
    simp only [mod2, node, arc, GPoint.ccw, sub_def, mk.injEq]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_emod, Int.sub_emod]
  }
}
theorem edge_mod2 {d : GDart} : (edge d).mod2 = d.mod2.ccw.ccw := by{
  match d with | ⟨x, y⟩ => {
    simp only [mod2, edge, arc, GPoint.ccw, sub_def, mk.injEq]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_emod]
  }
}
theorem face_ne {d : GDart} : face d ≠ d := by{
  simp only [face, ne_eq, add_eq_left]
  exact arc_ne_zero
}
theorem node_ne {d : GDart} : node d ≠ d := by{
  simp only [node, ne_eq, sub_eq_self]
  exact arc_ne_zero
}
theorem edge_ne {d : GDart} : edge d ≠ d := by{
  simp only [edge, ne_eq, add_eq_left, sub_eq_zero]
  simp only [arc]
  rw[ccw_2, sub_right_comm, sub_eq_iff_eq_add, sub_add_cancel, eq_sub_iff_add_eq]
  match d with | ⟨dx, dy⟩ => {
    simp only [mod2, add_def, x_ccw, y_ccw, mk.injEq, not_and]
    cases Int.emod_two_eq dx with
    | inl hx | inr hx => simp[hx]
  }
}

theorem face_2_ne {d : GDart} : face (face d) ≠ d := by{
  simp only [face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, add_def, ne_eq]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem face_3_ne {d : GDart} : face (face (face d)) ≠ d := by{
  simp only [face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, add_def, ne_eq]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem node_2_ne {d : GDart} : node (node d) ≠ d := by{
  simp only [node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, ne_eq]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem node_3_ne {d : GDart} : node (node (node d)) ≠ d := by{
  simp only [node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, ne_eq]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem end0_ne_end1 {d : GDart} : end0 d ≠ end1 d := by{
  rw[end0, end1, ne_eq, add_left_cancel_iff]
  exact Ne.symm ccw_ne
}
theorem face_end0_ne_end0 {d : GDart} : end0 (face d) ≠ end0 d :=by{
  rw[face_end0]
  exact Ne.symm end0_ne_end1
}
theorem face_2_end0_ne_end0 {d : GDart} : end0 (face (face d)) ≠ end0 d :=by{
  simp only [end0, face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, ne_eq, add_def, x_half, y_half]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem face_3_end0_ne_end0 {d : GDart} : end0 (face (face (face d))) ≠ end0 d :=by{
  simp only [end0, face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, ne_eq, add_def, x_half, y_half]
  match d with | ⟨dx, dy⟩ => {
    simp only [mk.injEq, not_and]
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy]; try omega
  }
}
theorem end0_add_end1_mod2_ne_zero {d : GDart} : (end0 d + end1 d).mod2 ≠ 0 := by{
  rw[end0, end1, add_assoc, add_left_comm _ d.half, ←add_assoc, ←two_nsmul]
  rw[mod2_add_double]
  apply GPoint.add_ccw_mod2_ne_zero
}
theorem end0_add_end1_eq_iff_eq_or_edge_eq {d0 d1 : GDart}
  : end0 d0 + end1 d0 = end0 d1 + end1 d1 ↔ d0 = d1 ∨ d0 = edge d1 := by{
    constructor
    · {
      intro h
      apply (em (d0 = d1)).imp_right
      intro h'
      unfold end0 end1 at h
      rw[add_assoc, add_left_comm _ d0.half, ←add_assoc, ←two_nsmul,
      ←add_assoc, double_half_add_mod2] at h
      symm at h
      rw[add_assoc, add_left_comm _ d1.half, ←add_assoc, ←two_nsmul,
      ←add_assoc, double_half_add_mod2] at h
      rw[edge, arc, arc]
      rw[sub_sub, ←add_sub_assoc (c:=GPoint.ccw _)]
      rw[←sub_add, ccw_2, add_sub_cancel, ←add_assoc, ←add_sub_assoc, h]
      rw[sub_add_eq_add_sub, add_sub_assoc, add_assoc]
      symm
      rw[add_eq_left, ←add_sub_assoc, sub_eq_zero]
      match d0, d1 with
      | ⟨d0x, d0y⟩, ⟨d1x, d1y⟩ => {
        simp only [GPoint.ccw, mod2, add_def, mk.injEq] at h
        simp only [mk.injEq, not_and] at h'
        simp only [GPoint.ccw, mod2, add_def, mk.injEq]
        rcases Int.emod_two_eq d0x with hd0x | hd0x
        all_goals
        rcases Int.emod_two_eq d1x with hd1x | hd1x
        all_goals
        rcases Int.emod_two_eq d0y with hd0y | hd0y
        all_goals
        rcases Int.emod_two_eq d1y with hd1y | hd1y
        all_goals
        simp only [hd1y, sub_zero, hd0y, add_left_inj, hd1x, add_zero, hd0x] at h
        have ⟨hx, hy⟩:=h
        apply congrArg (· % 2) at hx
        apply congrArg (· % 2) at hy
        try simp [Int.add_one_emod_two] at hx
        try simp [Int.add_one_emod_two] at hy
        try simp [h] at h'
        try simp[hd0x, hd1x, hd0y, hd1y] at hx hy
        try simp[hd0x, hd1x, hd0y, hd1y]
      }
    }
    · {
      intro h
      rcases h with h | h
      · simp[h]
      · simp[h, edge_end0, edge_end1, add_comm]
    }
  }
theorem half_eq_cases_face {d0 d1 : GDart}
  : d0.half = d1.half ↔ d0 = d1 ∨ d0 = face d1 ∨ d0 = face (face d1) ∨ d0 = face (face (face d1))
  := by{
    constructor
    · {
      intro h
      nth_rw 1 [face, arc]
      nth_rw 1 [face, face_mod2, arc, face, arc]
      nth_rw 1 [face, face_mod2, face_mod2, arc, face, face_mod2, arc, face, arc]
      rw[add_right_comm, ←add_sub_assoc, ←add_sub_assoc, ←add_sub_assoc, sub_add_cancel]
      rw[add_sub_assoc, add_sub_assoc, add_right_comm, ←add_sub_assoc, ←add_sub_assoc]
      rw[←add_sub_assoc, ←add_sub_assoc, sub_add_cancel]
      rw[←GPoint.double_half_add_mod2 (d:=d0)]
      rw[add_sub_right_comm, add_sub_right_comm, add_sub_right_comm]
      nth_rw 1 2 5 8 [←GPoint.double_half_add_mod2 (d:=d1)]
      rw[add_sub_cancel_right, h]
      simp only [add_left_cancel_iff]
      apply mod2_eq_mod2_cases
    }
    · {
      intro h
      rcases h with h | h | h | h
      all_goals
      simp[h, face_half]
    }
  }
theorem end0_eq_cases_node {d0 d1 : GDart}
  : end0 d0 = end0 d1 ↔ d0 = d1 ∨ d0 = node d1 ∨ d0 = node (node d1) ∨ d0 = node (node (node d1))
  := by{
    constructor
    · {
      intro h
      nth_rw 1 [node, arc]
      nth_rw 1 [node, node_mod2, arc, node, arc]
      nth_rw 1 [node, node_mod2, node_mod2, arc, node, node_mod2, arc, node, arc]
      rw[sub_sub, add_comm, ←add_sub_assoc, sub_add_cancel]
      rw[sub_sub, add_comm, ←add_sub_assoc, sub_add_cancel]
      simp only [←sub_add, sub_add_eq_add_sub, eq_sub_iff_add_eq]
      nth_rw 1 3 6 9 [←double_half_add_mod2 (d:=d1)]
      nth_rw 1 [←add_right_cancel_iff (a:=d1.mod2)]
      simp only [add_assoc, ←two_nsmul, ←nsmul_add]
      repeat rw[←end0, ←h]
      rw[end0, nsmul_add, two_nsmul d0.mod2, ←add_assoc, double_half_add_mod2]
      simp only [add_left_cancel_iff]
      simp only [Eq.comm (b:=d0.mod2)]
      apply mod2_eq_mod2_cases
    }
    · {
      intro h
      rcases h with h | h | h | h
      all_goals
      simp[h, node_end0]
    }
  }
theorem half_eq_exists_iterate {d0 d1 : GDart} : d0.half = d1.half ↔ ∃n, face^[n] d0 = d1 := by{
  constructor
  · {
    intro h
    rw[half_eq_cases_face] at h
    rcases h with h | h | h | h
    · use 0; simp[h]
    · use 3; simp[h, face_4]
    · use 2; simp[h, face_4]
    · use 1; simp[h, face_4]
  }
  · {
    intro ⟨n, hn⟩
    induction n generalizing d0 with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      specialize ih hn
      rw[face_half] at ih
      exact ih
    }
  }
}
theorem end0_eq_exists_iterate {d0 d1 : GDart} : end0 d0 = end0 d1 ↔ ∃n, node^[n] d0 = d1 := by{
  constructor
  · {
    intro h
    rw[end0_eq_cases_node] at h
    rcases h with h | h | h | h
    · use 0; simp[h]
    · use 3; simp[h, node_4]
    · use 2; simp[h, node_4]
    · use 1; simp[h, node_4]
  }
  · {
    intro ⟨n, hn⟩
    induction n generalizing d0 with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      specialize ih hn
      rw[node_end0] at ih
      exact ih
    }
  }
}
theorem end0_eq_exists_iterate_3 {d0 d1 : GDart} :
  end0 d0 = end0 d1 ↔ ∃n, (node ∘ node ∘ node)^[n] d0 = d1 := by{
  constructor
  · {
    intro h
    rw[end0_eq_cases_node] at h
    rcases h with h | h | h | h
    · use 0; simp[h]
    · use 1; simp[h, node_4]
    · use 2; simp[h, node_4]
    · use 3; simp[h, node_4]
  }
  · {
    intro ⟨n, hn⟩
    rw[end0_eq_exists_iterate]
    use n * 3
    rw[← hn]
    clear hn
    induction n with
    | zero => simp
    | succ n' ih => {
      rw[iterate_succ_apply', ← ih, Nat.succ_mul, add_comm, iterate_add_apply]
      rfl
    }
  }
}
abbrev GRegion := Set GPixel
abbrev GDartRegion:=GRegion
structure GInterval where
  lb : ℤ
  ub : ℤ
structure GRectangle where
  hspan : GInterval
  vspan : GInterval
def GInterval.toSet (I : GInterval) : Set ℤ := {x | I.lb ≤ x ∧ x < I.ub}
def GInterval.Mem (I : GInterval) (x : ℤ) : Prop := x ∈ I.toSet
@[inline] instance GInterval.instMembership : Membership ℤ GInterval where mem := GInterval.Mem
theorem GInterval.mem_iff (I : GInterval) (x : ℤ) : x ∈ I ↔ I.lb ≤ x ∧ x < I.ub := by rfl
theorem GInterval.mem_iff_toSet {I : GInterval} {x : ℤ} : x ∈ I ↔ x ∈ I.toSet := by{rfl}
def GRectangle.toRegion (R : GRectangle) : GRegion := {p | p.x ∈ R.hspan ∧ p.y ∈ R.vspan}
def GRectangle.Mem (R : GRectangle) (p : GPixel) : Prop := p ∈ R.toRegion
@[inline] instance GRectangle.instMembership :
  Membership GPoint GRectangle where mem := GRectangle.Mem
theorem GRectangle.mem_iff (R : GRectangle) (p : GPixel) :
  p ∈ R ↔ p.x ∈ R.hspan ∧ p.y ∈ R.vspan := by rfl
theorem GRectangle.mem_iff_toRegion {R : GRectangle} {x : GPixel} : x ∈ R ↔ x ∈ R.toRegion
  := by{rfl}
def GInterval.subset (I1 I2 : GInterval) : Prop := ∀ {x : ℤ}, x ∈ I1 → x ∈ I2
@[inline] instance GInterval.instHasSubset : HasSubset GInterval :=
  ⟨subset⟩
theorem GInterval.subset_iff {I1 I2 : GInterval} : I1 ⊆ I2 ↔ ∀ {x : ℤ}, x ∈ I1 → x ∈ I2 := by{rfl}
theorem GInterval.subset_iff_set_subset {I1 I2 : GInterval} : I1 ⊆ I2 ↔ I1.toSet ⊆ I2.toSet
:= by{
  rw[subset_iff, Set.subset_def]
  simp[mem_iff, toSet]
}
def GRectangle.subset (R1 R2 : GRectangle) : Prop := ∀ {x : GPoint}, x ∈ R1 → x ∈ R2
@[inline] instance GRectangle.instHasSubset : HasSubset GRectangle :=
  ⟨subset⟩
theorem GRectangle.subset_iff {R1 R2 : GRectangle}
  : R1 ⊆ R2 ↔ ∀ {x : GPoint}, x ∈ R1 → x ∈ R2 := by{rfl}
theorem GRectangle.subset_iff_region_subset {R1 R2 : GRectangle}
  : R1 ⊆ R2 ↔ R1.toRegion ⊆ R2.toRegion
:= by{
  rw[subset_iff]
  simp[mem_iff, toRegion]
}

namespace GInterval
def width (I : GInterval) : ℕ := (I.ub - I.lb).toNat
def enum (I : GInterval) : List ℤ := (List.range I.width).map (Int.ofNat · + I.lb)
theorem enum_length {I : GInterval} : I.enum.length = I.width := by{simp[enum]}
theorem enum_nodup {I : GInterval} : I.enum.Nodup := by{
  rw[enum]
  rw[List.nodup_map_iff]
  · exact List.nodup_range
  apply Injective.comp (g:=(· + I.lb)) ?_ Int.ofNat_injective
  exact fun _ _ => (Int.add_left_inj I.lb).mp
}
theorem mem_enum_iff {I : GInterval} {x : ℤ} : x ∈ I.enum ↔ x ∈ I := by{
  rw[enum, List.mem_map, mem_iff]
  simp only [List.mem_range, width]
  simp only [Int.lt_toNat, Int.ofNat_eq_natCast]
  constructor
  · {
    intro ⟨a, ha0, ha1⟩
    constructor
    · simp[←ha1]
    · {
      rw[←ha1]
      apply lt_of_lt_of_le (add_lt_add_left ha0 I.lb)
      rw[sub_add_cancel]
    }
  }
  · {
    intro ⟨h0, h1⟩
    simp only [←eq_sub_iff_add_eq]
    use (x - I.lb).toNat
    simp[h0, h1]
  }
}

theorem subset_of_contain {I1 I2 : GInterval} (hm : I2.lb ≤ I1.lb) (hM : I1.ub ≤ I2.ub)
  : I1 ⊆ I2 := by{
    simp only [subset_iff_set_subset, toSet, Set.setOf_subset_setOf, and_imp]
    intro a ha0 ha1
    constructor
    · exact le_trans hm ha0
    · exact lt_of_lt_of_le ha1 hM
  }
theorem empty_of_ge {I : GInterval} (hm : I.lb ≥ I.ub) : I.toSet = ∅ :=by{
  ext x
  simp only [toSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro h
  exact le_trans hm h
}
end GInterval

namespace GRectangle
def width (R : GRectangle) : ℕ := R.hspan.width
def height (R : GRectangle) : ℕ := R.vspan.width
def area (R : GRectangle) : ℕ := R.width * R.height
def proper (R : GRectangle) : Prop := R.area > 0
def enum (R : GRectangle) : List GPixel := (R.hspan.enum ×ˢ R.vspan.enum).map ofProd
theorem width_eta {R : GRectangle} : R.hspan.width = R.width := rfl
theorem height_eta {R : GRectangle} : R.vspan.width = R.height := rfl
theorem enum_length {R : GRectangle} : R.enum.length = R.area := by{
  simp[enum, area, GInterval.enum, List.length_product, width, height]
}
theorem enum_nodup {R : GRectangle} : R.enum.Nodup := by{
  rw[enum]
  rw[List.nodup_map_iff]
  · apply List.Nodup.product
    · exact GInterval.enum_nodup
    · exact GInterval.enum_nodup
  · exact ofProd_injective
}
theorem mem_enum_iff {R : GRectangle} {p : GPoint} : p ∈ R.enum ↔ p ∈ R := by{
  rw[enum, List.mem_map, mem_iff]
  constructor
  · {
    intro ⟨⟨x, y⟩, h0, h1⟩
    simp only [List.mem_product, GInterval.mem_enum_iff] at h0
    match p with
    | ⟨x', y'⟩ => {
      simp[ofProd] at h1
      simp[←h1.left, ←h1.right, h0]
    }
  }
  · {
    intro ⟨hdx, hdy⟩
    use ⟨p.x, p.y⟩
    simp[GInterval.mem_enum_iff, hdx, hdy, ofProd]
  }
}
theorem proper_of_mem {R : GRectangle} {p : GPoint} (h : p ∈ R) : R.proper := by{
  rw[←mem_enum_iff] at h
  rw[proper, ←enum_length]
  exact List.length_pos_of_mem h
}
theorem proper_iff_pos {R : GRectangle} : R.proper ↔ R.width > 0 ∧ R.height > 0 := by{
  rw[proper, area]
  simp
}
theorem empty_iff_any_empty {R : GRectangle}
  : R.toRegion = ∅ ↔ R.hspan.toSet = ∅ ∨ R.vspan.toSet = ∅
  := by{
    simp only [Set.ext_iff, Set.mem_empty_iff_false, iff_false, toRegion, Set.mem_setOf]
    simp only [Classical.not_and_iff_not_or_not, GInterval.mem_iff_toSet]
    constructor
    · {
      intro h
      cases em (∀x, x ∉ R.hspan.toSet) with
      | inl hh => exact Or.inl hh
      | inr hh => {
        rw[not_forall] at hh
        have ⟨x, hx⟩:=hh
        cases em (∀x, x ∉ R.vspan.toSet) with
        | inl hv => exact Or.inr hv
        | inr hv => {
          rw[not_forall] at hv
          have ⟨y, hy⟩:=hv
          rw[not_not] at hx hy
          have h':=h ⟨x, y⟩
          simp[hx, hy] at h'
        }
      }
    }
    · {
      intro h x
      rcases h with h | h
      · exact Or.inl (h x.x)
      · exact Or.inr (h x.y)
    }
  }

theorem subset_iff_enum {R1 R2 : GRectangle}
  : R1 ⊆ R2 ↔ R1.enum ⊆ R2.enum := by{
    simp[subset_iff, List.subset_def, ←mem_enum_iff]
  }
theorem subset.refl : ∀r : GRectangle, r ⊆ r := by{
  simp[GRectangle.subset_iff_enum]
}

theorem exists_ld_corner_of_proper {R : GRectangle} (hR : R.proper) :
  ∃p0, (∀x y : ℤ, p0 + ⟨x, y⟩ ∈ R ↔ (0 ≤ x ∧ x < R.width) ∧ (0 ≤ y ∧ y < R.height))
    ∧ ∀p ∈ R, ∃x y : ℕ, p = p0 + ⟨x, y⟩ ∧ x < R.width ∧ y < R.height := by{
  rw[proper_iff_pos] at hR
  match R with | ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ => {
    simp only [width, height, GInterval.width, ← Int.pos_iff_toNat_pos, Int.sub_pos] at hR
    use ⟨x0, y0⟩
    simp only [add_def, mem_iff, GInterval.mem_iff, le_add_iff_nonneg_right, width, GInterval.width,
      Int.ofNat_toNat, lt_sup_iff, height, Int.lt_toNat, and_imp, GPoint.ext_iff]
    constructor
    · omega
    intro p
    match p with | ⟨px, py⟩ => {
      simp only
      intro h0 h1 h2 h3
      use (px - x0).toNat, (py - y0).toNat
      simp[h0, h1, h2, h3]
    }
  }
}

theorem width_eq_sub_of_proper {R : GRectangle} (hR : R.proper) :
  R.width = R.hspan.ub - R.hspan.lb := by{
    have h := (proper_iff_pos.mp hR).left
    rw[width, GInterval.width]
    rw[width, GInterval.width] at h
    have h' := Int.pos_iff_toNat_pos.mpr h
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact le_of_lt h'
  }
theorem height_eq_sub_of_proper {R : GRectangle} (hR : R.proper) :
  R.height = R.vspan.ub - R.vspan.lb := by{
    have h := (proper_iff_pos.mp hR).right
    rw[height, GInterval.width]
    rw[height, GInterval.width] at h
    have h' := Int.pos_iff_toNat_pos.mpr h
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact le_of_lt h'
  }
theorem hspan_lt_of_proper {R : GRectangle} (hR : R.proper) :
  R.hspan.lb < R.hspan.ub := by{
    apply Int.lt_of_sub_pos
    rw[← width_eq_sub_of_proper hR]
    simp[proper_iff_pos.mp hR]
  }
theorem vspan_lt_of_proper {R : GRectangle} (hR : R.proper) :
  R.vspan.lb < R.vspan.ub := by{
    apply Int.lt_of_sub_pos
    rw[← height_eq_sub_of_proper hR]
    simp[proper_iff_pos.mp hR]
  }
end GRectangle

def GPoint.touch : GPixel → GRectangle
| ⟨x, y⟩ => ⟨⟨x - 1, x + 2⟩, ⟨y - 1, y + 2⟩⟩
def GPoint.gtouch : GPixel → GRectangle
| ⟨x, y⟩ => ⟨⟨x - 1, x + 1⟩, ⟨y - 1, y + 1⟩⟩

theorem GPoint.mem_touch {p : GPixel} : p ∈ p.touch := by{
  match p with | ⟨x, y⟩ => simp[GRectangle.mem_iff, GInterval.mem_iff, touch]
}
theorem GPoint.mem_gtouch {p : GPixel} : p ∈ p.gtouch := by{
  match p with | ⟨x, y⟩ => simp[GRectangle.mem_iff, GInterval.mem_iff, gtouch]
}
theorem end0_mem_touch {d : GDart} : end0 d ∈ d.half.touch := by{
  simp only [end0, touch, GRectangle.mem_iff, GInterval.mem_iff]
  simp only [add_def, tsub_le_iff_right, add_lt_add_iff_left]
  rw[add_assoc, le_add_iff_nonneg_right, add_assoc, le_add_iff_nonneg_right]
  simp only [x_mod2, y_mod2]
  simp only [Int.emod_lt_of_pos _ (by{simp} : 0 < (2 : ℤ)), and_true]
  cases Int.emod_two_eq d.x with | inl hx | inr hx =>
  cases Int.emod_two_eq d.y with | inl hy | inr hy =>
    simp[hx, hy]
}
theorem half_mem_touch_of_end0_eq_end0 {p q : GDart} (hpq : end0 q = end0 p)
  : q.half ∈ p.half.touch := by{
    have hpq:=hpq.symm
    simp only [touch, GRectangle.mem_iff, GInterval.mem_iff, x_half, y_half]
    simp only [end0, GPoint.ext_iff, add_def, x_half, y_half, x_mod2, y_mod2] at hpq
    simp only [sub_le_iff_le_add]
    rw[←eq_sub_iff_add_eq, ←eq_sub_iff_add_eq] at hpq
    simp only [hpq, sub_le_iff_le_add]
    simp only [sub_add_eq_add_sub, lt_sub_iff_add_lt, add_assoc]
    simp only [add_le_add_iff_left, add_lt_add_iff_left]
    simp only [lt_of_lt_of_le
      (Int.emod_lt_of_pos _ (by{simp}):_ % 2 < (2 : ℤ))
      (le_add_of_nonneg_left (Int.emod_nonneg _ (by{simp})) : (2 : ℤ) ≤ _ % 2 + 2)
    ]
    simp only [and_true]
    simp only [le_trans
      (Int.le_sub_one_of_lt (Int.emod_lt _ (by{simp})) : _ % 2 ≤ (1 : ℤ))
      (le_add_of_nonneg_right (Int.emod_nonneg _ (by{simp})) : (1 : ℤ) ≤ 1 + _ % 2)
    ]
    trivial
  }
theorem half_mem_touch_of_end0_eq_end0_face {p q : GDart} (hpq : end0 q = end0 (face p))
  : q.half ∈ p.half.touch := by{
    have hpq:=hpq.symm
    simp only [touch, GRectangle.mem_iff, GInterval.mem_iff, x_half, y_half]
    simp only [end0, face_half, face_mod2,
    GPoint.ext_iff, add_def, x_half, y_half, x_mod2, y_mod2, x_ccw, y_ccw] at hpq
    simp only [sub_le_iff_le_add]
    rw[←eq_sub_iff_add_eq, ←eq_sub_iff_add_eq] at hpq
    simp only [hpq, sub_le_iff_le_add]
    simp only [sub_add_eq_add_sub, lt_sub_iff_add_lt, add_assoc]
    simp only [add_le_add_iff_left, add_lt_add_iff_left]
    simp only [lt_of_lt_of_le
      (Int.emod_lt_of_pos _ (by{simp}):_ % 2 < (2 : ℤ))
      (le_add_of_nonneg_left (Int.emod_nonneg _ (by{simp})) : (2 : ℤ) ≤ _ % 2 + 2)
    ]
    simp only [and_true]
    simp only [le_trans
      (Int.le_sub_one_of_lt (Int.emod_lt _ (by{simp})) : _ % 2 ≤ (1 : ℤ))
      (le_add_of_nonneg_right (Int.emod_nonneg _ (by{simp})) : (1 : ℤ) ≤ 1 + _ % 2)
    ]
    simp only [and_true]
    rw[←add_sub_assoc, le_sub_iff_add_le]
    constructor
    · {
      apply add_le_add
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
    }
    rw[sub_lt_iff_lt_add, add_right_comm]
    apply lt_add_of_nonneg_of_lt
    · {
      apply add_nonneg
      · apply Int.emod_nonneg _ (by{simp})
      · apply Int.emod_nonneg _ (by{simp})
    }
    simp
  }
theorem half_mem_touch_of_end0_eq_end0_face_face {p q : GDart} (hpq : end0 q = end0 (face (face p)))
  : q.half ∈ p.half.touch := by{
    have hpq:=hpq.symm
    simp only [touch, GRectangle.mem_iff, GInterval.mem_iff, x_half, y_half]
    simp only [end0, face_half, face_mod2,
    GPoint.ext_iff, add_def, x_half, y_half, x_mod2, y_mod2, x_ccw, y_ccw] at hpq
    simp only [sub_le_iff_le_add]
    rw[←eq_sub_iff_add_eq, ←eq_sub_iff_add_eq] at hpq
    simp only [hpq, sub_le_iff_le_add]
    simp only [sub_add_eq_add_sub, lt_sub_iff_add_lt, add_assoc]
    simp only [add_le_add_iff_left, add_lt_add_iff_left]
    simp only [sub_lt_iff_lt_add]
    rw[add_right_comm (b:=2), add_right_comm (b:=2)]
    simp only [←add_sub_assoc, le_sub_iff_add_le]
    have h:=(by{
      intro n m
      apply add_le_add
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
    } : ∀{n m:ℤ}, n % 2 + m % 2 ≤ 1 + 1)
    simp only [h, true_and]
    have h':=(by{
      intro n m
      apply lt_add_of_nonneg_of_lt
      · {
        apply add_nonneg
        · apply Int.emod_nonneg _ (by{simp})
        · apply Int.emod_nonneg _ (by{simp})
      }
      simp
    } : ∀{n m:ℤ}, 1 < n % 2 + m % 2 + 2)
    simp[h']
  }
theorem half_mem_touch_of_end0_eq_end0_face_3 {p q : GDart}
(hpq : end0 q = end0 (face (face (face p))))
  : q.half ∈ p.half.touch := by{
    have hpq:=hpq.symm
    simp only [touch, GRectangle.mem_iff, GInterval.mem_iff, x_half, y_half]
    simp only [end0, face_half, face_mod2,
    GPoint.ext_iff, add_def, x_half, y_half, x_mod2, y_mod2, x_ccw, y_ccw] at hpq
    simp only [sub_le_iff_le_add]
    rw[←eq_sub_iff_add_eq, ←eq_sub_iff_add_eq] at hpq
    simp only [hpq, sub_le_iff_le_add]
    simp only [sub_add_eq_add_sub, lt_sub_iff_add_lt, add_assoc]
    simp only [add_le_add_iff_left, add_lt_add_iff_left]
    simp only [sub_lt_iff_lt_add]
    rw[add_right_comm (b:=2), add_right_comm (b:=2)]
    simp only [←add_sub_assoc, le_sub_iff_add_le]
    have h:=(by{
      intro n m
      apply add_le_add
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
      · apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
    } : ∀{n m:ℤ}, n % 2 + m % 2 ≤ 1 + 1)
    simp only [h, true_and]
    have h':=(by{
      intro n m
      apply lt_add_of_nonneg_of_lt
      · {
        apply add_nonneg
        · apply Int.emod_nonneg _ (by{simp})
        · apply Int.emod_nonneg _ (by{simp})
      }
      simp
    } : ∀{n m:ℤ}, 1 < n % 2 + m % 2 + 2)
    simp only [Int.reduceAdd, tsub_le_iff_right, h', and_true]
    rw[add_sub_assoc]
    constructor
    · {
      rw[←Int.lt_iff_add_one_le]
      apply lt_add_of_lt_of_nonneg
      · apply Int.emod_lt _ (by{simp})
      apply Int.emod_nonneg _ (by{simp})
    }
    · {
      apply lt_add_of_nonneg_of_lt
      · {
        apply add_nonneg
        · apply Int.emod_nonneg _ (by{simp})
        · {
          rw[le_sub_iff_add_le, zero_add]
          apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
        }
      }
      simp
    }
  }

theorem node_half_mem_touch_half {d : GDart} : (node d).half ∈ touch d.half := by{
  apply half_mem_touch_of_end0_eq_end0
  rw[node_end0]
}
theorem face_half_mem_touch_half {d : GDart} : (face d).half ∈ touch d.half := by{
  apply half_mem_touch_of_end0_eq_end0_face
  rfl
}
theorem edge_half_mem_touch_half {d : GDart} : (edge d).half ∈ touch d.half := by{
  apply half_mem_touch_of_end0_eq_end0_face
  rw[edge_end0, face_end0]
}
theorem node_mem_touch {p : GPixel} : node p ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      omega
    }
  }
}
theorem nn_mem_touch {p : GPixel} : node (node p) ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      omega
    }
  }
}
theorem face_mem_touch {p : GPixel} : face p ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}
theorem ff_mem_touch {p : GPixel} : face (face p) ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}
theorem edge_mem_touch {p : GPixel} : edge p ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, edge, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}
theorem fe_mem_touch {p : GPixel} : face (edge p) ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, face, edge, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}
theorem en_mem_touch {p : GPixel} : edge (node p) ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, edge, node, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}
theorem nf_mem_touch {p : GPixel} : (node (face p)) ∈ touch p := by{
  match p with | ⟨px, py⟩ => {
    simp only [touch, node, face, arc, sub_def, x_ccw, y_mod2, x_mod2, y_ccw, GRectangle.mem_iff,
      GInterval.mem_iff, tsub_le_iff_right, add_def]
    cases Int.emod_two_eq px with | inl hdx | inr hdx =>
    cases Int.emod_two_eq py with | inl hdy | inr hdy => {
      simp[hdx, hdy]
      try omega
    }
  }
}

def chop (d : GDart) : GRegion :=
  {p |
    match d.toUnitSquareDart with
    | gp00 => d.half.y ≤ p.y
    | gp01 => d.half.x ≤ p.x
    | gp10 => d.half.x ≥ p.x
    | gp11 => d.half.y ≥ p.y }

theorem half_mem_chop {d : GDart} : d.half ∈ chop d := by{
  unfold chop
  rw[Set.mem_setOf]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp only [ge_iff_le, le_refl]
}

theorem mem_edge_chop_iff {d : GDart} {p : GPixel} : p ∈ chop (edge d) ↔ p ∉ chop d := by{
  unfold chop
  simp only [Set.mem_setOf, edge_toUnitSquareDart, edge_half']
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[opp, Int.add_one_le_iff, Int.le_sub_one_iff]
}

theorem fn_chop_eq_ff_chop {d : GDart} : chop (face (node d)) = chop (face (face d)) := by{
  ext p
  unfold chop
  simp only [face_toUnitSquareDart, node_toUnitSquareDart, face_half, node_half', ge_iff_le
  , Set.mem_setOf]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[UnitSquareDart.ccw]
}

theorem fef_chop_eq {d : GDart} : chop (face (edge (face d))) = chop d := by{
  ext p
  unfold chop
  simp only [face_toUnitSquareDart, edge_toUnitSquareDart, face_half, edge_half', ge_iff_le,
    Set.mem_setOf]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[UnitSquareDart.ccw, UnitSquareDart.opp]
}

theorem f3e_chop_eq {d : GDart} : chop (face (face (face (edge d)))) = chop (face d) := by{
  rw[←fn_chop_eq_ff_chop, nfe_cancel]
}

theorem end0_mem_chop_face {d : GDart} : end0 d ∈ chop (face d) := by{
  rw[end0, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, add_def, ge_iff_le,
      add_le_iff_nonpos_right, le_add_iff_nonneg_right]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      simp only [x_mod2, y_mod2]
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem node_half_mem_chop {d : GDart} : (node d).half ∈ chop d := by{
  rw[node_half_eq_end0_sub, chop, end0, Set.mem_setOf]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [add_def, sub_def, x_mod2, y_mod2, x_ccw, y_ccw]
    have h':=toUnitSquareDart_toGCorner (d:=d)
    rw[hd] at h'
    simp only [toGCorner, GPoint.ext_iff, x_mod2, y_mod2] at h'
    simp[←h'.left, ←h'.right]
  }
}
theorem end0_mem_chop_face_face {d : GDart} : end0 d ∈ chop (face (face d)) := by{
  rw[end0, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, add_def, ge_iff_le,
      add_le_iff_nonpos_right, le_add_iff_nonneg_right]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      simp only [x_mod2, y_mod2]
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem half_mem_chop_face {d : GDart} : d.half ∈ chop (face d) := by{
  rw[chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, ge_iff_le]
    apply le_refl
  }
}
theorem node_half_mem_chop_face {d : GDart} : (node d).half ∈ chop (face d) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem node_node_half_mem_chop_face {d : GDart} : (node (node d)).half ∈ chop (face d) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart, face_half, node_mod2, node_half]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem node_node_node_half_mem_chop_face {d : GDart}
  : (node (node (node d))).half ∈ chop (face d) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart, face_half, node_mod2, node_half]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem half_mem_chop_face_of_end0_eq {d a : GDart} (hda : end0 a = end0 d)
  : a.half ∈ chop (face d) := by{
    rw[end0_eq_cases_node] at hda
    rcases hda with hda | hda | hda | hda
    · rw[hda]; apply half_mem_chop_face
    · rw[hda]; apply node_half_mem_chop_face
    · rw[hda]; apply node_node_half_mem_chop_face
    · rw[hda]; apply node_node_node_half_mem_chop_face
  }

theorem half_mem_chop_face_face {d : GDart} : d.half ∈ chop (face (face d)) := by{
  rw[chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, ge_iff_le]
    apply le_refl
  }
}
theorem half_mem_chop_face_face_face {d : GDart} : d.half ∈ chop (face (face (face d))) := by{
  rw[chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, ge_iff_le]
    apply le_refl
  }
}
theorem half_mem_chop_of_half_eq {d a : GDart} (hda : a.half = d.half)
: a.half ∈ chop d := by{
  rw[Eq.comm, half_eq_cases_face] at hda
  rcases hda with hda | hda | hda | hda
  · rw[hda]; apply half_mem_chop
  · rw[hda]; apply half_mem_chop_face
  · rw[hda]; apply half_mem_chop_face_face
  · rw[hda]; apply half_mem_chop_face_face_face
}
theorem node_half_mem_chop_face_face {d : GDart} : (node d).half ∈ chop (face (face d)) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, face_half, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem node_node_half_mem_chop_face_face {d : GDart}
: (node (node d)).half ∈ chop (face (face d)) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart, face_half, node_mod2, node_half]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem node_node_node_half_mem_chop_face_face {d : GDart}
  : (node (node (node d))).half ∈ chop (face (face d)) := by{
  rw[node_half, chop, Set.mem_setOf]
  simp only [face_toUnitSquareDart, face_half, node_mod2, node_half]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [UnitSquareDart.ccw, add_def, ge_iff_le, sub_def]
    simp only [x_mod2, y_mod2, x_ccw, y_ccw]
    simp only [toUnitSquareDart, x_mod2, y_mod2] at hd
    match d with | ⟨dx, dy⟩ => {
      simp only at hd
      cases Int.emod_two_eq dx with | inl hx | inr hx =>
      cases Int.emod_two_eq dy with | inl hy | inr hy =>
        simp[hx, hy] at hd
        try simp[hx, hy]
    }
  }
}
theorem half_mem_chop_face_face_of_end0_eq {d a : GDart} (hda : end0 a = end0 d)
  : a.half ∈ chop (face (face d)) := by{
    rw[end0_eq_cases_node] at hda
    rcases hda with hda | hda | hda | hda
    · rw[hda]; apply half_mem_chop_face_face
    · rw[hda]; apply node_half_mem_chop_face_face
    · rw[hda]; apply node_node_half_mem_chop_face_face
    · rw[hda]; apply node_node_node_half_mem_chop_face_face
  }

theorem half_mem_chop_of_end0_eq_end0_face_face {d a : GDart}
(hda : end0 a = end0 (face (face d))) : a.half ∈ chop d := by{
  rw[chop, Set.mem_setOf]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    have hd':=toUnitSquareDart_toGCorner (d:=d)
    rw[hd] at hd'
    simp only [toGCorner] at hd'
    simp only [end0, face_half, face_mod2, ←hd', GPoint.ccw] at hda
    simp only [add_def, sub_self, sub_zero, add_zero, mk.injEq] at hda
    rw[←eq_sub_iff_add_eq (c:=a.mod2.x)] at hda
    rw[←eq_sub_iff_add_eq (c:=a.mod2.y)] at hda
    simp only [hda, x_mod2, y_mod2]
    try simp only [add_sub_assoc, le_add_iff_nonneg_right, Int.sub_nonneg,
      ge_iff_le, tsub_le_iff_right]
    try apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
    try apply Int.emod_nonneg _ (by{simp})
  }
}

theorem half_mem_chop_of_end0_eq_end0_face_3 {d a : GDart}
(hda : end0 a = end0 (face (face (face d)))) : a.half ∈ chop d := by{
  rw[chop, Set.mem_setOf]
  match hd : d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    have hd':=toUnitSquareDart_toGCorner (d:=d)
    rw[hd] at hd'
    simp only [toGCorner] at hd'
    simp only [end0, face_half, face_mod2, ←hd', GPoint.ccw] at hda
    simp only [add_def, sub_self, sub_zero, add_zero, mk.injEq] at hda
    rw[←eq_sub_iff_add_eq (c:=a.mod2.x)] at hda
    rw[←eq_sub_iff_add_eq (c:=a.mod2.y)] at hda
    simp only [hda, x_mod2, y_mod2]
    try simp only [add_sub_assoc, le_add_iff_nonneg_right, Int.sub_nonneg,
      ge_iff_le, tsub_le_iff_right]
    try apply Int.le_of_lt_add_one (Int.emod_lt _ (by{simp}))
    try apply Int.emod_nonneg _ (by{simp})
  }
}

theorem chop_disjoint_edge_chop {d : GDart} : Disjoint (chop d) (chop (edge d)) := by{
  rw[Set.disjoint_iff_forall_ne]
  simp only [mem_edge_chop_iff]
  intro a ha b hb hab
  exact hb (hab ▸ ha)
}

def chop1 (d : GDart) := chop (face (face (edge d)))
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
theorem f3e_chop1_eq {d : GDart} : chop1 (face (face (face (edge d)))) = chop1 (face d) := by{
  rw[chop1, chop1, face_3, edge_2, ←fn_chop_eq_ff_chop]
  congr
  apply node_injective
  rw[node_3, edge_2, nfe_cancel]
}

def chopRect (r : GRectangle) (d : GDart) : GRectangle :=
  match d.toUnitSquareDart with
  | gp00 => ⟨r.hspan, ⟨max r.vspan.lb d.half.y, r.vspan.ub⟩⟩
  | gp01 => ⟨⟨max r.hspan.lb d.half.x, r.hspan.ub⟩, r.vspan⟩
  | gp10 => ⟨⟨r.hspan.lb, min r.hspan.ub (d.half.x + 1)⟩, r.vspan⟩
  | gp11 => ⟨r.hspan, ⟨r.vspan.lb, min r.vspan.ub (d.half.y + 1)⟩⟩

theorem chopRect_toRegion {r : GRectangle} {d : GDart}
: (chopRect r d).toRegion = r.toRegion ∩ chop d := by{
  ext p
  simp only [Set.mem_inter_iff]
  simp only [chopRect, chop, GRectangle.toRegion, Set.mem_setOf]
  simp only [GInterval.mem_iff]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [max_le_iff, lt_min_iff, Int.lt_add_one_iff]
    tauto
  }
}

theorem chopRect_subset_chop {r : GRectangle} {d : GDart}
: (chopRect r d).toRegion ⊆ chop d := by{
  rw[chopRect_toRegion]
  apply Set.inter_subset_right
}
theorem chopRect_subset_rect {r : GRectangle} {d : GDart}
: chopRect r d ⊆ r := by{
  rw[GRectangle.subset_iff_region_subset, chopRect_toRegion]
  apply Set.inter_subset_left
}

def chop1Rect (r : GRectangle) (d : GDart) : GRectangle := chopRect r (face (face (edge d)))
theorem chop1Rect_toRegion {r : GRectangle} {d : GDart}
: (chop1Rect r d).toRegion = r.toRegion ∩ chop1 d := by{
  rw[chop1Rect, chopRect_toRegion, chop1]
}
theorem chop1Rect_subset_chop1 {r : GRectangle} {d : GDart}
: (chop1Rect r d).toRegion ⊆ chop1 d := by{
  rw[chop1Rect_toRegion]
  apply Set.inter_subset_right
}
theorem chop1Rect_subset_rect {r : GRectangle} {d : GDart}
: chop1Rect r d ⊆ r := by{
  rw[GRectangle.subset_iff_region_subset, chop1Rect_toRegion]
  apply Set.inter_subset_left
}
theorem chopRect_subset_chop1Rect {r : GRectangle} {d : GDart}
: chopRect r d ⊆ chop1Rect r d := by{
  rw[GRectangle.subset_iff_region_subset, chopRect_toRegion, chop1Rect_toRegion]
  apply Set.inter_subset_inter_right
  exact chop_subset_chop1
}

def GRegion.zoom (r : GRegion) : GRegion :=
  {p | p.half ∈ r}
def GRectangle.zoom : GRectangle → GRectangle
| ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ => ⟨⟨x0 * 2, x1 * 2⟩, ⟨y0 * 2, y1 * 2⟩⟩
theorem GRectangle.mem_zoom {r : GRectangle} {p : GPixel} : p ∈ r.zoom ↔ p.half ∈ r := by{
  simp only [zoom, mem_iff, GInterval.mem_iff, half]
  rw[Int.le_ediv_iff_mul_le (by{simp})]
  rw[Int.le_ediv_iff_mul_le (by{simp})]
  rw[Int.ediv_lt_iff_lt_mul (by{simp})]
  rw[Int.ediv_lt_iff_lt_mul (by{simp})]
}
theorem GRectangle.width_zoom {r : GRectangle} : r.zoom.width = r.width * 2 := by{
  simp only [width, GInterval.width, zoom]
  rw[←Int.sub_mul]
  rw[Int.toNat_mul_right_nonneg]
  · rfl
  · simp
}
theorem GRectangle.height_zoom {r : GRectangle} : r.zoom.height = r.height * 2 := by{
  simp only [height, GInterval.width, zoom]
  rw[←Int.sub_mul]
  rw[Int.toNat_mul_right_nonneg]
  · rfl
  · simp
}
theorem GRectangle.area_zoom {r : GRectangle} : r.zoom.area = r.area * 4 := by{
  simp[area, width_zoom, height_zoom]
  ring
}
theorem GRectangle.zoom_toRegion {r : GRectangle}
: r.zoom.toRegion = r.toRegion.zoom := by{
  ext x
  rw[←mem_iff_toRegion, GRegion.zoom, Set.mem_setOf, mem_zoom,
  ←mem_iff_toRegion]
}
theorem GRectangle.zoom_proper_iff {R : GRectangle} : R.zoom.proper ↔ R.proper := by{
  rw[proper, proper, area_zoom]
  simp
}

def GRectangle.inner : GRectangle → GRectangle
| ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ => ⟨⟨x0 + 1, x1 - 1⟩, ⟨y0 + 1, y1 - 1⟩⟩

theorem GRectangle.mem_inner_iff {r : GRectangle} {p : GPixel}
: p ∈ r.inner ↔ touch p ⊆ r := by{
  simp only [touch, subset_iff, mem_iff, GInterval.mem_iff, inner]
  simp only [tsub_le_iff_right, and_imp, lt_sub_iff_add_lt]
  simp only [Int.lt_iff_add_one_le (a:=p.x + 1), Int.lt_iff_add_one_le (a:=p.y + 1)]
  rw[add_assoc (b:=1) (c:=1)]
  rw[add_assoc (b:=1) (c:=1)]
  constructor
  · {
    intro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩ q h0' h1' h2' h3'
    constructor
    · {
      constructor
      · apply Int.le_of_add_le_add_right (b:=1); exact le_trans h0 h0'
      · apply lt_of_lt_of_le h1' h1
    }
    · {
      constructor
      · apply Int.le_of_add_le_add_right (b:=1); exact le_trans h2 h2'
      · apply lt_of_lt_of_le h3' h3
    }
  }
  · {
    intro h
    have h0:=@h (p + ⟨1, 1⟩)
    simp only [add_def, add_lt_add_iff_left, Nat.one_lt_ofNat, forall_const] at h0
    ring_nf at h0
    simp only [le_add_iff_nonneg_left, Nat.ofNat_nonneg, forall_const] at h0
    simp only [←add_assoc, ←Int.lt_iff_add_one_le]
    ring_nf
    simp only [h0, and_true]
    have h1:=@h (p - ⟨1, 1⟩)
    simp only [sub_def, sub_add_cancel, Std.le_refl, forall_const] at h1
    ring_nf at h1
    simp only [Int.reduceNeg, add_lt_add_iff_right, Int.reduceLT, le_neg_add_iff_add_le,
      neg_add_lt_iff_lt_add, forall_const] at h1
    repeat rw[add_comm 1] at h1
    simp only [←Int.lt_iff_add_one_le] at h1
    simp[h1]
  }
}

theorem GRectangle.inner_subset {r : GRectangle}
  : r.inner ⊆ r := by{
    intro p
    rw[mem_inner_iff]
    intro h
    apply h
    apply mem_touch
  }

theorem GRectangle.inner_zoom_subset_zoom_inner {r : GRectangle}
  : r.inner.zoom ⊆ r.zoom.inner := by{
    intro ⟨dx, dy⟩ hx
    match r with
    | ⟨⟨rx0, rx1⟩, ⟨ry0, ry1⟩⟩ => {
      simp[inner, zoom, mem_iff, GInterval.mem_iff] at hx
      simp[inner, zoom, mem_iff, GInterval.mem_iff]
      omega
    }
  }

theorem touch_subset_chop1_iff_mem_chop {p : GPixel} {d : GDart} :
  (touch p).toRegion ⊆ chop1 d ↔ p ∈ chop d:=by{
    rw[chop1]
    simp only [chop, face_toUnitSquareDart, edge_toUnitSquareDart]
    simp only [face_half, edge_half]
    simp only [add_def, sub_def, x_half, y_half, touch, GRectangle.toRegion]
    simp only [x_ccw, y_ccw, x_mod2, y_mod2, Set.mem_setOf, Set.subset_def]
    simp only [GInterval.mem_iff, UnitSquareDart.ccw, opp]
    have hd:=toUnitSquareDart_toGCorner (d:=d)
    simp only [toGCorner, GPoint.ext_iff, x_mod2, y_mod2] at hd
    match hdu : d.toUnitSquareDart with
    | gp00 | gp01 | gp10 | gp11 => {
      simp only [ge_iff_le]
      simp only [hdu] at hd
      simp only [← hd, sub_zero, add_sub_cancel_right, add_zero, sub_self]
      constructor
      · {
        intro h
        have h0:=h ⟨p.x, p.y-1⟩
        have h1:=h ⟨p.x-1, p.y⟩
        have h2:=h ⟨p.x+1, p.y⟩
        have h3:=h ⟨p.x, p.y+1⟩
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one, lt_add_iff_pos_right,
          Nat.ofNat_pos, and_self, Std.le_refl, true_and, sub_add_cancel, and_true,
          add_lt_add_iff_left, Nat.one_lt_ofNat, sub_lt_iff_lt_add] at h0 h1 h2 h3
        simp only [add_assoc, Int.reduceAdd, lt_add_iff_pos_right, Nat.ofNat_pos, forall_const,
          le_add_iff_nonneg_right, Nat.ofNat_nonneg, add_le_add_iff_right] at h0 h1 h2 h3
        assumption
      }
      · {
        omega
      }
    }
  }

theorem mem_chop1Rect_inner_iff_mem_inner_chopRect {r : GRectangle} {p : GPixel}
  {d : GDart} : p ∈ (chop1Rect r d).inner ↔ p ∈ chopRect r.inner d :=by{
    rw[GRectangle.mem_inner_iff]
    rw[GRectangle.mem_iff_toRegion, chopRect_toRegion]
    rw[Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion, GRectangle.mem_inner_iff]
    rw[GRectangle.subset_iff_region_subset, chop1Rect_toRegion]
    rw[Set.subset_inter_iff, ←GRectangle.subset_iff_region_subset]
    apply and_congr
    · rfl
    · apply touch_subset_chop1_iff_mem_chop
  }

theorem GRectangle.area_le_area_of_subset {r1 r2 : GRectangle}
  (h : r1 ⊆ r2) : r1.area ≤ r2.area := by{
    rw[←enum_length, ←enum_length]
    apply List.length_le_length_of_nodup_of_subset
    · apply r1.enum_nodup
    · apply r2.enum_nodup
    rw[←subset_iff_enum]
    exact h
  }

theorem GRectangle.proper_of_subset {R1 R2 : GRectangle} (hR12 : R1 ⊆ R2) (hR1 : R1.proper) :
  R2.proper := by{
    apply lt_of_lt_of_le hR1
    exact area_le_area_of_subset hR12
  }

theorem GRectangle.subset.is_trans : IsTrans GRectangle (· ⊆ ·) where
  trans:=by{simp only [subset_iff_region_subset]; intro _ _ _ h1 h2; apply Set.Subset.trans h1 h2}
@[implicit_reducible] instance GRectangle.subset.instTrans
: Trans (α:=GRectangle) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans:=by{apply is_trans.trans}
theorem GRectangle.subset.trans {a b c : GRectangle} : a ⊆ b → b ⊆ c → a ⊆ c := instTrans.trans

theorem GRectangle.toRegion_eq_of_subset_of_area_eq {r1 r2 : GRectangle}
  (h : r1 ⊆ r2) (h' : r1.area = r2.area) : r1.toRegion = r2.toRegion := by{
    rw[←enum_length, ←enum_length] at h'
    have ih:=List.perm_of_nodup_subset_length_eq r1.enum_nodup r2.enum_nodup
      (by{rw[←subset_iff_enum]; exact h}) h'
    ext x
    rw[←mem_iff_toRegion, ←mem_iff_toRegion]
    rw[←mem_enum_iff, ←mem_enum_iff]
    rw[List.perm_ext_iff_of_nodup r1.enum_nodup r2.enum_nodup] at ih
    apply ih
  }

theorem chopRect_area_le_area {r : GRectangle} {d : GDart}
  : (chopRect r d).area ≤ r.area := by{
    apply GRectangle.area_le_area_of_subset
    apply chopRect_subset_rect
  }

theorem chopRect_area_lt_of_mem_inner {r : GRectangle} {d : GDart}
  (hrd : d.half ∈ r.inner) : (chopRect r d).area < r.area := by{
    have ih1:=chopRect_area_le_area (r:=r) (d:=d)
    apply lt_or_eq_of_le at ih1
    apply ih1.resolve_right
    intro h
    have ih2:=GRectangle.toRegion_eq_of_subset_of_area_eq chopRect_subset_rect h
    have ih3:(edge d).half ∈ r:=by{
      rw[GRectangle.mem_inner_iff] at hrd
      apply hrd
      apply edge_half_mem_touch_half
    }
    have ih4:(edge d).half ∉ chopRect r d:=by{
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff, not_and]
      intro _
      nth_rw 1 [←edge_2 (d:=d)]
      rw[mem_edge_chop_iff, not_not]
      apply half_mem_chop
    }
    rw[GRectangle.mem_iff_toRegion] at ih3 ih4
    rw[ih2] at ih4
    exact ih4 ih3
  }

theorem chopRect_edge_area_lt_of_mem_inner {r : GRectangle} {d : GDart}
  (hrd : d.half ∈ r.inner) : (chopRect r (edge d)).area < r.area := by{
    have ih1:=chopRect_area_le_area (r:=r) (d:=edge d)
    apply lt_or_eq_of_le at ih1
    apply ih1.resolve_right
    intro h
    have ih2:=GRectangle.toRegion_eq_of_subset_of_area_eq chopRect_subset_rect h
    have ih3:d.half ∈ r:=by{
      apply GRectangle.inner_subset
      exact hrd
    }
    have ih4:d.half ∉ chopRect r (edge d):=by{
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff, not_and]
      intro _
      rw[mem_edge_chop_iff, not_not]
      apply half_mem_chop
    }
    rw[GRectangle.mem_iff_toRegion] at ih3 ih4
    rw[ih2] at ih4
    exact ih4 ih3
  }

theorem half_not_mem_chopRect_inner {r : GRectangle} {d : GDart}
  : d.half ∉ (chopRect r d).inner := by{
    rw[GRectangle.mem_inner_iff]
    intro h
    have h0:(edge d).half ∈ touch (d.half) := by{
      apply edge_half_mem_touch_half
    }
    have h1:(edge d).half ∉ chopRect r d := by{
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
      rw[not_and]
      intro h
      nth_rw 1 [←edge_2 (d:=d)]
      rw[mem_edge_chop_iff, not_not]
      apply half_mem_chop
    }
    exact h1 (h h0)
  }

theorem rectangle_subset_chop_of_mem_of_edge_not_mem {r : GRectangle} {d : GDart}
  (hd : d.half ∈ r) (hed : (edge d).half ∉ r) : r.toRegion ⊆ chop d := by{
    match d, r with
    | ⟨dx, dy⟩, ⟨⟨rx0, rx1⟩, ⟨ry0, ry1⟩⟩ => {
      simp only [edge_half, add_def, x_half, x_ccw, y_mod2, y_half, y_ccw, x_mod2,
        sub_def, GRectangle.mem_iff, not_and, GInterval.mem_iff] at hd hed
      intro x
      simp only [GRectangle.toRegion, Set.mem_setOf, GInterval.mem_iff, chop, toUnitSquareDart]
      simp only [x_mod2, y_mod2, x_half, y_half]
      cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
      cases Int.emod_two_eq dy with | inl hdy | inr hdy => {
        simp[hdx, ↓reduceIte, hdy, one_ne_zero, and_imp]
        omega
      }
    }
  }
theorem rectangle_subset_chop1_of_mem_inner_of_edge_not_mem_inner {r : GRectangle} {d : GDart}
  (hd : d.half ∈ r.inner) (hed : (edge d).half ∉ r.inner) : r.toRegion ⊆ chop1 d := by{
    apply rectangle_subset_chop_of_mem_of_edge_not_mem
    · {
      rw[face_half, face_half]
      rw[GRectangle.mem_inner_iff] at hd
      apply hd
      apply edge_half_mem_touch_half
    }
    · {
      match d, r with
      | ⟨dx, dy⟩, ⟨⟨rx0, rx1⟩, ⟨ry0, ry1⟩⟩ => {
        simp only [edge_half, add_def, x_half, x_ccw, y_mod2, y_half, y_ccw, x_mod2,
          sub_def, GRectangle.mem_iff, not_and, GInterval.mem_iff, GRectangle.inner] at hd hed
        simp only [edge_half, face_half, add_def, x_half, x_ccw, y_mod2, y_half, y_ccw, x_mod2,
          sub_def, sub_add_sub_cancel, GRectangle.mem_iff, not_and]
        simp only [face ,edge, arc, mod2, add_def, sub_def, x_ccw, y_ccw, GInterval.mem_iff]
        cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
        cases Int.emod_two_eq dy with | inl hdy | inr hdy => {
          simp[hdx, hdy, and_imp]
          omega
        }
      }
    }
  }

theorem GRectangle.inner_subset_inner_of_subset {r1 r2 : GRectangle} (hr12 : r1 ⊆ r2)
  : r1.inner ⊆ r2.inner := by{
    intro d hd
    rw[mem_inner_iff] at *
    match d, r1, r2 with
    | ⟨dx, dy⟩, ⟨⟨r0x0, r0x1⟩, ⟨r0y0, r0y1⟩⟩, ⟨⟨r1x0, r1x1⟩, ⟨r1y0, r1y1⟩⟩ => {
        simp only [subset_iff, mem_iff, GInterval.mem_iff, and_imp, touch] at *
        intro x h0 h1 h2 h3
        have hd':=hd h0 h1 h2 h3
        have hr12':=hr12 hd'.left.left hd'.left.right hd'.right.left hd'.right.right
        exact hr12'
      }
  }

theorem half_mem_chopRect_of_edge_mem_of_mem_chopRect {r : GRectangle} {d : GDart}
  (hem : (edge d).half ∈ r) {p : GPixel} (hpm : p ∈ chopRect r d)
  : d.half ∈ chopRect r d := by{
    match d, p, r with
    | ⟨dx, dy⟩, ⟨px, py⟩, ⟨⟨rx0, rx1⟩, ⟨ry0, ry1⟩⟩ => {
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion]
      rw[GRectangle.mem_iff_toRegion, chopRect_toRegion] at hpm
      rw[GRectangle.mem_iff_toRegion] at hem
      simp only [GRectangle.toRegion, GInterval.mem_iff, edge_half, add_def, x_half, x_ccw, y_mod2,
        y_half, y_ccw, x_mod2, sub_def, Set.mem_setOf_eq, chop, toUnitSquareDart, ge_iff_le,
        Set.mem_inter_iff, Std.le_refl] at *
      cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
      cases Int.emod_two_eq dy with | inl hdy | inr hdy => {
        simp[hdx, hdy] at hem hpm
        simp[hdx, hdy]
        omega
      }
    }
  }

theorem mem_touch_iff_mem_all_chop1_face {d : GDart} {p : GPixel}
  : p ∈ d.half.touch ↔
  ∀d' ∈ [d, face d, face (face d), face (face (face d))], p ∈ chop1 d' := by{
    constructor
    · {
      intro h d' hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
      refine (touch_subset_chop1_iff_mem_chop.mpr ?_) h
      rcases hd' with hd' | hd' | hd' | hd'
      all_goals
      rw[hd']
      apply half_mem_chop_of_half_eq
      simp[face_half]
    }
    · {
      intro h
      have h0:=h d
      have h1:=h (face d)
      have h2:=h (face (face d))
      have h3:=h (face (face (face d)))
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, forall_const,
        or_true, chop1, chop, toUnitSquareDart, face_mod2, edge_mod2, GPoint.ccw_4,
        face_half, edge_half, add_def, sub_def, x_ccw, y_ccw, x_mod2, y_mod2] at h0 h1 h2 h3
      simp only [touch, GRectangle.mem_iff, GInterval.mem_iff, tsub_le_iff_right]
      cases Int.emod_two_eq d.x with | inl hx | inr hx =>
      cases Int.emod_two_eq d.y with | inl hy | inr hy =>
        simp[hx, hy] at h0 h1 h2 h3
        omega
    }
  }

theorem mem_touch_iff_mem_all_chop1_half_eq {d : GDart} {p : GPixel}
  : p ∈ d.half.touch ↔
  ∀d', d'.half = d.half → p ∈ chop1 d' := by{
    rw[mem_touch_iff_mem_all_chop1_face]
    simp[half_eq_cases_face]
  }

def GRectangle.extend : GRectangle → GPoint → GRectangle
| ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩, ⟨x, y⟩ => ⟨⟨min x0 x, max x1 (x + 1)⟩, ⟨min y0 y, max y1 (y + 1)⟩⟩
theorem GRectangle.mem_extend {R : GRectangle} {p : GPoint} : p ∈ R.extend p := by{
  match R, p with | ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩, ⟨x, y⟩ => {
    simp[GRectangle.mem_iff, GInterval.mem_iff, extend]
  }
}
theorem GRectangle.subset_extend {R : GRectangle} {p : GPoint} : R ⊆ R.extend p := by{
  match R, p with | ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩, ⟨x, y⟩ => {
    simp[GRectangle.subset_iff_region_subset, GRectangle.toRegion, extend,
    GInterval.mem_iff]
    omega
  }
}

theorem x_succ_end0_eq_or_half_eq {dx dy} : end0 ⟨dx, dy⟩ = end0 ⟨dx + 1, dy⟩
  ∨ GPoint.half ⟨dx, dy⟩ = GPoint.half ⟨dx + 1, dy⟩ := by{
    simp only [end0, half, add_def, x_mod2, y_mod2, mk.injEq, and_true,
    Int.add_one_emod_two]
    rcases Int.emod_two_eq dx with hdx | hdx
    · simp[hdx, Int.add_one_ediv_two_of_mod_zero hdx]
    · simp[hdx, Int.add_one_ediv_two_of_mod_one hdx]
  }
theorem y_succ_end0_eq_or_half_eq {dx dy} : end0 ⟨dx, dy⟩ = end0 ⟨dx, dy + 1⟩
  ∨ GPoint.half ⟨dx, dy⟩ = GPoint.half ⟨dx, dy + 1⟩ := by{
    simp only [end0, half, add_def, x_mod2, y_mod2, mk.injEq, true_and,
    Int.add_one_emod_two]
    rcases Int.emod_two_eq dy with hdy | hdy
    · simp[hdy, Int.add_one_ediv_two_of_mod_zero hdy]
    · simp[hdy, Int.add_one_ediv_two_of_mod_one hdy]
  }

end GridPlane
