import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Dynamics.PeriodicPts.Defs
import FourColorTheorem.Utils.Int

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

theorem end0_edge {d : GDart} : end0 (edge d) = end1 d := by{
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

theorem end1_edge {d : GDart} : end1 (edge d) = end0 d := by{
  nth_rw 2 [←edge_2 (d:=d)]
  rw[end0_edge]
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

theorem face_end0 {d : GDart} : end0 (face d) = end1 d := by{
  match d with | ⟨x, y⟩ => {
    simp only [end0, end1, half, face, arc, GPoint.ccw, mod2, sub_def]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign, Int.add_emod]
  }
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
      · simp[h, end0_edge, end1_edge, add_comm]
    }
  }

def GRegion := Set GPixel
abbrev GDartRegion:=GRegion
structure GInterval where
  min : ℤ
  max : ℤ
structure GRectangle where
  hspan : GInterval
  vspan : GInterval
@[inline] instance GRegion.instMembership : Membership GPixel GRegion := Set.instMembership
theorem GRegion.mem_iff {R : GRegion} {p : GPixel} : p ∈ R ↔ R p := by rfl
@[ext] theorem GRegion.ext {R1 R2 : GRegion} (h : ∀ p, p ∈ R1 ↔ p ∈ R2) : R1 = R2 :=
  Set.ext h
@[inline] instance GRegion.instEmptyCollection
  : EmptyCollection (GRegion) := Set.instEmptyCollection
theorem GRegion.empty_def_iff : (∅ : GRegion) = {_p : GPoint | False} := by rfl
theorem GRegion.mem_empty_iff {p : GPixel} : p ∈ (∅ : GRegion) ↔ False := by rfl
@[inline] instance GRegion.instHasSubset : HasSubset (GRegion) := Set.instHasSubset
theorem GRegion.subset_iff {R1 R2 : GRegion} : R1 ⊆ R2 ↔ ∀ p, p ∈ R1 → p ∈ R2 := by rfl
@[inline] instance GRegion.instHasUnion : Union GRegion := Set.instUnion
theorem GRegion.mem_union_iff {R1 R2 : GRegion} {p : GPixel} :
  p ∈ R1 ∪ R2 ↔ p ∈ R1 ∨ p ∈ R2 := by rfl
theorem GRegion.union_def_iff {R1 R2 : GRegion} : R1 ∪ R2 = {p | p ∈ R1 ∨ p ∈ R2} := by rfl
@[inline] instance GRegion.instHasInter : Inter GRegion := Set.instInter
theorem GRegion.mem_inter_iff {R1 R2 : GRegion} {p : GPixel} :
  p ∈ R1 ∩ R2 ↔ p ∈ R1 ∧ p ∈ R2 := by rfl
theorem GRegion.inter_def_iff {R1 R2 : GRegion} : R1 ∩ R2 = {p | p ∈ R1 ∧ p ∈ R2} := by rfl
def GInterval.toSet (I : GInterval) : Set ℤ := {x | I.min ≤ x ∧ x < I.max}
def GInterval.Mem (I : GInterval) (x : ℤ) : Prop := x ∈ I.toSet
@[inline] instance GInterval.instMembership : Membership ℤ GInterval where mem := GInterval.Mem
theorem GInterval.mem_iff (I : GInterval) (x : ℤ) : x ∈ I ↔ I.min ≤ x ∧ x < I.max := by rfl
def GRectangle.toRegion (R : GRectangle) : GRegion := {p | p.x ∈ R.hspan ∧ p.y ∈ R.vspan}
def GRectangle.Mem (R : GRectangle) (p : GPixel) : Prop := p ∈ R.toRegion
@[inline] instance GRectangle.instMembership :
  Membership GPoint GRectangle where mem := GRectangle.Mem
theorem GRectangle.mem_iff (R : GRectangle) (p : GPixel) :
  p ∈ R ↔ p.x ∈ R.hspan ∧ p.y ∈ R.vspan := by rfl

namespace GInterval
def width (I : GInterval) : ℕ := (I.max - I.min).toNat
def enum (I : GInterval) : List ℤ := (List.range I.width).map (Int.ofNat · + I.min)
theorem enum_length {I : GInterval} : I.enum.length = I.width := by{simp[enum]}
theorem enum_nodup {I : GInterval} : I.enum.Nodup := by{
  rw[enum]
  rw[List.nodup_map_iff]
  · exact List.nodup_range
  apply Injective.comp (g:=(· + I.min)) ?_ Int.ofNat_injective
  exact fun _ _ => (Int.add_left_inj I.min).mp
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
      apply lt_of_lt_of_le (add_lt_add_left ha0 I.min)
      rw[sub_add_cancel]
    }
  }
  · {
    intro ⟨h0, h1⟩
    simp only [←eq_sub_iff_add_eq]
    use (x - I.min).toNat
    simp[h0, h1]
  }
}
end GInterval

namespace GRectangle
def width (R : GRectangle) : ℕ := R.hspan.width
def height (R : GRectangle) : ℕ := R.vspan.width
def area (R : GRectangle) : ℕ := R.width * R.height
def proper (R : GRectangle) : Prop := R.area > 0
def enum (R : GRectangle) : List GPixel := (R.hspan.enum ×ˢ R.vspan.enum).map ofProd
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

def chop (d : GDart) : GRegion :=
  {p |
    match d.toUnitSquareDart with
    | gp00 => d.half.y ≤ p.y
    | gp01 => d.half.x ≤ p.x
    | gp10 => d.half.x ≥ p.x
    | gp11 => d.half.y ≥ p.y }

theorem GPoint.half_mem_chop {d : GDart} : d.half ∈ chop d := by{
  unfold chop
  rw[GRegion.mem_iff]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp only [ge_iff_le, setOf, le_refl]
}

theorem mem_edge_chop_iff {d : GDart} {p : GPixel} : p ∈ chop (edge d) ↔ p ∉ chop d := by{
  unfold chop
  simp only [GRegion.mem_iff, edge_toUnitSquareDart, edge_half']
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[opp, setOf, Int.add_one_le_iff, Int.le_sub_one_iff]
}

theorem fn_chop_eq_ff_chop {d : GDart} : chop (face (node d)) = chop (face (face d)) := by{
  ext p
  unfold chop
  simp only [face_toUnitSquareDart, node_toUnitSquareDart, face_half, node_half', ge_iff_le,
    GRegion.mem_iff]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[UnitSquareDart.ccw]
}

theorem fef_chop_eq {d : GDart} : chop (face (edge (face d))) = chop d := by{
  ext p
  unfold chop
  simp only [face_toUnitSquareDart, edge_toUnitSquareDart, face_half, edge_half', ge_iff_le,
    GRegion.mem_iff]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => simp[UnitSquareDart.ccw, UnitSquareDart.opp]
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

def chopRect (r : GRectangle) (d : GDart) : GRectangle :=
  match d.toUnitSquareDart with
  | gp00 => ⟨r.hspan, ⟨max r.vspan.min d.half.y, r.vspan.max⟩⟩
  | gp01 => ⟨⟨max r.hspan.min d.half.x, r.hspan.max⟩, r.vspan⟩
  | gp10 => ⟨⟨r.hspan.min, min r.hspan.max (d.half.x + 1)⟩, r.vspan⟩
  | gp11 => ⟨r.hspan, ⟨r.vspan.min, min r.vspan.max (d.half.y + 1)⟩⟩

theorem chopRect_toRegion {r : GRectangle} {d : GDart}
: (chopRect r d).toRegion = r.toRegion ∩ chop d := by{
  ext p
  simp only [GRegion.mem_iff, GRegion.inter_def_iff, setOf]
  simp only [chopRect, chop, GRectangle.toRegion, setOf]
  match d.toUnitSquareDart with
  | gp00 | gp01 | gp10 | gp11 => {
    simp only [GInterval.mem_iff, max_le_iff, lt_min_iff, Int.lt_add_one_iff]
    tauto
  }
}

def chop1Rect (r : GRectangle) (d : GDart) : GRectangle := chopRect r (face (face (edge d)))

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

end GridPlane
