import FourColorTheorem.GridPlane.Defs.Darts

/-! 标记每个像素四个角点 -/

open Function
open Relation

namespace GridPlane

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

namespace GPoint
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

theorem neg_toUnitSquareDart {p : GPoint} : (-p).toUnitSquareDart = p.toUnitSquareDart := by{
  match p with
  | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
    simp[toUnitSquareDart, mod2, hx, hy]
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

theorem toUnitSquareDart_eq_iff_mod2_eq {d1 d2 : GDart}
: d1.toUnitSquareDart = d2.toUnitSquareDart ↔ d1.mod2 = d2.mod2 := by{
  match d1, d2 with | ⟨d1x, d1y⟩, ⟨d2x, d2y⟩ => {
    simp only [toUnitSquareDart, mod2]
    cases Int.emod_two_eq_zero_or_one d1x with | inl h1x | inr h1x =>
    cases Int.emod_two_eq_zero_or_one d1y with | inl h1y | inr h1y =>
    cases Int.emod_two_eq_zero_or_one d2x with | inl h2x | inr h2x =>
    cases Int.emod_two_eq_zero_or_one d2y with | inl h2y | inr h2y =>
      simp[h1x, h1y, h2x, h2y]
  }
}

theorem toUnitSquare_eq_gp00 {d : GDart} : d.toUnitSquareDart = gp00 ↔ d.mod2 = (0, 0) := by{
  match d with | ⟨dx, dy⟩ => {
    simp only [toUnitSquareDart, mod2, Prod.mk.injEq]
    split_ifs with h <;> simp[h] <;> split_ifs with h <;> simp[h]
  }
}
theorem toUnitSquare_eq_gp10 {d : GDart} : d.toUnitSquareDart = gp10 ↔ d.mod2 = (1, 0) := by{
  match d with | ⟨dx, dy⟩ => {
    simp only [toUnitSquareDart, mod2, Prod.mk.injEq]
    split_ifs with h <;> simp[h] <;> split_ifs with h <;> simp[h]
    omega
  }
}
theorem toUnitSquare_eq_gp11 {d : GDart} : d.toUnitSquareDart = gp11 ↔ d.mod2 = (1, 1) := by{
  match d with | ⟨dx, dy⟩ => {
    simp only [toUnitSquareDart, mod2, Prod.mk.injEq]
    split_ifs with h <;> simp[h] <;> split_ifs with h <;> simp[h]
    omega
  }
}
theorem toUnitSquare_eq_gp01 {d : GDart} : d.toUnitSquareDart = gp01 ↔ d.mod2 = (0, 1) := by{
  match d with | ⟨dx, dy⟩ => {
    simp only [toUnitSquareDart, mod2, Prod.mk.injEq]
    split_ifs with h <;> simp[h] <;> split_ifs with h <;> simp[h]
    omega
  }
}

end GPoint
open GPoint

theorem face_toUnitSquareDart {d : GDart} : (face d).toUnitSquareDart = d.toUnitSquareDart.ccw
:= by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
    simp[face, arc, GPoint.ccw, mod2, toUnitSquareDart, hx, hy, Int.add_neg_eq_sub]
    simp[Int.add_one_emod_two, Int.sub_one_emod_two, hx, hy]
    rfl
  }
}
theorem node_toUnitSquareDart {d : GDart} : (node d).toUnitSquareDart = d.toUnitSquareDart.ccw
:= by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
    simp[node, arc, GPoint.ccw, mod2, toUnitSquareDart, hx, hy]
    simp[Int.add_one_emod_two, Int.sub_one_emod_two, hx, hy]
    rfl
  }
}
theorem edge_toUnitSquareDart {d : GDart} : (edge d).toUnitSquareDart = d.toUnitSquareDart.opp
:= by{
  nth_rw 2 [←nfe_cancel d]
  rw[node_toUnitSquareDart, face_toUnitSquareDart]
  rw[UnitSquareDart.opp_eq_ccw_2]
  simp[UnitSquareDart.ccw_4]
}

theorem node_half' {d : GDart} : (node d).half = match d.toUnitSquareDart with
  | gp00 => (d.half.1 - 1, d.half.2)
  | gp01 => (d.half.1, d.half.2 + 1)
  | gp10 => (d.half.1, d.half.2 - 1)
  | gp11 => (d.half.1 + 1, d.half.2)
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
    simp only [half, node, arc, GPoint.ccw, mod2, toUnitSquareDart]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign, h]
  }
}

theorem edge_half' {d : GDart} : (edge d).half = match d.toUnitSquareDart with
  | gp00 => (d.half.1, d.half.2 - 1)
  | gp01 => (d.half.1 - 1, d.half.2)
  | gp10 => (d.half.1 + 1, d.half.2)
  | gp11 => (d.half.1, d.half.2 + 1)
:= by{
  match d with | ⟨x, y⟩ => {
    simp only [half, edge, arc, GPoint.ccw, mod2, toUnitSquareDart]
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, Int.add_ediv, Int.sign]
      try simp[Int.add_neg_eq_sub]
  }
}

end GridPlane
