import FourColorTheorem.GridPlane.Defs.Point
import FourColorTheorem.Utils.Relations

/-! 像素的四个镖点对应的函数。end0 end1对应起终点，enf对应像素里的置换 -/

open Function
open Relation

namespace GridPlane

open GPoint

def end0 (d : GDart) : GPixel := d.half + d.mod2
def end1 (d : GDart) : GPixel := d.half + d.mod2.ccw

theorem end0_ne_end1 {d : GDart} : end0 d ≠ end1 d := by{
  rw[end0, end1, ne_eq, add_left_cancel_iff]
  exact Ne.symm ccw_ne
}

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

theorem end0_double {p : GPixel} : end0 (2 • p) = p := by{
  rw[end0, half_double, mod2_double, add_zero]
}
theorem end0_add_end1_mod2_ne_zero {d : GDart} : (end0 d + end1 d).mod2 ≠ 0 := by{
  rw[end0, end1, add_assoc, add_left_comm _ d.half, ←add_assoc, ←two_nsmul]
  rw[mod2_add_double]
  apply GPoint.add_ccw_mod2_ne_zero
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
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, edge, node, face, arc, mod2, ccw]; omega
  }
}
theorem nfe_cancel : ∀d, node (face (edge d)) = d:=by{
  intro d
  match d with
  | ⟨x, y⟩ => {
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, edge, node, face, arc, mod2, ccw]; omega
  }
}
theorem fen_cancel : ∀d, face (edge (node d)) = d:=by{
  intro d
  match d with
  | ⟨x, y⟩ => {
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, edge, node, face, arc, mod2, ccw]; omega
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
    change _ = _
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, face, arc, mod2, ccw]; omega
  }
}
theorem node_4_periodic {d : GDart} : IsPeriodicPt node 4 d := by{
  match d with | ⟨x, y⟩ => {
    change _ = _
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, node, arc, mod2, ccw]; omega
  }
}
theorem edge_2_periodic {d : GDart} : IsPeriodicPt edge 2 d := by{
  match d with | ⟨x, y⟩ => {
    change _ = _
    cases Int.emod_two_eq x with
    | inl hx | inr hx => cases Int.emod_two_eq y with
      | inl hy | inr hy => simp[hx, hy, edge, arc, mod2, ccw]; omega
  }
}

theorem face_4 {d : GDart} : face (face (face (face d))) = d := face_4_periodic
theorem node_4 {d : GDart} : node (node (node (node d))) = d := node_4_periodic
theorem edge_2 {d : GDart} : edge (edge d) = d := edge_2_periodic
theorem face_3 {d : GDart} : face (face (face d)) = edge (node d) := by{
  apply face_injective
  rw[face_4, fen_cancel]
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
  match d with | ⟨dx, dy⟩ => {
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy, face, node, arc, ccw, mod2]; try omega
  }
}
theorem face_ne_edge {d : GDart} : face d ≠ edge d :=by{
  match d with | ⟨dx, dy⟩ => {
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy, face, edge, arc, ccw, mod2]; try omega
  }
}
theorem node_ne_edge {d : GDart} : node d ≠ edge d :=by{
  match d with | ⟨dx, dy⟩ => {
    cases Int.emod_two_eq_zero_or_one dx with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one dy with | inl hy | inr hy =>
      simp[hx, hy, node, edge, arc, ccw, mod2]; try omega
  }
}
theorem node_ne_face {d : GDart} : node d ≠ face d := face_ne_node.symm
theorem edge_ne_face {d : GDart} : edge d ≠ face d := face_ne_edge.symm
theorem edge_ne_node {d : GDart} : edge d ≠ node d := node_ne_edge.symm
theorem face_ne {d : GDart} : face d ≠ d := by{
  simp only [face, ne_eq, add_eq_left]
  exact arc_ne_zero
}
theorem node_ne {d : GDart} : node d ≠ d := by{
  simp only [node, ne_eq, sub_eq_self]
  exact arc_ne_zero
}
theorem edge_ne {d : GDart} : edge d ≠ d := by{
  match d with | ⟨dx, dy⟩ => {
    simp[edge, mod2, arc, ccw]; omega
  }
}
theorem face_2_ne {d : GDart} : face (face d) ≠ d := by{
  rcases d with ⟨dx, dy⟩
  simp[face, arc, mod2, ccw]
  omega
}
theorem face_3_ne {d : GDart} : face (face (face d)) ≠ d := by{
  rcases d with ⟨dx, dy⟩
  simp[face, arc, mod2, ccw]
  omega
}
theorem node_2_ne {d : GDart} : node (node d) ≠ d := by{
  rcases d with ⟨dx, dy⟩
  simp[node, arc, mod2, ccw]
  omega
}
theorem node_3_ne {d : GDart} : node (node (node d)) ≠ d := by{
  rcases d with ⟨dx, dy⟩
  simp[node, arc, mod2, ccw]
  omega
}

theorem face_3_eq_add_arc_ccw {d : GDart} : face (face (face d)) = d + d.mod2.ccw.arc := by{
  apply face_injective
  rw[face_4, face]
  match d with | ⟨dx, dy⟩ => {
    cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
    cases Int.emod_two_eq dy with | inl hdy | inr hdy =>
      simp[mod2, arc, ccw, hdx, hdy]
      omega
  }
}

def border (m : GRegion) : GRegion := {d | d.half ∈ m ∧ (edge d).half ∉ m}
def mrlink (d1 d2 : GDart) : Prop := end1 d1 = end0 d2

theorem mrlink_Irrefl : Std.Irrefl mrlink := ⟨by{
  intro a
  rw[mrlink]
  exact Ne.symm end0_ne_end1
}⟩
theorem mrlink_irrefl : ∀d, ¬mrlink d d := mrlink_Irrefl.irrefl

end GridPlane

theorem List.ne_singleton_of_isCycleChain_mrlink {l : List GridPlane.GDart}
  (hlc : l.IsCycleChain GridPlane.mrlink) (d : GridPlane.GDart) : l ≠ [d] := by{
    intro hl
    simp only [IsCycleChain, hl, cons_ne_self, ↓reduceDIte, IsChain.singleton, getLast_singleton,
      head_cons, true_and] at hlc
    exact GridPlane.mrlink_irrefl _ hlc
  }
