import FourColorTheorem.GridPlane.Defs

open Function
open Relation

namespace GridPlane

open GPoint

theorem face_half {d : GDart} : (face d).half = d.half := by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[face, half, arc, ccw, mod2, hx, hy]
      omega
  }
}
theorem edge_half {d : GDart} : (edge d).half = d.half + d.mod2.ccw + d.mod2 - ⟨1, 1⟩ := by{
  match d with | ⟨x, y⟩ => {
    simp[edge, half, arc, mod2, ccw]
    omega
  }
}
theorem edge_half_ne {d : GDart} : (edge d).half ≠ d.half := by{
  match d with | ⟨x, y⟩ => {
    simp[edge, half, arc, mod2, ccw]
    omega
  }
}
theorem edge_half_eq_edge0_add {d : GDart} : (edge d).half = end0 d + d.mod2.ccw - ⟨1, 1⟩:=by{
  rw[edge_half, add_right_comm, ←end0]
}
theorem node_half {d : GDart} : (node d).half = d.half - d.mod2.ccw + d.mod2 := by{
  match d with | ⟨x, y⟩ => {
    simp[node, half, arc, mod2, ccw]
    omega
  }
}
theorem node_half_ne {d : GDart} : (node d).half ≠ d.half := by{
  match d with | ⟨x, y⟩ => {
    simp[node, half, arc, mod2, ccw]
    omega
  }
}
theorem node_half_eq_end0_sub {d : GDart} : (node d).half = end0 d - d.mod2.ccw := by{
  rw[node_half, end0, add_sub_right_comm]
}
theorem face_mod2 {d : GDart} : (face d).mod2 = d.mod2.ccw := by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[hx, hy, face, arc, mod2, ccw]; omega
  }
}
theorem node_mod2 {d : GDart} : (node d).mod2 = d.mod2.ccw := by{
  match d with | ⟨x, y⟩ => {
    match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[node, arc, mod2, ccw]; omega
  }
  }
}
theorem edge_mod2 {d : GDart} : (edge d).mod2 = d.mod2.ccw.ccw := by{
  match d with | ⟨x, y⟩ => {
    match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[edge, arc, mod2, ccw]; omega
  }
  }
}

theorem edge_end0 {d : GDart} : end0 (edge d) = end1 d := by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq x with | inl hx | inr hx => cases Int.emod_two_eq y with
    | inl hy | inr hy => {
      simp[edge, arc, mod2, ccw, hx, hy, end0, end1, half]
      omega
    }
  }
}
theorem edge_end1 {d : GDart} : end1 (edge d) = end0 d := by{
  nth_rw 2 [←edge_2 (d:=d)]
  rw[edge_end0]
}
theorem face_end0 {d : GDart} : end0 (face d) = end1 d := by{
  match d with | ⟨x, y⟩ => {
    cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
    cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
      simp[end0, half, face, arc, ccw, mod2, hx, hy, end1]
      omega
  }
}
theorem node_end0 {d : GDart} : end0 (node d) = end0 d :=by{
  nth_rw 2 [←fen_cancel d]
  rw[face_end0, edge_end1]
}

theorem face_end0_ne_end0 {d : GDart} : end0 (face d) ≠ end0 d :=by{
  rw[face_end0]
  exact Ne.symm end0_ne_end1
}
theorem face_2_end0_ne_end0 {d : GDart} : end0 (face (face d)) ≠ end0 d :=by{
  rcases d with ⟨x, y⟩
  cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
  cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
  simp[face, end0, arc, ccw, mod2, half, hx, hy]
  omega
}
theorem face_3_end0_ne_end0 {d : GDart} : end0 (face (face (face d))) ≠ end0 d :=by{
  rcases d with ⟨x, y⟩
  cases Int.emod_two_eq_zero_or_one x with | inl hx | inr hx =>
  cases Int.emod_two_eq_zero_or_one y with | inl hy | inr hy =>
  simp[face, end0, arc, ccw, mod2, half, hx, hy]
  omega
}

theorem end0_add_end1_eq_iff_eq_or_edge_eq {d0 d1 : GDart}
  : end0 d0 + end1 d0 = end0 d1 + end1 d1 ↔ d0 = d1 ∨ d0 = edge d1 := by{
  rcases d0 with ⟨d0x, d0y⟩
  rcases d1 with ⟨d1x, d1y⟩
  simp[end0, end1, half, mod2, ccw, edge, arc]
  omega
}
theorem half_eq_cases_face {d0 d1 : GDart}
  : d0.half = d1.half ↔ d0 = d1 ∨ d0 = face d1 ∨ d0 = face (face d1) ∨ d0 = face (face (face d1))
  := by{
  rcases d0 with ⟨d0x, d0y⟩
  rcases d1 with ⟨d1x, d1y⟩
  simp[half, mod2, ccw, face, arc]
  omega
}
theorem end0_eq_cases_node {d0 d1 : GDart}
  : end0 d0 = end0 d1 ↔ d0 = d1 ∨ d0 = node d1 ∨ d0 = node (node d1) ∨ d0 = node (node (node d1))
  := by{
  rcases d0 with ⟨d0x, d0y⟩
  rcases d1 with ⟨d1x, d1y⟩
  cases Int.emod_two_eq_zero_or_one d0x with | inl h0x | inr h0x =>
  cases Int.emod_two_eq_zero_or_one d0y with | inl h0y | inr h0y =>
  cases Int.emod_two_eq_zero_or_one d1x with | inl h1x | inr h1x =>
  cases Int.emod_two_eq_zero_or_one d1y with | inl h1y | inr h1y =>
  simp[end0, half, mod2, ccw, node, arc, h0x, h0y, h1x, h1y]
  omega
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

theorem x_succ_end0_eq_or_half_eq {dx dy} : end0 ⟨dx, dy⟩ = end0 ⟨dx + 1, dy⟩
  ∨ GPoint.half ⟨dx, dy⟩ = GPoint.half ⟨dx + 1, dy⟩ := by{
    simp[end0, half, mod2]
    omega
  }
theorem y_succ_end0_eq_or_half_eq {dx dy} : end0 ⟨dx, dy⟩ = end0 ⟨dx, dy + 1⟩
  ∨ GPoint.half ⟨dx, dy⟩ = GPoint.half ⟨dx, dy + 1⟩ := by{
    simp[end0, half, mod2]
    omega
  }

theorem edge_face_ne_edge {d : GDart} : edge (face d) ≠ edge d := by{
  rw[edge_injective.ne_iff]
  apply face_ne
}
theorem fef_ne_edge {d : GDart} : face (edge (face d)) ≠ edge d := by{
  rw[← node_injective.ne_iff, ← edge_eq_node_face, edge_2]
  rw[← node_injective.ne_iff, ← edge_eq_node_face]
  symm
  apply node_2_ne
}

theorem mrlink_face {d : GDart} : mrlink d (face d) := by{
  rw[mrlink, face_end0]
}

theorem half_edge_nodeinvDart_eq_node {q : GPixel} :
  (edge q.nodeinvDart).half = node q := by{
  rw[edge_half, nodeinvDart_mod2, ccw_4, nodeinvDart_half]
  rw[node, arc, ccw_2]
  ring
}
theorem nodeinvDart_node {q : GPixel}
: (node q).nodeinvDart = edge (node (edge q.nodeinvDart))
:= by{
  rw[nodeinvDart, node_mod2, ccw_4]
  rw[← half_mod2_ext]
  constructor
  · {
    rw[half_add_double, half_mod2, add_zero]
    rw[← face_3, face_half, face_half, face_half]
    rw[half_edge_nodeinvDart_eq_node]
  }
  · {
    rw[mod2_add_double, mod2_mod2]
    rw[edge_mod2, node_mod2, edge_mod2, ccw_4]
    rw[nodeinvDart_mod2, ccw_4]
  }
}
theorem nodeinvDart_face_edge {q : GPixel}
: (face (edge q)).nodeinvDart = edge (face q.nodeinvDart)
:= by{
  rw[← node_3, nodeinvDart_node]
  rw[edge_inj, nodeinvDart_node, edge_2]
  rw[nodeinvDart_node, edge_2, node_3, edge_2]
}

end GridPlane
