import FourColorTheorem.GridPlane.Basic
import FourColorTheorem.GridPlane.Matte.Defs

/-! 起点：单个像素可以作为一个Matte -/

open Function
open Relation

namespace GridPlane
namespace Matte

open GPoint

namespace Singleton
/- Lemmas and tools for Matte.ofPixel -/
def diskOf (p : GPixel) : List GPixel := [p]
def ringOf (p : GPoint) : List GDart := (List.range 4).map (face^[·] (2 • p))
@[simp] theorem ringOf_eq_tuple_4 {p : GPixel}
  : ringOf p = [2 • p, face (2 • p), face (face (2 • p)), face (face (face (2 • p)))]
  := rfl
theorem ringOf_ne_nil {p : GPixel} : ringOf p ≠ [] := by{
  simp[ringOf_eq_tuple_4]
}
theorem ringOf_cycle {p : GPoint}
  : (ringOf p).IsCycleChain mrlink := by{
    rw[List.IsCycleChain, dite_eq_right_of_eq_false (eq_false ringOf_ne_nil)]
    simp only [ringOf_eq_tuple_4, List.isChain_cons_cons, mrlink_face,
      List.IsChain.singleton, and_self, ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons,
      List.cons_ne_self, List.getLast_singleton, List.head_cons, true_and]
    have h:=mrlink_face (d:=face (face (face (2 • p))))
    rw[face_4] at h
    exact h
  }
theorem ringOf_simple {p : GPoint} : ((ringOf p).map end0).Nodup := by{
  rw[ringOf_eq_tuple_4]
  simp only [end0, List.map_cons, GPoint.half_double, GPoint.mod2_double, face_half, face_mod2]
  simp[GPoint.zero_def, GPoint.ccw]
}
theorem ringOf_def' {p : GPoint} : ∀d, d ∈ ringOf p ↔ d ∈ {d | d.half = p} := by{
  simp only [ringOf_eq_tuple_4, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  intro d
  constructor
  · {
    intro h
    match h with
    | Or.inl h
    | Or.inr (Or.inl h)
    | Or.inr (Or.inr (Or.inl h))
    | (Or.inr (Or.inr (Or.inr h)))  => simp only [h, GPoint.half_double, face_half]
  }
  · {
    intro h
    have hx:=Int.mul_ediv_add_emod d.1 2
    have hy:=Int.mul_ediv_add_emod d.2 2
    simp only [GPoint.half] at h
    simp only [← h, Prod.smul_mk, Int.nsmul_eq_mul, Nat.cast_ofNat, face, arc, ccw, mod2,
      Int.mul_emod_right, sub_zero, Prod.mk_sub_mk, sub_self, Prod.mk_add_mk, add_zero,
      Int.mul_add_emod_self_left, Int.one_emod_two, zero_sub, Int.reduceNeg, add_neg_cancel_right]
    cases Int.emod_two_eq d.1 with | inl hx' | inr hx' =>
    cases Int.emod_two_eq d.2 with | inl hy' | inr hy' =>
      simp[hx'] at hx
      simp[hy'] at hy
      simp[hx, hy]
  }
}
theorem ringOf_def {p : GPoint} : ∀d, d ∈ ringOf p ↔ d ∈ border (diskOf p).toFinset
:= by{
  simp only [ringOf_def', Set.mem_ofPred, border]
  simp only [List.coe_toFinset, Set.mem_ofPred_eq]
  simp only [diskOf, List.mem_singleton]
  intro d
  constructor
  · {
    intro hd
    apply And.intro hd
    rw[←hd]
    apply edge_half_ne
  }
  · intro ⟨hd, _⟩; exact hd
}
theorem mem_ringOf_iff_half_eq {d p : GPoint} : d ∈ ringOf p ↔ d.half = p := by{
  simp only [ringOf_eq_tuple_4, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · {
    intro h
    rcases h with h | h | h | h
    all_goals
    apply congrArg GPoint.half at h
    try simp only [face_half] at h
    rw[GPoint.half_double] at h
    exact h
  }
  · {
    intro h
    rw[←GPoint.double_half_add_mod2 (d:=face (face (face (2 • p))))]
    simp only [face_half, GPoint.half_double, face_mod2, GPoint.mod2_double]
    rw[←GPoint.double_half_add_mod2 (d:=face (face (2 • p)))]
    simp only [face_half, GPoint.half_double, face_mod2, GPoint.mod2_double]
    rw[←GPoint.double_half_add_mod2 (d:=face (2 • p))]
    simp only [face_half, GPoint.half_double, face_mod2, GPoint.mod2_double]
    rw[←GPoint.double_half_add_mod2 (d:=d)]
    simp only [h]
    simp only [add_left_cancel_iff, add_eq_left]
    simp only [GPoint.zero_def]
    rw[GPoint.ccw, GPoint.ccw, GPoint.ccw]
    simp only [sub_zero, sub_self]
    simp only [GPoint.mod2]
    cases Int.emod_two_eq d.1 with | inl hx | inr hx =>
    cases Int.emod_two_eq d.2 with | inl hy | inr hy =>
      simp[hx, hy]
  }
}

end Singleton

def ofGPixel (p : GPixel) : Matte where
  disk := Singleton.diskOf p
  ring := Singleton.ringOf p
  disk_ne_nil := by{simp[Singleton.diskOf]}
  ring_cycle := Singleton.ringOf_cycle
  ring_simple := Singleton.ringOf_simple
  mem_ring_iff_mem_disk_border := Singleton.ringOf_def

theorem ofGPixel_disk {p : GPixel} : (ofGPixel p).disk = [p] := rfl
theorem ofGPixel_ring' {p : GPixel} : (ofGPixel p).ring = (List.range 4).map (face^[·] (2 • p))
  := rfl
theorem ofGPixel_ring {p : GPixel} : (ofGPixel p).ring = [2 • p, face (2 • p),
  face (face (2 • p)), face (face (face (2 • p)))] := rfl
theorem mem_ofGPixel_iff {p q : GPixel} : q ∈ ofGPixel p ↔ q = p := by{
  simp[mem_def, ofGPixel_disk]
}

end Matte
end GridPlane
