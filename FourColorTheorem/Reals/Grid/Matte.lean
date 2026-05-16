import Mathlib.Algebra.Group.Action.Basic
import FourColorTheorem.Utils.Chain
import FourColorTheorem.Reals.Grid.Basic

open Function
open Relation

namespace GridPlane

def mrlink (d1 d2 : GDart) : Prop := end1 d1 = end0 d2
theorem mrlink_of_face {d : GDart} : mrlink d (face d) := by{
  rw[mrlink, face_end0]
}

def border (m : List GPixel) : GDartRegion := {d | d.half ∈ m ∧ (edge d).half ∉ m}

structure Matte where
  disk : List GPixel
  ring : List GDart
  disk_ne_nil : disk ≠ []
  ring_cycle : ring.IsCycleChain mrlink
  ring_simple : (ring.map end0).Nodup
  mem_ring_iff_mem_disk_border : ∀x, x ∈ ring ↔ x ∈ border disk
deriving DecidableEq

namespace Matte

theorem edge_not_mem_ring_of_mem_ring {m : Matte} {p : GPoint} (hp : p ∈ m.ring)
  : edge p ∉ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, GRegion.mem_iff, setOf] at *
    intro ⟨hl, _⟩
    apply hp.right
    exact hl
  }
theorem not_mem_ring_of_edge_mem_ring {m : Matte} {p : GPoint} (hp : edge p ∈ m.ring)
  : p ∉ m.ring := swap edge_not_mem_ring_of_mem_ring hp

theorem ring_nodup {m : Matte} : m.ring.Nodup :=
  List.Nodup.of_map _ m.ring_simple

def adj (m1 m2 : Matte) : Prop := ∃p ∈ m2.ring, edge p ∈ m1.ring
theorem adj_symm {m1 m2 : Matte} : m1.adj m2 → m2.adj m1 := by{
  intro ⟨p, hp2, hp1⟩
  use edge p
  apply And.intro hp1
  rw[edge_2]
  exact hp2
}
theorem adj_Symm : Std.Symm adj := ⟨fun _ _ => adj_symm⟩
theorem adj_Irrefl : Std.Irrefl adj where
  irrefl:=by{
    intro m
    unfold adj
    rw[not_exists]
    intro p hp
    rw[mem_ring_iff_mem_disk_border] at hp
    rw[border, GRegion.mem_iff, setOf] at hp
    rw[mem_ring_iff_mem_disk_border] at hp
    rw[border, GRegion.mem_iff, setOf] at hp
    exact hp.left.right hp.right.left
  }
theorem adj_irrefl : ∀m : Matte, ¬m.adj m := adj_Irrefl.irrefl

def Mem (m : Matte) (p : GPixel) : Prop := p ∈ m.disk
@[inline] instance Mem.instDecidable {m : Matte} {p : GPixel} : Decidable (m.Mem p) := by{
  apply List.instDecidableMemOfLawfulBEq
}
@[inline] instance instMembership : Membership GPoint Matte := ⟨Matte.Mem⟩
theorem mem_iff {m : Matte} {p : GPoint} : p ∈ m ↔ p ∈ m.disk := by rfl
@[inline] instance instDecidableMem {m : Matte} {p : GPoint} : Decidable (p ∈ m)
:= Matte.Mem.instDecidable

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
    rw[List.IsCycleChain, dite_cond_eq_false (eq_false ringOf_ne_nil)]
    simp only [ringOf_eq_tuple_4, List.isChain_cons_cons, mrlink_of_face,
      List.IsChain.singleton, and_self, ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons,
      List.cons_ne_self, List.getLast_singleton, List.head_cons, true_and]
    have h:=mrlink_of_face (d:=face (face (face (2 • p))))
    rw[face_4] at h
    exact h
  }
theorem ringOf_simple {p : GPoint} : ((ringOf p).map end0).Nodup := by{
  rw[ringOf_eq_tuple_4]
  simp[end0, GPoint.half_double, GPoint.mod2_double, face_half, face_mod2]
  simp[GPoint.zero_def, GPoint.x_ccw, GPoint.y_ccw, GPoint.ext_iff]
}
theorem ringOf_def' {p : GPoint} : ∀d, d ∈ ringOf p ↔ d ∈ {d | d.half = p} := by{
  simp only [ringOf_eq_tuple_4, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
  intro d
  constructor
  · {
    intro h
    match h with
    | Or.inl h
    | Or.inr (Or.inl h)
    | Or.inr (Or.inr (Or.inl h))
    | (Or.inr (Or.inr (Or.inr h)))  => simp[h, GPoint.half_double, face_half]
  }
  · {
    intro h
    have hx:=Int.mul_ediv_add_emod d.x 2
    have hy:=Int.mul_ediv_add_emod d.y 2
    simp only [GPoint.half, GPoint.ext_iff] at h
    simp only [two_nsmul, GPoint.add_def, ← h, GPoint.ext_iff, face,
    GPoint.x_arc, GPoint.y_mod2, GPoint.x_mod2, GPoint.y_arc]
    simp only [← Int.two_mul, Int.mul_emod_right, sub_zero, sub_self, add_zero,
      Int.mul_add_emod_self_left, Int.one_emod_two, zero_sub, Int.reduceNeg, add_neg_cancel_right]
    cases Int.emod_two_eq d.x with | inl hx' | inr hx' =>
    cases Int.emod_two_eq d.y with | inl hy' | inr hy' =>
      simp[hx'] at hx
      simp[hy'] at hy
      simp[hx, hy]
  }
}
theorem ringOf_def {p : GPoint} : ∀d, d ∈ ringOf p ↔ d ∈ border (diskOf p)
:= by{
  simp only [ringOf_def', Set.mem_setOf, border, GRegion.mem_iff]
  simp only [setOf, diskOf, List.mem_singleton]
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
    simp only [GPoint.mod2, GPoint.mk.injEq]
    cases Int.emod_two_eq d.x with | inl hx | inr hx =>
    cases Int.emod_two_eq d.y with | inl hy | inr hy =>
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

namespace Refine
/- Lemmas and tools for Matte.zoom -/

def ringOf (l : List GDart) : List GDart :=
  l.flatMap (fun d => [d, face d].map (fun p => 2 • p + d.mod2))
def diskOf (l : List GPixel) : List GPixel :=
  l.flatMap Singleton.ringOf
theorem ringOf_eq_nil_iff {l : List GDart} : ringOf l = [] ↔ l = [] := by{
  simp[ringOf]
  simp[List.eq_nil_iff_forall_not_mem]
}
theorem diskOf_eq_nil_iff {l : List GPixel} : diskOf l = [] ↔ l = [] := by{
  simp[diskOf, Singleton.ringOf_eq_tuple_4]
  simp[List.eq_nil_iff_forall_not_mem]
}
@[simp] theorem ringOf_nil : ringOf [] = [] := rfl
@[simp] theorem diskOf_nil : diskOf [] = [] := rfl
@[simp] theorem ringOf_singleton {d : GDart} : ringOf [d] = [2 • d + d.mod2, 2 • face d + d.mod2] :=
  rfl
theorem diskOf_singleton_eq_ofPixel_ring {p : GPixel} : diskOf [p] = Singleton.ringOf p := rfl
@[simp] theorem diskOf_singleton {p : GPixel}
  : diskOf [p] = [2 • p, face (2 • p), face (face (2 • p)), face (face (face (2 • p)))] := by{
    rw[diskOf_singleton_eq_ofPixel_ring, Singleton.ringOf_eq_tuple_4]
  }

theorem ringOf_chain_of_chain {l : List GDart} (hl : l.IsChain mrlink)
  : (ringOf l).IsChain mrlink := by{
    match l with
    | [] => simp
    | [d] => {
      simp only [ringOf_singleton, GPoint.add_def, GPoint.x_double, GPoint.x_mod2, GPoint.y_double,
        GPoint.y_mod2, face, GPoint.x_arc, GPoint.y_arc, List.isChain_cons_cons, mrlink, end1,
        GPoint.mod2_ccw, GPoint.x_half, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        Int.mul_add_ediv_left,
        Int.emod_ediv_pos
            (by { simp
            } : (0 : Int) < 2),
        add_zero, GPoint.x_ccw, GPoint.y_half, GPoint.y_ccw, Int.add_emod_emod,
        Int.mul_add_emod_self_left, end0, GPoint.mk.injEq, List.IsChain.singleton, and_true]
      rw[Int.sub_emod, Int.mul_add_emod_self_left, Int.emod_emod]
      simp[Int.one_sub_emod_two]
      ring_nf
      simp
    }
    | d0::d1::l' => {
      rw[List.isChain_cons_cons] at hl
      have ih:=ringOf_chain_of_chain hl.right
      rw[ringOf] at ih
      rw[ringOf, List.map_cons, List.flatten_cons, List.map_cons, List.map_singleton]
      rw[List.cons_append, List.singleton_append, List.isChain_cons_cons]
      constructor
      · {
        simp[mrlink, end1, end0, GPoint.x_ccw, GPoint.y_ccw, GPoint.x_half, GPoint.y_half,
        GPoint.x_mod2, GPoint.y_mod2, GPoint.x_double, GPoint.y_double, Int.mul_add_ediv_left,
        face, GPoint.x_arc, GPoint.y_arc, Int.emod_ediv_pos]
        ring_nf
        simp
      }
      rw[List.isChain_cons_iff_of_ne_nil (by{simp})]
      refine ⟨?_, ih⟩
      simp only [GPoint.add_def, List.map_cons, List.map_nil, List.flatten_cons, List.cons_append,
        List.nil_append, List.head_cons]
      simp only [mrlink, end1, GPoint.add_def, GPoint.x_half, GPoint.x_ccw, GPoint.y_mod2,
        GPoint.y_half, GPoint.y_ccw, GPoint.x_mod2, end0, GPoint.mk.injEq] at hl
      rw[GPoint.x_double, GPoint.y_double]
      simp only [face, GPoint.add_def, GPoint.x_arc, GPoint.y_mod2, GPoint.x_mod2, GPoint.y_arc]
      simp only [mrlink, end1, GPoint.add_def, GPoint.x_half, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, Int.mul_add_ediv_left, gt_iff_lt, Nat.ofNat_pos, Int.emod_ediv_pos,
        add_zero, GPoint.x_ccw, GPoint.y_mod2, Int.add_emod_emod, Int.mul_add_emod_self_left,
        GPoint.y_half, GPoint.y_ccw, GPoint.x_mod2, end0, GPoint.x_double, GPoint.y_double,
        GPoint.mk.injEq]
      ring_nf
      rw[←add_sub_assoc, sub_eq_iff_eq_add] at hl
      rw[←add_sub_assoc, sub_eq_iff_eq_add, ←sub_eq_add_neg, sub_eq_iff_eq_add]
      have hl0:=congrArg (· * 2) hl.1.1
      ring_nf at hl0
      apply congrArg (· + d0.x % 2) at hl0
      rw[add_assoc, Int.ediv_mul_add_emod] at hl0
      nth_rw 2 [mul_two] at hl0
      rw[←add_assoc, Int.ediv_mul_add_emod] at hl0
      rw[hl0]
      ring_nf
      simp only [true_and]
      rw[add_assoc, ←sub_eq_neg_add, sub_eq_iff_eq_add]
      have hl1:=congrArg (· * 2) hl.1.2
      ring_nf at hl1
      apply congrArg (· + d0.y % 2) at hl1
      rw[add_assoc, add_left_comm, Int.ediv_mul_add_emod] at hl1
      nth_rw 3 [mul_two] at hl1
      rw[←add_assoc, Int.ediv_mul_add_emod] at hl1
      exact hl1
    }
  }

theorem ringOf_head {l : List GDart} (hln : l ≠ []) :
  (ringOf l).head (by{simp[ringOf_eq_nil_iff, hln]}) = 2 • (l.head hln) + (l.head hln).mod2
:= by{
  match l with | d :: _ => {
    simp[ringOf]
  }
}
theorem ringOf_getLast {l : List GDart} (hln : l ≠ []) :
  (ringOf l).getLast (by{simp[ringOf_eq_nil_iff, hln]})
  = 2 • (face (l.getLast hln)) + (l.getLast hln).mod2
:= by{
  have ⟨l', d, hl⟩:=List.ne_nil_iff_exists_concat.mp hln
  simp[ringOf, ←hl]
}

theorem ringOf_cycle_of_cycle {l : List GDart} (hl : l.IsCycleChain mrlink)
  : (ringOf l).IsCycleChain mrlink := by{
    cases em (l = []) with
    | inl hln => simp[hln]
    | inr hln => {
      rw[List.IsCycleChain, dite_cond_eq_false (by{simp[ringOf_eq_nil_iff, hln]})]
      rw[List.IsCycleChain, dite_cond_eq_false (by{simp[hln]})] at hl
      apply And.intro (ringOf_chain_of_chain hl.left)
      rw[ringOf_head hln, ringOf_getLast hln]
      rw[mrlink, end1_add_double, end0_add_double, end1_mod2, end0_mod2]
      rw[mrlink, end0, end1] at hl
      have hl':=hl.right
      rw[←eq_sub_iff_add_eq'] at hl'
      rw[hl']
      rw[←add_sub_assoc, sub_eq_iff_eq_add, add_right_comm, ←add_assoc]
      congr 1
      rw[face]
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=l.getLast hln)]
      rw[two_nsmul, add_assoc, add_assoc, add_assoc]
      symm
      rw[add_comm]
      congr 1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=l.head hln)]
      rw[two_nsmul, add_right_comm, ←add_assoc, ←add_assoc]
      congr 1
      rw[GPoint.arc, add_assoc, add_sub_cancel, hl.right]
    }
  }

theorem mem_ringOf_iff {l : List GDart} {d : GDart} : d ∈ ringOf l ↔
  ∃d0 ∈ l, d.mod2 = d0.mod2 ∧ (d.half = d0 ∨ d.half = face d0) := by{
    rw[ringOf, List.mem_flatMap]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · {
      intro ⟨d0, hd0l, hd0m⟩
      use d0
      apply And.intro hd0l
      rcases hd0m with hd0m | hd0m
      all_goals
      simp only [hd0m, GPoint.mod2_add_double, GPoint.mod2_mod2,
      GPoint.half_add_double, GPoint.half_mod2]
      simp
    }
    · {
      intro ⟨d0, hd0l, hd0m, hd0h⟩
      use d0
      apply And.intro hd0l
      rcases hd0h with hd0h | hd0h
      all_goals
      simp only [←hd0m]
      simp only [←hd0h, GPoint.double_half_add_mod2]
      simp
    }
  }

theorem ringOf_simple {l : List GDart} (hls : (l.map end0).Nodup)
  (hle : ∀ p ∈ l, edge p ∉ l) : ((ringOf l).map end0).Nodup := by{
    rw[ringOf, List.map_flatMap, List.nodup_flatMap]
    constructor
    · {
      intro x hxl
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_self, and_true]
      rw[end0, GPoint.half_add_double, GPoint.mod2_add_double,
      GPoint.half_mod2, GPoint.mod2_mod2, add_zero]
      rw[end0, GPoint.half_add_double, GPoint.mod2_add_double,
      GPoint.half_mod2, GPoint.mod2_mod2, add_zero, add_right_cancel_iff]
      exact Ne.symm face_ne
    }
    · {
      rw[List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.map_cons, List.map_nil, List.disjoint_cons_right,
        List.mem_cons, List.not_mem_nil, or_false, not_or, end0_add_double, end0_mod2]
      rw[List.nodup_iff_getElem_ne_getElem'] at hls
      simp only [List.length_map, List.getElem_map, ne_eq] at hls
      nth_rw 1 3 [←GPoint.double_half_add_mod2 (d:=l[j])]
      rw[two_nsmul]
      nth_rw 1 5 [←GPoint.double_half_add_mod2 (d:=l[i])]
      rw[two_nsmul, face, GPoint.arc, add_assoc (b:= _ - _), sub_add_cancel]
      rw[face, GPoint.arc, add_assoc (b:= _ - _), sub_add_cancel]
      nth_rw 9 11 [←GPoint.double_half_add_mod2 (d:=l[j])]
      rw[two_nsmul]
      nth_rw 5 11 [←GPoint.double_half_add_mod2 (d:=l[i])]
      rw[two_nsmul]
      rw[add_right_comm (b:=GPoint.half l[j]) (c:=GPoint.mod2 _)]
      rw[add_right_comm (b:=GPoint.half l[i]) (c:=GPoint.mod2 _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[add_assoc (b:=GPoint.half _)]
      rw[←end0, ←end1]
      rw[←end0, ←end1]
      simp only [List.disjoint_nil_right, and_true]
      constructor
      · {
        constructor
        · {
          rw[←two_nsmul, ←two_nsmul, GPoint.nsmul_cancel_iff (by{trivial})]
          apply hls
          · exact ne_of_gt hij
          · exact hj
          · exact hi
        }
        · {
          rw[←two_nsmul]
          intro h
          have ih:=GPoint.mod2_eq_zero_iff_exists_double.mpr ⟨end0 l[j], h.symm⟩
          exact end0_add_end1_mod2_ne_zero ih
        }
      }
      · {
        constructor
        · {
          rw[←two_nsmul]
          intro h
          have ih:=GPoint.mod2_eq_zero_iff_exists_double.mpr ⟨end0 l[i], h⟩
          exact end0_add_end1_mod2_ne_zero ih
        }
        · {
          rw[end0_add_end1_eq_iff_eq_or_edge_eq, not_or]
          constructor
          · {
            intro hij'
            have hls':=hls j i (ne_of_gt hij) hj hi
            apply hls'
            rw[hij']
          }
          · {
            intro hi
            apply hle l[i] (List.getElem_mem _)
            rw[←hi]
            apply List.getElem_mem
          }
        }
      }
    }
  }

theorem ringOf_def {lr : List GDart} {ld : List GPixel}
  (hld : ∀x, x ∈ lr ↔ x ∈ border ld):
  ∀x, x ∈ ringOf lr ↔ x ∈ border (diskOf ld)
:= by{
  intro x
  rw[mem_ringOf_iff, border]
  have hle : ∀ p ∈ lr, edge p ∉ lr := by{
    intro p hlp
    rw[hld, border]
    rw[hld, border] at hlp
    change ¬(_ ∧ _)
    change _ ∧ _ at hlp
    simp[hlp]
  }
  change _ ↔ _ ∧ _
  rw[diskOf, List.mem_flatMap, List.mem_flatMap, not_exists]
  simp only [Singleton.mem_ringOf_iff_half_eq]
  simp only [↓existsAndEq, and_true, not_and]
  simp only [border] at hld
  change ∀ x, x ∈ lr ↔ _ ∧ _ at hld
  have change_lemma {p : GPoint}: (∀x ∈ ld, p ≠ x) ↔ p ∉ ld := by{
    constructor
    intro h
    · have h':=h p; simp at h'; simp[h']
    · intro h x hx hpx; apply h; exact hpx ▸ hx
  }
  rw[change_lemma]
  constructor
  · {
    intro ⟨d0, hd00, hd01, hd02⟩
    rw[hld] at hd00
    change _ ∧ _ at hd00
    constructor
    · {
      rcases hd02 with hd02 | hd02
      all_goals
      rw[hd02]
      try rw[face_half]
      exact hd00.left
    }
    · {
      rw[edge_half]
      cases hd02 with
      | inl hd02 => {
        rw[hd02, hd01, add_right_comm]
        nth_rw 1 [←GPoint.double_half_add_mod2 (d:=d0)]
        rw[add_assoc (c:=d0.mod2), ←two_nsmul, ←nsmul_add, add_sub_assoc, GPoint.half_add_double]
        rw[GPoint.mod2_ccw, GPoint.half_mod2_sub_unit, ←add_sub_assoc, add_right_comm]
        rw[←GPoint.mod2_ccw, ←edge_half]
        exact hd00.right
      }
      | inr hd02 => {
        rw[hd02, face, GPoint.arc, hd01, add_right_comm, add_assoc (b:=_ - _)]
        rw[sub_add_cancel, add_assoc, ←two_nsmul]
        nth_rw 1 [←GPoint.double_half_add_mod2 (d:=d0)]
        rw[add_right_comm, ←nsmul_add, add_sub_assoc, GPoint.half_add_double]
        rw[GPoint.half_mod2_sub_unit, ←add_sub_assoc, ←edge_half]
        exact hd00.right
      }
    }
  }
  · {
    intro ⟨h0, h1⟩
    have h2 : x.half.half ≠ (edge x).half.half:=by{
      intro h
      apply h1
      exact h ▸ h0
    }
    rw[edge_half] at h2
    symm at h2
    nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h2
    rw[ne_eq, add_sub_assoc, add_assoc, add_assoc, GPoint.half_add_double, add_eq_left] at h2
    rw[←add_assoc, ←add_sub_assoc] at h2
    have h3:x.half.mod2 ≠ x.mod2.ccw.ccw := by{
      intro h3
      rw[h3, GPoint.ccw_2, add_right_comm, sub_add_cancel, add_sub_cancel_left] at h2
      simp[GPoint.mod2_ccw, GPoint.half_mod2] at h2
    }
    have h4:x.half.mod2 ≠ x.mod2.ccw.ccw.ccw := by{
      intro h3
      rw[h3, GPoint.ccw_2, sub_add_cancel, add_sub_cancel_left] at h2
      simp[GPoint.half_mod2] at h2
    }
    have h5:=GPoint.mod2_eq_mod2_cases (p:=x.half) (q:=x)
    simp only [h3, h4, or_self, or_false] at h5
    cases h5 with
    | inl h5 => {
      use x.half
      rw[h5]
      refine ⟨?_, rfl, Or.inl rfl⟩
      rw[hld]
      refine ⟨h0, ?_⟩
      rw[edge, GPoint.arc, GPoint.arc, h5]
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)]
      rw[add_sub, add_assoc, h5, add_sub_cancel, ←sub_add, sub_add_eq_add_sub]
      rw[add_assoc, ←two_nsmul, ←nsmul_add, GPoint.ccw_2, ←sub_add, sub_add_eq_add_sub]
      rw[add_sub_assoc, GPoint.half_add_double, GPoint.half_mod2_sub_unit, ←add_sub_assoc]
      rw[edge_half] at h1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h1
      rw[h5, add_right_comm, add_assoc (c:=x.mod2), ←two_nsmul, ←nsmul_add] at h1
      rw[add_sub_assoc, GPoint.half_add_double, GPoint.mod2_ccw, GPoint.half_mod2_sub_unit] at h1
      rw[←GPoint.mod2_ccw, ←add_sub_assoc, add_right_comm] at h1
      exact h1
    }
    | inr h5 => {
      use edge (node x.half)
      rw[fen_cancel, edge_mod2, node_mod2, h5, GPoint.ccw_4]
      refine ⟨?_, rfl, Or.inr rfl⟩
      have h6 : (edge (node x.half)).half = x.half.half := by{
        nth_rw 2 [←fen_cancel x.half]
        rw[face_half]
      }
      rw[hld, h6]
      refine ⟨h0, ?_⟩
      rw[edge_half, h6, edge_mod2, node_mod2, h5, GPoint.ccw_4, GPoint.ccw_4]
      rw[edge_half] at h1
      nth_rw 1 [←GPoint.double_half_add_mod2 (d:=x.half)] at h1
      rw[h5, add_assoc (c:=x.mod2.ccw), ←two_nsmul, ←nsmul_add, add_sub_assoc] at h1
      rw[GPoint.half_add_double, GPoint.half_mod2_sub_unit, ←add_sub_assoc] at h1
      exact h1
    }
  }
}

end Refine

def zoom (m : Matte) : Matte where
  disk := Refine.diskOf m.disk
  ring := Refine.ringOf m.ring
  disk_ne_nil := by{simp[Refine.diskOf_eq_nil_iff, m.disk_ne_nil]}
  ring_cycle := by{simp[Refine.ringOf_cycle_of_cycle m.ring_cycle]}
  ring_simple := by{
    apply Refine.ringOf_simple
    · exact m.ring_simple
    exact fun p => m.edge_not_mem_ring_of_mem_ring (p:=p)
  }
  mem_ring_iff_mem_disk_border := by{
    apply Refine.ringOf_def
    · exact m.mem_ring_iff_mem_disk_border
  }

end Matte

end GridPlane
