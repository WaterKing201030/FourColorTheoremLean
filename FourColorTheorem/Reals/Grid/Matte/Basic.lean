import Mathlib.Algebra.Group.Action.Basic
import FourColorTheorem.Utils.Chain
import FourColorTheorem.Reals.Grid.Basic

open Function
open Relation

namespace GridPlane

def sepNodeDart (p : GPixel) : GDart :=
  -- the dart of p whose edge separates p from node p
  2 • p + p.mod2.ccw.ccw.ccw

def mrlink (d1 d2 : GDart) : Prop := end1 d1 = end0 d2
theorem mrlink_face {d : GDart} : mrlink d (face d) := by{
  rw[mrlink, face_end0]
}
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

namespace GridPlane

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
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at *
    intro ⟨hl, _⟩
    apply hp.right
    exact hl
  }
theorem not_mem_ring_of_edge_mem_ring {m : Matte} {p : GPoint} (hp : edge p ∈ m.ring)
  : p ∉ m.ring := swap edge_not_mem_ring_of_mem_ring hp

theorem ring_nodup {m : Matte} : m.ring.Nodup :=
  List.Nodup.of_map _ m.ring_simple

lemma exists_border_of_disk_ne_nil {l : List GPixel} (hln : l ≠ [])
 : ∃x, x ∈ border l := by{
  have ih : ∃d ∈ l, ⟨d.x, d.y - 1⟩ ∉ l := by{
    let n := l.minOn GPoint.y hln
    use n
    apply And.intro List.minOn_mem
    intro h
    have hn:=List.min_map hln (f:=GPoint.y)
    change _ = n.y at hn
    rw[List.min_eq_iff] at hn
    have hn':=hn.right (n.y - 1) (by{
      simp only [List.mem_map]
      use ⟨n.x, n.y - 1⟩
    })
    simp at hn'
  }
  have ⟨d, hd, hd0⟩:=ih
  use 2 • d
  rw[border, Set.mem_setOf, GPoint.half_double, edge_half, GPoint.mod2_double, GPoint.half_double]
  rw[add_zero, GPoint.zero_def, GPoint.ccw]
  simp[hd, hd0]
}

theorem ring_ne_nil {m : Matte} : m.ring ≠ [] := by{
  rw[ne_eq, List.eq_nil_iff_forall_not_mem, not_forall]
  simp only [not_not, mem_ring_iff_mem_disk_border]
  apply exists_border_of_disk_ne_nil
  exact m.disk_ne_nil
}

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
    rw[border, Set.mem_setOf] at hp
    rw[mem_ring_iff_mem_disk_border] at hp
    rw[border, Set.mem_setOf] at hp
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

end Matte

namespace Matte

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
    simp only [ringOf_eq_tuple_4, List.isChain_cons_cons, mrlink_face,
      List.IsChain.singleton, and_self, ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons,
      List.cons_ne_self, List.getLast_singleton, List.head_cons, true_and]
    have h:=mrlink_face (d:=face (face (face (2 • p))))
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
  simp only [ringOf_def', Set.mem_setOf, border]
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
      rw[ringOf, List.flatMap_cons, List.map_cons, List.map_singleton]
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
      simp only [GPoint.add_def, List.map_cons, List.map_nil, List.flatMap_cons, List.cons_append,
      List.head_cons]
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
  (hld : ∀ x, x ∈ lr ↔ x ∈ border ld) :
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
    · intro h; have h':=h p; simp at h'; simp[h']
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

theorem mem_zoom_iff {m : Matte} {p : GPixel} :
  p ∈ m.zoom ↔ p.half ∈ m := by{
    rw[mem_iff, mem_iff, zoom]
    simp only
    rw[Refine.diskOf, List.mem_flatMap]
    simp only [Singleton.ringOf_eq_tuple_4, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · {
      intro ⟨a, ha0, ha1⟩
      rcases ha1 with ha1 | ha1 | ha1 | ha1
      all_goals
      rw[ha1]
      simp[face_half, GPoint.half_double, ha0]
    }
    · {
      intro h
      use p.half
      apply And.intro h
      rw[←half_eq_cases_face, GPoint.half_double]
    }
  }

section extend_matte
def ehex (d : GDart) := chopRect d.half.touch d
def equad (d : GDart) := chopRect (ehex d) (face d)

theorem half_mem_ehex {d : GDart} : d.half ∈ ehex d := by{
  rw[ehex, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  rw[←GRectangle.mem_iff_toRegion]
  apply And.intro GPoint.mem_touch
  apply half_mem_chop
}
theorem half_mem_equad {d : GDart} : d.half ∈ equad d := by{
  rw[equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  rw[←GRectangle.mem_iff_toRegion]
  apply And.intro half_mem_ehex
  apply half_mem_chop_face
}
theorem half_node_mem_ehex {d : GDart} : (node d).half ∈ ehex d := by{
  rw[ehex, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  rw[←GRectangle.mem_iff_toRegion]
  constructor
  · {
    apply half_mem_touch_of_end0_eq_end0
    rw[node_end0]
  }
  · apply node_half_mem_chop
}
theorem half_node_mem_equad {d : GDart} : (node d).half ∈ equad d := by{
  rw[equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  rw[←GRectangle.mem_iff_toRegion]
  apply And.intro half_node_mem_ehex
  apply node_half_mem_chop_face
}
theorem equad_subset_ehex {d : GDart} : equad d ⊆ ehex d := by{
  rw[equad]
  apply chopRect_subset_rect
}
theorem exists_mem_equad_of_end0_mem {m : Matte} {d : GDart} (hd : end0 d ∈ m)
: ∃d0 ∈ m, d0 ∈ equad (face d) := by{
  simp only [equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  simp only [ehex, chopRect_toRegion, Set.mem_inter_iff]
  use end0 d
  apply And.intro hd
  refine ⟨⟨?_, end0_mem_chop_face⟩, end0_mem_chop_face_face⟩
  rw[face_half, ←GRectangle.mem_iff_toRegion]
  exact end0_mem_touch
}
theorem exists_mem_equad_of_end0_mem_ring_map_end0 {m : Matte} {d : GDart}
(hd : end0 d ∈ m.ring.map end0) : ∃d0 ∈ m, d0 ∈ equad (face d) := by{
  rw[List.mem_map] at hd
  have ⟨a, ha⟩:=hd
  have ha':=ha.left
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at ha'
  use a.half
  apply And.intro ha'.left
  rw[equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
  rw[ehex, face_half, chopRect_toRegion, Set.mem_inter_iff, ←GRectangle.mem_iff_toRegion]
  rw[and_assoc]
  apply And.intro (half_mem_touch_of_end0_eq_end0 ha.right)
  apply And.intro (half_mem_chop_face_of_end0_eq ha.right)
  exact half_mem_chop_face_face_of_end0_eq ha.right
}
theorem half_mem_ehex_of_end0_eq_end0_face_face {d a : GDart} (hda : end0 a = end0 (face (face d)))
  : a.half ∈ ehex d :=by{
    rw[ehex, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
    rw[←GRectangle.mem_iff_toRegion]
    constructor
    · apply half_mem_touch_of_end0_eq_end0_face_face hda
    · apply half_mem_chop_of_end0_eq_end0_face_face hda
  }
theorem half_mem_ehex_of_end0_eq_end0_face_3 {d a : GDart}
(hda : end0 a = end0 (face (face (face d))))
  : a.half ∈ ehex d := by{
    rw[ehex, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
    rw[←GRectangle.mem_iff_toRegion]
    constructor
    · apply half_mem_touch_of_end0_eq_end0_face_3 hda
    · apply half_mem_chop_of_end0_eq_end0_face_3 hda
  }
theorem half_mem_equad_of_end0_eq_end0_face_3
{d a : GDart} (hda : end0 a = end0 (face (face (face d))))
  : a.half ∈ equad d := by{
    rw[equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
    rw[←GRectangle.mem_iff_toRegion]
    constructor
    · apply half_mem_ehex_of_end0_eq_end0_face_3 hda
    · apply half_mem_chop_of_end0_eq_end0_face_face hda
  }

theorem ehex_disjoint_edge_chop {d : GDart} : Disjoint (ehex d).toRegion (chop (edge d)) := by{
  rw[ehex, chopRect_toRegion]
  apply Set.disjoint_of_subset_left (Set.inter_subset_right)
  apply chop_disjoint_edge_chop
}
theorem ehex_subset_touch {d : GDart} : ehex d ⊆ d.half.touch := by{
  apply chopRect_subset_rect
}
theorem equad_subset_touch {d : GDart} : equad d ⊆ d.half.touch := by{
  apply GRectangle.subset.trans (b:=ehex d)
  · apply equad_subset_ehex
  · apply ehex_subset_touch
}

theorem ehex_cases {d : GDart} {p : GPixel} : p ∈ ehex d ↔
  p = d.half ∨ p = (edge (face d)).half ∨ p = (node (edge (face d))).half ∨
  p = (edge (face (face d))).half ∨ p = (edge (face (node d))).half ∨ p = (node d).half := by{
    match p, d with | ⟨px, py⟩, ⟨dx, dy⟩ => {
      simp only [edge_half, node_half, edge_mod2, face_mod2, node_mod2, GPoint.ccw_4]
      simp only [GPoint.ccw_2 (p:=GPoint.ccw _)]
      simp only [GPoint.ccw_2]
      rw[add_sub_assoc, add_right_comm, add_assoc, ←add_sub_assoc, sub_add_cancel]
      rw[add_sub_assoc, add_right_comm, add_assoc, ←add_sub_assoc, ←add_sub_assoc, ←add_sub_assoc]
      rw[←add_sub_assoc, sub_add_cancel, add_sub_assoc, add_sub_assoc, add_sub_assoc]
      simp only [ehex, chopRect, GPoint.toUnitSquareDart, GPoint.x_mod2, GPoint.y_mod2,
        GPoint.touch, GPoint.x_half, GPoint.y_half, tsub_le_iff_right, le_add_iff_nonneg_right,
        zero_le_one, sup_of_le_right, add_le_add_iff_left, Nat.one_le_ofNat, inf_of_le_right,
        GRectangle.mem_iff, GInterval.mem_iff, GPoint.ext_iff, face, GPoint.arc, GPoint.sub_def,
        GPoint.x_ccw, GPoint.y_ccw, GPoint.add_def, sub_sub_cancel, sub_sub_cancel_left,
        node]
      cases Int.emod_two_eq dx with | inl hdx | inr hdx =>
      cases Int.emod_two_eq dy with | inl hdy | inr hdy => {
        simp only [hdx, one_ne_zero, ↓reduceIte, hdy, tsub_le_iff_right, sub_self, zero_sub,
          Int.reduceNeg, Int.add_neg_eq_sub, add_zero, Int.sub_one_emod_two, add_neg_cancel_right,
          sub_zero, add_sub_cancel_right, sub_add_cancel, Int.add_one_emod_two]
        try simp only [Int.add_one_ediv_two_of_mod_zero hdx, Int.reduceNeg, sub_neg_eq_add]
        try simp only [Int.add_one_ediv_two_of_mod_zero hdy]
        try simp only [Int.sub_one_ediv_two_of_mod_one hdx, Int.reduceNeg, sub_neg_eq_add]
        try simp only [Int.sub_one_ediv_two_of_mod_one hdy]
        try simp only [Int.add_one_ediv_two_of_mod_one hdx, Int.reduceNeg, sub_neg_eq_add]
        try simp only [Int.add_one_ediv_two_of_mod_one hdy, Int.reduceNeg, sub_neg_eq_add]
        try simp only [Int.sub_one_ediv_two_of_mod_zero hdx]
        try simp only [Int.sub_one_ediv_two_of_mod_zero hdy]
        set dx':=dx / 2
        set dy':=dy / 2
        constructor
        · {
          intro h
          rw[←sub_lt_iff_lt_add' (a:=px), ←sub_lt_iff_lt_add' (a:=py)] at h
          nth_rw 1 [←zero_add dx', ←zero_add dy'] at h
          rw[Int.add_le_iff_le_sub, Int.add_le_iff_le_sub] at h
          try rw[←sub_add_eq_add_sub px] at h
          try rw[←sub_add_eq_add_sub py] at h
          try rw[←sub_le_iff_le_add] at h
          try rw[←sub_le_iff_le_add] at h
          simp only [←sub_eq_zero (a:=px), ←sub_eq_zero (a:=py), ←sub_sub, ←sub_add]
          set ddx := px - dx'
          set ddy := py - dy'
          match hddx:ddx with
          | -1 | 0 | 1 => match hddy:ddy with
            | -1 | 0 | 1 =>
              unfold ddx dx' at hddx
              unfold ddy dy' at hddy
              simp at h
              try simp[Int.add_one_emod_two, hdx, hdy, Int.add_neg_eq_sub]
              try simp[Int.add_one_ediv_two_of_mod_one hdx]
              try simp[Int.add_one_ediv_two_of_mod_zero hdx]
              try simp[Int.add_one_ediv_two_of_mod_one hdy]
              try simp[Int.sub_one_ediv_two_of_mod_one hdy]
              try simp[←sub_sub, hddx, hddy]
        }
        · {
          intro h
          rcases h with h | h | h | h | h | h
          all_goals
          omega
        }
      }
    }
  }

theorem equad_cases {d : GDart} {p : GPixel} : p ∈ equad d ↔
  p = d.half ∨ p = (edge (face (face d))).half ∨
  p = (edge (face (node d))).half ∨ p = (node d).half := by{
    rw[equad, GRectangle.mem_iff_toRegion, chopRect_toRegion, Set.mem_inter_iff]
    rw[←GRectangle.mem_iff_toRegion, ehex_cases]
    constructor
    · {
      intro ⟨h0, h1⟩
      have h0':(p = GPoint.half d ∨ p = GPoint.half (edge (face (face d)))
      ∨ p = GPoint.half (edge (face (node d))) ∨ p = GPoint.half (node d)) ∨
      p = (edge (face d)).half ∨ p = (node (edge (face d))).half := by{
        tauto
      }
      apply h0'.resolve_right
      rw[not_or]
      constructor
      · {
        intro h
        revert h1
        rw[imp_false, ←mem_edge_chop_iff, h]
        apply half_mem_chop
      }
      · {
        intro h
        revert h1
        rw[imp_false, ←mem_edge_chop_iff, h]
        apply node_half_mem_chop
      }
    }
    · {
      intro h
      rcases h with h | h | h | h
      · {
        simp only [h, true_or, true_and]
        apply half_mem_chop_face
      }
      · {
        simp only [h, true_or, or_true, true_and]
        rw[←face_half, ←fef_chop_eq]
        apply half_mem_chop
      }
      · {
        simp only [h, true_or, or_true, true_and]
        rw[←face_half]
        have h0:face (edge (face (node d))) = node (node (edge (node d))) := by{
          rw[edge_eq_node_face, edge_eq_node_face, node_3, edge_eq_node_face]
        }
        rw[h0, ←fef_chop_eq]
        nth_rw 1 [edge_eq_node_face]
        rw[face_3]
        apply node_half_mem_chop_face
      }
      · {
        simp only [h, or_true, true_and]
        apply node_half_mem_chop_face
      }
    }
  }

def extDisk (m : Matte) (d : GDart) := d.half :: m.disk

namespace Extend1

def ext1Hp (m : Matte) (d : GDart) : Prop :=
  (edge d).half ∈ m ∧ m.disk.Disjoint (ehex d).enum

theorem half_not_mem {m : Matte} {d : GDart} (h : ext1Hp m d)
: d.half ∉ m := by{
  rw[ext1Hp] at h
  intro h'
  have ih:=h.right h'
  apply ih
  rw[GRectangle.mem_enum_iff]
  apply half_mem_ehex
}
theorem edge_mem_ring {m : Matte} {d : GDart} (h : ext1Hp m d)
: edge d ∈ m.ring := by{
  rw[mem_ring_iff_mem_disk_border, border]
  change _ ∧ _
  rw[Extend1.ext1Hp] at h
  apply And.intro h.left
  rw[edge_2]
  apply Extend1.half_not_mem h
}

def ext1loop (d : GDart) := [face d, face (face d), face (face (face d))]
theorem ext1loop_map_end0_nodup {d : GDart} : ((ext1loop d).map end0).Nodup := by{
  simp[ext1loop, face_end0_ne_end0.symm, face_2_end0_ne_end0.symm]
}
theorem ext1loop_nodup {d : GDart} : (ext1loop d).Nodup := by{
  apply List.Nodup.of_map end0
  exact ext1loop_map_end0_nodup
}
theorem ext1loop_ne_nil {d : GDart} : ext1loop d ≠ [] := by{simp[ext1loop]}
theorem head_ext1loop {d : GDart} : (ext1loop d).head ext1loop_ne_nil = face d := rfl
theorem getLast_ext1loop {d : GDart} : (ext1loop d).getLast ext1loop_ne_nil = face (face (face d))
  := rfl
theorem ext1loop_isChain_mrlink {d : GDart} : (ext1loop d).IsChain mrlink := by{
  simp[ext1loop, mrlink_face]
}

abbrev ext1Disk := extDisk
def ext1Ring (m : Matte) (d : GDart) : List GDart :=
  ext1loop d ++ (m.ring.rotate (m.ring.idxOf (edge d))).tail

theorem ext1Disk_ne_nil {m : Matte} {d : GDart} : ext1Disk m d ≠ [] := by{simp[extDisk]}
theorem ext1Ring_ne_nil {m : Matte} {d : GDart} : ext1Ring m d ≠ [] := by{
  rw[ext1Ring]
  apply List.append_ne_nil_of_left_ne_nil
  exact ext1loop_ne_nil
}
theorem ext1Ring_chain {m : Matte} {d : GDart} (h : ext1Hp m d)
  : (ext1Ring m d).IsChain mrlink := by{
    have hln:=m.ring_ne_nil
    have hlc:=m.ring_cycle
    have he:=edge_mem_ring h
    rw[ext1Ring, List.isChain_append]
    have hlc':=hlc.rotate (m.ring.idxOf (edge d))
    rw[List.IsCycleChain] at hlc'
    simp only [List.rotate_eq_nil_iff, dite_then_true] at hlc'
    have hlc'':=hlc' hln
    apply And.intro ext1loop_isChain_mrlink
    apply And.intro hlc''.left.tail
    rw[List.getLast?_eq_some_getLast ext1loop_ne_nil, getLast_ext1loop]
    simp only [Option.mem_def, Option.some.injEq, List.head?_tail, forall_eq']
    have h_lemma : 1 < m.ring.length := by{
      have hl:=List.ne_singleton_of_isCycleChain_mrlink hlc
      generalize hmr : m.ring = mr
      match mr with
      | _::_::_ => simp
      | [_] => simp[hmr] at hl
      | [] => contradiction
    }
    rw[List.getElem?_eq_some_getElem]
    · {
      simp only [Option.some.injEq, forall_eq']
      have hlc''':=List.isChain_iff_getElem.mp hlc''.left 0 (by{simp[h_lemma]})
      rw[List.getElem_zero_eq_head, List.head_rotate_idxOf he] at hlc'''
      rw[mrlink] at hlc'''
      rw[mrlink, ←hlc''']
      rw[←face_end0, face_4, ←face_end0]
      nth_rw 1 [←nfe_cancel d]
      rw[node_end0]
    }
    · simp[h_lemma]
  }
theorem ext1Ring_cycleChain {m : Matte} {d : GDart} (h : ext1Hp m d)
: (ext1Ring m d).IsCycleChain mrlink := by{
  have hln:=m.ring_ne_nil
  have hlc:=m.ring_cycle
  have he:=edge_mem_ring h
  rw[List.IsCycleChain]
  rw[dite_cond_eq_false (by{simp[ext1Ring_ne_nil]})]
  constructor
  · apply ext1Ring_chain h
  simp only [ext1Ring, List.head_append_of_ne_nil ext1loop_ne_nil, head_ext1loop]
  rw[List.getLast_append_of_right_ne_nil _ _ (by{
    have h':=List.ne_singleton_of_isCycleChain_mrlink hlc
    generalize hmr : m.ring = mr
    match mr with
    | _::_::_ => rw[ne_eq, List.eq_nil_iff_length_eq_zero]; simp
    | [_] => simp[hmr] at h'
    | [] => contradiction
  })]
  rw[List.getLast_tail]
  have hlc':=hlc.rotate (m.ring.idxOf (edge d))
  rw[List.IsCycleChain] at hlc'
  simp only [List.rotate_eq_nil_iff, dite_then_true] at hlc'
  have hlc'':=(hlc' hln).right
  rw[mrlink] at hlc''
  rw[mrlink]
  rw[hlc'']
  rw[List.head_rotate_idxOf he]
  rw[edge_end0, face_end0]
}

theorem end0_face_2_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext1Hp m d)
: end0 (face (face d)) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext1Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  have hc':=hc.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply half_mem_ehex_of_end0_eq_end0_face_face
  exact hxf
}
theorem end0_face_3_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext1Hp m d)
: end0 (face (face (face d))) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext1Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  have hc':=hc.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply half_mem_ehex_of_end0_eq_end0_face_3
  exact hxf
}

theorem ext1loop_disjoint_ring {m : Matte} {d : GDart} (hc : ext1Hp m d)
  : (ext1loop d).Disjoint m.ring := by{
    intro x hx
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf]
    simp only [imp_false, not_and, Decidable.not_not]
    rw[ext1Hp] at hc
    intro hx'
    have hx'':=hc.right hx'
    simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at hx
    exfalso
    apply hx''
    rcases hx with hx | hx | hx
    all_goals
    rw[GRectangle.mem_enum_iff]
    simp[hx, face_half, half_mem_ehex]
  }
theorem half_ext1loop_edge_mem_ehex {d : GDart} : ∀x ∈ ext1loop d, (edge x).half ∈ ehex d := by{
  intro x hx
  simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx
  · {
    rw[hx]
    apply half_mem_ehex_of_end0_eq_end0_face_face
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx]
    apply half_mem_ehex_of_end0_eq_end0_face_3
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx, face_3, edge_2]
    apply half_node_mem_ehex
  }
}

theorem ext1Ring_simple {m : Matte} {d : GDart} (hc : ext1Hp m d)
: ((ext1Ring m d).map end0).Nodup := by{
    have hls:=m.ring_simple
    have hld:=m.ring_nodup
    have he:=edge_mem_ring hc
    rw[ext1Ring, List.nodup_map_iff_inj_on]
    · {
      intro x hx y hy hxy
      rw[List.mem_append] at hx hy
      wlog hx': x ∈ ext1loop d generalizing x y with H
      · {
        apply (Or.resolve_left · hx') at hx
        cases hy with
        | inl hy => {
          have H':=H y (Or.inl hy) x (Or.inr hx) hxy.symm hy
          exact H'.symm
        }
        | inr hy => {
          have hx':=List.mem_of_mem_tail hx
          have hy':=List.mem_of_mem_tail hy
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate, List.nodup_map_iff_inj_on] at hls'
          · exact hls' _ hx' _ hy' hxy
          simp[hld]
        }
      }
      cases hy with
      | inl hy => {
        have hls':=ext1loop_map_end0_nodup (d:=d)
        rw[List.nodup_map_iff_inj_on] at hls'
        · exact hls' _ hx' _ hy hxy
        apply ext1loop_nodup
      }
      | inr hy => {
        rw[ext1Hp] at hc
        have hy':=List.mem_rotate.mp (List.mem_of_mem_tail hy)
        have hy'':=hy'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hy'
        have hc':=hc.right hy'.left
        rw[GRectangle.mem_enum_iff] at hc'
        rw[ext1loop] at hx'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        rcases hx' with hx' | hx' | hx'
        · {
          exfalso
          have hyd : y = edge d := by{
            have h0:end0 (edge d) = end0 x:=by{
              rw[hx', edge_end0, face_end0]
            }
            rw[hxy] at h0
            rw[List.nodup_map_iff_inj_on hld] at hls
            have hls':=hls _ he _ hy'' h0
            rw[hls']
          }
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate] at hls'
          have ⟨a, l', hal'⟩:=List.exists_cons_of_ne_nil
            (l:=m.ring.rotate (List.idxOf (edge d) m.ring))
            (by{simp[m.ring_ne_nil]})
          rw[hal', List.map_cons] at hls'
          rw[List.nodup_cons] at hls'
          rw[hal', List.tail_cons] at hy
          apply hls'.left
          have h':=List.head_rotate_idxOf he
          simp only [hal', List.head_cons] at h'
          rw[h', ←hyd]
          rw[List.mem_map]
          use y
        }
        · {
          exfalso
          apply hc'
          apply half_mem_ehex_of_end0_eq_end0_face_face
          rw[←hx', hxy]
        }
        · {
          exfalso
          apply hc'
          apply half_mem_ehex_of_end0_eq_end0_face_3
          rw[←hx', hxy]
        }
      }
    }
    · {
      rw[List.nodup_append']
      apply And.intro ext1loop_nodup
      constructor
      · {
        apply List.Nodup.tail
        rw[List.nodup_rotate]
        exact hld
      }
      apply List.disjoint_of_subset_right (List.tail_subset _)
      rw[List.disjoint_rotate_right]
      apply ext1loop_disjoint_ring hc
    }
  }

theorem mem_ext1Ring_iff {m : Matte} {d : GDart} (hc : ext1Hp m d) :
  ∀x, x ∈ ext1Ring m d ↔ x ∈ border (ext1Disk m d) := by{
    intro x
    rw[ext1Ring, List.mem_append]
    rw[ext1Disk, extDisk, border, Set.mem_setOf, List.mem_cons, List.mem_cons, not_or]
    constructor
    · {
      intro h
      cases h with
      | inl h => {
        constructor
        · {
          left
          simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          all_goals
          simp[h, face_half]
        }
        rw[ext1Hp, List.disjoint_comm] at hc
        constructor
        · {
          rw[edge_half]
          simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          all_goals
          simp only [h, face_half, face_mod2, add_sub_assoc, add_assoc, add_eq_left]
          simp only [←add_sub_assoc, sub_eq_zero]
          simp only [GPoint.add_def, GPoint.ext_iff,
          GPoint.x_ccw, GPoint.y_ccw, GPoint.x_mod2, GPoint.y_mod2]
          cases Int.emod_two_eq d.x with | inl hx | inr hx =>
          cases Int.emod_two_eq d.y with | inl hy | inr hy =>
            simp[hx, hy]
        }
        · {
          apply hc.right
          rw[GRectangle.mem_enum_iff]
          apply half_ext1loop_edge_mem_ehex
          exact h
        }
      }
      | inr h => {
        have h':=List.mem_rotate.mp (List.mem_of_mem_tail h)
        have h'':=h'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at h'
        refine ⟨Or.inr h'.left, ?_⟩
        rw[ext1Hp] at hc
        constructor
        · {
          have hls:=m.ring_simple
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hls
          rw[←List.map_rotate] at hls'
          have h3'_lemma : m.ring.rotate (List.idxOf (edge d) m.ring) ≠ [] := by{
            rw[ne_eq, List.eq_nil_iff_length_eq_zero]
            simp[m.ring_ne_nil]
          }
          rw[←List.cons_head_tail h3'_lemma] at hls'
          rw[List.map_cons, List.nodup_cons, List.head_rotate_idxOf (edge_mem_ring hc)] at hls'
          have hls'':=hls'.left
          rw[List.mem_map, not_exists] at hls''
          simp only [not_and] at hls''
          have hls0:=hls'' _ h
          have hld:=m.ring_nodup
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge d))).mpr hld
          rw[←List.cons_head_tail h3'_lemma, List.nodup_cons] at hld'
          have he:=edge_mem_ring hc
          rw[List.head_rotate_idxOf he] at hld'
          have hld'':=hld'.left
          rw[half_eq_cases_face, not_or, not_or, not_or]
          constructor
          · {
            intro h
            apply hls0
            rw[←h, edge_2]
          }
          rw[mem_ring_iff_mem_disk_border] at h''
          constructor
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2] at h
            rw[h] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply half_mem_ehex_of_end0_eq_end0_face_face
            rw[edge_end0, face_end0]
          }
          constructor
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2] at h
            rw[h] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply half_mem_ehex_of_end0_eq_end0_face_3
            rw[edge_end0, face_end0]
          }
          · {
            intro h
            apply congrArg edge at h
            rw[edge_2, face_3, edge_2] at h
            rw[h] at h''
            have hc':=hc.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply half_node_mem_ehex
          }
        }
        exact h'.right
      }
    }
    · {
      intro ⟨h0, h1, h2⟩
      cases h0 with
      | inl h0 => {
        left
        rw[half_eq_cases_face] at h0
        simp only [ext1loop, List.mem_cons, List.not_mem_nil, or_false]
        apply h0.resolve_left
        rw[ext1Hp] at hc
        intro h
        apply h2
        exact h ▸ hc.left
      }
      | inr h0 => {
        right
        have h3 : x ∈ m.ring := by{
          rw[mem_ring_iff_mem_disk_border]
          exact ⟨h0, h2⟩
        }
        have h3':=(List.mem_rotate (n:=m.ring.idxOf (edge d))).mpr h3
        have h3'_lemma : m.ring.rotate (List.idxOf (edge d) m.ring) ≠ [] := by{
          rw[ne_eq, List.eq_nil_iff_length_eq_zero]
          simp[m.ring_ne_nil]
        }
        rw[←List.cons_head_tail h3'_lemma] at h3'
        rw[List.mem_cons] at h3'
        apply h3'.resolve_left
        rw[List.head_rotate_idxOf (edge_mem_ring hc)]
        intro h
        apply h1
        rw[h, edge_2]
      }
    }
  }

end Extend1

def extend1 {m : Matte} {d : GDart} (hd : Extend1.ext1Hp m d) : Matte where
  disk := Extend1.ext1Disk m d
  ring := Extend1.ext1Ring m d
  disk_ne_nil := Extend1.ext1Disk_ne_nil
  ring_cycle := Extend1.ext1Ring_cycleChain hd
  ring_simple := Extend1.ext1Ring_simple hd
  mem_ring_iff_mem_disk_border:=Extend1.mem_ext1Ring_iff hd

namespace Extend2

def ext2Hp (m : Matte) (d : GDart) : Prop :=
  (edge d).half ∈ m ∧ (edge (face d)).half ∈ m ∧ m.disk.Disjoint (equad d).enum
def ext2loop (d : GDart) := [face (face d), face (face (face d))]
abbrev ext2Disk := extDisk
def ext2Ring (m : Matte) (d : GDart) :=
  ext2loop d ++ (m.ring.rotate (m.ring.idxOf (edge (face d)))).drop 2

theorem ext2Disk_ne_nil {m : Matte} {d : GDart} : ext2Disk m d ≠ [] := by{simp[extDisk]}
theorem ext2Ring_ne_nil {m : Matte} {d : GDart} : ext2Ring m d ≠ [] := by{simp[ext2Ring, ext2loop]}

theorem half_not_mem {m : Matte} {d : GDart} (h : ext2Hp m d)
  : d.half ∉ m := by{
    rw[ext2Hp] at h
    intro h'
    have ih:=h.right.right h'
    apply ih
    rw[GRectangle.mem_enum_iff]
    apply half_mem_equad
  }
theorem edge_face_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
  : edge (face d) ∈ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2, face_half]
    rw[ext2Hp] at h
    apply And.intro h.right.left
    apply half_not_mem h
  }
theorem edge_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
  : edge d ∈ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2]
    rw[ext2Hp] at h
    apply And.intro h.left
    apply half_not_mem h
  }
theorem face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: face d ∉ m.ring:= by{
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, not_and, face_half]
  have h:=half_not_mem h
  rw[mem_iff] at h
  simp[h]
}
theorem node_2_face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: node (node (face d)) ∉ m.ring:= by{
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, not_and]
  intro _
  rw[not_not]
  rw[←face_half, fen_cancel, ←edge_eq_node_face]
  exact h.left
}
lemma ef_ne_e (d : GDart) : edge (face d) ≠ edge d := by{
    intro hn
    apply congrArg GPoint.half at hn
    rw[edge_half, face_half, face_mod2, edge_half] at hn
    rw[add_sub_assoc, add_sub_assoc, add_assoc, add_assoc, add_left_cancel_iff] at hn
    rw[←add_sub_assoc, ←add_sub_assoc] at hn
    apply congrArg (· + ⟨1, 1⟩) at hn
    rw[sub_add_cancel, sub_add_cancel, add_comm, add_left_cancel_iff] at hn
    apply GPoint.ccw_2_ne hn
  }
lemma fef_ne_e (d : GDart) : face (edge (face d)) ≠ edge d := by{
    intro hn
    apply congrArg GPoint.half at hn
    rw[face_half, edge_half, face_half, face_mod2, edge_half] at hn
    rw[add_sub_assoc, add_sub_assoc, add_assoc, add_assoc, add_left_cancel_iff] at hn
    rw[←add_sub_assoc, ←add_sub_assoc] at hn
    apply congrArg (· + ⟨1, 1⟩) at hn
    rw[sub_add_cancel, sub_add_cancel, add_comm, add_left_cancel_iff] at hn
    apply GPoint.ccw_2_ne hn
  }
theorem node_3_face_not_mem_ring {m : Matte} {d : GDart} (h : ext2Hp m d)
: node (node (node (face d))) ∉ m.ring:= by{
  rw[node_3]
  intro h0
  have h1:end0 (face (edge (face d))) = end0 (edge d) := by{
    rw[face_end0, edge_end1, face_end0, edge_end0]
  }
  have h2:face (edge (face d)) ≠ edge d := fef_ne_e d
  have hs := m.ring_simple
  rw[List.nodup_map_iff_inj_on m.ring_nodup] at hs
  have hs':=hs _ h0 _ (edge_mem_ring h) h1
  exact h2 hs'
}
theorem edge_face_next {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring[(m.ring.idxOf (edge (face d)) + 1) % m.ring.length]'(by{
    apply Nat.mod_lt
    apply List.length_pos_of_ne_nil
    exact m.ring_ne_nil
  }) = edge d := by{
    have hlc := m.ring_cycle
    rw[List.isCycleChain_iff_getElem m.ring_ne_nil] at hlc
    have hlc':=hlc (m.ring.idxOf (edge (face d)))
    have hef := edge_face_mem_ring h
    simp only [Nat.mod_eq_of_lt (List.idxOf_lt_length_of_mem hef)] at hlc'
    rw[List.getElem_idxOf] at hlc'
    rw[mrlink, edge_end1] at hlc'
    nth_rw 3 [edge_eq_node_face]
    symm at hlc'
    rw[end0_eq_cases_node] at hlc'
    have h0:=face_not_mem_ring h
    have h2:=node_2_face_not_mem_ring h
    have h3:=node_3_face_not_mem_ring h
    rcases hlc' with hlc' | hlc' | hlc' | hlc'
    · rw[←hlc'] at h0; simp at h0
    · rw[hlc']
    · rw[←hlc'] at h2; simp at h2
    · rw[←hlc'] at h3; simp at h3
  }
theorem ring_length_ge_2 {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring.length ≥ 2 := by{
    have h0:=edge_face_mem_ring h
    have h1:=edge_mem_ring h
    have h2:=ef_ne_e d
    have h3:=List.length_erase_add_one h0
    have h5:=(m.ring_nodup.mem_erase_iff).mpr ⟨h2.symm, h1⟩
    have h6:=List.length_erase_add_one h5
    rw[←h3, ←h6]
    simp
  }
theorem ring_length_gt_2 {m : Matte} {d : GDart} (h : ext2Hp m d)
  : m.ring.length > 2 := by{
    have h0:=ring_length_ge_2 h
    have h1:=edge_face_mem_ring h
    have h2:=edge_mem_ring h
    have h3:=ef_ne_e d
    apply lt_of_le_of_ne h0
    have hlc:=m.ring_cycle
    generalize hmr : m.ring = mr
    rw[hmr] at hlc h0 h1 h2
    match mr with
    | [a, b] => {
      exfalso
      simp only [List.IsCycleChain, reduceCtorEq, ↓reduceDIte, List.isChain_cons_cons,
        List.IsChain.singleton, and_true, ne_eq, List.cons_ne_self, not_false_eq_true,
        List.getLast_cons, List.getLast_singleton, List.head_cons] at hlc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
      cases h1 with
      | inl h1 => {
        have h2:=h2.resolve_left (by{intro h; simp[←h, h3] at h1})
        have hlc':=hlc.right
        rw[mrlink, ←h2, ←h1] at hlc'
        rw[edge_end0, edge_end1, end0, end1, face_half, face_mod2] at hlc'
        rw[add_left_cancel_iff] at hlc'
        symm at hlc'
        apply GPoint.ccw_2_ne hlc'
      }
      | inr h1 => {
        have h2:=h2.resolve_right (by{intro h; simp[←h, h3] at h1})
        have hlc':=hlc.left
        rw[mrlink, ←h2, ←h1] at hlc'
        rw[edge_end0, edge_end1, end0, end1, face_half, face_mod2] at hlc'
        rw[add_left_cancel_iff] at hlc'
        symm at hlc'
        apply GPoint.ccw_2_ne hlc'
      }
    }
    | _::_::_::_ => simp
  }

theorem end0_face_3_not_mem_ring_end0 {m : Matte} {d : GDart} (hc : ext2Hp m d)
: end0 (face (face (face d))) ∉ m.ring.map end0 := by{
  rw[List.mem_map, not_exists]
  simp only [not_and]
  intro x hx hxf
  rw[ext2Hp] at hc
  rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  have hc':=hc.right.right hx.left
  apply hc'
  rw[GRectangle.mem_enum_iff]
  apply half_mem_equad_of_end0_eq_end0_face_3
  exact hxf
}

theorem ext2loop_disjoint_ring {m : Matte} {d : GDart} (hc : ext2Hp m d)
  : (ext2loop d).Disjoint m.ring := by{
    intro x hx
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf]
    simp only [imp_false, not_and, Decidable.not_not]
    rw[ext2Hp] at hc
    intro hx'
    have hx'':=hc.right.right hx'
    simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at hx
    exfalso
    apply hx''
    rcases hx with hx | hx
    all_goals
    rw[GRectangle.mem_enum_iff, hx]
    simp[face_half, half_mem_equad]
  }
theorem half_ext2loop_edge_mem_equad {d : GDart} : ∀x ∈ ext2loop d, (edge x).half ∈ equad d := by{
  intro x hx
  simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx
  · {
    rw[hx]
    apply half_mem_equad_of_end0_eq_end0_face_3
    rw[edge_end0, face_end0]
  }
  · {
    rw[hx, face_3, edge_2]
    apply half_node_mem_equad
  }
}

theorem ext2loop_map_end0_nodup {d : GDart} : ((ext2loop d).map end0).Nodup := by{
  simp[ext2loop, face_end0_ne_end0.symm]
}
theorem ext2loop_nodup {d : GDart} : (ext2loop d).Nodup := by{
  apply List.Nodup.of_map end0
  exact ext2loop_map_end0_nodup
}
theorem ext2loop_ne_nil {d : GDart} : ext2loop d ≠ [] := by{simp[ext2loop]}
theorem head_ext2loop {d : GDart} : (ext2loop d).head ext2loop_ne_nil = face (face d) := rfl
theorem getLast_ext2loop {d : GDart} : (ext2loop d).getLast ext2loop_ne_nil = face (face (face d))
  := rfl
theorem ext2loop_isChain_mrlink {d : GDart} : (ext2loop d).IsChain mrlink := by{
  simp[ext2loop, mrlink_face]
}
theorem ext2Ring_getLast {m : Matte} {d : GDart} (h : ext2Hp m d)
: (ext2Ring m d).getLast ext2Ring_ne_nil =
  (m.ring.rotate (m.ring.idxOf (edge (face d)))).getLast (by{simp[m.ring_ne_nil]}) := by{
    simp only [ext2Ring]
    have h':List.drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring)) ≠ [] := by{
      simp[ring_length_gt_2 h]
    }
    rw[List.getLast_append_of_right_ne_nil _ _ h']
    rw[List.getLast_drop]
  }
theorem ext2Ring_head {m : Matte} {d : GDart}
: (ext2Ring m d).head ext2Ring_ne_nil = face (face d) := by{
    simp only [ext2Ring]
    rw[List.head_append_left ext2loop_ne_nil, head_ext2loop]
  }

theorem ext2Ring_chain {m : Matte} {d : GDart} (h : ext2Hp m d)
  : (ext2Ring m d).IsChain mrlink := by{
  rw[ext2Ring, List.isChain_append]
  apply And.intro ext2loop_isChain_mrlink
  have hc := m.ring_cycle
  have hc':=m.ring_cycle.rotate (m.ring.idxOf (edge (face d)))
  rw[List.IsCycleChain] at hc'
  rw[dite_cond_eq_false (by{simp[m.ring_ne_nil]})] at hc'
  apply And.intro (hc'.left.drop _)
  rw[List.getLast?_eq_some_getLast ext2loop_ne_nil]
  simp only [Option.mem_def, Option.some.injEq, List.head?_drop, forall_eq']
  rw[List.getElem?_eq_some_getElem (by{simp[ring_length_gt_2 h]})]
  simp only [List.getElem_rotate, Option.some.injEq, forall_eq']
  rw[getLast_ext2loop]
  have h0:=edge_face_next h
  have hc'':=(List.isCycleChain_iff_getElem m.ring_ne_nil).mp hc
    (m.ring.idxOf (edge (face d)) + 1)
  rw[h0] at hc''
  rw[mrlink]
  rw[mrlink] at hc''
  simp only [add_assoc, Nat.reduceAdd] at hc''
  simp only [add_comm (b:=2)] at hc''
  rw[←hc'', face_3, edge_end1, edge_end1, node_end0]
}
theorem ext2Ring_cycleChain {m : Matte} {d : GDart} (h : ext2Hp m d)
  : (ext2Ring m d).IsCycleChain mrlink := by{
    rw[List.IsCycleChain]
    rw[dite_cond_eq_false (by{simp[ext2Ring_ne_nil]})]
    apply And.intro (ext2Ring_chain h)
    rw[ext2Ring_getLast h, ext2Ring_head]
    have hc := m.ring_cycle
    have hc':=m.ring_cycle.rotate (m.ring.idxOf (edge (face d)))
    rw[List.IsCycleChain] at hc'
    rw[dite_cond_eq_false (by{simp[m.ring_ne_nil]})] at hc'
    have hc'':=hc'.right
    rw[List.head_rotate_idxOf (edge_face_mem_ring h), mrlink] at hc''
    rw[mrlink, hc'', edge_end0, face_end0]
  }

lemma take_two {m : Matte} {d : GDart} (h : ext2Hp m d) :
List.take 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))
= [edge (face d), edge d] := by{
  rw[←List.cons_head_tail (by{simp[m.ring_ne_nil]}
  : m.ring.rotate (List.idxOf (edge (face d)) m.ring) ≠ [])]
  rw[List.take_succ_cons]
  simp only [List.cons.injEq, List.head_rotate_idxOf (edge_face_mem_ring h), true_and]
  rw[←List.cons_head_tail (by{
    rw[ne_eq, List.eq_nil_iff_length_eq_zero]
    simp only [List.length_tail, List.length_rotate]
    intro h'
    apply Nat.le_of_sub_eq_zero at h'
    have h'':=ring_length_gt_2 h
    have h''':=lt_of_lt_of_le h'' h'
    simp at h'''
  } : (m.ring.rotate (List.idxOf (edge (face d)) m.ring)).tail ≠ [])]
  rw[List.take_succ_cons, List.take_zero]
  simp only [List.head_tail, List.getElem_rotate, List.cons.injEq, and_true]
  simp only [add_comm 1, edge_face_next h]
}

theorem ext2Ring_simple {m : Matte} {d : GDart} (h : ext2Hp m d)
  : ((ext2Ring m d).map end0).Nodup := by{
    rw[List.nodup_map_iff_inj_on]
    · {
      have hls:=m.ring_simple
      have hld:=m.ring_nodup
      have he:=edge_mem_ring h
      have hef:=edge_face_mem_ring h
      intro x hx y hy hxy
      rw[ext2Ring, List.mem_append] at hx hy
      wlog hx': x ∈ ext2loop d generalizing x y with H
      · {
        apply (Or.resolve_left · hx') at hx
        cases hy with
        | inl hy => {
          have H':=H y (Or.inl hy) x (Or.inr hx) hxy.symm hy
          exact H'.symm
        }
        | inr hy => {
          have hx':=List.mem_of_mem_drop hx
          have hy':=List.mem_of_mem_drop hy
          have hls':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hls
          rw[←List.map_rotate, List.nodup_map_iff_inj_on] at hls'
          · exact hls' _ hx' _ hy' hxy
          simp[hld]
        }
      }
      cases hy with
      | inl hy => {
        have hls':=ext2loop_map_end0_nodup (d:=d)
        rw[List.nodup_map_iff_inj_on] at hls'
        · exact hls' _ hx' _ hy hxy
        apply ext2loop_nodup
      }
      | inr hy => {
        rw[ext2Hp] at h
        have hy':=List.mem_rotate.mp (List.mem_of_mem_drop hy)
        have hy'':=hy'
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hy'
        have hc':=h.right.right hy'.left
        rw[GRectangle.mem_enum_iff] at hc'
        rw[ext2loop] at hx'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
        exfalso
        rcases hx' with hx' | hx'
        · {
          have hyd : y = edge (face d) := by{
            have h0:end0 (edge (face d)) = end0 x:=by{
              rw[hx', edge_end0, face_end0]
            }
            rw[hxy] at h0
            rw[List.nodup_map_iff_inj_on hld] at hls
            have hls':=hls _ hef _ hy'' h0
            rw[hls']
          }
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hld
          rw[←List.take_append_drop 2
            (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at hld'
          have h_take := take_two h
          rw[h_take, List.nodup_append'] at hld'
          apply (hld'.right.right · hy)
          simp[hyd]
        }
        · {
          apply hc'
          apply half_mem_equad_of_end0_eq_end0_face_3
          rw[←hx', hxy]
        }
      }
    }
    · {
      rw[ext2Ring, List.nodup_append']
      apply And.intro ext2loop_nodup
      apply And.intro (List.nodup_drop (List.nodup_rotate.mpr m.ring_nodup))
      apply List.disjoint_of_subset_right (List.drop_subset _ _)
      rw[List.disjoint_rotate_right]
      apply ext2loop_disjoint_ring h
    }
  }

theorem mem_ext2Ring_iff {m : Matte} {d : GDart} (h : ext2Hp m d)
  : ∀x, x ∈ ext2Ring m d ↔ x ∈ border (ext2Disk m d) := by{
    intro x
    rw[ext2Ring, List.mem_append]
    rw[ext2Disk, extDisk, border, Set.mem_setOf, List.mem_cons, List.mem_cons, not_or]
    constructor
    · {
      intro h'
      cases h' with
      | inl h' => {
        constructor
        · {
          left
          simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at h'
          rcases h' with h' | h'
          all_goals
          simp[h', face_half]
        }
        rw[ext2Hp, List.disjoint_comm] at h
        constructor
        · {
          rw[edge_half]
          simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false] at h'
          rcases h' with h' | h'
          all_goals
          simp only [h', face_half, face_mod2, add_sub_assoc, add_assoc, add_eq_left]
          simp only [←add_sub_assoc, sub_eq_zero]
          simp only [GPoint.add_def, GPoint.ext_iff,
          GPoint.x_ccw, GPoint.y_ccw, GPoint.x_mod2, GPoint.y_mod2]
          cases Int.emod_two_eq d.x with | inl hx | inr hx =>
          cases Int.emod_two_eq d.y with | inl hy | inr hy =>
            simp[hx, hy]
        }
        · {
          apply h.right.right
          rw[GRectangle.mem_enum_iff]
          apply half_ext2loop_edge_mem_equad
          exact h'
        }
      }
      | inr h' => {
        have h'':=List.mem_rotate.mp (List.mem_of_mem_drop h')
        have h''':=h''
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at h''
        refine ⟨Or.inr h''.left, ?_⟩
        rw[ext2Hp] at h
        constructor
        · {
          have hld:=m.ring_nodup
          have hld':=(List.nodup_rotate (n:=m.ring.idxOf (edge (face d)))).mpr hld
          rw[←List.take_append_drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at hld'
          rw[take_two h, List.nodup_append'] at hld'
          rw[half_eq_cases_face, not_or, not_or, not_or]
          have hls'':=(hld'.right.right · h')
          simp only [List.mem_cons, List.not_mem_nil, or_false, imp_false, not_or] at hls''
          rw[←edge_inj (x:=x), ←edge_inj (x:=x), edge_2, edge_2] at hls''
          simp only [hls'', not_false_eq_true, true_and]
          constructor
          · {
            intro h0
            apply congrArg edge at h0
            rw[edge_2] at h0
            rw[h0] at h'''
            have hc':=h.right.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply half_mem_equad_of_end0_eq_end0_face_3
            rw[h0, edge_end0, face_end0]
          }
          · {
            intro h0
            apply congrArg edge at h0
            rw[edge_2, face_3, edge_2] at h0
            rw[h0] at h''
            have hc':=h.right.right h''.left
            apply hc'
            rw[GRectangle.mem_enum_iff]
            apply half_node_mem_equad
          }
        }
        · exact h''.right
      }
    }
    · {
      intro ⟨h0, h1, h2⟩
      cases h0 with
      | inl h0 => {
        left
        rw[half_eq_cases_face] at h0
        simp only [ext2loop, List.mem_cons, List.not_mem_nil, or_false]
        rw[←or_assoc] at h0
        apply h0.resolve_left
        rw[ext2Hp] at h
        intro h'
        apply h2
        rcases h' with h' | h'
        · rw[h']; exact h.left
        · rw[h']; exact h.right.left
      }
      | inr h0 => {
        right
        have h3 : x ∈ m.ring := by{
          rw[mem_ring_iff_mem_disk_border]
          exact ⟨h0, h2⟩
        }
        have h3':=(List.mem_rotate (n:=m.ring.idxOf (edge (face d)))).mpr h3
        rw[←List.take_append_drop 2 (m.ring.rotate (List.idxOf (edge (face d)) m.ring))] at h3'
        rw[List.mem_append] at h3'
        apply h3'.resolve_left
        rw[take_two h]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor
        · {
          intro h
          apply h1
          rw[h, edge_2, face_half]
        }
        · {
          intro h
          apply h1
          rw[h, edge_2]
        }
      }
    }
  }

end Extend2

def extend2 {m : Matte} {d : GDart} (hd : Extend2.ext2Hp m d) : Matte where
  disk := Extend2.ext2Disk m d
  ring := Extend2.ext2Ring m d
  disk_ne_nil := Extend2.ext2Disk_ne_nil
  ring_cycle := Extend2.ext2Ring_cycleChain hd
  ring_simple := Extend2.ext2Ring_simple hd
  mem_ring_iff_mem_disk_border:=Extend2.mem_ext2Ring_iff hd

inductive Extension (m : Matte) : Matte → Prop
| refl : Extension m m
| step {d : GDart} {xm0 xm : Matte} (hme  : Extension m xm0)
  (hdr : edge d ∈ xm0.ring) (hdisk : ∀x, x ∈ xm ↔ x ∈ extDisk xm0 d)
  : Extension m xm

theorem Extension.subset {m xm : Matte} (h : Extension m xm) : m.disk ⊆ xm.disk := by{
  induction h with
  | refl => apply List.Subset.refl
  | step hme hdr hdisk ih => {
    apply ih.trans
    intro x
    simp only [mem_iff] at hdisk
    simp only [hdisk, extDisk, List.mem_cons]
    apply Or.inr
  }
}
theorem Extension.extend1 {m : Matte} {d : GDart} (ext1p : Extend1.ext1Hp m d)
  : Extension m (extend1 ext1p) :=by{
    rw[Extend1.ext1Hp] at ext1p
    apply Extension.step (d:=d) (xm0:=m)
    · apply Extension.refl
    · {
      rw[m.mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2]
      refine ⟨ext1p.left, ext1p.right.symm ?_⟩
      rw[GRectangle.mem_enum_iff]
      apply half_mem_ehex
    }
    · simp[Matte.extend1, mem_iff, Extend1.ext1Disk]
  }
theorem Extension.extend2 {m : Matte} {d : GDart} (ext2p : Extend2.ext2Hp m d)
  : Extension m (extend2 ext2p) := by{
    rw[Extend2.ext2Hp] at ext2p
    apply Extension.step (d:=d) (xm0:=m)
    · apply Extension.refl
    · {
      rw[m.mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2]
      refine ⟨ext2p.left, ext2p.right.right.symm ?_⟩
      rw[GRectangle.mem_enum_iff]
      apply half_mem_equad
    }
    · simp[Matte.extend2, mem_iff, Extend2.ext2Disk]
  }

def extendsIn (m : Matte) (r : GRectangle) (p : GPixel) : Prop :=
  ∃xm, Extension m xm ∧ xm.disk ⊆ r.enum ∪ m.disk ∧ p ∈ xm
theorem extendsIn_of_subset {m : Matte} {r1 r2 : GRectangle} (hr : r1 ⊆ r2)
  : ∀p, extendsIn m r1 p → extendsIn m r2 p := by{
    intro p h
    let ⟨xm, ext, sub, con⟩ := h
    refine ⟨xm, ext, fun q hq => (List.mem_union_iff.mp (sub hq)).elim
      (fun hr1 => by{
        apply List.mem_union_left
        rw[GRectangle.mem_enum_iff]
        rw[GRectangle.mem_enum_iff] at hr1
        exact hr hr1
      }) (by{
        intro h
        apply List.mem_union_right
        exact h
      }), con⟩
  }
theorem extendsIn_of_mem {m : Matte} (r : GRectangle) {p : GPixel} (hp : p ∈ m)
  : extendsIn m r p := by{
    use m
    apply And.intro Extension.refl
    apply And.intro List.subset_union_right
    exact hp
  }
theorem extendsIn_of_extend1 {m : Matte} {r : GRectangle} {d : GDart}
  (ext1p : Extend1.ext1Hp m d) (hdr : d.half ∈ r) : extendsIn m r d.half := by{
    use extend1 ext1p
    refine ⟨Extension.extend1 ext1p, ?_, ?_⟩
    · {
      simp only [extend1, Extend1.ext1Disk, extDisk]
      intro x
      simp only [List.mem_cons, List.mem_union_iff]
      apply Or.imp_left
      intro h
      simp[h, GRectangle.mem_enum_iff, hdr]
    }
    · {
      rw[mem_iff, extend1]
      simp[Extend1.ext1Disk, extDisk]
    }
  }
theorem extendsIn_of_extend2 {m : Matte} {r : GRectangle} {d : GDart}
  (ext2p : Extend2.ext2Hp m d) (hdr : d.half ∈ r) : extendsIn m r d.half := by{
    use extend2 ext2p
    refine ⟨Extension.extend2 ext2p, ?_, ?_⟩
    · {
      simp only [extend2, Extend2.ext2Disk, extDisk]
      intro x
      simp only [List.mem_cons, List.mem_union_iff]
      apply Or.imp_left
      intro h
      simp[h, GRectangle.mem_enum_iff, hdr]
    }
    · {
      rw[mem_iff, extend2]
      simp[Extend2.ext2Disk, extDisk]
    }
  }

def coarseIn (r : GRegion) (m : Matte) :=
  ∀p ∈ r, ∀q, q.half = p.half → (q ∈ m ↔ p ∈ m)
theorem coarseIn_zoom {r : GRegion} {m : Matte} :
  coarseIn r m.zoom := by{
    rw[coarseIn]
    simp only [mem_zoom_iff]
    intro _ _ _ hqp
    rw[hqp]
  }
theorem coarseIn_of_subset {r0 r1 : GRegion} {m : Matte}
  (hr : r0 ⊆ r1) : coarseIn r1 m → coarseIn r0 m := by{
    intro h p hpr q hqp
    apply h p (hr hpr) _ hqp
  }

lemma extendsIn_ehex {m : Matte} {r : GRectangle}
  {p : GPixel} (hpr : p ∈ r) {d : GDart} (hdp : d.half = p)
  (hehex : m.disk.Disjoint (ehex d).enum) (ih : extendsIn m (chopRect r (edge d)) (edge d).half)
  : extendsIn m r p := by{
    have ⟨xm, hxme, hxms, hxmp⟩ := ih
    have hpm : p ∉ m := by{
      rw[←hdp]
      apply hehex.symm
      rw[GRectangle.mem_enum_iff]
      apply half_mem_ehex
    }
    have hext1 : Extend1.ext1Hp xm d := by{
      rw[Extend1.ext1Hp]
      apply And.intro hxmp
      apply List.disjoint_of_subset_left hxms
      rw[List.disjoint_union_left]
      refine ⟨?_, hehex⟩
      rw[List.Disjoint]
      simp only [imp_false, GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion]
      simp only [chopRect_toRegion, Set.mem_inter_iff]
      intro a ⟨_, ha⟩
      have h:=ehex_disjoint_edge_chop (d:=d)
      rw[Set.disjoint_iff_forall_ne] at h
      intro ha'
      have h':=h ha' ha
      exact h' rfl
    }
    use xm.extend1 hext1
    constructor
    · {
      apply Extension.step (xm0:=xm) (d:=d)
      · apply hxme
      · {
        rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf, edge_2, hdp]
        refine ⟨hxmp, ?_⟩
        rw[Extend1.ext1Hp] at hext1
        apply hext1.right.symm
        rw[←hdp, GRectangle.mem_enum_iff]
        apply half_mem_ehex
      }
      · simp[extDisk, extend1, mem_iff]
    }
    constructor
    · {
      rw[extend1]
      simp only [Extend1.ext1Disk, extDisk]
      simp only [List.cons_subset, List.mem_union_iff]
      constructor
      · {
        left
        simp only [hdp, GRectangle.mem_enum_iff, hpr]
      }
      · {
        apply hxms.trans
        intro x
        simp only [List.mem_union_iff]
        apply Or.imp_left
        simp only [GRectangle.mem_enum_iff]
        apply chopRect_subset_rect
      }
    }
    · {
      rw[extend1, mem_iff]
      simp only [Extend1.ext1Disk, extDisk, ←hdp, List.mem_cons, true_or]
    }
  }

end extend_matte
end Matte
end GridPlane
