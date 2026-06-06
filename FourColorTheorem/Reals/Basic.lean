import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Dynamics.PeriodicPts.Defs

/- Definitions for points, regions, and maps in the real plane -/

open Function
open Relation

namespace RealPlane

@[ext] structure Point where
  x : ℝ
  y : ℝ
def Point.toProd : Point → ℝ × ℝ
| ⟨x, y⟩ => ⟨x, y⟩
def Point.ofProd : ℝ × ℝ → Point
| ⟨x, y⟩ => ⟨x, y⟩
def Point.equivProd : Point ≃ ℝ × ℝ where
  toFun:=toProd
  invFun:=ofProd
@[implicit_reducible] instance Point.instAddCommGroup : AddCommGroup Point
  := equivProd.addCommGroup

abbrev Region:=Set Point
abbrev Map:=Point → Region
structure Interval where
  lb : ℝ
  ub : ℝ
structure Rectangle where
  hspan : Interval
  vspan : Interval

theorem Map.mem_map_apply_iff {m : Map} {p1 p2 : Point}
  : p2 ∈ m p1 ↔ m p1 p2 := by rfl
theorem Map.map_apply_iff_mem {m : Map} {p1 p2 : Point}
  : m p1 p2 ↔ p2 ∈ m p1 := by rfl

def Interval.toSet (I : Interval) : Set ℝ := {x | I.lb < x ∧ x < I.ub}
def Interval.Mem (I : Interval) (x : ℝ) : Prop := x ∈ I.toSet
@[inline] instance Interval.instMembership : Membership ℝ Interval where mem := Interval.Mem
theorem Interval.mem_iff (I : Interval) (x : ℝ) : x ∈ I ↔ I.lb < x ∧ x < I.ub := by rfl
theorem Interval.mem_iff_toSet (I : Interval) (x : ℝ) : x ∈ I ↔ x ∈ I.toSet := by rfl
def Rectangle.toRegion (R : Rectangle) : Region := {p | p.x ∈ R.hspan ∧ p.y ∈ R.vspan}
def Rectangle.Mem (R : Rectangle) (p : Point) : Prop := p ∈ R.toRegion
@[inline] instance Rectangle.instMembership :
  Membership Point Rectangle where mem := Rectangle.Mem
theorem Rectangle.mem_iff (R : Rectangle) (p : Point) :
  p ∈ R ↔ p.x ∈ R.hspan ∧ p.y ∈ R.vspan := by rfl
theorem Rectangle.mem_iff_toRegion (R : Rectangle) (p : Point) :
  p ∈ R ↔ p ∈ R.toRegion := by rfl

def Interval.inter : Interval → Interval → Interval
| ⟨x0, x1⟩, ⟨y0, y1⟩ => ⟨max x0 y0, min x1 y1⟩
@[inline] instance Interval.instInter : Inter Interval := ⟨inter⟩
theorem Interval.inter_toSet {I1 I2 : Interval}
  : (I1 ∩ I2).toSet = I1.toSet ∩ I2.toSet := by{
    change (I1.inter I2).toSet = _
    ext x
    simp[toSet, inter]
    tauto
  }
theorem Interval.mem_inter_iff {I1 I2 : Interval} {x : ℝ}
  : x ∈ I1 ∩ I2 ↔ x ∈ I1 ∧ x ∈ I2 := by{
    simp only [mem_iff_toSet, inter_toSet, Set.mem_inter_iff]
  }
theorem Interval.inter_lb {I1 I2 : Interval}
  : (I1 ∩ I2).lb = max I1.lb I2.lb := rfl
theorem Interval.inter_ub {I1 I2 : Interval}
  : (I1 ∩ I2).ub = min I1.ub I2.ub := rfl
def Rectangle.inter : Rectangle → Rectangle → Rectangle
| ⟨r0x, r0y⟩, ⟨r1x, r1y⟩ => ⟨r0x ∩ r1x, r0y ∩ r1y⟩
@[inline] instance Rectangle.instInter : Inter Rectangle := ⟨inter⟩
theorem Rectangle.inter_toRegion {R1 R2 : Rectangle}
  : (R1 ∩ R2).toRegion = R1.toRegion ∩ R2.toRegion := by{
    change (R1.inter R2).toRegion = _
    ext x
    simp[toRegion, inter, Interval.mem_inter_iff]
    tauto
  }
theorem Rectangle.mem_inter_iff {R1 R2 : Rectangle} {x : Point}
  : x ∈ R1 ∩ R2 ↔ x ∈ R1 ∧ x ∈ R2 := by{
    simp only [mem_iff_toRegion, inter_toRegion, Set.mem_inter_iff]
  }
noncomputable def sepInterval (x1 x2 : ℝ) : Interval :=
  let w := (x1 + x2) / 2
  ⟨if x2 ≤ w then x2 - 1 else w, if x2 ≥ w then x2 + 1 else w⟩
theorem right_mem_sepInterval {x1 x2 : ℝ}
  : x2 ∈ sepInterval x1 x2 := by{
    rcases lt_trichotomy x2 ((x1 + x2) / 2) with h | h | h
    all_goals
    simp[sepInterval, Interval.mem_iff]
    try simp[le_of_lt h, not_le_of_gt h]
    try simp[h.symm]
    try simp[h]
  }
theorem left_notMem_sepInterval_of_ne {x1 x2 : ℝ}
  (h12 : x1 ≠ x2) : x1 ∉ sepInterval x1 x2 := by{
    rcases lt_trichotomy x2 ((x1 + x2) / 2) with h | h | h
    · {
      simp only [sepInterval, ge_iff_le, Interval.mem_iff, not_and, not_lt]
      simp only [le_of_lt h, ↓reduceIte, not_le_of_gt h]
      rw[lt_div_iff₀ (by{simp}), mul_two, add_lt_add_iff_right] at h
      rw[div_le_iff₀ (by{simp}), mul_two, add_le_add_iff_left]
      simp[le_of_lt h]
    }
    · {
      rw[eq_div_iff (by{simp}), mul_two, add_right_cancel_iff, Eq.comm] at h
      contradiction
    }
    · {
      simp only [sepInterval, ge_iff_le, Interval.mem_iff, not_and, not_lt]
      simp only [le_of_lt h, ↓reduceIte, not_le_of_gt h]
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_right] at h
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_left]
      simp[not_lt_of_gt h]
    }
  }
theorem sepInterval_antisymm' {x y t : ℝ} (htxy : t ∈ sepInterval x y)
  (htyx : t ∈ sepInterval y x) : x = y := by{
    apply of_not_not
    intro h
    wlog hxy : x < y with H
    · exact H htyx htxy (Ne.symm h) ((lt_or_gt_of_ne h).resolve_left hxy)
    have hxw : x < (y + x) / 2 := by{
      rw[lt_div_iff₀ (by{simp}), mul_two, add_lt_add_iff_right]
      exact hxy
    }
    have hwy : (x + y) / 2 < y := by{
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_right]
      exact hxy
    }
    simp only [sepInterval, not_le_of_gt hwy, ↓reduceIte, ge_iff_le, le_of_lt hwy,
      Interval.mem_iff] at htxy
    simp only [sepInterval, not_le_of_gt hxw, ↓reduceIte, le_of_lt hxw,
      Interval.mem_iff] at htyx
    rw[add_comm] at htyx
    apply lt_asymm htyx.2 htxy.1
  }
noncomputable def sepRectangle : Point → Point → Rectangle
| ⟨x0, y0⟩, ⟨x1, y1⟩ => ⟨sepInterval x0 x1, sepInterval y0 y1⟩
theorem right_mem_sepRectangle {p1 p2 : Point}
  : p2 ∈ sepRectangle p1 p2 := by{
    match p1, p2 with | ⟨x1, y1⟩, ⟨x2, y2⟩ => {
      rw[sepRectangle, Rectangle.mem_iff]
      exact ⟨right_mem_sepInterval, right_mem_sepInterval⟩
    }
  }
theorem left_notMem_sepRectangle_of_ne {p1 p2 : Point}
  (h12 : p1 ≠ p2) : p1 ∉ sepRectangle p1 p2 := by{
    match p1, p2 with | ⟨x1, y1⟩, ⟨x2, y2⟩ => {
      simp only [ne_eq, Point.mk.injEq, not_and] at h12
      rw[sepRectangle, Rectangle.mem_iff, not_and]
      intro h
      apply left_notMem_sepInterval_of_ne
      apply h12
      apply of_not_not
      intro h'
      have h'':=left_notMem_sepInterval_of_ne h'
      contradiction
    }
  }
theorem sepRectangle_antisymm' {p0 p1 t : Point} (htxy : t ∈ sepRectangle p0 p1)
  (htyx : t ∈ sepRectangle p1 p0) : p0 = p1 := by{
    match t, p0, p1 with
    | ⟨tx, ty⟩, ⟨x0, y0⟩, ⟨x1, y1⟩ => {
      rw[sepRectangle, Rectangle.mem_iff] at htxy htyx
      have h0:=sepInterval_antisymm' htxy.left htyx.left
      have h1:=sepInterval_antisymm' htxy.right htyx.right
      rw[h0, h1]
    }
  }

def Region.meet (R1 R2 : Region) : Prop := (R1 ∩ R2).Nonempty
theorem Region.meet_iff {R1 R2 : Region} : R1.meet R2 ↔ ∃ p, p ∈ R1 ∩ R2 := by rfl
def Map.cover (m : Map) : Region := fun p => m p p
theorem Map.cover_iff {m : Map} {p : Point} : m.cover p ↔ m p p := by rfl
def Map.submap (m1 m2 : Map) : Prop := ∀ p, m1 p ⊆ m2 p
theorem Map.submap_iff {m1 m2 : Map} : m1.submap m2 ↔ ∀ p, m1 p ⊆ m2 p := by rfl
def Map.at_most_regions (m : Map) (n : ℕ) : Prop :=
  ∃ f:Fin n → Point, ∀ p, m.cover p → ∃ i, m (f i) p
def Map.at_most_regions' (m : Map) (n : ℕ) : Prop :=
  ∃f : ℕ → Point, ∀p, m.cover p → ∃i < n, m (f i) p
theorem Map.at_most_regions_eq_at_most_regions'
: at_most_regions = at_most_regions' := by{
  ext m n
  rw[at_most_regions, at_most_regions']
  constructor
  · {
    intro ⟨f, h⟩
    let f' := fun x => if h : x < n then f ⟨x, h⟩ else ⟨0, 0⟩
    use f'
    intro p hp
    have ⟨⟨i, hi⟩, hfi⟩ := h p hp
    refine ⟨i, hi, ?_⟩
    unfold f'
    simp[hi, hfi]
  }
  · {
    intro ⟨f, h⟩
    use f ∘ Fin.val
    intro p hp
    have ⟨i, hi, hfi⟩ := h p hp
    use ⟨i, hi⟩
    simp[hfi]
  }
}
theorem Map.at_most_regions_iff {m : Map} {n : ℕ} :
  m.at_most_regions n ↔ ∃ f:Fin n → Point, ∀ p, m.cover p → ∃ i, m (f i) p := by rfl
theorem sepRectangle_antisymm'_of_meet {p0 p1 : Point}
  (htyx : Region.meet (sepRectangle p0 p1).toRegion (sepRectangle p1 p0).toRegion)
  : p0 = p1 := by{
    have ⟨t, ht⟩:=htyx
    rw[Set.mem_inter_iff, ←Rectangle.mem_iff_toRegion,
    ←Rectangle.mem_iff_toRegion] at ht
    exact sepRectangle_antisymm' ht.left ht.right
  }

theorem submap_refl : ∀m : Map, m.submap m := by{
  simp[Map.submap_iff]
}
theorem submap_trans {m1 m2 m3 : Map} (h12 : m1.submap m2)
  (h23 : m2.submap m3) : m1.submap m3 := by{
    intro p1 p2 hp12
    exact h23 _ (h12 _ hp12)
  }
theorem submap_antisymm {m1 m2 : Map} (h12 : m1.submap m2)
(h21 : m2.submap m1) : m1 = m2 := by{
  apply funext₂
  intro z1 z2
  have h12':=h12 z1
  have h21':=h21 z1
  have h12'':=Set.Subset.antisymm h12' h21'
  rw[h12'']
}
theorem cover_subset_of_submap {m1 m2 : Map} (hm : m1.submap m2) :
  m1.cover ⊆ m2.cover := by{
    intro z hz
    exact hm _ hz
  }

theorem at_most_regions_le {m : Map} {n1 n2 : ℕ} (hn12 : n1 ≤ n2)
  (hm : m.at_most_regions n1) : m.at_most_regions n2 := by{
    rw[Map.at_most_regions_eq_at_most_regions'] at *
    have ⟨f, h⟩:=hm
    let f' := fun i => if i < n1 then f i else f 0
    use f'
    intro p hp
    have ⟨i, hin, hi⟩:=h p hp
    refine ⟨i, lt_of_lt_of_le hin hn12, ?_⟩
    unfold f'
    simp[hin, hi]
  }
@[simp] theorem submap_bot_iff {m : Map} : m.submap ⊥ ↔ m = ⊥ := by{
  constructor
  · {
    intro h
    ext a b
    simp only [Pi.bot_apply, Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
    intro h'
    have h'':=h _ h'
    simp at h''
  }
  · {
    intro h
    rw[h]
    apply submap_refl
  }
}

def Region.open (R : Region) : Prop :=
  ∀ p ∈ R, ∃ u:Rectangle, p ∈ u ∧ u.toRegion ⊆ R
theorem Region.open_rectangle_iff {R : Region} :
  R.open ↔ ∀ p ∈ R, ∃ u:Rectangle, p ∈ u ∧ u.toRegion ⊆ R := by rfl
theorem Region.rectangle_toRegion_open (R : Rectangle) : R.toRegion.open :=
  fun _ hp => ⟨R, hp, Set.Subset.rfl⟩
theorem Region.open_iff {R : Region} :
  R.open ↔ ∀ p ∈ R, ∃ u:Region, u.open ∧ p ∈ u ∧ u ⊆ R := by{
  constructor
  · {
    intro h p hp
    rw[Region.open_rectangle_iff] at h
    have ⟨u, hpu, husub⟩ := h p hp
    exact ⟨u.toRegion, rectangle_toRegion_open u, hpu, husub⟩
  }
  · {
    intro h p hp
    have ⟨u, huopen, hpu, husub⟩ := h p hp
    rw[Region.open_rectangle_iff] at huopen
    have ⟨v, hvp, hvsub⟩ := huopen p hpu
    exact ⟨v, hvp, Set.Subset.trans hvsub husub⟩
  }
}
@[simp] theorem empty_open : Region.open ∅ := by{
  simp[Region.open]
}
@[simp] theorem univ_open : Region.open Set.univ := by{
  simp only [Region.open, Set.mem_univ, Set.subset_univ, and_true, forall_const]
  intro p
  use ⟨⟨p.x - 1, p.x + 1⟩, ⟨p.y - 1, p.y + 1⟩⟩
  simp[Rectangle.mem_iff, Interval.mem_iff]
}
def Region.closure (R : Region) : Region := {p | ∀ u:Region, u.open → p ∈ u → meet R u}
theorem Region.closure_def_iff {R : Region} :
  R.closure = {p | ∀ u:Region, u.open → p ∈ u → R.meet u} := by rfl
theorem Region.mem_closure_iff {R : Region} {p : Point} :
  p ∈ R.closure ↔ ∀ u:Region, u.open → p ∈ u → R.meet u := by rfl
theorem Region.mem_closure_rectangle_iff {R : Region} {p : Point} :
  p ∈ R.closure ↔ ∀ u:Rectangle, p ∈ u → R.meet u.toRegion := by {
  rw[mem_closure_iff]
  constructor
  · {
    intro h u hu
    exact h u.toRegion (rectangle_toRegion_open u) hu
  }
  · {
    intro h u hu hup
    have ⟨v, hvp, hvsub⟩ := Region.open_rectangle_iff.mp hu p hup
    have ⟨p, hp⟩:=h v hvp
    rw[Set.mem_inter_iff] at hp
    use p
    rw[Set.mem_inter_iff]
    exact ⟨hp.left, Set.mem_of_subset_of_mem hvsub hp.right⟩
  }
}
theorem Region.closure_rectangle_def_iff {R : Region} :
  R.closure = {p | ∀ u:Rectangle, p ∈ u → R.meet u.toRegion} := by {
  ext p
  exact mem_closure_rectangle_iff
}
theorem Region.closure_subset_closure_of_subset {R1 R2 : Region}
  (h12 : R1 ⊆ R2) : R1.closure ⊆ R2.closure := by{
    intro x hx
    rw[mem_closure_iff] at *
    intro u hu hxu
    have hx':=hx u hu hxu
    have ⟨q, hq1, hqu⟩:=hx'
    exact ⟨q, h12 hq1, hqu⟩
  }
def Region.connected (R : Region) : Prop :=
  ∀ R1 R2, R1.open → R2.open → R ⊆ R1 ∪ R2 → meet R R1 → meet R R2 → meet R1 R2
@[simp] theorem empty_meet {R : Region} : ¬Region.meet ∅ R := by{simp[Region.meet]}
@[simp] theorem meet_empty {R : Region} : ¬Region.meet R ∅ := by{simp[Region.meet]}
@[simp] theorem empty_connected : Region.connected ∅ := by{
  simp[Region.connected]
}
@[simp] theorem univ_meet_iff {R : Region} : Region.meet Set.univ R ↔ R ≠ ∅ := by{
  simp[Region.meet, Set.nonempty_iff_empty_ne, Eq.comm]
}
theorem meet_comm {R1 R2 : Region} : R1.meet R2 = R2.meet R1 := by{
  ext
  constructor
  · intro ⟨x, h1, h2⟩; exact ⟨x, h2, h1⟩
  · intro ⟨x, h1, h2⟩; exact ⟨x, h2, h1⟩
}
-- @[simp] theorem univ_connected : Region.connected Set.univ := by{
--   simp only [Region.connected, Set.univ_subset_iff,
--   univ_meet_iff, ne_eq, ←Set.nonempty_iff_ne_empty,
--   Set.eq_univ_iff_forall, Set.mem_union]
--   intro R1 R2 R1o R2o R1uR2 R1n R2n
--   rw[Region.open] at R1o R2o
--   sorry
-- }

def Map.border (m : Map) (p0 p1 : Point) : Region := (m p0).closure ∩ (m p1).closure
theorem Map.border_def_iff {m : Map} {p0 p1 : Point} :
  m.border p0 p1 = (m p0).closure ∩ (m p1).closure := by rfl
theorem Map.mem_border_iff {m : Map} {p0 p1 p : Point} :
  p ∈ m.border p0 p1 ↔ p ∈ (m p0).closure ∧ p ∈ (m p1).closure := by rfl
def Map.corner_map (m : Map) (p : Point) : Map :=
  fun q0 => {q1 | p ∈ (m q0).closure ∧ q1 ∈ (m q0)}
theorem Map.corner_map_def_iff {m : Map} {p q0 : Point} :
  m.corner_map p q0 = {q1 | p ∈ (m q0).closure ∧ q1 ∈ (m q0)} := by rfl
theorem Map.mem_corner_map_iff {m : Map} {p q0 q1 : Point} :
  q1 ∈ m.corner_map p q0 ↔ p ∈ (m q0).closure ∧ q1 ∈ (m q0) := by rfl
def Map.not_corner (m : Map) : Region := {p | at_most_regions (m.corner_map p) 2}
theorem Map.not_corner_def_iff {m : Map} :
  m.not_corner = {p | at_most_regions (m.corner_map p) 2} := by rfl
theorem Map.mem_not_corner_iff {m : Map} {p : Point} :
  p ∈ m.not_corner ↔ at_most_regions (m.corner_map p) 2 := by rfl
def Map.adjacent (m : Map) (p0 p1 : Point) : Prop :=
  p1 ∉ m p0 ∧ m.not_corner.meet (m.border p0 p1)

class IsPlainMap (m : Map) : Prop where
  map_symm {p1 p2 : Point}: p2 ∈ m p1 → p1 ∈ m p2
  map_trans {p1 p2 : Point} : p2 ∈ m p1 → m p2 ⊆ m p1
class IsColoringMap (m k : Map) : Prop where
  coloring_plain : IsPlainMap k
  coloring_cover : k.cover ⊆ m.cover
  coloring_consistent : m.submap k
  coloring_adjacent {p1 p2 : Point}: m.adjacent p1 p2 → ¬k p1 p2
class IsSimpleMap (m : Map) : Prop extends IsPlainMap m where
  map_open : ∀ p, (m p).open
  map_connected : ∀ p, (m p).connected
class IsFiniteSimpleMap (m : Map) : Prop extends IsSimpleMap m where
  map_finite : ∃ n, m.at_most_regions n

def Map.colorable_with (m : Map) (n : ℕ) : Prop :=
  ∃ k, IsColoringMap m k ∧ k.at_most_regions n

section plain_lemmas

variable {m : Map}
variable [IsPlainMap m]
theorem map_symm {p1 p2 : Point} : p2 ∈ m p1 → p1 ∈ m p2 := IsPlainMap.map_symm
theorem map_trans {p1 p2 : Point} : p2 ∈ m p1 → m p2 ⊆ m p1 := IsPlainMap.map_trans
theorem map_symm' {z1 z2 : Point} : m z1 z2 → m z2 z1 := IsPlainMap.map_symm
@[implicit_reducible] def map_Symm : Std.Symm m :=
  ⟨fun _ _ => map_symm'⟩
theorem map_comm {z1 z2 : Point} : m z1 z2 = m z2 z1 := by{
  ext
  let := map_Symm (m:=m)
  apply comm
}
theorem map_trans' {z1 z2 z3 : Point} : m z1 z2 → m z2 z3 → m z1 z3 := by{
  intro h1 h2
  apply map_trans h1 h2
}
theorem eq_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : m z1 = m z2 := by{
    ext z
    change m z1 z ↔ m z2 z
    constructor
    · apply map_trans'; exact map_symm' h12
    · apply map_trans' h12
  }
theorem congr_left_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z1 z ↔ m z2 z:=by{
    simp[eq_of_rel h12]
  }
theorem congr_right_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z z1 ↔ m z z2:=by{
    intro z
    simp only [map_comm (z1:=z), congr_left_of_rel h12]
  }
theorem refl_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : m.cover z1 ∧ m.cover z2 := by{
    have h21 := map_symm' h12
    exact ⟨map_trans' h12 h21, map_trans' h21 h12⟩
  }
end plain_lemmas

@[simp] theorem bot_cover {p : Point} : ¬Map.cover ⊥ p := by{
  simp only [Map.cover, Pi.bot_apply, Set.bot_eq_empty]
  change p ∉ (∅ : Set Point)
  simp
}
theorem bot_atmost_zero : Map.at_most_regions ⊥ 0 := by{
  simp[Map.at_most_regions]
}
@[simp] theorem top_cover {p : Point} : Map.cover ⊤ p := by{
  simp only [Map.cover, Pi.top_apply,Set.top_eq_univ]
  change p ∈ Set.univ
  simp
}
theorem top_atmost_one : Map.at_most_regions ⊤ 1 := by{
  simp only [Map.at_most_regions, top_cover, Pi.top_apply, Set.top_eq_univ, exists_const,
    forall_const]
  change ∀p, p ∈ Set.univ
  simp
}

@[simp] theorem bot_isPlainMap : IsPlainMap ⊥ where
  map_symm := by{simp}
  map_trans := by{simp}
@[simp] theorem top_isPlainMap : IsPlainMap ⊤ where
  map_symm := by{simp}
  map_trans := by{simp}
@[simp] theorem bot_isSimpleMap : IsSimpleMap ⊥ where
  toIsPlainMap := bot_isPlainMap
  map_open := by{simp}
  map_connected := by{simp}
-- @[simp] theorem top_isSimpleMap : IsSimpleMap ⊤ where
--   toIsPlainMap := by{simp}
--   map_open := by{simp}
--   map_connected := by{simp}
@[simp] theorem bot_isFiniteSimpleMap : IsFiniteSimpleMap ⊥ where
  toIsSimpleMap := by{simp}
  map_finite := ⟨0, bot_atmost_zero⟩
-- @[simp] theorem top_isFiniteSimpleMap : IsFiniteSimpleMap ⊤ where
--   toIsSimpleMap := by{simp}
--   map_finite := ⟨1, top_atmost_one⟩

end RealPlane
