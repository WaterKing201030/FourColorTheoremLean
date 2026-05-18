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

structure Point where
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
def Map:=Point → Region
structure Interval where
  min : ℝ
  max : ℝ
structure Rectangle where
  hspan : Interval
  vspan : Interval

theorem Map.mem_map_apply_iff {m : Map} {p1 p2 : Point}
  : p2 ∈ m p1 ↔ m p1 p2 := by rfl
theorem Map.map_apply_iff_mem {m : Map} {p1 p2 : Point}
  : m p1 p2 ↔ p2 ∈ m p1 := by rfl

def Interval.toSet (I : Interval) : Set ℝ := {x | I.min < x ∧ x < I.max}
def Interval.Mem (I : Interval) (x : ℝ) : Prop := x ∈ I.toSet
@[inline] instance Interval.instMembership : Membership ℝ Interval where mem := Interval.Mem
theorem Interval.mem_iff (I : Interval) (x : ℝ) : x ∈ I ↔ I.min < x ∧ x < I.max := by rfl
def Rectangle.toRegion (R : Rectangle) : Region := {p | p.x ∈ R.hspan ∧ p.y ∈ R.vspan}
def Rectangle.Mem (R : Rectangle) (p : Point) : Prop := p ∈ R.toRegion
@[inline] instance Rectangle.instMembership :
  Membership Point Rectangle where mem := Rectangle.Mem
theorem Rectangle.mem_iff (R : Rectangle) (p : Point) :
  p ∈ R ↔ p.x ∈ R.hspan ∧ p.y ∈ R.vspan := by rfl

def Region.Nonempty (R : Region) : Prop := ∃ p, p ∈ R
theorem Region.Nonempty_iff {R : Region} : R.Nonempty ↔ ∃ p, p ∈ R := by rfl
theorem Region.Nonempty_iff_ne_empty {R : Region}
  : R.Nonempty ↔ R ≠ ∅ := Set.nonempty_iff_ne_empty
def Region.meet (R1 R2 : Region) : Prop := Nonempty (R1 ∩ R2)
theorem Region.meet_iff {R1 R2 : Region} : R1.meet R2 ↔ ∃ p, p ∈ R1 ∩ R2 := by rfl
def Map.cover (m : Map) : Region := fun p => m p p
theorem Map.cover_iff {m : Map} {p : Point} : m.cover p ↔ m p p := by rfl
def Map.submap (m1 m2 : Map) : Prop := ∀ p, m1 p ⊆ m2 p
theorem Map.submap_iff {m1 m2 : Map} : m1.submap m2 ↔ ∀ p, m1 p ⊆ m2 p := by rfl
def Map.at_most_regions (m : Map) (n : ℕ) : Prop :=
  ∃ f:Fin n → Region, ∀ p, m.cover p → ∃ i, p ∈ f i
theorem Map.at_most_regions_iff {m : Map} {n : ℕ} :
  m.at_most_regions n ↔ ∃ f:Fin n → Region, ∀ p, m.cover p → ∃ i, p ∈ f i := by rfl

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
def Region.connected (R : Region) : Prop :=
  ∀ R1 R2, R1.open → R2.open → R ⊆ R1 ∪ R2 → meet R R1 → meet R R2 → meet R1 R2

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

end RealPlane
