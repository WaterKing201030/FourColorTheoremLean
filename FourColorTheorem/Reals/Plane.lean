import FourColorTheorem.Reals.Basic

/- Definitions for points, regions, and maps in the real plane -/

structure Point (α : Type _) [RealStructure α] where
  x : α
  y : α
def Region (α : Type _) [RealStructure α]:=Set (Point α)
def Map (α : Type _) [RealStructure α]:=Point α → Region α
structure Interval (α : Type _) [RealStructure α] where
  left : α
  right : α
structure Rectangle (α : Type _) [RealStructure α] where
  hspan : Interval α
  vspan : Interval α

variable {α : Type _}
variable [RealStructure α]

@[inline] instance Region.instMembership : Membership (Point α) (Region α) := Set.instMembership
theorem Region.mem_iff {R : Region α} {p : Point α} : p ∈ R ↔ R p := by rfl
@[ext] theorem Region.ext {R1 R2 : Region α} (h : ∀ p, p ∈ R1 ↔ p ∈ R2) : R1 = R2 :=
  Set.ext h
@[inline] instance Region.instEmptyCollection
  : EmptyCollection (Region α) := Set.instEmptyCollection
theorem Region.empty_def_iff : (∅ : Region α) = {_p : Point α | False} := by rfl
theorem Region.mem_empty_iff {p : Point α} : p ∈ (∅ : Region α) ↔ False := by rfl
@[inline] instance Region.instHasSubset : HasSubset (Region α) := Set.instHasSubset
theorem Region.subset_iff {R1 R2 : Region α} : R1 ⊆ R2 ↔ ∀ p, p ∈ R1 → p ∈ R2 := by rfl
@[inline] instance Region.instHasUnion : Union (Region α) := Set.instUnion
theorem Region.mem_union_iff {R1 R2 : Region α} {p : Point α} :
  p ∈ R1 ∪ R2 ↔ p ∈ R1 ∨ p ∈ R2 := by rfl
theorem Region.union_def_iff {R1 R2 : Region α} : R1 ∪ R2 = {p | p ∈ R1 ∨ p ∈ R2} := by rfl
@[inline] instance Region.instHasInter : Inter (Region α) := Set.instInter
theorem Region.mem_inter_iff {R1 R2 : Region α} {p : Point α} :
  p ∈ R1 ∩ R2 ↔ p ∈ R1 ∧ p ∈ R2 := by rfl
theorem Region.inter_def_iff {R1 R2 : Region α} : R1 ∩ R2 = {p | p ∈ R1 ∧ p ∈ R2} := by rfl
theorem Map.mem_map_apply_iff {m : Map α} {p1 p2 : Point α}
  : p2 ∈ m p1 ↔ m p1 p2 := by rfl
theorem Map.map_apply_iff_mem {m : Map α} {p1 p2 : Point α}
  : m p1 p2 ↔ p2 ∈ m p1 := by rfl

def Interval.toSet (I : Interval α) : Set α := {x | I.left < x ∧ x < I.right}
def Interval.Mem (I : Interval α) (x : α) : Prop := x ∈ I.toSet
@[inline] instance Interval.instMembership : Membership α (Interval α) where mem := Interval.Mem
theorem Interval.mem_iff (I : Interval α) (x : α) : x ∈ I ↔ I.left < x ∧ x < I.right := by rfl
def Rectangle.toRegion (R : Rectangle α) : Region α := {p | p.x ∈ R.hspan ∧ p.y ∈ R.vspan}
def Rectangle.Mem (R : Rectangle α) (p : Point α) : Prop := p ∈ R.toRegion
@[inline] instance Rectangle.instMembership :
  Membership (Point α) (Rectangle α) where mem := Rectangle.Mem
theorem Rectangle.mem_iff (R : Rectangle α) (p : Point α) :
  p ∈ R ↔ p.x ∈ R.hspan ∧ p.y ∈ R.vspan := by rfl

def Region.Nonempty (R : Region α) : Prop := ∃ p, p ∈ R
theorem Region.Nonempty_iff {R : Region α} : R.Nonempty ↔ ∃ p, p ∈ R := by rfl
theorem Region.Nonempty_iff_ne_empty {R : Region α}
  : R.Nonempty ↔ R ≠ ∅ := Set.nonempty_iff_ne_empty
def Region.meet (R1 R2 : Region α) : Prop := Nonempty (R1 ∩ R2)
theorem Region.meet_iff {R1 R2 : Region α} : R1.meet R2 ↔ ∃ p, p ∈ R1 ∩ R2 := by rfl
def Map.cover (m : Map α) : Region α := fun p => m p p
theorem Map.cover_iff {m : Map α} {p : Point α} : m.cover p ↔ m p p := by rfl
def Map.submap (m1 m2 : Map α) : Prop := ∀ p, m1 p ⊆ m2 p
theorem Map.submap_iff {m1 m2 : Map α} : m1.submap m2 ↔ ∀ p, m1 p ⊆ m2 p := by rfl
def Map.at_most_regions (m : Map α) (n : ℕ) : Prop :=
  ∃ f:Fin n → Region α, ∀ p, m.cover p → ∃ i, p ∈ f i
theorem Map.at_most_regions_iff {m : Map α} {n : ℕ} :
  m.at_most_regions n ↔ ∃ f:Fin n → Region α, ∀ p, m.cover p → ∃ i, p ∈ f i := by rfl

def Region.open (R : Region α) : Prop :=
  ∀ p ∈ R, ∃ u:Rectangle α, p ∈ u ∧ u.toRegion ⊆ R
theorem Region.open_rectangle_iff {R : Region α} :
  R.open ↔ ∀ p ∈ R, ∃ u:Rectangle α, p ∈ u ∧ u.toRegion ⊆ R := by rfl
theorem Region.rectangle_toRegion_open (R : Rectangle α) : R.toRegion.open :=
  fun _ hp => ⟨R, hp, Set.Subset.rfl⟩
theorem Region.open_iff {R : Region α} :
  R.open ↔ ∀ p ∈ R, ∃ u:Region α, u.open ∧ p ∈ u ∧ u ⊆ R := by{
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
def Region.closure (R : Region α) : Region α := {p | ∀ u:Region α, u.open → p ∈ u → meet R u}
theorem Region.closure_def_iff {R : Region α} :
  R.closure = {p | ∀ u:Region α, u.open → p ∈ u → R.meet u} := by rfl
theorem Region.mem_closure_iff {R : Region α} {p : Point α} :
  p ∈ R.closure ↔ ∀ u:Region α, u.open → p ∈ u → R.meet u := by rfl
theorem Region.mem_closure_rectangle_iff {R : Region α} {p : Point α} :
  p ∈ R.closure ↔ ∀ u:Rectangle α, p ∈ u → R.meet u.toRegion := by {
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
    rw[Region.mem_inter_iff] at hp
    use p
    rw[Region.inter_def_iff]
    exact ⟨hp.left, Set.mem_of_subset_of_mem hvsub hp.right⟩
  }
}
theorem Region.closure_rectangle_def_iff {R : Region α} :
  R.closure = {p | ∀ u:Rectangle α, p ∈ u → R.meet u.toRegion} := by {
  ext p
  exact mem_closure_rectangle_iff
}
def Region.connected (R : Region α) : Prop :=
  ∀ R1 R2, R1.open → R2.open → R ⊆ R1 ∪ R2 → meet R R1 → meet R R2 → meet R1 R2

def Map.border (m : Map α) (p0 p1 : Point α) : Region α := (m p0).closure ∩ (m p1).closure
theorem Map.border_def_iff {m : Map α} {p0 p1 : Point α} :
  m.border p0 p1 = (m p0).closure ∩ (m p1).closure := by rfl
theorem Map.mem_border_iff {m : Map α} {p0 p1 p : Point α} :
  p ∈ m.border p0 p1 ↔ p ∈ (m p0).closure ∧ p ∈ (m p1).closure := by rfl
def Map.corner_map (m : Map α) (p : Point α) : Map α :=
  fun q0 => {q1 | p ∈ (m q0).closure ∧ q1 ∈ (m q0)}
theorem Map.corner_map_def_iff {m : Map α} {p q0 : Point α} :
  m.corner_map p q0 = {q1 | p ∈ (m q0).closure ∧ q1 ∈ (m q0)} := by rfl
theorem Map.mem_corner_map_iff {m : Map α} {p q0 q1 : Point α} :
  q1 ∈ m.corner_map p q0 ↔ p ∈ (m q0).closure ∧ q1 ∈ (m q0) := by rfl
def Map.not_corner (m : Map α) : Region α := {p | at_most_regions (m.corner_map p) 2}
theorem Map.not_corner_def_iff {m : Map α} :
  m.not_corner = {p | at_most_regions (m.corner_map p) 2} := by rfl
theorem Map.mem_not_corner_iff {m : Map α} {p : Point α} :
  p ∈ m.not_corner ↔ at_most_regions (m.corner_map p) 2 := by rfl
def Map.adjacent (m : Map α) (p0 p1 : Point α) : Prop :=
  p1 ∉ m p0 ∧ m.not_corner.meet (m.border p0 p1)

class IsPlainMap (m : Map α) : Prop where
  map_symm {p1 p2 : Point α}: p2 ∈ m p1 → p1 ∈ m p2
  map_trans {p1 p2 : Point α} : p2 ∈ m p1 → m p2 ⊆ m p1
class IsColoringMap (m k : Map α) : Prop where
  coloring_plain : IsPlainMap k
  coloring_cover : k.cover ⊆ m.cover
  coloring_consistent : m.submap k
  coloring_adjacent {p1 p2 : Point α}: m.adjacent p1 p2 → ¬k p1 p2
class IsSimpleMap (m : Map α) : Prop extends IsPlainMap m where
  map_open : ∀ p, (m p).open
  map_connected : ∀ p, (m p).connected
class IsFiniteSimpleMap (m : Map α) : Prop extends IsSimpleMap m where
  map_finite : ∃ n, m.at_most_regions n

def Map.colorable_with (m : Map α) (n : ℕ) : Prop :=
  ∃ k, IsColoringMap m k ∧ k.at_most_regions n
