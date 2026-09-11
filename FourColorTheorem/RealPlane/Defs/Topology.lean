import FourColorTheorem.RealPlane.Defs.Rectangle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.PathConnected

theorem exists_Ioo_subset_of_isOpen {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s) :
    ∃ a b, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ s := by{
  rw[Metric.isOpen_iff] at hs
  rcases hs x hx with ⟨ε, hε, hball⟩
  use x - ε, x + ε
  constructor
  · simp [Set.mem_Ioo, hε]
  intro y hy
  apply hball
  unfold Metric.ball
  rw[Set.mem_setOf]
  rw[Real.dist_eq, abs_lt]
  split_ands <;> linarith [hy.1, hy.2]
}

namespace RealPlane

open Set Topology

namespace Rectangle
theorem isOpen (R : Rectangle) : IsOpen (R : Set Point) := by{
  apply IsOpen.prod <;> apply isOpen_Ioo
}
end Rectangle

namespace Region

def meet (R1 R2 : Region) : Prop := (R1 ∩ R2).Nonempty
theorem meet_iff {R1 R2 : Region} : R1.meet R2 ↔ ∃ p, p ∈ R1 ∩ R2 := by rfl
theorem meet_iff_nonempty {R1 R2 : Region} : R1.meet R2 ↔ (R1 ∩ R2).Nonempty := by rfl
@[symm] theorem meet_symm {R1 R2 : Region} : R1.meet R2 → R2.meet R1 := by{
  unfold meet
  simp[inter_comm]
}
theorem meet_comm {R1 R2 : Region} : R1.meet R2 ↔ R2.meet R1 := ⟨meet_symm, meet_symm⟩
theorem sepRectangle_antisymm'_of_meet {p0 p1 : Point}
  (htyx : Region.meet (sepRectangle p0 p1) (sepRectangle p1 p0))
  : p0 = p1 := by{
    have ⟨t, ht⟩:=htyx
    rw[Set.mem_inter_iff] at ht
    exact sepRectangle_antisymm' ht.left ht.right
  }
theorem meet_of_meet_subset_left {R1 R2 R3 : Region} (h13 : R1 ⊆ R3) (h : R1.meet R2) : R3.meet R2
:= by{
  unfold meet at h
  rcases h with ⟨p, hp1, hp2⟩
  exact ⟨p, h13 hp1, hp2⟩
}
theorem meet_of_meet_subset_right {R1 R2 R3 : Region} (h23 : R2 ⊆ R3) (h : R1.meet R2) : R1.meet R3
:= by{
  symm at *
  exact meet_of_meet_subset_left h23 h
}
@[simp] theorem empty_meet {R : Region} : ¬meet ∅ R := by{simp[meet]}
@[simp] theorem meet_empty {R : Region} : ¬meet R ∅ := by{simp[meet]}

def isOpen' (R : Region) := ∀p ∈ R, ∃u : Rectangle, p ∈ u ∧ (u : Set Point) ⊆ R
theorem isOpen_iff_isOpen' (R : Region)
: IsOpen R ↔ R.isOpen' := by{
  constructor
  · {
    intro h p Rp
    rw[isOpen_prod_iff] at h
    specialize h p.1 p.2 Rp
    rcases h with ⟨U, V, hU, hV, hxp, hyp, hUV⟩
    rcases exists_Ioo_subset_of_isOpen hU hxp with ⟨a1, b1, hxp_in1, hI1⟩
    rcases exists_Ioo_subset_of_isOpen hV hyp with ⟨a2, b2, hyp_in2, hI2⟩
    use ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
    rw[Rectangle.mem_iff']
    constructor
    · exact ⟨hxp_in1, hyp_in2⟩
    intro z hz
    rw[mem_prod] at hz
    apply hUV
    rw[mem_prod]
    apply hz.imp
    · apply hI1
    · apply hI2
  }
  · {
    intro h
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    rcases h p hp with ⟨u, hpu, huR⟩
    exact ⟨_, huR, u.isOpen, hpu⟩
  }
}
theorem isOpen_iff_forall (R : Region) :
  IsOpen R ↔ ∀p ∈ R, ∃u : Region, IsOpen u ∧ p ∈ u ∧ u ⊆ R := by{
  rw[isOpen_iff_forall_mem_open]
  simp only [and_left_comm, and_comm]
}

def closure' (R : Region) : Region := {p | ∀ u:Region, IsOpen u → p ∈ u → R.meet u}
theorem closure_eq_closure' (R : Region) : closure R = R.closure' := by{
  ext x
  rw[mem_closure_iff_nhds]
  unfold closure'
  simp only [Set.mem_setOf]
  constructor
  · {
    intro hx u hu hxu
    symm
    apply hx
    rw[mem_nhds_iff]
    use u
  }
  · {
    intro hx t ht
    rw[mem_nhds_iff] at ht
    have ⟨u, hut, huo, hxu⟩ := ht
    specialize hx u huo hxu
    rcases hx with ⟨z, zR, zu⟩
    exact ⟨z, hut zu, zR⟩
  }
}

theorem meet_of_open_of_meet_closure {R1 R2 : Region} (h1 : IsOpen R1)
(h12 : R1.meet (closure R2)) : R1.meet R2 := by {
  have ⟨z, hz1, hz2⟩ := h12
  rw[closure_eq_closure', closure'] at hz2
  rw[Set.mem_setOf] at hz2
  specialize hz2 _ h1 hz1
  symm
  assumption
}
theorem meet_iff_meet_closure_of_open {R1 R2 : Region} (h1 : IsOpen R1) :
  R1.meet (closure R2) ↔ R1.meet R2 := by{
  apply Iff.intro (meet_of_open_of_meet_closure h1)
  intro ⟨z, hz1, hz2⟩
  exact ⟨z, hz1, subset_closure hz2⟩
}
theorem mem_closure_rectangle_iff {R : Region} {p : Point} :
  p ∈ closure R ↔ ∀ u:Rectangle, p ∈ u → R.meet u := by {
  rw[mem_closure_iff]
  constructor
  · {
    intro h u hu
    symm
    exact h _ u.isOpen hu
  }
  · {
    intro h u hu hup
    have ⟨v, hvp, hvsub⟩ := (isOpen_iff_isOpen' _).mp hu p hup
    have ⟨p, hp⟩:=h v hvp
    rw[Set.mem_inter_iff] at hp
    use p
    rw[Set.mem_inter_iff]
    exact ⟨hvsub hp.right, hp.left⟩
  }
}
theorem closure_subset_closure_of_subset {R1 R2 : Region}
  (h12 : R1 ⊆ R2) : closure R1 ⊆ closure R2 := by{
    intro x hx
    rw[mem_closure_iff] at *
    intro u hu hxu
    specialize hx u hu hxu
    apply meet_of_meet_subset_right h12 hx
  }

theorem interior_closure_subset {R : Region}
: closure (interior R) ⊆ closure R := by{
  apply closure_subset_closure_of_subset
  apply interior_subset
}

def connected' (R : Region) : Prop :=
  ∀ R1 R2, IsOpen R1 → IsOpen R2 → R ⊆ R1 ∪ R2 → meet R R1 → meet R R2 → meet R1 R2
theorem isPreconnected_iff_connected'_of_isOpen {R : Region} (hR : IsOpen R) :
  IsPreconnected R ↔ connected' R := by{
    constructor
    · {
      intro h
      intro R1 R2 h1 h2 h3 h4 h5
      specialize h _ _ h1 h2 h3 h4 h5
      rcases h with ⟨z, _, hz1, hz2⟩
      exact ⟨z, hz1, hz2⟩
    }
    · {
      intro h R1 R2 hR1 hR2 hcover hR1_meet hR2_meet
      by_contra h_empty
      have hU1_open : IsOpen (R1 ∩ R) := hR1.inter hR
      have hU2_open : IsOpen (R2 ∩ R) := hR2.inter hR
      have h_cov' : R ⊆ (R1 ∩ R) ∪ (R2 ∩ R) := by{
        intro p hp
        rcases hcover hp with h1 | h2
        · left; exact ⟨h1, hp⟩
        · right; exact ⟨h2, hp⟩
      }
      have h1' : meet R (R1 ∩ R) := by{
        rcases hR1_meet with ⟨x, hxR, hx1⟩
        exact ⟨x, hxR, hx1, hxR⟩
      }
      have h2' : meet R (R2 ∩ R) := by{
        rcases hR2_meet with ⟨y, hyR, hy2⟩
        exact ⟨y, hyR, hy2, hyR⟩
      }
      have h_meet := h _ _ hU1_open hU2_open h_cov' h1' h2'
      rcases h_meet with ⟨z, ⟨hz1, hzR1⟩, ⟨hz2, hzR2⟩⟩
      exact h_empty ⟨z, hzR1, hz1, hz2⟩
    }
  }

end Region

namespace Map
def boundary (m : Map) (p0 p1 : Point) : Region := closure (m p0) ∩ closure (m p1)
theorem mem_boundary_iff {m : Map} {p0 p1 : Point} {p : Point} :
  p ∈ boundary m p0 p1 ↔ (p ∈ closure (m p0) ∧ p ∈ closure (m p1)) := Iff.rfl
theorem boundary_comm {m : Map} {p0 p1 : Point} : boundary m p0 p1 = boundary m p1 p0
  := Set.inter_comm _ _
def corner_map (m : Map) (p : Point) : Map :=
  fun q0 q1 => p ∈ closure (m q0) ∧ m q0 q1
theorem corner_map_def_iff {m : Map} {p q0 : Point} :
  m.corner_map p q0 = {q1 | p ∈ closure (m q0) ∧ m q0 q1} := by rfl
theorem mem_corner_map_iff {m : Map} {p q0 q1 : Point} :
  q1 ∈ m.corner_map p q0 ↔ p ∈ closure (m q0) ∧ m q0 q1 := by rfl
def not_corner (m : Map) : Region := {p | at_most_regions (m.corner_map p) 2}
theorem not_corner_def_iff {m : Map} :
  m.not_corner = {p | at_most_regions (m.corner_map p) 2} := by rfl
theorem mem_not_corner_iff {m : Map} {p : Point} :
  p ∈ m.not_corner ↔ at_most_regions (m.corner_map p) 2 := by rfl
def adjacent (m : Map) (p0 p1 : Point) : Prop :=
  ¬m p0 p1 ∧ m.not_corner.meet (m.boundary p0 p1)
end Map

instance instConnectedSpace : ConnectedSpace Point := by{
  unfold Point
  apply @instConnectedSpaceProd
}

end RealPlane
