import FourColorTheorem.RealPlane.Defs.Rectangle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.PathConnected

/-! 拓扑性质：开集、闭集；在这里定义了相邻 -/

open Function
open Relation

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
  rw[Set.mem_ofPred]
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
  simp only [Set.mem_ofPred]
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
  rw[Set.mem_ofPred] at hz2
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

instance instConnectedSpace : ConnectedSpace Point := by{
  unfold Point
  apply @instConnectedSpaceProd
}

namespace PlainMap
def boundary (m : PlainMap) (p0 p1 : Point) : Region := closure (m p0) ∩ closure (m p1)
theorem open_meet_of_mem_boundary {m : PlainMap} {p0 p1 z : Point} :
  z ∈ m.boundary p0 p1 → ∀R : Region, IsOpen R → z ∈ R → R.meet (m p0) ∧ R.meet (m p1)
:= by{
  intro ⟨h0, h1⟩ R hR hzR
  have h0' : R.meet (closure (m p0)) := ⟨z, hzR, h0⟩
  have h1' : R.meet (closure (m p1)) := ⟨z, hzR, h1⟩
  apply Region.meet_of_open_of_meet_closure hR at h0'
  apply Region.meet_of_open_of_meet_closure hR at h1'
  exact ⟨h0', h1'⟩
}
theorem rect_meet_of_mem_boudnary {m : PlainMap} {p0 p1 z : Point} :
  z ∈ m.boundary p0 p1 → ∀R : Rectangle, z ∈ R → (∃z' ∈ R, z' ∈ m p0) ∧ (∃z' ∈ R, z' ∈ m p1) := by{
  intro h R hzR
  apply open_meet_of_mem_boundary at h
  specialize h R R.isOpen hzR
  exact h
}
theorem mem_boundary_iff {m : PlainMap} {p0 p1 : Point} {p : Point} :
  p ∈ boundary m p0 p1 ↔ (p ∈ closure (m p0) ∧ p ∈ closure (m p1)) := Iff.rfl
theorem boundary_comm {m : PlainMap} {p0 p1 : Point} : boundary m p0 p1 = boundary m p1 p0
  := Set.inter_comm _ _
def corner_map (m : PlainMap) (p : Point) : PlainMap where
  getRegion := fun q0 => {q1 | p ∈ closure (m q0) ∧ m q0 q1}
  getRegion_symm := by{
    intro x y ⟨hl, hr⟩
    change _ ∧ _
    constructor
    · {
      apply Eq.mp ?_ hl
      congr 2
      apply m.eq_of_rel
      exact hr
    }
    · symm; assumption
  }
  getRegion_trans := by{
    intro x y ⟨h0l, h0r⟩ z ⟨h1l, h1r⟩
    change _ ∧ _
    constructor
    · exact h0l
    · exact trans h0r h1r
  }
theorem corner_map_def_iff {m : PlainMap} {p q0 : Point} :
  m.corner_map p q0 = {q1 | p ∈ closure (m q0) ∧ m q0 q1} := by rfl
theorem mem_corner_map_iff {m : PlainMap} {p q0 q1 : Point} :
  q1 ∈ m.corner_map p q0 ↔ p ∈ closure (m q0) ∧ m q0 q1 := by rfl
theorem corner_map_submap {m : PlainMap} {p : Point} :
  m.corner_map p ≤ m := by{
  apply submap_iff.mpr
  intro q0 q1 ⟨hpq0, hq01⟩
  exact hq01
}
def not_corner (m : PlainMap) : Region := {p | at_most_regions (m.corner_map p) 2}
theorem not_corner_def_iff {m : PlainMap} :
  m.not_corner = {p | at_most_regions (m.corner_map p) 2} := by rfl
theorem mem_not_corner_iff {m : PlainMap} {p : Point} :
  p ∈ m.not_corner ↔ at_most_regions (m.corner_map p) 2 := by rfl
def adjacent (m : PlainMap) (p0 p1 : Point) : Prop :=
  ¬m p0 p1 ∧ m.not_corner.meet (m.boundary p0 p1)
theorem adjacent_Symm {m : PlainMap} : Std.Symm m.adjacent := ⟨by{
  intro p0 p1 hp0
  rw[adjacent] at *
  rwa[m.comm, boundary_comm]
}⟩
@[symm] theorem adjacent_symm
{m : PlainMap} {z1 z2 : Point} : m.adjacent z1 z2 → m.adjacent z2 z1 :=
  m.adjacent_Symm.symm _ _
theorem adjacent_comm {m : PlainMap} {z1 z2 : Point} : m.adjacent z1 z2 ↔ m.adjacent z2 z1 :=
  ⟨m.adjacent_symm, m.adjacent_symm⟩
theorem cover_of_adjacent_left {m : PlainMap} {p1 p2 : Point} (h12 : m.adjacent p1 p2) :
  m.cover p1 := by{
  have ⟨h12m, ⟨k, hkc, hkb⟩⟩ := h12
  rw[mem_boundary_iff] at hkb
  apply And.left at hkb
  rw[Region.closure_eq_closure'] at hkb
  unfold Region.closure' at hkb
  rw[Set.mem_ofPred] at hkb
  specialize hkb Set.univ (by{simp}) (by{simp})
  have ⟨q, hq, _⟩ := hkb
  exact cover_of_rel_left hq
}
theorem cover_of_adjacent_right {m : PlainMap} {p1 p2 : Point} (h12 : m.adjacent p1 p2) :
  m.cover p2 := by{
  have ⟨h12m, ⟨k, hkc, hkb⟩⟩ := h12
  rw[mem_boundary_iff] at hkb
  apply And.right at hkb
  rw[Region.closure_eq_closure'] at hkb
  unfold Region.closure' at hkb
  rw[Set.mem_ofPred] at hkb
  specialize hkb Set.univ (by{simp}) (by{simp})
  have ⟨q, hq, _⟩ := hkb
  exact cover_of_rel_left hq
}

theorem congr_adjacent_left_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m.adjacent z1 z ↔ m.adjacent z2 z:=by{
  intro z
  unfold adjacent
  rw[congr_left_of_rel h12, and_congr_right_iff]
  intro mz2
  apply propext_iff.mp
  congr 1
  unfold boundary
  congr 2
  rw[eq_of_rel h12]
}
theorem adjacent_eq_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : m.adjacent z1 = m.adjacent z2 := by{
  ext z
  rw[congr_adjacent_left_of_rel h12]
}
theorem congr_adjacent_right_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m.adjacent z z1 ↔ m.adjacent z z2:=by{
  simp only [adjacent_comm]
  apply congr_adjacent_left_of_rel h12
}
theorem not_same_of_adjacent {m : PlainMap} {p0 p1 : Point}
  (h : m.adjacent p0 p1) : ¬m p0 p1 := h.1
theorem ne_of_adjacent {m : PlainMap} {p0 p1 : Point}
  (h : m.adjacent p0 p1) : p0 ≠ p1 := by{
  have h' := not_same_of_adjacent h
  contrapose h'
  rw[h']
  apply cover_of_adjacent_right h
}

def allOpen (m : PlainMap) : Prop :=
  ∀p, IsOpen (m p)
def allPreconnected (m : PlainMap) : Prop :=
  ∀p, IsPreconnected (m p)
theorem empty_allOpen : allOpen empty := by{
  intro p
  simp[empty]
}
theorem univ_allOpen : allOpen univ := by{
  intro p
  simp[univ]
}
theorem empty_allPreconnected : allPreconnected empty := by{
  intro p
  simp[empty, IsPreconnected]
}
theorem univ_allPreconnected : allPreconnected univ := by{
  intro p
  change IsPreconnected Set.univ
  apply isPreconnected_univ
}

end PlainMap

theorem ioo_separable {I1 I2 : Ioo} {p1 p2 : ℝ}
  (hp12 : p1 ≠ p2) (hpI1 : p1 ∈ I1) (hpI2 : p2 ∈ I2) : ∃I1' I2',
    I1' <+ I1 ∧ I2' <+ I2 ∧ p1 ∈ I1' ∧ p2 ∈ I2'
    ∧ ∀p, p ∈ I1' → p ∉ I2' := by{
  wlog hp12' : p1 < p2 with IH
  · {
    apply le_of_not_gt at hp12'
    apply lt_of_ne_of_le hp12.symm at hp12'
    specialize IH hp12.symm hpI2 hpI1 hp12'
    have ⟨I2', I1', h⟩ := IH
    use I1', I2'
    simp only [h, true_and]
    intro p
    rw[Imp.swap]
    apply h.2.2.2.2
  }
  let w := (p1 + p2) / 2
  let I1' : Ioo := ⟨I1.inf, min I1.sup w⟩
  let I2' : Ioo := ⟨max I2.inf w, I2.sup⟩
  use I1', I2'
  rw[Ioo.mem_iff] at hpI1 hpI2
  split_ands <;> try {
      simp[I1', I2', w]
      try linarith
    }
  · simp only [lt_min_iff, w, I1']; split_ands <;> linarith
  · simp only [max_lt_iff, w, I2']; split_ands <;> linarith
  intro p
  simp only [Ioo.mem_iff, lt_min_iff, max_lt_iff, not_and, not_lt, and_imp, I1', I2']
  intros
  linarith
}

theorem rect_separable {R1 R2 : Rectangle} {p1 p2 : Point}
  (hp12 : p1 ≠ p2) (hpR1 : p1 ∈ R1) (hpR2 : p2 ∈ R2) : ∃R1' R2',
    R1' <+ R1 ∧ R2' <+ R2 ∧ p1 ∈ R1' ∧ p2 ∈ R2'
    ∧ ∀p, p ∈ R1' → p ∉ R2' := by{
  rcases em' (p1.1 = p2.1) with hx | hx
  · {
    rw[Rectangle.mem_iff'] at hpR1 hpR2
    have ⟨I1', I2', IH⟩ := ioo_separable hx hpR1.1 hpR2.1
    let R1' : Rectangle := ⟨I1', R1.2⟩
    let R2' : Rectangle := ⟨I2', R2.2⟩
    have IH' := Rectangle.disjoint_of_hspan_disjoint (R1 := R1') (R2 := R2') IH.2.2.2.2
    use R1', R2'
    simp only [Ioo.subioo_def] at IH
    simp only [Ioo.mem_iff] at hpR1 hpR2 IH
    split_ands <;> try {
      simp[R1', R2']
      try linarith
    }
    exact IH'
  }
  have hy : p1.2 ≠ p2.2 := by{
    contrapose hp12
    ext <;> assumption
  }
  rw[Rectangle.mem_iff'] at hpR1 hpR2
  have ⟨I1', I2', IH⟩ := ioo_separable hy hpR1.2 hpR2.2
  let R1' : Rectangle := ⟨R1.1, I1'⟩
  let R2' : Rectangle := ⟨R2.1, I2'⟩
  have IH' := Rectangle.disjoint_of_vspan_disjoint (R1 := R1') (R2 := R2') IH.2.2.2.2
  use R1', R2'
  simp only [Ioo.subioo_def] at IH
  simp only [Ioo.mem_iff] at hpR1 hpR2 IH
  split_ands <;> try {
    simp[R1', R2']
    try linarith
  }
  exact IH'
}

theorem rect_fin_separable_from {n : ℕ} {R : Rectangle} {p : Point}
  {k : Fin n → Point} {f : Fin n → Rectangle}
  (hpR : p ∈ R) (hkp : ∀ i, k i ≠ p)
  (hkf : ∀ i, k i ∈ f i)
  : ∃ R' : Rectangle, ∃ f' : Fin n → Rectangle,
  R' <+ R ∧ (∀i, f' i <+ f i)
  ∧ p ∈ R' ∧ (∀i, k i ∈ f' i)
  ∧ ∀p ∈ R', ∀i, p ∉ f' i
  := by{
  have rect_separable' {R1 R2 : Rectangle} {p1 p2 : Point}
  (hp12 : p1 ≠ p2) (hpR1 : p1 ∈ R1) (hpR2 : p2 ∈ R2) :
  ∃RR : Rectangle × Rectangle,
    RR.1 <+ R1 ∧ RR.2 <+ R2 ∧ p1 ∈ RR.1 ∧ p2 ∈ RR.2
    ∧ ∀p, p ∈ RR.1 → p ∉ RR.2 := by{
    have ⟨R1, R2, h⟩ := rect_separable hp12 hpR1 hpR2
    use (R1, R2)
  }
  let f'2 : Fin n → Rectangle × Rectangle := fun i =>
    Classical.choose (rect_separable' (hkp i).symm hpR (hkf i))
  have hf'2 := fun i => Classical.choose_spec (rect_separable' (hkp i).symm hpR (hkf i))
  change ∀i, (f'2 i).1 <+ R ∧ (f'2 i).2 <+ f i ∧
      p ∈ (f'2 i).1 ∧
        k i ∈ (f'2 i).2 ∧ ∀ p_1 ∈ (f'2 i).1, p_1 ∉ (f'2 i).2 at hf'2
  let f' : Fin n → Rectangle := fun i => (f'2 i).2
  rcases eq_zero_or_pos n with hn0 | hnp
  · {
    use R
    simp only [hn0, Fin.isEmpty_iff, IsEmpty.forall_iff, implies_true, and_self,
      nonempty_fun, true_or, exists_const, hpR, Rectangle.subrect_refl]
  }
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := by{
    use ⟨0, hnp⟩
    simp
  }
  let R' : Rectangle := Rectangle.iInter' hs (fun i => (f'2 i).1)
  use R', f'
  constructor
  · {
    apply Rectangle.iInter'_subrect_of_subrect
    intro i _
    exact (hf'2 i).1
  }
  constructor
  · {
    intro i
    exact (hf'2 i).2.1
  }
  constructor
  · {
    unfold R'; rw[Rectangle.mem_iInter'_iff]
    intro i _
    exact (hf'2 i).2.2.1
  }
  constructor
  · {
    intro i
    exact (hf'2 i).2.2.2.1
  }
  intro p hp i
  unfold R' at hp; rw[Rectangle.mem_iInter'_iff] at hp
  exact (hf'2 i).2.2.2.2 p (hp i (by{simp}))
}

theorem rect_fin_separable {n : ℕ} {k : Fin n → Point} {f : Fin n → Rectangle}
  (hk : Injective k) (hkf : ∀ i, k i ∈ f i) : ∃ f' : Fin n → Rectangle,
  (∀i, k i ∈ f' i) ∧ (∀i, f' i <+ f i)
  ∧ (∀i j p, p ∈ f' i → p ∈ f' j → i = j)
  := by{
  induction n with
  | zero => simp
  | succ n ih => {
    let k' : Fin n → Point := fun i => k i.castSucc
    let f' : Fin n → Rectangle := fun i => f i.castSucc
    specialize ih (k := k') (f := f')
      (by{
        intro i1 i2 hi12
        unfold k' at hi12
        apply hk at hi12
        apply Fin.castSucc_injective at hi12
        exact hi12
      }) (by{
        intro i
        unfold k' f'
        apply hkf
      })
    rcases ih with ⟨f'', hkf'', hff'', hfI''⟩
    let p := k (Fin.last n)
    let R := f (Fin.last n)
    have hpR : p ∈ R := hkf _
    have hk'p : ∀ i, k' i ≠ p := by{
      intro i
      unfold k' p
      rw[hk.ne_iff]
      simp
    }
    have ⟨R', f3, hf3⟩ := rect_fin_separable_from hpR hk'p hkf''
    let f4 : Fin (n + 1) → Rectangle := fun i =>
      if hi : i = Fin.last n then R'
      else f3 (Fin.castPred i hi)
    use f4
    constructor
    · {
      intro i
      unfold f4
      split_ifs with hi
      · rw[hi]; exact hf3.2.2.1
      · {
        have hf3' := hf3.2.2.2.1 (Fin.castPred i hi)
        exact hf3'
      }
    }
    constructor
    · {
      intro i
      unfold f4
      split_ifs with hi
      · rw[hi]; exact hf3.1
      · {
        have hf3' := hf3.2.1 (Fin.castPred i hi)
        have hff''' := hff'' (Fin.castPred i hi)
        exact Rectangle.subrect_trans hf3' hff'''
      }
    }
    · {
      intro i j p hpi hpj
      unfold f4 at hpi hpj
      split_ifs at hpi hpj with hi hj hj
      · rw[hi, hj]
      · {
        have hf3' := hf3.2.2.2.2 _ hpi _ hpj
        contradiction
      }
      · {
        have hf3' := hf3.2.2.2.2 _ hpj _ hpi
        contradiction
      }
      · {
        have hpi' : p ∈ f'' (i.castPred hi) := by{
          have hf3' := hf3.2.1 (i.castPred hi)
          apply hf3'.subset
          exact hpi
        }
        have hpj' : p ∈ f'' (j.castPred hj) := by{
          have hf3' := hf3.2.1 (j.castPred hj)
          apply hf3'.subset
          exact hpj
        }
        have hfI3 := hfI'' (Fin.castPred i hi) (Fin.castPred j hj)
          p hpi' hpj'
        rw[Fin.castPred_inj] at hfI3
        exact hfI3
      }
    }
  }
}

end RealPlane
