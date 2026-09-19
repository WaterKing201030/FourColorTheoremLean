import FourColorTheorem.GridPlane.Matte

namespace GridPlane

abbrev AdjIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
@[inline] instance AdjIndex.instFintype {n : ℕ}
: Fintype (AdjIndex n) := inferInstance
@[inline] instance AdjIndex.instMembership {n : ℕ}
: Membership (Fin n) (AdjIndex n) where
  mem := fun b a => a = b.val.1 ∨ a = b.val.2
theorem AdjIndex.mem_iff {n : ℕ} {i : Fin n} {e : AdjIndex n}
: i ∈ e ↔ i = e.val.1 ∨ i = e.val.2 := Iff.rfl

structure AdjBox (n : ℕ) where
  ab : AdjIndex n → GRectangle
  ab_injOn : ∀e f p, p ∈ ab e → p ∈ ab f → e = f

theorem AdjBox.disjoint {n : ℕ} {AB : AdjBox n} :
  ∀e f, e ≠ f → ∀p ∈ AB.ab e, p ∉ AB.ab f := by{
  intro e f hef p hpe hpf
  apply hef
  apply AB.ab_injOn _ _ _ hpe hpf
}

end GridPlane
