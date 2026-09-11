import FourColorTheorem.RealPlane.Defs

namespace RealPlane

open Set

class IsColoringMap (m k : Map) : Prop where
  coloring_plain : IsPlainMap k
  coloring_cover : k.cover ⊆ m.cover
  coloring_consistent : m.submap k
  coloring_adjacent {p1 p2 : Point}: m.adjacent p1 p2 → ¬k p1 p2

def Map.colorable_with (m : Map) (n : ℕ) : Prop :=
  ∃ k, IsColoringMap m k ∧ k.at_most_regions n
def Map.finColorable (nc : ℕ) := ∀ m : Map, [IsFiniteSimpleMap m] → m.colorable_with nc

theorem Map.finColorable_pos {nc : ℕ} (h : finColorable nc) : nc > 0 := by {
  specialize h ⊤
  by_contra hnc
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hnc
  rw[hnc] at h
  unfold Map.colorable_with at_most_regions at h
  have ⟨k, hk, f, hf⟩ := h
  have hk' : k = ⊤ := by{
    ext a b
    change k a b ↔ True
    simp only [iff_true]
    apply hk.coloring_consistent
    trivial
  }
  simp only [not_lt_zero, false_and, exists_const, imp_false, Prod.forall, hk', Pi.top_apply,
    top_eq_univ] at *
  apply hf 0 0
  trivial
}

end RealPlane
