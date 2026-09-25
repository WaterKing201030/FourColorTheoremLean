import FourColorTheorem.RealPlane.Defs

/-! 地图的染色的定义 -/

namespace RealPlane

open Set
namespace PlainMap
class hasColoring (m k : PlainMap) : Prop where
  coloring_cover : k.cover ⊆ m.cover
  coloring_consistent : m ≤ k
  coloring_adjacent {p1 p2 : Point}: m.adjacent p1 p2 → ¬k p1 p2

def colorableWith (m : PlainMap) (n : ℕ) : Prop :=
  ∃ k, m.hasColoring k ∧ k.at_most_regions n

def simpleColorable (nc : ℕ) := ∀ m : PlainMap,
m.allOpen → m.allPreconnected
→ m.colorableWith nc
def simpleFinColorable (nc : ℕ) := ∀ m : PlainMap,
m.allOpen → m.allPreconnected → m.isFinite
→ m.colorableWith nc

theorem simpleFinColorable_of_simpleColorable {nc : ℕ}
  (hnc : simpleColorable nc) : simpleFinColorable nc :=by{
  intro m hmO hmC _
  exact hnc m hmO hmC
}
theorem simpleFinColorable_pos {nc : ℕ} (h : simpleFinColorable nc) : nc > 0 := by {
  specialize h ⊤ univ_allOpen univ_allPreconnected univ_isFinite
  by_contra hnc
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hnc
  rw[hnc] at h
  unfold colorableWith at_most_regions at h
  have ⟨k, hk, f, hf⟩ := h
  have hk' : k = ⊤ := by{
    ext a b
    change k a b ↔ True
    simp only [iff_true]
    apply hk.coloring_consistent
    trivial
  }
  simp only [not_lt_zero, false_and, exists_const, imp_false, Prod.forall, hk'] at *
  apply hf 0 0
  trivial
}

end PlainMap

end RealPlane
