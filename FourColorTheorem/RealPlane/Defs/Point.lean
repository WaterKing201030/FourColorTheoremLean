import Mathlib.Data.Real.Basic

namespace RealPlane

abbrev Point := ℝ × ℝ
abbrev Region := Set Point
abbrev Map := Point → Region

namespace Map

theorem mem_region_iff {m : Map} {x y : Point} :
  x ∈ m y ↔ m y x := Iff.rfl

def cover (m : Map) : Region :=
  {z | m z z}
theorem cover_iff {m : Map} {z : Point} :
  z ∈ cover m ↔ m z z := Iff.rfl

def submap (m1 m2 : Map) :=
  ∀p, m1 p ⊆ m2 p
@[inline] instance instPartialOrder : PartialOrder Map where
  le := submap
  le_refl := by intro m; simp [submap]
  le_trans := by intros m1 m2 m3 h1 h2; simp [submap]; tauto
  le_antisymm := by intros m1 m2 h12 h21; ext x y; exact ⟨by apply h12, by apply h21⟩
theorem submap_iff {m1 m2 : Map} : m1 ≤ m2 ↔ ∀ p, m1 p ⊆ m2 p := by rfl
@[inline] instance instOrderBot : OrderBot Map where
  bot_le := by intro a; rw[submap_iff]; simp
@[refl] theorem submap_refl : ∀m : Map, m ≤ m := le_refl
theorem submap_trans {m1 m2 m3 : Map} : m1 ≤ m2 → m2 ≤ m3 → m1 ≤ m3 :=
  le_trans
theorem submap_antisymm {m1 m2 : Map} : m1 ≤ m2 → m2 ≤ m1 → m1 = m2 :=
  le_antisymm

theorem cover_subset_of_submap {m1 m2 : Map} (hm : m1 ≤ m2) : cover m1 ⊆ cover m2 := by{
  intro z hz
  exact hm _ hz
}

def at_most_regions (m : Map) (n : ℕ) : Prop :=
  ∃ f : ℕ → Point, ∀p, m.cover p → ∃i < n, m (f i) p

theorem at_most_regions_def {m : Map} {n : ℕ}
  : at_most_regions m n ↔ ∃ f : ℕ → Point, ∀p, m.cover p → ∃i < n, m (f i) p := by rfl
theorem at_most_regions_iff {m : Map} {n : ℕ}
  : at_most_regions m n ↔
  ∃ f : Fin n → Point, ∀ p, m.cover p → ∃ i, m (f i) p := by{
  rw[at_most_regions]
  constructor
  · {
    intro ⟨f, h⟩
    use f ∘ Fin.val
    intro p hp
    have ⟨i, hi, hfi⟩ := h p hp
    use ⟨i, hi⟩
    simp[hfi]
  }
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
}
theorem at_most_regions_le {m : Map} {n1 n2 : ℕ} (hn12 : n1 ≤ n2)
  (hm : m.at_most_regions n1) : m.at_most_regions n2 := by{
    have ⟨f, h⟩:=hm
    let f' := fun i => if i < n1 then f i else f 0
    use f'
    intro p hp
    have ⟨i, hin, hi⟩:=h p hp
    refine ⟨i, lt_of_lt_of_le hin hn12, ?_⟩
    unfold f'
    simp[hin, hi]
  }

end Map
end RealPlane
