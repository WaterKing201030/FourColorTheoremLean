import Mathlib.Basic.Real.Basic

/-! 实平面上点、区域和地图的定义 -/

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

@[ext] structure PlainMap where
  getRegion : Point → Region
  getRegion_symm {x y} : y ∈ getRegion x → x ∈ getRegion y
  getRegion_trans {x y} : y ∈ getRegion x → getRegion y ⊆ getRegion x

namespace PlainMap

@[inline] instance instCoeFun
: CoeFun PlainMap (fun _ => Point → Region) where
  coe := getRegion

theorem mem_region_iff {m : PlainMap} {x y : Point} :
  x ∈ m y ↔ m y x := Iff.rfl
@[symm] theorem symm {m : PlainMap} {x y : Point} : m x y → m y x := by{
  apply getRegion_symm
}
@[trans] theorem trans {m : PlainMap} {x y z : Point} : m x y → m y z → m x z := by{
  intro h
  apply getRegion_trans
  exact h
}
theorem comm {m : PlainMap} {z1 z2 : Point} : m z1 z2 = m z2 z1 := by{
  ext
  exact ⟨symm, symm⟩
}
theorem eq_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : m z1 = m z2 := by{
    ext z
    change m z1 z ↔ m z2 z
    constructor
    · apply trans; exact symm h12
    · apply trans h12
  }
theorem congr_left_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z1 z ↔ m z2 z:=by{
    simp[eq_of_rel h12]
  }
theorem congr_right_of_rel {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z z1 ↔ m z z2:=by{
  intro z
  simp only [comm (z1:=z), congr_left_of_rel h12]
}

def empty : PlainMap where
  getRegion := ⊥
  getRegion_symm := by{simp}
  getRegion_trans := by{simp}
def univ : PlainMap where
  getRegion := ⊤
  getRegion_symm := by{simp}
  getRegion_trans := by{simp}
theorem empty_getRegion {p : Point} : empty p = ∅ := rfl
theorem univ_getRegion {p : Point} : univ p = Set.univ := rfl
theorem empty_rel_eq {p q : Point} : empty p q = False := rfl
theorem univ_rel_eq {p q : Point} : univ p q = True := rfl
@[simp] theorem not_empty_rel {p q : Point} : ¬empty p q := by{simp[empty_rel_eq]}
@[simp] theorem univ_rel {p q : Point} : univ p q := by{simp[univ_rel_eq]}

def cover (m : PlainMap) : Region :=
  {z | m z z}
theorem cover_iff {m : PlainMap} {z : Point} :
  z ∈ cover m ↔ m z z := Iff.rfl
theorem cover_of_rel_left {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : m.cover z1 := by{
    have h21 := symm h12
    exact trans h12 h21
  }
theorem cover_of_rel_right {m : PlainMap} {z1 z2 : Point} (h12 : m z1 z2)
  : m.cover z2 := by{
    have h21 := symm h12
    exact trans h21 h12
  }
@[simp] theorem empty_cover : empty.cover = ∅ := rfl
@[simp] theorem univ_cover : univ.cover = Set.univ := rfl

def submap (m1 m2 : PlainMap) :=
  ∀p, m1 p ⊆ m2 p
@[inline] instance instPartialOrder : PartialOrder PlainMap where
  le := submap
  le_refl := by intro m; simp [submap]
  le_trans := by intros m1 m2 m3 h1 h2; simp [submap]; tauto
  le_antisymm := by intros m1 m2 h12 h21; ext x y; exact ⟨by apply h12, by apply h21⟩
theorem submap_iff {m1 m2 : PlainMap} : m1 ≤ m2 ↔ ∀ p, m1 p ⊆ m2 p := by rfl
@[inline] instance instOrderBot : OrderBot PlainMap where
  bot := empty
  bot_le := by intro a; rw[submap_iff]; simp[empty_getRegion]
@[inline] instance instOrderTop : OrderTop PlainMap where
  top := univ
  le_top := by intro a; rw[submap_iff]; simp[univ_getRegion]
@[refl] theorem submap_refl : ∀m : PlainMap, m ≤ m := le_refl
theorem submap_trans {m1 m2 m3 : PlainMap} : m1 ≤ m2 → m2 ≤ m3 → m1 ≤ m3 :=
  le_trans
theorem submap_antisymm {m1 m2 : PlainMap} : m1 ≤ m2 → m2 ≤ m1 → m1 = m2 :=
  le_antisymm

theorem cover_subset_of_submap {m1 m2 : PlainMap} (hm : m1 ≤ m2) : cover m1 ⊆ cover m2 := by{
  intro z hz
  exact hm _ hz
}

def at_most_regions (m : PlainMap) (n : ℕ) : Prop :=
  ∃ f : ℕ → Point, ∀p, m.cover p → ∃i < n, m (f i) p

theorem at_most_regions_def {m : PlainMap} {n : ℕ}
  : at_most_regions m n ↔ ∃ f : ℕ → Point, ∀p, m.cover p → ∃i < n, m (f i) p := by rfl
theorem at_most_regions_iff {m : PlainMap} {n : ℕ}
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
theorem at_most_regions_le {m : PlainMap} {n1 n2 : ℕ} (hn12 : n1 ≤ n2)
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

def isFinite (m : PlainMap) : Prop :=
  ∃ n, m.at_most_regions n
theorem empty_region_0 : empty.at_most_regions 0 := by{
  use fun _ => (0, 0)
  intro p hp
  simp at hp
  contradiction
}
theorem empty_isFinite : isFinite empty := by{
  use 0
  exact empty_region_0
}
theorem univ_region_1 : univ.at_most_regions 1 := by{
  use fun _ => (0, 0)
  intro p _
  use 0, by{simp}
  simp
}
theorem univ_isFinite : isFinite univ := by{
  use 1
  exact univ_region_1
}

end PlainMap
end RealPlane
