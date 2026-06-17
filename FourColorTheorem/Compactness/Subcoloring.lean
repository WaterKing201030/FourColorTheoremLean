import FourColorTheorem.Reals.PartialMap

namespace RealPlane

/-
 - 子涂色
 - 满足三个条件：
 - 1. 涂色部分平凡（对称传递）
 - 2. 相邻不同色；这并不平凡，因为
 - 3. 涂色颜色不超过nc种颜色上限；后续我们将要证明存在这样的上界
 - 与涂色coloring比较，可以发现它并没有规定每个区域内部颜色是否相同

 - 局部涂色
 - 满足两个条件
 - 1. k是一个m上的涂色
 - 2. 前n个标准点规定的区域被涂色方案k覆盖；
 - 也就是说，现在规定在前n个标准点规定的区域中，k必须让每个区域内只有一种颜色

 - 可扩展涂色
 - 对于任意的标准点数量n，都存在一种部分涂色方案k，并且该方案在前n0个标准点上与原始涂色方案k0一致
 - 可以理解为，对于R^2上的地图，若其存在一种涂色方案，则对于其上的任意部分涂色方案，添加任意数量标准点
 - 连接的区域，也存在部分涂色方案
 -/

class IsSubColoringMap (m : Map) (nc : ℕ) (k : Map) : Prop where
  coloring_plain : IsPlainMap k
  coloring_adjacent {p1 p2 : Point}: m.adjacent p1 p2 → ¬k p1 p2
  coloring_size : k.at_most_regions nc
def partialColoring (m : Map) (nc : ℕ) (k : Map) (n : ℕ) : Prop :=
  IsSubColoringMap m nc k ∧ (m.partialMap n m).submap k
def extensibleColoring (m : Map) (nc : ℕ) (k0 : Map) (n0 : ℕ):=
  ∀n, ∃k, partialColoring m nc k n ∧ partialEqOn m n0 k0 k

@[simp] theorem subColoring_of_bot {m : Map} {nc : ℕ} : IsSubColoringMap m nc ⊥ where
  coloring_plain := bot_isPlainMap
  coloring_adjacent := by{
    simp only [Pi.bot_apply, Set.bot_eq_empty]
    intro _ p2 _
    change p2 ∉ (∅ : Set Point)
    simp
  }
  coloring_size := at_most_regions_le (Nat.zero_le _) bot_atmost_zero
@[simp] theorem partialColoring_zero_iff_subColoring {m : Map} {nc : ℕ} {k : Map}
  : partialColoring m nc k 0 ↔ IsSubColoringMap m nc k := by{
    simp only [partialColoring, partialMap_zero, and_iff_left_iff_imp]
    intro _
    intro z1 z2 hz2
    change False at hz2
    exact hz2.elim
  }
@[simp] theorem partialColoring_bot_iff_eq_bot {m : Map} {nc : ℕ} {n : ℕ}
  : partialColoring m nc ⊥ n ↔ m.partialMap n m = ⊥ := by{
    simp[partialColoring]
  }
@[simp] theorem partialColoring_bot_iff_eq_empty {m : Map} [IsPlainMap m] {nc : ℕ} {n : ℕ}
  : partialColoring m nc ⊥ n ↔ m.partialRegion n = ∅ := by{
    simp[partialColoring, partialMap_eq_bot_iff_partialRegion_eq_empty]
  }
@[simp] theorem extensibleColoring_zero_iff {m : Map} {nc : ℕ} {k0 : Map}
  : extensibleColoring m nc k0 0 ↔ ∀n, ∃k, partialColoring m nc k n := by{
    simp[extensibleColoring]
  }

def finColorMap (n : ℕ) (g : Point → ℕ) : Map :=
  fun z t => g z = g t ∧ g t < n
def finColorMap' (n : ℕ) (g : Point → ℝ) : Map :=
  fun z t => g z = g t ∧ g t < n
theorem finColorMap_symm {n : ℕ} {g : Point → ℕ} {z1 z2 : Point}
  : finColorMap n g z1 z2 → finColorMap n g z2 z1 := by{
    simp only [finColorMap]
    intro ⟨h1, h2⟩
    exact ⟨h1.symm, h1 ▸ h2⟩
  }
theorem finColorMap_trans {n : ℕ} {g : Point → ℕ} {z1 z2 z3 : Point}
  : finColorMap n g z1 z2 → finColorMap n g z2 z3 → finColorMap n g z1 z3 := by{
    simp only [finColorMap]
    intro ⟨h11, h12⟩ ⟨h21, h22⟩
    exact ⟨h11.trans h21, h22⟩
  }
@[implicit_reducible] def finColorMap_isPlainMap {n : ℕ} {g : Point → ℕ}
  : IsPlainMap (finColorMap n g) where
  map_symm := finColorMap_symm
  map_trans := fun h _ => finColorMap_trans h
def finColorMap_eq_finColorMap' {n : ℕ} {g : Point → ℕ}
  : finColorMap n g = finColorMap' n (fun z => g z) := by{
    apply funext₂
    intro z1 z2
    rw[finColorMap, finColorMap']
    simp
  }

theorem partialMap_subcoloring_of_subcoloring {m : Map} {nc : ℕ} {k : Map} {n : ℕ}
  (hs : IsSubColoringMap m nc k) : IsSubColoringMap m nc (m.partialMap n k) := by{
    have ⟨kP, adj'k, h⟩:=hs
    apply IsSubColoringMap.mk
    · apply partialMap_isPlainMap
    · {
      intro _ _ hp12 ⟨kp12, _⟩
      exact adj'k hp12 kp12
    }
    · apply size_partialMap m n h
  }

theorem partialColoring_exists (m : Map) [IsSimpleMap m] {nc : ℕ} (n : ℕ)
  (fin_colorable : finColorable nc) : ∃ k : Map, partialColoring m nc k n := by{
    have ⟨k, ⟨kP, n_k, k_n, adj'k⟩, nc_k⟩ :=
      fin_colorable (m.partialMap n m) partialMap_isFiniteSimpleMap
    have clos_n (z t : Point) : z ∈ m.partialRegion n → t ∈ (m z).closure →
    (m.partialMap n m z).closure t := by{
      intro n_z m0zt r rP r_t
      have ⟨u, m0zu, r_u⟩:=m0zt r rP r_t
      refine ⟨u, ⟨m0zu, n_z, ?_⟩, r_u⟩
      apply map_apply_subset_of_mem_partialRegion n_z m0zu
    }
    refine ⟨k, ⟨kP, ?_, nc_k⟩, k_n⟩
    intro z1 z2 ⟨m0'z12, ⟨z, ⟨f, fP⟩, ⟨z1z, z2z⟩⟩⟩ kz12
    have ⟨n_z1, hz1, _⟩:=n_k (refl_of_rel kz12).left
    have ⟨n_z2, hz2, _⟩:=n_k (refl_of_rel kz12).right
    apply adj'k ?_ kz12
    rw[Map.adjacent]
    constructor
    · {
      rw[Map.mem_map_apply_iff, Map.partialMap]
      rw[Map.mem_map_apply_iff] at m0'z12
      simp[m0'z12]
    }
    have z1z':=clos_n _ _ hz1 z1z
    have z2z':=clos_n _ _ hz2 z2z
    use z
    rw[Set.mem_inter_iff]
    constructor
    · {
      rw[Map.not_corner, Set.mem_setOf]
      use f
      intro p hp
      have h' : (m.corner_map z).cover p := by{
        simp only [Map.cover, Map.corner_map] at hp
        change _ ∧ m.partialMap _ _ _ _ at hp
        rw[Map.partialMap] at hp
        simp only [Map.cover, Map.corner_map]
        change _ ∧ _
        refine ⟨?_, hp.right.left⟩
        apply Region.closure_subset_closure_of_subset ?_ hp.left
        apply partialMap_submap
      }
      have hp': p ∈ m.partialRegion n := by{
        simp only [Map.cover, Map.corner_map] at hp
        change _ ∧ m.partialMap _ _ _ _ at hp
        rw[Map.partialMap] at hp
        exact hp.2.2.1
      }
      have ⟨i, hi0, hi1⟩:=fP _ h'
      simp only [Map.corner_map]
      change ∃i, _ ∧ _
      simp only [Map.mem_map_apply_iff]
      simp only [@map_comm (m.partialMap n m) partialMap_isPlainMap]
      simp only [partialMap_apply_eq_of_mem_partialRegion hp']
      use i
      rw[map_comm (m:=m)]
      refine ⟨?_, hi1⟩
      have hfi : f i ∈ m.partialRegion n := by{
        apply map_apply_subset_of_mem_partialRegion hp'
        exact map_symm hi1
      }
      simp only [partialMap_apply_eq_of_mem_partialRegion hfi]
      exact hi0
    }
    · {
      rw[Map.border, Set.mem_inter_iff]
      exact ⟨z1z', z2z'⟩
    }
  }
theorem partialColoring_of_le {m : Map} {nc : ℕ} {k : Map} {n1 n2 : ℕ}
  (len12 : n1 ≤ n2) : partialColoring m nc k n2 → partialColoring m nc k n1 := by{
    intro ⟨k_n2, n_k⟩
    apply And.intro k_n2
    intro z1 z2 n1z12
    apply n_k
    apply partialMap_submap_of_le len12
    apply n1z12
  }
theorem extensible_partialMap_of_le {m : Map} {nc : ℕ} {k : Map} {n1 n2 : ℕ}
  (le_n12 : n1 ≤ n2) (ext_k : extensibleColoring m nc k n2)
  : extensibleColoring m nc (m.partialMap n1 k) n1 := by{
    intro n
    have ⟨k', k'P, Ekk'⟩:=ext_k n
    use k'
    apply And.intro k'P
    have Ekk'':=partialEqOn_of_partialEqOn_of_ge le_n12 Ekk'
    apply partialEqOn_trans ?_ Ekk''
    apply partialEqOn_symm
    apply partialEqOn_partialMap
  }

end RealPlane
