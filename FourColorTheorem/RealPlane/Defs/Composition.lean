import FourColorTheorem.RealPlane.Defs.Point
import FourColorTheorem.RealPlane.Defs.Topology

namespace RealPlane

open Set

class IsPlainMap (m : Map) : Prop where
  map_symm {p1 p2 : Point}: m p1 p2 → m p2 p1
  map_trans {p1 p2 p3 : Point} : m p1 p2 → m p2 p3 → m p1 p3

namespace Map
variable {m : Map}
variable [IsPlainMap m]

@[symm] theorem symm {p1 p2 : Point} : m p1 p2 → m p2 p1 := IsPlainMap.map_symm
theorem comm {z1 z2 : Point} : m z1 z2 = m z2 z1 := by{
  ext
  exact ⟨symm, symm⟩
}
theorem trans {p1 p2 p3 : Point} : m p1 p2 → m p2 p3 → m p1 p3 := IsPlainMap.map_trans
theorem cover_of_rel_left {z1 z2 : Point} (h12 : m z1 z2)
  : m.cover z1 := by{
    have h21 := symm h12
    exact trans h12 h21
  }
theorem cover_of_rel_right {z1 z2 : Point} (h12 : m z1 z2)
  : m.cover z2 := by{
    have h21 := symm h12
    exact trans h21 h12
  }
theorem eq_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : m z1 = m z2 := by{
    ext z
    change m z1 z ↔ m z2 z
    constructor
    · apply trans; exact symm h12
    · apply trans h12
  }
theorem congr_left_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z1 z ↔ m z2 z:=by{
    simp[eq_of_rel h12]
  }
theorem congr_right_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m z z1 ↔ m z z2:=by{
  intro z
  simp only [comm (z1:=z), congr_left_of_rel h12]
}

instance cornermap_plain {p : Point} : IsPlainMap (m.corner_map p) := by{
  constructor
  · {
    intro p1 p2 hp12
    unfold corner_map at *
    have h0 := eq_of_rel hp12.2
    nth_rw 1 [←h0]
    apply hp12.imp_right symm
  }
  · {
    intro p1 p2 p3 hp12 hp23
    unfold corner_map at *
    apply hp12.imp_right (trans · hp23.2)
  }
}

theorem adjacent_Symm : Std.Symm m.adjacent := ⟨by{
  intro p0 p1 hp0
  rw[adjacent] at *
  rwa[m.comm, boundary_comm]
}⟩
@[symm] theorem adjacent_symm {z1 z2 : Point} : m.adjacent z1 z2 → m.adjacent z2 z1 :=
  m.adjacent_Symm.symm _ _
theorem adjacent_comm {z1 z2 : Point} : m.adjacent z1 z2 ↔ m.adjacent z2 z1 :=
  ⟨m.adjacent_symm, m.adjacent_symm⟩
theorem cover_of_adjacent_left {p1 p2 : Point} (h12 : m.adjacent p1 p2) :
  m.cover p1 := by{
  have ⟨h12m, ⟨k, hkc, hkb⟩⟩ := h12
  rw[mem_boundary_iff] at hkb
  apply And.left at hkb
  rw[Region.closure_eq_closure'] at hkb
  unfold Region.closure' at hkb
  rw[Set.mem_setOf] at hkb
  specialize hkb Set.univ (by{simp}) (by{simp})
  have ⟨q, hq, _⟩ := hkb
  exact cover_of_rel_left hq
}
theorem cover_of_adjacent_right {p1 p2 : Point} (h12 : m.adjacent p1 p2) :
  m.cover p2 := by{
  have ⟨h12m, ⟨k, hkc, hkb⟩⟩ := h12
  rw[mem_boundary_iff] at hkb
  apply And.right at hkb
  rw[Region.closure_eq_closure'] at hkb
  unfold Region.closure' at hkb
  rw[Set.mem_setOf] at hkb
  specialize hkb Set.univ (by{simp}) (by{simp})
  have ⟨q, hq, _⟩ := hkb
  exact cover_of_rel_left hq
}

theorem congr_adjacent_left_of_rel {z1 z2 : Point} (h12 : m z1 z2)
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
theorem adjacent_eq_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : m.adjacent z1 = m.adjacent z2 := by{
  ext z
  rw[congr_adjacent_left_of_rel h12]
}
theorem congr_adjacent_right_of_rel {z1 z2 : Point} (h12 : m z1 z2)
  : ∀z, m.adjacent z z1 ↔ m.adjacent z z2:=by{
  simp only [adjacent_comm]
  apply congr_adjacent_left_of_rel h12
}
end Map

class IsSimpleMap (m : Map) : Prop extends IsPlainMap m where
  map_open : ∀p, IsOpen (m p)
  map_connected : ∀p, IsPreconnected (m p)

class IsFiniteSimpleMap (m : Map) : Prop extends IsSimpleMap m where
  map_finite : ∃ n, m.at_most_regions n

instance isPlainMap_bot : IsPlainMap ⊥ where
  map_symm := by{intros;contradiction}
  map_trans := by{intros;contradiction}

instance isPlainMap_top : IsPlainMap ⊤ where
  map_symm := by{intros; trivial}
  map_trans := by{intros; trivial}

instance isSimpleMap_bot : IsSimpleMap ⊥ where
  toIsPlainMap := isPlainMap_bot
  map_open := by{intros; simp}
  map_connected := by{intros;intro;simp}

instance isSimpleMap_top : IsSimpleMap ⊤ where
  toIsPlainMap := isPlainMap_top
  map_open := by{intros; simp}
  map_connected := by{
    intro p
    change IsPreconnected Set.univ
    apply isPreconnected_univ
  }

instance isFiniteSimpleMap_bot : IsFiniteSimpleMap ⊥ where
  toIsSimpleMap := isSimpleMap_bot
  map_finite := by{
    exists 0
    simp[Map.at_most_regions, Map.cover]
    aesop
  }

instance isFiniteSimpleMap_top : IsFiniteSimpleMap ⊤ where
  toIsSimpleMap := isSimpleMap_top
  map_finite := by{
    exists 1
    simp[Map.at_most_regions, Map.cover]
    aesop
  }

end RealPlane
