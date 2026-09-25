import FourColorTheorem.RealPlane.Defs

/-! 一些基本的引理，用来构造AdjBox -/

namespace RealPlane
namespace PlainMap
theorem exists_boundarypoint_of_adjacent {m : PlainMap} {p0 p1 : Point}
  : m.adjacent p0 p1 →
  ∃p, p ∈ m.boundary p0 p1
  ∧ ∀p2, p ∈ closure (m p2) → m p0 p2 ∨ m p1 p2 := by{
  intro h
  have h0 := cover_of_adjacent_left h
  have h1 := cover_of_adjacent_right h
  unfold adjacent at h
  have ⟨z, hz1, hz2⟩ := h.2
  use z
  apply And.intro hz2
  intro p2
  rw[mem_not_corner_iff] at hz1
  intro hp2
  rcases hz2 with ⟨hp0, hp1⟩
  have h' := h.1
  have ⟨f, hf⟩ := hz1
  have ⟨i, hi, hip⟩ := hf p0 ⟨hp0, h0⟩
  have ⟨j, hj, hjp⟩ := hf p1 ⟨hp1, h1⟩
  have h2 : (m p2).Nonempty := by{
    rw[← closure_nonempty_iff]
    apply Set.nonempty_of_mem hp2
  }
  rw[← cover_iff_nonempty] at h2
  have ⟨k, hk, hkp⟩ := hf p2 ⟨hp2, h2⟩
  have hij : i ≠ j := by{
    intro hij
    apply h'
    apply corner_map_submap (p := z)
    rw[← hij] at hjp
    exact trans (symm hip) hjp
  }
  have hkij : k = i ∨ k = j := by{omega}
  rcases hkij with hki | hkj
  · left; rw[hki] at hkp; apply corner_map_submap (p := z); exact trans (symm hip) hkp
  · right; rw[hkj] at hkp; apply corner_map_submap (p := z); exact trans (symm hjp) hkp
}
theorem exists_disjoint_rect_of_adjacent {m : PlainMap} {p0 p1 p2 : Point}
: m.adjacent p0 p1 → m.cover p2 → ¬m p0 p2 → ¬m p1 p2 →
  ∃R : Rectangle, (∃p ∈ R, p ∈ m.boundary p0 p1)
  ∧ ∀z ∈ R, z ∉ closure (m p2) := by{
  intro hap01 hp2 hm02 hm12
  have ⟨p, hpb, hpc⟩ := exists_boundarypoint_of_adjacent hap01
  have hp2 : p ∉ closure (m p2) := by{
    intro h
    specialize hpc p2 h
    simp[hm02, hm12] at hpc
  }
  rw[Region.mem_closure_rectangle_iff] at hp2
  push Not at hp2
  have ⟨u, hu0, hu1⟩ := hp2
  use u, (by{use p})
  intro z hzu hzu'
  apply hu1
  symm
  rw[← Region.meet_iff_meet_closure_of_open (Rectangle.isOpen _)]
  symm
  use z, hzu'
  exact hzu
}
theorem exists_disjoint_rect_of_edge {m : PlainMap} {p0 p1 p p2 : Point}
: p ∈ m.boundary p0 p1 →
  (∀p2, p ∈ closure (m p2) → m p0 p2 ∨ m p1 p2)
  → m.cover p2 → ¬m p0 p2 → ¬m p1 p2 →
  ∃R : Rectangle, p ∈ R ∧ ∀z ∈ R, z ∉ closure (m p2) := by{
  intro hpb01 hpd hp2 hp02 hp12
  have hp2' : p ∉ closure (m p2) := by{
    intro hp2
    exact (hpd p2 hp2).elim hp02 hp12
  }
  rw[Region.mem_closure_rectangle_iff] at hp2'
  push Not at hp2'
  have ⟨R, hRp, hRc⟩ := hp2'
  use R, hRp
  intro z hzR hzR'
  apply hRc
  symm
  rw[← Region.meet_iff_meet_closure_of_open (Rectangle.isOpen _)]
  symm
  exact ⟨z, hzR', hzR⟩
}
theorem exists_adjbox_of_finite_of_edge {m : PlainMap} {p0 p1 p : Point}
  (hmF : m.isFinite) : p ∈ m.boundary p0 p1 →
  (∀p2, p ∈ closure (m p2) → m p0 p2 ∨ m p1 p2) →
  ∃R : Rectangle, p ∈ R
  ∧ ∀p2, ∀z ∈ R, z ∈ m p2 → m p0 p2 ∨ m p1 p2 := by{
  intro hpb01 hp2
  unfold isFinite at hmF
  simp only [at_most_regions_iff] at hmF
  rcases hmF with ⟨n, f, hf⟩
  have ⟨R, hR⟩ := exists_rect_to_mem p
  classical
  let ab : Fin n → Rectangle := fun i =>
    if hfi01 : m (f i) p0 ∨ m (f i) p1 then
      R
    else if hfi : m.cover (f i) then
      Classical.choose (exists_disjoint_rect_of_edge hpb01
        hp2 hfi (by{
          rw[not_or] at hfi01
          have hfi01 := hfi01.left
          contrapose hfi01
          exact symm hfi01
        }) (by{
          rw[not_or] at hfi01
          have hfi01 := hfi01.right
          contrapose hfi01
          exact symm hfi01
        }))
    else
      Rectangle.null
  let s : Finset (Fin n) := Finset.univ.filter
    (fun i => m.cover (f i))
  have ⟨hp0, hp1⟩ := hpb01
  have hp0' : m.cover p0 := by{
    rw[cover_iff_nonempty, ← closure_nonempty_iff]
    apply Set.nonempty_of_mem hp0
  }
  have hs : s.Nonempty := by{
    have ⟨i, hi⟩ := hf _ hp0'
    use i
    unfold s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact cover_of_rel_left hi
  }
  let R' : Rectangle :=
    Rectangle.iInter' hs ab
  use R'
  constructor
  · {
    unfold R'
    rw[Rectangle.mem_iInter'_iff]
    intro i his
    unfold s at his
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at his
    unfold ab
    simp only [his, ↓reduceDIte]
    split_ifs with h
    · exact hR
    have h' := not_or.mp h
    have ih := Classical.choose_spec (exists_disjoint_rect_of_edge
      hpb01 hp2 his (by{
        rw[not_or] at h
        have hfi01 := h.left
        contrapose hfi01
        exact symm hfi01
      }) (by{
        rw[not_or] at h
        have hfi01 := h.right
        contrapose hfi01
        exact symm hfi01
      }))
    exact ih.1
  }
  · {
    intro p2 z hzR' hz
    unfold R' at hzR'
    rw[Rectangle.mem_iInter'_iff] at hzR'
    have ⟨i, hi⟩ := hf _ (cover_of_rel_right hz)
    have hp2z := hp2 z
    have hi' := cover_of_rel_left hi
    have hzR'' := hzR' i (by{simpa[s]})
    simp only [ab] at hzR''
    simp only [hi', ↓reduceDIte] at hzR''
    split_ifs at hzR'' with H
    · {
      apply H.imp <;> {
        intro h
        exact trans (symm h) (trans hi (symm hz))
      }
    }
    have H' := Classical.choose_spec (exists_disjoint_rect_of_edge
      hpb01 hp2 hi' (by{
        rw[not_or] at H
        have hfi01 := H.left
        contrapose hfi01
        exact symm hfi01
      }) (by{
        rw[not_or] at H
        have hfi01 := H.right
        contrapose hfi01
        exact symm hfi01
      }))
    have H'' := H'.2 _ hzR''
    exfalso
    apply H''
    apply subset_closure
    exact hi
  }
}
theorem exists_adjbox_of_finite_of_adjacent {m : PlainMap} {p0 p1 : Point}
  (hmF : m.isFinite) : m.adjacent p0 p1 →
  ∃R : Rectangle, (∃p ∈ R, p ∈ m.boundary p0 p1)
  ∧ ∀p2, ∀z ∈ R, z ∈ m p2 → m p0 p2 ∨ m p1 p2 := by{
  intro h
  have ⟨p, hp1, hp2⟩ := exists_boundarypoint_of_adjacent h
  have ⟨R, hR1, hR2⟩ := exists_adjbox_of_finite_of_edge hmF hp1 hp2
  refine ⟨R, ⟨p, hR1, hp1⟩, hR2⟩
}

end PlainMap

end RealPlane
