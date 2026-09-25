import FourColorTheorem.RealPlane.Defs

/-! 在每个区域中选择一个点 -/

namespace RealPlane
namespace PlainMap

@[ext] structure IndexedMap (m0 : PlainMap) (n : ℕ) where
  some : Fin n → Point
  some_covered : ∀i, m0.cover (some i)
  some_injOn : ∀i j, m0 (some i) (some j) → i = j
  some_surjOn : ∀p, m0.cover p → ∃i, m0 (some i) p

namespace IndexedMap

variable {m0 : PlainMap} {n : ℕ}

@[inline] instance instCoeFun :
  CoeFun (IndexedMap m0 n) (fun _ => Fin n → Point) where
  coe := some
theorem some_surjOn_iff {m0 : PlainMap} {n : ℕ}
  {MR : IndexedMap m0 n} : ∀p, m0.cover p ↔ ∃i, m0 (MR i) p := by{
  intro p
  apply Iff.intro (MR.some_surjOn p)
  intro ⟨i, hi⟩
  exact m0.cover_of_rel_right hi
}

theorem finiteMap {MR : IndexedMap m0 n} : m0.isFinite := by{
  use n
  rw[at_most_regions_iff]
  use MR.some
  exact MR.some_surjOn
}

def cover (MR : IndexedMap m0 n)
  : Region := {z | ∃i, m0 (MR i) z}

theorem cover_eq (MR : IndexedMap m0 n)
  : MR.cover = m0.cover := by{
  ext p
  unfold cover PlainMap.cover
  rw[Set.mem_ofPred, Set.mem_ofPred]
  constructor
  · intro ⟨i, hi⟩; exact cover_of_rel_right hi
  · apply MR.some_surjOn
}

theorem unique_some (MR : IndexedMap m0 n)
: ∀p, m0.cover p → ∃! i, m0 (MR i) p := by{
  intro p hp
  have ⟨i, hi⟩ := MR.some_surjOn p hp
  use i, hi
  intro j hj
  apply MR.some_injOn
  exact trans hj (symm hi)
}

noncomputable def index (MR : IndexedMap m0 n) (p : Point) (hp : m0.cover p)
: Fin n := Classical.choose (MR.unique_some p hp)
end IndexedMap

theorem exists_indexedMap {m0 : PlainMap}
  (hmF : m0.isFinite) :
  ∃n, Nonempty (IndexedMap m0 n)
:= by{
  rcases hmF with ⟨n, k, hkm⟩
  classical
  let s : Finset (Fin n) := {i | m0.cover (k i) ∧ ∀j : Fin n, j > i → m0 (k j) ≠ m0 (k i)}
  use s.card
  have hs_cover : ∀ i ∈ s, m0.cover (k i) := by{
    unfold s
    intro i hi
    simp at hi
    simp[hi]
  }
  have hs_inj : ∀i ∈ s, ∀j : Fin n, j > i → m0 (k j) ≠ m0 (k i) := by{
    unfold s
    intro i hi
    simp only [gt_iff_lt, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2
  }
  have hs_fc : ∀p, m0.cover p → ∃i ∈ s, m0 (k i) p := by{
    intro p hp
    specialize hkm p hp
    have hkm' : ∃i : Fin n, m0.getRegion (k i) p := by{
      rcases hkm with ⟨i, hi, hip⟩
      use ⟨i, hi⟩
    }
    rw[Fin.exists_iff_exists_maximal] at hkm'
    rcases hkm' with ⟨i, hip, him⟩
    use i
    refine ⟨?_, hip⟩
    unfold s
    simp only [gt_iff_lt, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · apply cover_of_rel_left hip
    intro j hij
    specialize him j hij
    contrapose him
    exact him ▸ hip
  }
  let MR : IndexedMap m0 s.card := {
    some := fun i => k s.toList[i],
    some_covered := by{
      intro i
      apply hs_cover
      rw[← Finset.mem_toList]
      simp
    },
    some_injOn := by{
      intro i j hij
      by_contra hnij
      wlog hlij : s.toList[i] < s.toList[j] with IH
      · {
        specialize IH n k hkm hs_cover hs_inj hs_fc
          j i (m0.symm hij) (Ne.symm hnij)
        apply IH
        apply le_of_not_gt at hlij
        apply lt_of_le_of_ne hlij
        rw[ne_eq]
        intro h
        have hs' := @s.nodup_toList.getElem_inj
        simp[hs'] at h
        omega
      }
      clear hnij
      specialize hs_inj (s.toList[i]) (by{
        rw[← Finset.mem_toList]
        simp
      })  _ hlij
      apply hs_inj
      apply eq_of_rel
      apply m0.symm hij
    },
    some_surjOn := by{
      intro z hz
      specialize hs_fc _ hz
      rcases hs_fc with ⟨i, hi, hip⟩
      rw[← Finset.mem_toList, List.mem_iff_getElem] at hi
      rcases hi with ⟨j, hj, hji⟩
      use ⟨j, by{simp at hj; simp[hj]}⟩
      simpa[hji]
    }
  }
  apply Nonempty.intro MR
}

end PlainMap
end RealPlane
