import FourColorTheorem.RealPlane.Defs

/-! 将有限地图编码 -/

namespace RealPlane
namespace PlainMap

structure MapRepr (m0 : PlainMap) (n : ℕ) where
  mr : Fin n → Point
  mr_covered : ∀i, m0.cover (mr i)
  mr_injOn : ∀i j, m0 (mr i) (mr j) → i = j

def MapRepr.cover {m0 : PlainMap} {n : ℕ} (MR : MapRepr m0 n)
  : Region := {z | ∃i, m0 (MR.mr i) z}

theorem exists_mapRepr {m0 : PlainMap}
  (hmO : m0.allOpen) (hmC : m0.allPreconnected) (hmF : m0.isFinite) :
  ∃n, ∃MR : MapRepr m0 n, m0.cover ⊆ MR.cover
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
  let MR : MapRepr m0 s.card := {
    mr := fun i => k s.toList[i],
    mr_covered := by{
      intro i
      apply hs_cover
      rw[← Finset.mem_toList]
      simp
    },
    mr_injOn := by{
      intro i j hij
      by_contra hnij
      wlog hlij : s.toList[i] < s.toList[j] with IH
      · {
        specialize IH hmO hmC n k hkm hs_cover hs_inj hs_fc
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
    }
  }
  use MR
  intro z hz
  unfold MR
  rw[MapRepr.cover, Set.mem_ofPred]
  specialize hs_fc _ hz
  rcases hs_fc with ⟨i, hi, hip⟩
  rw[← Finset.mem_toList, List.mem_iff_getElem] at hi
  rcases hi with ⟨j, hj, hji⟩
  use ⟨j, by{simp at hj; simp[hj]}⟩
  simpa[hji]
}

end PlainMap

end RealPlane
