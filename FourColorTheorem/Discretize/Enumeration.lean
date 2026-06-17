import FourColorTheorem.Reals.Approx

namespace RealPlane
open GridPlane

abbrev MapRepr (n : ℕ) := Fin n → Point
def MapRepr.proper (m : Map) {n : ℕ} (mr : MapRepr n) : Prop :=
  ∀i, m.cover (mr i) ∧ (∀j, m (mr i) (mr j) → i = j)
def MapRepr.cover (m : Map) {n : ℕ} (mr : MapRepr n) : Region :=
  {z | ∃i, m (mr i) z}

theorem mapRepr_cover_subset {m : Map} [IsPlainMap m] {n : ℕ} {mr : MapRepr n} :
  mr.cover m ⊆ m.cover := by{
    intro z hz
    change ∃_, _ at hz
    have ⟨_, hi⟩:=hz
    exact (refl_of_rel hi).right
  }
theorem exists_mapRepr (m : Map) [IsFiniteSimpleMap m] :
  ∃n, ∃(mr : MapRepr n), mr.proper m ∧ m.cover ⊆ mr.cover m := by{
    have ⟨k, ⟨mr0, sm0r0⟩⟩:=IsFiniteSimpleMap.map_finite (m:=m)
    let mr0k : MapRepr k := mr0
    have ⟨n, ⟨mr, mrP, sr0mr⟩⟩
    : ∃n, ∃mr : MapRepr n,  mr.proper m ∧ mr0k.cover m ⊆ mr.cover m := by{
      clear sm0r0
      induction k with
      | zero => {
        use 0
        simp[MapRepr.proper, MapRepr.cover]
      }
      | succ k ih => {
        let mr0' : Fin k → Point := mr0 ∘ Fin.castSucc
        have ⟨n, mr, mrP, sr0mr⟩:=ih mr0'
        let t := mr0 (Fin.last k)
        rcases em (m.cover t → mr.cover m t) with mr_t | mr't
        · {
          refine ⟨n, mr, mrP, ?_⟩
          intro z ⟨j, hj⟩
          rcases Fin.eq_castSucc_or_eq_last j with ⟨j', hj'⟩ | hj'
          · {
            apply sr0mr
            use j'
            unfold mr0'
            rw[Function.comp_apply, ←hj']
            exact hj
          }
          · {
            rw[MapRepr.cover, Set.mem_setOf]
            rw[hj'] at hj
            change m t z at hj
            have ⟨i, hi⟩:=mr_t (refl_of_rel hj).left
            exact ⟨i, map_trans hi hj⟩
          }
        }
        simp only [Classical.not_imp] at mr't
        use n + 1
        use fun i =>
          if hi : i = Fin.last n then t
          else mr (Classical.choose (Fin.eq_castSucc_of_ne_last hi))
        constructor
        · {
          rw[MapRepr.proper]
          intro i
          rw[MapRepr.cover] at mr't
          change _ ∧ ¬∃_, _ at mr't
          simp only [not_exists] at mr't
          rcases em (i = Fin.last n) with hi' | hi'
          · {
            simp only [hi', ↓reduceDIte, mr't, true_and]
            intro j
            rcases em (j = Fin.last n) with hj' | hj'
            · simp[hj']
            · {
              simp only [map_comm (m:=m) (z2:=t)] at mr't
              simp[hj', mr't]
            }
          }
          · {
            simp only [hi', ↓reduceDIte]
            have spec := Classical.choose_spec (Fin.eq_castSucc_of_ne_last hi')
            have ih' := mrP (Classical.choose (Fin.eq_castSucc_of_ne_last hi'))
            simp only [ih', true_and]
            intro j
            rcases em (j = Fin.last n) with hj' | hj'
            · simp[hj', hi', mr't]
            · {
              simp only [hj', ↓reduceDIte]
              intro h'
              have ih'':=ih'.right (Classical.choose (Fin.eq_castSucc_of_ne_last hj')) h'
              have spec' := Classical.choose_spec (Fin.eq_castSucc_of_ne_last hj')
              rw[←spec, ←spec']
              rw[Fin.castSucc_inj]
              exact ih''
            }
          }
        }
        · {
          intro z hz
          have ⟨i, hi⟩:=hz
          change ∃i, _
          simp only
          rcases em (i = Fin.last k) with hi' | hi'
          · {
            rw[hi'] at hi
            change m t z at hi
            use Fin.last n
            simp[hi]
          }
          · {
            have ⟨j, hj⟩:=Fin.eq_castSucc_of_ne_last hi'
            have sr0mr' : mr0' j ∈ MapRepr.cover m mr0' := by{
              change ∃_, _
              use j
              unfold mr0'
              simp only [Function.comp_apply, hj]
              exact (refl_of_rel hi).left
            }
            have ⟨j', hj'⟩:=sr0mr sr0mr'
            use j'.castSucc
            simp only [Fin.castSucc_ne_last, ↓reduceDIte, Fin.castSucc_inj, Classical.choose_eq]
            apply map_trans' hj'
            unfold mr0'
            simp only [Function.comp_apply, hj]
            exact hi
          }
        }
      }
    }
    refine ⟨n, mr, mrP, ?_⟩
    apply Set.Subset.trans ?_ sr0mr
    intro x hx
    have ⟨i, hi⟩:=sm0r0 x hx
    use i
  }

end RealPlane
