import FourColorTheorem.Compactness.Prefixcoloring

namespace RealPlane

/-
染色极限
由于PrefixColoring总是取最小的，所以染色方案是唯一的
-/

def limitColoring (m : Map) (nc : ℕ) : Map :=
  fun z1 z2 => ∃k, isPrefixColoring m nc k ∧ k z1 z2

theorem limitColoring_symm {m : Map} {nc : ℕ}
  {z1 z2 : Point} : limitColoring m nc z1 z2 → limitColoring m nc z2 z1 := by{
    intro ⟨k, ⟨n, hn⟩, kz12⟩
    have ⟨h0, h1⟩:=partialColoring_of_prefixColoring hn
    have h2:=h0.coloring_plain
    exact ⟨k, ⟨n, hn⟩, map_symm kz12⟩
  }

theorem limitColoring_isColoring (m : Map) [IsSimpleMap m] {nc : ℕ}
  (fin_colorable : finColorable nc) : IsColoringMap m (limitColoring m nc) := by{
    apply IsColoringMap.mk
    · {
      apply IsPlainMap.mk limitColoring_symm
      intro z1 z2 ⟨k1, ⟨n1, k1Pn⟩, k1z12⟩ z3 ⟨k3, ⟨n3, k3Pn⟩, k3z23⟩
      have ⟨k1P, _⟩ := partialColoring_of_prefixColoring k1Pn
      have ⟨k, kPn, ⟨k_z12, k_z23⟩⟩ : ∃k, isPrefixColoring m nc k ∧ k z1 z2 ∧ k z2 z3 := by{
        cases le_total n1 n3 with
        | inl le_n13 => {
          have ih := submap_of_prefixColoring_of_le le_n13 k1Pn k3Pn
          refine ⟨k3, ⟨n3, k3Pn⟩, ih _ k1z12, k3z23⟩
        }
        | inr le_n31 => {
          have ih := submap_of_prefixColoring_of_le le_n31 k3Pn k1Pn
          refine ⟨k1, ⟨n1, k1Pn⟩, k1z12, ih _ k3z23⟩
        }
      }
      have ⟨_, h⟩:=kPn
      have ⟨kP, _⟩:=partialColoring_of_prefixColoring h
      have kP' := kP.coloring_plain
      refine ⟨k, kPn, ?_⟩
      apply map_trans k_z12 k_z23
    }
    · {
      intro z ⟨k, ⟨n, ⟨h2, kPn⟩⟩, kz⟩
      have ⟨h0, h1⟩:=partialColoring_of_prefixColoring ⟨h2, kPn⟩
      have h2':=h2 _ kz
      rw[Map.mem_map_apply_iff, Map.partialMap] at h2'
      have ⟨_, _, h⟩ := h2'.2.1
      exact (refl_of_rel h).left
    }
    · {
      intro z1 z2 m0z12
      have ⟨m0z1, m0z2⟩:=refl_of_rel m0z12
      have ⟨i1, m0iz1⟩:=exists_stdPoint_of_cover m0z1
      have ⟨i2, m0iz2⟩:=exists_stdPoint_of_cover m0z2
      have ⟨n, lt_i1n, lt_i2n⟩ : ∃n, i1 < n ∧ i2 < n := by{
        use (max i1 i2) + 1
        simp[Nat.lt_succ_iff]
      }
      have ⟨k, kPn⟩:=prefixColoring_exists m n fin_colorable
      refine ⟨k, ⟨n, kPn⟩, ?_⟩
      have nz1 : z1 ∈ m.partialRegion n := ⟨i1, lt_i1n, m0iz1⟩
      have nz2 : z2 ∈ m.partialRegion n := ⟨i2, lt_i2n, m0iz2⟩
      have hm : m.partialMap n m z1 z2 := ⟨m0z12, nz1, nz2⟩
      exact (partialColoring_of_prefixColoring kPn).right _ hm
    }
    · {
      intro z1 z2 adj_z12 ⟨k, ⟨⟨n, hn⟩, kz1z2⟩⟩
      have ⟨h0, h1⟩:=partialColoring_of_prefixColoring hn
      have h0':=h0.coloring_adjacent adj_z12
      exact h0' kz1z2
    }
  }

theorem size_limitColoring (m : Map) [IsSimpleMap m] {nc : ℕ}
  (fin_colorable : finColorable nc) : (limitColoring m nc).at_most_regions nc := by{
    let inmf (n : ℕ) (k : Map) (f : ℕ → Point) := ∀i < n, k.cover (f i)
    let injf (n : ℕ) (k : Map) (f : ℕ → Point) := ∀i j, i < j → j < n → ¬k (f i) (f j)
    let minsize (n : ℕ) (k : Map) := ∃f, inmf n k f ∧ injf n k f
    have inmf_of_le {n1 n2 : ℕ} {k : Map} {f : ℕ → Point} (le_n12 : n1 ≤ n2) :
      inmf n2 k f → inmf n1 k f := by{
        intro h i lt_i_n1
        apply h _ (lt_of_lt_of_le lt_i_n1 le_n12)
      }
    have injf_of_le {n1 n2 : ℕ} {k : Map} {f : ℕ → Point} (le_n12 : n1 ≤ n2) :
      injf n2 k f → injf n1 k f := by{
        intro h i j lt_ij lt_j_n1
        apply h _ _ lt_ij (lt_of_lt_of_le lt_j_n1 le_n12)
      }
    have minsize_of_le {n1 n2 : ℕ} {k : Map} (le_n12 : n1 ≤ n2)
    : minsize n2 k → minsize n1 k := by{
      intro ⟨f, h0, h1⟩
      use f
      exact ⟨inmf_of_le le_n12 h0, injf_of_le le_n12 h1⟩
    }
    have wls {k : Map} : ¬minsize (nc + 1) k → k.at_most_regions nc := by{
      apply Nat.recAux (motive := fun n => ¬minsize (n + 1) k → k.at_most_regions n)
      · {
        simp only [Map.cover, zero_add, Nat.lt_one_iff, forall_eq, not_exists, not_and, not_forall,
          not_not, exists_const,
          imp_false, Map.at_most_regions, IsEmpty.exists_iff, minsize, inmf, injf]
        simp only [exists_prop]
        simp only [↓existsAndEq, not_lt_zero, true_and, false_and, exists_const, imp_false]
        intro h p
        exact h (fun _ => p)
      }
      intro n IHn min'n2
      rcases em' (minsize (n + 1) k) with min'n1 | ⟨f, k_f, inj_fk⟩
      · apply at_most_regions_le (Nat.le_succ _) (IHn min'n1)
      rw[Map.at_most_regions_eq_at_most_regions']
      use f
      intro z k_z
      let fz (i : ℕ) := if i < n + 1 then f i else z
      apply (not_imp_comm.mp · min'n2)
      intro kf'n
      simp only [not_exists, not_and] at kf'n
      use fz
      have h0 : inmf (n + 1 + 1) k fz := by{
        unfold inmf
        intro i le_in1
        rw[Nat.lt_succ_iff] at le_in1
        rcases lt_or_eq_of_le le_in1 with lt_in1 | eq_in1
        · {
          unfold fz
          simp only [lt_in1, ↓reduceIte]
          apply k_f _ lt_in1
        }
        · {
          unfold fz
          simp[eq_in1, k_z]
        }
      }
      apply And.intro h0
      have h1 : injf (n + 1 + 1) k fz := by{
        unfold injf
        intro i j lt_ij le_jn1
        rw[Nat.lt_succ_iff] at le_jn1
        have lt_in1 := lt_of_lt_of_le lt_ij le_jn1
        rcases lt_or_eq_of_le le_jn1 with lt_jn1 | eq_jn1
        · {
          unfold fz
          simp only [lt_in1, lt_jn1, ↓reduceIte]
          apply inj_fk _ _ lt_ij lt_jn1
        }
        · {
          unfold fz
          simp only [eq_jn1, lt_irrefl, lt_in1, ↓reduceIte]
          apply kf'n _ lt_in1
        }
      }
      exact h1
    }
    apply (em (minsize (nc + 1) (limitColoring m nc))).elim ?_ wls
    intro ⟨f, lim_f, inj_limf⟩
    have ⟨k, kPn, k_f⟩ : ∃k, isPrefixColoring m nc k ∧ inmf (nc + 1) k f := by{
      have := Nat.le_refl (nc + 1)
      revert this
      apply Nat.recAux (motive := fun n => n ≤ nc + 1 → ∃ k, isPrefixColoring m nc k ∧ inmf n k f)
      · {
        simp only [le_add_iff_nonneg_left, zero_le, not_lt_zero, IsEmpty.forall_iff, implies_true,
          and_true, forall_const, inmf]
        have ⟨k, kP⟩:=prefixColoring_exists m 0 fin_colorable
        use k
        use 0
      }
      intro n IHn le_nnc
      rw[Nat.succ_le_succ_iff] at le_nnc
      have ⟨k1, ⟨n1, inj_k1f⟩, k1_f⟩ := IHn (Nat.le_succ_of_le le_nnc)
      have ⟨k2, ⟨n2, k2Pn⟩, k2_fn⟩ := lim_f n (Nat.lt_succ_of_le le_nnc)
      rcases le_total n1 n2 with le_n12 | le_n21
      · {
        refine ⟨k2, ⟨n2, k2Pn⟩, ?_⟩
        unfold inmf
        simp only [Nat.lt_succ_iff]
        intro i le_in
        rcases lt_or_eq_of_le le_in with lt_in | eq_in
        · apply submap_of_prefixColoring_of_le le_n12 inj_k1f k2Pn; apply k1_f _ lt_in
        · exact eq_in ▸ k2_fn
      }
      · {
        refine ⟨k1, ⟨n1, inj_k1f⟩, ?_⟩
        unfold inmf
        simp only [Nat.lt_succ_iff]
        intro i le_in
        rcases lt_or_eq_of_le le_in with lt_in | eq_in
        · exact k1_f _ lt_in
        · apply submap_of_prefixColoring_of_le le_n21 k2Pn inj_k1f; apply eq_in ▸ k2_fn
      }
    }
    have ⟨nk, hnk⟩:=kPn
    have ⟨⟨kP, _, hfk⟩, _⟩ := partialColoring_of_prefixColoring hnk
    rw[Map.at_most_regions_eq_at_most_regions'] at hfk
    have ⟨fk, fk_k⟩:=hfk
    let s_spec (n : ℕ) (s : List ℕ)
      := ∀i < n, s.getD i 0 < nc ∧ k (fk (s.getD i 0)) (f i)
    have ⟨s, Ls, Ds⟩ : ∃s, s.length = nc + 1 ∧ s_spec (nc + 1) s := by{
      clear lim_f
      revert inj_limf
      revert k_f
      revert f
      apply Nat.recAux (motive:=fun n => ∀f,
        let s_spec := fun n (s : List ℕ) ↦ ∀ i < n, s.getD i 0 < nc ∧ k (fk (s.getD i 0)) (f i);
        inmf n k f → injf n (limitColoring m nc) f →
        ∃ s, s.length = n ∧ s_spec n s)
      · simp
      intro n IHn f s_spec k_f inj_limf
      have ⟨s, Ls, Ds⟩ := IHn (fun i => f (i + 1)) (by{
        intro i lt_i_n
        apply k_f
        exact Nat.succ_lt_succ lt_i_n
      }) (by{
        intro i j lt_ij lt_jn
        apply inj_limf
        · exact Nat.succ_lt_succ lt_ij
        · exact Nat.succ_lt_succ lt_jn
      })
      have ⟨j, lt_j_nc, k_fkj_f0⟩:=fk_k (f 0) (k_f _ (Nat.zero_lt_succ _))
      use j::s
      simp only [List.length_cons, Ls, true_and]
      simp only [s_spec]
      intro i le_i_n
      rw[Nat.lt_succ_iff] at le_i_n
      match i with
      | 0 => simp[lt_j_nc, k_fkj_f0]
      | i' + 1 => {
        simp only [List.getD_cons_succ]
        apply Ds
        exact Nat.lt_of_succ_le le_i_n
      }
    }
    have Us : s.Nodup := by{
      rw[List.nodup_iff_getElem_ne_getElem]
      intro i1 i2 lt_i12 lt_i2s
      have lt_i1s := lt_trans lt_i12 lt_i2s
      have lt_i1n := Ls ▸ lt_i1s
      have lt_i2n := Ls ▸ lt_i2s
      have ⟨_, k_s_fi1⟩:=Ds i1 lt_i1n
      have ⟨_, k_s_fi2⟩:=Ds i2 lt_i2n
      rw[← List.getElem_eq_getD (h:=lt_i1s)] at k_s_fi1
      rw[← List.getElem_eq_getD (h:=lt_i2s)] at k_s_fi2
      intro hsi12
      apply inj_limf i1 i2 lt_i12 lt_i2n
      refine ⟨k, kPn, ?_⟩
      rw[hsi12] at k_s_fi1
      exact map_trans (map_symm k_s_fi1) k_s_fi2
    }
    have hs : ∀x ∈ s, x < nc := by{
      unfold s_spec at Ds
      intro x hxs
      rw[List.mem_iff_getElem] at hxs
      have ⟨j, hj0, hj1⟩:=hxs
      rw[Ls] at hj0
      have Ds' := Ds _ hj0
      rw[← List.getElem_eq_getD (h := by{assumption})] at Ds'
      exact hj1 ▸ Ds'.left
    }
    have h' : s.length ≤ nc := by{
      rw[← List.length_range (n:=nc)]
      apply List.length_le_length_of_nodup_of_subset Us List.nodup_range
      intro x
      rw[List.mem_range]
      exact hs x
    }
    simp[Ls] at h'
  }

end RealPlane
