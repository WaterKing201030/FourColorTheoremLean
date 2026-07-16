import FourColorTheorem.Compactness.Subcoloring

namespace RealPlane

/-
最小性：
给定一个涂色方案k0和标准点数量上限n，考虑i小于n个标准点，对于任意的，满足和k0在前i个点相同，
且在i+1个点时可扩展的涂色方案k，在k下标准点i和标准点j颜色相同，那么必定存在一个不大于j的标准点j0
使得j0和i在k0中颜色相同
该方案可以保证最小性的原理如下：首先k0和k在前i个点相同，因此只需要比较标号为i的点即可
然后，k也是一个可扩展上色；若k将标号为j的点和标号为i的点连接，那么在k0中，必然存在一个不大于j的标准点
与i连接

前缀染色：
k是一个字典序上最小的染色方案，并且可以扩展任意有限次。由于submap的反对称性，
实际上就是在说k本来就是限制在前几个点上的子染色
-/

def minimalColoring (m : Map) (nc : ℕ) (k0 : Map) (n : ℕ) :=
  ∀ i < n, ∀ j, ∀ k : Map, partialEqOn m i k0 k
  → extensibleColoring m nc k (i + 1)
  → (m.partialMap (i + 1) k) (stdPoint j) (stdPoint i) → ∃j0 ≤ j, k0 (stdPoint j0) (stdPoint i)
def prefixColoring (m : Map) (nc : ℕ) (k : Map) (n : ℕ) :=
  k.submap (m.partialMap n k) ∧
  extensibleColoring m nc k n ∧ minimalColoring m nc k n
def isPrefixColoring (m : Map) (nc : ℕ) (k : Map) :=
  ∃n, prefixColoring m nc k n

@[simp] theorem minimalColoring_zero {m : Map} {nc : ℕ} {k0 : Map} :
  minimalColoring m nc k0 0 := by{simp[minimalColoring]}

theorem partialColoring_of_prefixColoring {m : Map} {nc : ℕ} {k : Map} {n : ℕ}
  : prefixColoring m nc k n → partialColoring m nc k n := by{
    intro ⟨n_k, hk, h⟩
    have ⟨k', ⟨hk', h'nm0⟩, Ekk'⟩:=hk n
    have ⟨K'P, adj'k', hk''⟩:=hk'
    have ⟨f, k'f_nk'⟩:=size_partialMap m n hk''
    have k'_k : k.submap k' := by{
      intro z1 z2 hz
      have ⟨kz12, nz1, nz2⟩:=n_k _ hz
      have Ekk'':=Ekk' z1 z2 nz1 nz2
      apply Ekk''.mp kz12
    }
    have n_k' : m.partialMap n k = k := by{
      apply submap_antisymm
      · apply partialMap_submap
      · apply n_k
    }
    have kP : IsPlainMap k := by{
      apply IsPlainMap.mk
      · {
        intro z1 z2 kz1z2
        have mkz1z2 := n_k _ kz1z2
        rw[Map.mem_map_apply_iff, Map.partialMap] at mkz1z2
        rw[Map.mem_map_apply_iff]
        rw[Ekk' _ _ mkz1z2.right.right mkz1z2.right.left]
        apply map_symm'
        rw[←Ekk' _ _ mkz1z2.right.left mkz1z2.right.right]
        exact mkz1z2.left
      }
      · {
        intro z1 z2 kz1z2 z3 kz2z3
        have ⟨_, hz1, hz2⟩ := n_k _ kz1z2
        have ⟨_, _, hz3⟩ := n_k _ kz2z3
        rw[Map.mem_map_apply_iff]
        rw[Ekk' _ _ hz1 hz3]
        apply map_trans' (z2:=z2)
        · rw[←Ekk' _ _ hz1 hz2]; exact kz1z2
        · rw[←Ekk' _ _ hz2 hz3]; exact kz2z3
      }
    }
    have adj'k:∀ {p1 p2 : Point}, m.adjacent p1 p2 → ¬k p1 p2:=by{
      intro z1 z2 mz1z2 kz1z2
      apply adj'k' mz1z2
      have ⟨_, hz1, hz2⟩ := n_k _ kz1z2
      rw[←Ekk' _ _ hz1 hz2]
      exact kz1z2
    }
    have hnm0 : (m.partialMap n m).submap k := by{
      intro z1 z2 mnz1z2
      have ⟨mz1z2, hz1, hz2⟩:=mnz1z2
      have Ekk'':=Ekk' z1 z2 hz1 hz2
      apply Ekk''.mpr
      apply h'nm0
      assumption
    }
    refine ⟨⟨kP, adj'k, ?_⟩, hnm0⟩
    use f
    intro z hz
    have ⟨k'z', nz, _, ⟩:=n_k _ hz
    have k'z:=k'_k _ k'z'
    have ⟨⟨i, ellt_i_nc⟩, ⟨k'fiz, nfi, _⟩⟩:=k'f_nk' z ⟨k'z, nz, nz⟩
    use ⟨i, ellt_i_nc⟩
    have h':=Ekk' _ _ nfi nz
    exact h'.mpr k'fiz
  }

theorem prefixColoring_exists (m : Map) [IsSimpleMap m] {nc : ℕ} (n : ℕ)
  (fin_colorable : finColorable nc) : ∃k, prefixColoring m nc k n := by{
    induction n with
    | zero => {
      use ⊥
      split_ands
      · {
        intro _ _
        simp only [Map.mem_map_apply_iff, Map.partialMap, partialRegion_zero,
        Set.mem_empty_iff_false, and_false, Pi.bot_apply, Set.bot_eq_empty, imp_false,
        not_false_iff]
      }
      · {
        simp only [extensibleColoring, partialEqOn, Map.partialRegion, not_lt_zero, false_and,
          exists_const, Set.setOf_false, Set.mem_empty_iff_false, IsEmpty.forall_iff,
          implies_true, and_true]
        intro _
        apply partialColoring_exists
        apply fin_colorable
      }
      · {
        simp only [minimalColoring, not_lt_zero,
          IsEmpty.forall_iff, implies_true]
      }
    }
    | succ n ih => {
      have ⟨k0, ⟨n_k0, ext_k0, min_k0⟩⟩:=ih
      rcases em' (stdPoint n ∈ m.partialRegion (n + 1)) with n1_n | n1_n
      · {
        have hr : m.partialRegion (n + 1) = m.partialRegion n := by{
          ext x
          simp only [mem_partialRegion_iff, Nat.lt_succ_iff]
          refine ⟨?_, fun ⟨i, hin, hi⟩ => ⟨i, le_of_lt hin, hi⟩⟩
          intro ⟨i, hin, hi⟩
          rcases lt_or_eq_of_le hin with hin | hin
          · exact ⟨i, hin, hi⟩
          simp only [mem_partialRegion_iff, not_exists, not_and] at n1_n
          have hi':=hin ▸ (refl_of_rel hi).right
          exfalso
          apply n1_n n (by{simp})
          exact hi'
        }
        use k0
        split_ands
        · {
          apply submap_trans n_k0
          apply partialMap_submap_of_le
          simp
        }
        · {
          intro n'
          have ⟨k, kP, Ek0k⟩:=ext_k0 n'
          refine ⟨k, kP, ?_⟩
          rw[partialEqOn]
          simp only [hr]
          exact Ek0k
        }
        · {
          simp only [minimalColoring, Nat.lt_succ_iff]
          intro i hi
          rcases lt_or_eq_of_le hi with hi | hi
          · {
            have min_k0':=min_k0 i hi
            apply min_k0'
          }
          · {
            simp only [hi, Map.partialMap, hr]
            intro j k
            simp[hr ▸ n1_n]
          }
        }
      }
      let ext (n0 : ℕ) (j : ℕ) (k : Map) := partialColoring m nc k n0 ∧ partialEqOn m n k0 k
        ∧ m.partialMap (n + 1) k (stdPoint j) (stdPoint n)
      let limit_min (j0 : ℕ) := ∃n0 > n, ∀j k, ext n0 j k → j0 ≤ j
      have ext_k0' : ¬limit_min (n+1) := by{
        intro ⟨n0, lt_nn0, min_n0⟩
        have ⟨k, ⟨kP, k_n0⟩, eq_k0k⟩:=ext_k0 n0
        have h:=min_n0 n k
        simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_false] at h
        apply h
        refine ⟨⟨kP, k_n0⟩, eq_k0k, ⟨?_, n1_n, n1_n⟩⟩
        apply k_n0
        change (m.partialMap _ _).cover _
        rw[partialMap_cover]
        apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_nn0 n1_n
      }
      have ext_0 : limit_min 0 := by{
        use n + 1
        simp
      }
      classical
      set j0 := Nat.findGreatest limit_min (n + 1) with hj0
      have hj0':=hj0
      simp only [ext_k0', not_false_eq_true, Nat.findGreatest_of_not] at hj0'
      have le_j0n := hj0' ▸ Nat.findGreatest_le (P:=limit_min) n
      have ⟨n0, lt_nn0, min_j0⟩ : limit_min j0 := by{
        rw[hj0]
        apply Nat.findGreatest_spec (Nat.zero_le _) ext_0
      }
      have min'j1 : ∀j1 > j0, j1 ≤ n + 1 → ¬limit_min j1 := by{
        intro j1 hj01 hj1n
        exact Nat.findGreatest_is_greatest (hj0 ▸ hj01) hj1n
      }
      have min'j1' : ¬limit_min (j0 + 1) := by{
        apply min'j1 _ (by{simp}) (by{simp[le_j0n]})
      }
      have ext0P {n' : ℕ} (le_n0n' : n0 ≤ n') : ∃k, partialColoring m nc k n' ∧ ext n0 j0 k := by{
        have lt_nn' := lt_of_lt_of_le lt_nn0 le_n0n'
        apply not_imp_comm.mp ?_ min'j1'
        intro ext'n'
        refine ⟨n', lt_nn', ?_⟩
        intro j k ⟨kP, Ek0k, k_jn⟩
        have kPn0 : partialColoring m nc k n0 := partialColoring_of_le le_n0n' kP
        simp only [not_exists, not_and] at ext'n'
        have ext'n'' := ext'n' _ kP
        simp only [kPn0, Ek0k, true_and, ext] at ext'n''
        have h':j0 ≠ j := by{
          intro hj
          simp[hj] at ext'n''
          contradiction
        }
        rw[Nat.succ_le_iff]
        apply lt_of_le_of_ne ?_ h'
        apply min_j0 _ k
        refine ⟨kPn0, Ek0k, k_jn⟩
      }
      have ⟨k1, _, Dk1⟩ := ext0P (le_refl n0)
      let k2 := m.partialMap (n + 1) k1
      have Ek12 : partialEqOn m (n + 1) k1 k2 := by{
        apply partialEqOn_partialMap
      }
      have m1P {z : Point} (hz : z ∈ m.partialRegion (n + 1))
      : ∃j ≤ n, m.partialMap n0 m z (stdPoint j) := by{
        have hz' := hz
        simp only [mem_partialRegion_iff, Nat.lt_succ_iff] at hz
        have ⟨j, le_jn, hj⟩ := hz
        have hz'' : z ∈ m.partialRegion n0 := by{
          apply partialRegion_subset_of_le ?_ hz'
          simp[Nat.succ_le_iff, lt_nn0]
        }
        have hj'' : stdPoint j ∈ m.partialRegion n0 := by{
          apply map_apply_subset_of_mem_partialRegion hz'' hj
        }
        refine ⟨j, le_jn, hj, hz'', hj''⟩
      }
      have n1j0 : stdPoint j0 ∈ m.partialRegion (n + 1) := by{
        unfold ext Map.partialMap at Dk1
        apply partialRegion_subset_of_le ?_ Dk1.right.right.right.left
        simp
      }
      use k2
      constructor
      · apply partialMap_submap_partialMap_partialMap
      constructor
      · {
        intro n'
        have ⟨k3, k3P, Dk3⟩:=ext0P (n' := max n0 n') (by{simp})
        have Ek13 : partialEqOn m (n + 1) k1 k3 := by{
          clear! k2
          clear k3P
          intro z1 z2 hi1' hi2'
          have ⟨i1, le_i1n, n0iz1⟩ := m1P hi1'
          have ⟨i2, le_i2n, n0iz2⟩ := m1P hi2'
          have ⟨_, _, n0i1⟩ := n0iz1
          have ⟨_, _, n0i2⟩ := n0iz2
          have wls (H : ∀k1 k3, ext n0 j0 k1 → ext n0 j0 k3 → k1 z1 z2 → k3 z1 z2)
            : k1 z1 z2 ↔ k3 z1 z2 := by{
              constructor
              · apply H _ _ Dk1 Dk3
              · apply H _ _ Dk3 Dk1
            }
          apply wls
          intro k1 k3 Dk1 Dk3
          have ⟨⟨k1P, k1n0⟩, Ek01, ⟨k1j0n, _, _⟩⟩ := Dk1
          have ⟨⟨k3P, k3n0⟩, Ek03, ⟨k3j0n, _, _⟩⟩ := Dk3
          have k1P' := k1P.coloring_plain
          have k3P' := k3P.coloring_plain
          have k13i : k1 (stdPoint i1) (stdPoint i2) → k3 (stdPoint i1) (stdPoint i2) := by{
            clear! z1 z2
            wlog lt_i12 : i1 < i2 with H
            · {
              rw[not_lt] at lt_i12
              rcases eq_or_lt_of_le lt_i12 with eq_i12 | lt_i21
              · {
                clear H
                simp only [eq_i12]
                intro IHi
                apply k3n0
                change (m.partialMap n0 m).cover _
                rw[partialMap_cover]
                assumption
              }
              · {
                simp only [map_comm (z1 := stdPoint i1)]
                apply H (m:=m) (nc:=nc) (n:=n) (k0:=k0) (n0:=n0)
                all_goals
                assumption
              }
            }
            have lt_i1n := lt_of_lt_of_le lt_i12 le_i2n
            have n_i1 : stdPoint i1 ∈ m.partialRegion n := by{
              apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
                lt_i1n n0i1
            }
            have Ek13 := partialEqOn_trans (partialEqOn_symm Ek01) Ek03
            rcases eq_or_lt_of_le le_i2n with k1i2n | lti2n
            · {
              simp only [k1i2n]
              rw[← congr_right_of_rel k3j0n]
              intro k1i1n
              have n_j0 : stdPoint j0 ∈ m.partialRegion n := by{
                apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt ?_ n1j0
                refine lt_of_le_of_lt ?_ lt_i1n
                apply min_j0 i1 k1
                constructor
                · {
                  constructor
                  · assumption
                  · assumption
                }
                constructor
                · assumption
                nth_rw 2 [←k1i2n]
                rw[Map.partialMap]
                refine ⟨?_, partialRegion_subset_of_le (Nat.le_succ _) n_i1,
                stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
                  (k1i2n ▸ Nat.lt_succ_self _) n0i2⟩
                rw[k1i2n]
                exact k1i1n
              }
              simp only [← Ek13 _ _ n_i1 n_j0]
              rw[congr_right_of_rel k1j0n]
              apply k1i1n
            }
            · {
              refine (Ek13 _ _ n_i1 ?_).mp
              apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lti2n n0i2
            }
          }
          have k1iz1 := k1n0 _ n0iz1
          have k1iz2 := k1n0 _ n0iz2
          have k3iz1 := k3n0 _ n0iz1
          have k3iz2 := k3n0 _ n0iz2
          intro k1z12
          rw[congr_left_of_rel k1iz1] at k1z12
          rw[congr_right_of_rel k1iz2] at k1z12
          rw[congr_left_of_rel k3iz1]
          rw[congr_right_of_rel k3iz2]
          exact k13i k1z12
        }
        have Ek23 := partialEqOn_trans (partialEqOn_symm Ek12) Ek13
        refine ⟨k3, partialColoring_of_le (by{simp}) k3P, Ek23⟩
      }
      · {
        have ⟨_, Ek01, k2_j0n⟩:=Dk1
        intro i le_i_n j k Ek2k ext_k i1k_ji
        rw[Nat.lt_succ_iff] at le_i_n
        have Ek02 : partialEqOn m n k0 k2 := by{
          apply partialEqOn_trans Ek01
          apply partialEqOn_of_partialEqOn_of_ge (Nat.le_succ n) Ek12
        }
        have Ek0k : partialEqOn m i k0 k := by{
          apply partialEqOn_trans ?_ Ek2k
          apply partialEqOn_of_partialEqOn_of_ge le_i_n Ek02
        }
        rcases eq_or_lt_of_le le_i_n with Di | lt_i_n
        · {
          simp only [Di] at i1k_ji Ek0k ext_k
          simp only [Di]
          have ⟨k', k'P, Ekk'⟩:=ext_k n0
          have ⟨k_ji, n1j, _⟩:=i1k_ji
          use j0
          constructor
          · {
            apply min_j0 j k'
            unfold ext
            rw[Map.partialMap]
            have Ek0k':=partialEqOn_trans Ek0k (partialEqOn_of_partialEqOn_of_ge
              (Nat.le_succ n) Ekk')
            simp only [k'P, Ek0k', n1j, n1_n, and_self, and_true, true_and]
            rw[← Ekk' _ _ n1j n1_n]
            exact k_ji
          }
          · apply k2_j0n
        }
        · {
          have ⟨j1, le_j1j, hj1⟩:=min_k0 i lt_i_n j k Ek0k ext_k i1k_ji
          refine ⟨j1, le_j1j, ?_⟩
          apply n_k0 at hj1
          rw[Map.mem_map_apply_iff, Map.partialMap] at hj1
          rw[← Ek02 _ _ hj1.right.left hj1.right.right]
          apply hj1.left
        }
      }
    }
  }

theorem submap_of_prefixColoring_of_le {m : Map} [IsSimpleMap m] {nc : ℕ} {k1 k2 : Map} {n1 n2 : ℕ}
  (le_n12 : n1 ≤ n2) (k1pre : prefixColoring m nc k1 n1) (k2pre' : prefixColoring m nc k2 n2) :
  k1.submap k2 := by{
    have ⟨n1k1, _, _⟩ := k1pre
    wlog k2pre : prefixColoring m nc k2 n1 with H
    · {
      apply submap_trans ?_ (partialMap_submap (m0:=m) (m:=k2) (n:=n1))
      apply H (m:=m) (nc:=nc) (n1 := n1) (n2:=n1) (le_refl _) k1pre ?_ n1k1 (by{assumption})
        (by{assumption})
      all_goals
      refine ⟨partialMap_submap_partialMap_partialMap, ?_⟩
      have ⟨n2k2, k2_ext, k2_min⟩:=k2pre'
      have ⟨k2P, _⟩:=partialColoring_of_prefixColoring k2pre'
      have k2P' := k2P.coloring_plain
      refine ⟨extensible_partialMap_of_le le_n12 k2_ext, ?_⟩
      intro i lt_i_n1 j k Ek2k k_ext i1k_ji
      have lt_i_n2 := lt_of_lt_of_le lt_i_n1 le_n12
      have ⟨_, i1j, i1i⟩:=i1k_ji
      have n1i := stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_i_n1 i1i
      have ⟨j0, le_j0j, k2j0i⟩ := k2_min i lt_i_n2 j k (by{
        apply partialEqOn_trans ?_ Ek2k
        apply partialEqOn_of_partialEqOn_of_ge (n2:=n1) (le_of_lt lt_i_n1)
        apply partialEqOn_partialMap
      }) k_ext i1k_ji
      have ⟨n2j0', k2i⟩:=refl_of_rel k2j0i
      have ⟨_, n2j0, _⟩:=n2k2 _ n2j0'
      rcases le_or_gt i j with le_i_j | lt_j_i
      · refine ⟨i, le_i_j, ⟨k2i, n1i, n1i⟩⟩
      have lt_j0_n1 := lt_of_le_of_lt le_j0j (lt_trans lt_j_i lt_i_n1)
      refine ⟨j0, le_j0j, ⟨k2j0i, ?_, n1i⟩⟩
      apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_j0_n1 n2j0
    }
    clear! n2
    have Ek12 : partialEqOn m n1 k1 k2 := by{
      have leqnn := le_refl n1
      revert leqnn
      apply Nat.recAux (motive := fun n => n ≤ n1 → partialEqOn m n k1 k2)
      · simp
      intro n IHn lt_nn1 z1 z2 n_z1 n_z2
      rw[Nat.succ_le_iff] at lt_nn1
      have m1P (z : Point) : z ∈ m.partialRegion (n + 1) →
        ∃i ≤ n, m.partialMap n1 m z (stdPoint i) := by{
          intro h
          have h':=map_apply_subset_of_mem_partialRegion h
          have ⟨i, le_i_n, n1zi⟩:=h
          rw[Nat.lt_succ_iff] at le_i_n
          refine ⟨i, le_i_n, ⟨n1zi, partialRegion_subset_of_le (Nat.succ_le_of_lt lt_nn1) h,
          stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
            (lt_of_le_of_lt le_i_n lt_nn1) (h' n1zi)⟩⟩
      }
      have ⟨i1, le_i1n, n1iz1⟩ := m1P z1 n_z1
      have ⟨i2, le_i2n, n1iz2⟩ := m1P z2 n_z2
      have IHn' := IHn (le_of_lt lt_nn1)
      have wls (H : ∀k1 k2, prefixColoring m nc k1 n1 → prefixColoring m nc k2 n1
      → partialEqOn m n k1 k2 → k1 z1 z2 → k2 z1 z2)
        : k1 z1 z2 ↔ k2 z1 z2 := by{
          constructor
          · apply H _ _ k1pre k2pre IHn'
          · apply H _ _ k2pre k1pre (partialEqOn_symm IHn')
        }
      apply wls
      clear! k1 k2
      intro k1 k2 k1pre k2pre IHn IHk
      have ⟨k1P, k1n1⟩:=partialColoring_of_prefixColoring k1pre
      have ⟨k2P, k2n1⟩:=partialColoring_of_prefixColoring k2pre
      have k1P' := k1P.coloring_plain
      have k2P' := k2P.coloring_plain
      have ⟨_, _, n1i1⟩:=n1iz1
      have ⟨_, _, n1i2⟩:=n1iz2
      have k12i : k1 (stdPoint i1) (stdPoint i2) → k2 (stdPoint i1) (stdPoint i2) := by{
        clear! z1 z2
        wlog lt_i12 : i1 < i2 with IHi
        · {
          rw[not_lt] at lt_i12
          rcases lt_or_eq_of_le lt_i12 with lt_i21 | eq_i12
          · {
            simp only [map_comm (z1:=stdPoint i1)]
            apply IHi (m:=m) (nc:=nc) (n1:=n1)
            all_goals
            assumption
          }
          · {
            intro _
            apply k2n1
            rw[eq_i12]
            change (m.partialMap _ _).cover _
            rw[partialMap_cover]
            exact n1i1
          }
        }
        have lt_i1n1 := lt_of_le_of_lt le_i1n lt_nn1
        have lt_i2n1 := lt_of_le_of_lt le_i2n lt_nn1
        have lt_i1n := lt_of_lt_of_le lt_i12 le_i2n
        rcases lt_or_eq_of_le le_i2n with lt12n | Di2
        · {
          apply Iff.mp (IHn _ _ ?_ ?_)
          · apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_i1n n1i1
          · apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt12n n1i2
        }
        simp only [Di2] at n1i2 lt_i12 le_i1n lt_i2n1
        simp only [Di2]
        clear! i2
        clear lt_nn1
        clear lt_i12
        clear le_i1n
        have lt_i1n' := lt_i1n
        revert i1
        apply Nat.recAux (motive := fun n3 => ∀ (i1 : ℕ),
        stdPoint i1 ∈ m.partialRegion n1 → i1 < n1 → i1 < n → i1 < n3
        → k1 (stdPoint i1) (stdPoint n) → k2 (stdPoint i1) (stdPoint n))
        · simp
        intro n3 IHn3 i1 n1i1 lt_i1n1 lt_i1n lt_i1n3 k1i1n
        have ⟨n1k1, k1ext, k1min⟩:=k1pre
        have ⟨n1k2, k2ext, k2min⟩:=k2pre
        have n'_i1 := stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
          (Nat.lt_succ_of_lt lt_i1n) n1i1
        have n'_n := stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
          (Nat.lt_succ_self n) n1i2
        have ⟨i3, le_i31, k2i3n⟩:=k2min n lt_i2n1 i1 (m.partialMap (n + 1) k1) (by{
          apply partialEqOn_trans (partialEqOn_symm IHn)
          apply partialEqOn_of_partialEqOn_of_ge (Nat.le_succ _)
          apply partialEqOn_partialMap
        }) (extensible_partialMap_of_le lt_i2n1 k1ext) (by{
          refine ⟨?_, n'_i1, n'_n⟩
          refine ⟨?_, n'_i1, n'_n⟩
          apply k1i1n
        })
        rcases eq_or_lt_of_le le_i31 with Di3 | lt_i31
        · {
          simp only [Nat.succ_eq_add_one, Di3, Std.le_refl] at *
          exact k2i3n
        }
        have lt_i3n := lt_of_le_of_lt le_i31 lt_i1n
        have n'i3 : stdPoint i3 ∈ m.partialRegion (n + 1) := by{
          have ⟨_, h, _⟩:=n1k2 _ k2i3n
          apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt (Nat.lt_succ_of_lt lt_i3n) h
        }
        have h := extensible_partialMap_of_le lt_i2n1 k2ext
        have ⟨i4, le_i43, k1i4n⟩:=k1min n lt_i2n1 i3 (m.partialMap (n + 1) k2) (by{
          apply partialEqOn_trans IHn
          apply partialEqOn_of_partialEqOn_of_ge (Nat.le_succ n)
          apply partialEqOn_partialMap
        }) (extensible_partialMap_of_le lt_i2n1 k2ext) (by{
          refine ⟨?_, n'i3, n'_n⟩
          refine ⟨?_, n'i3, n'_n⟩
          apply k2i3n
        })
        have lt_i4n := lt_of_le_of_lt le_i43 lt_i3n
        have lt_i41 := lt_of_le_of_lt le_i43 lt_i31
        have lt_i4n3 := lt_of_lt_of_le lt_i41 (Nat.le_of_lt_succ lt_i1n3)
        have n1i4 : stdPoint i4 ∈ m.partialRegion n1 := by{
          apply (n1k1 _ k1i4n).2.1
        }
        have lt_i4n1 := lt_trans lt_i4n lt_i2n1
        have k2i4n : k2 (stdPoint i4) (stdPoint n) := by{
          apply IHn3 _ n1i4 lt_i4n1 lt_i4n lt_i4n3 k1i4n
        }
        rw[← congr_right_of_rel k2i4n]
        have ni1 : stdPoint i1 ∈ m.partialRegion n := by{
          apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_i1n n'_i1
        }
        have ni4 : stdPoint i4 ∈ m.partialRegion n := by{
          apply stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt lt_i4n n1i4
        }
        rw[← IHn _ _ ni1 ni4]
        apply map_trans' k1i1n
        apply map_symm k1i4n
      }
      have k1iz1 := k1n1 _ n1iz1
      have k1iz2 := k1n1 _ n1iz2
      have k2iz1 := k2n1 _ n1iz1
      have k2iz2 := k2n1 _ n1iz2
      revert IHk
      rw[congr_left_of_rel k1iz1, congr_right_of_rel k1iz2]
      rw[congr_left_of_rel k2iz1, congr_right_of_rel k2iz2]
      apply k12i
    }
    intro z1 z2 hz1z2
    have ⟨k1z, nz1, nz2⟩:=n1k1 _ hz1z2
    change k2 z1 z2
    rw[← Ek12 _ _ nz1 nz2]
    exact k1z
  }
end RealPlane
