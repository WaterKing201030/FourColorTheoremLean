import FourColorTheorem.Reals.Approx
import FourColorTheorem.Reals.Grid.Matte
import FourColorTheorem.Utils.Infinite

namespace GridPlane
@[implicit_reducible] def GPoint.instCountable : Countable GPoint :=
  Countable.of_equiv _ GPoint.equivProd.symm
@[implicit_reducible] def GPoint.instInfinite : Infinite GPoint :=
  (Equiv.infinite_iff GPoint.equivProd.symm).mp inferInstance
end GridPlane

namespace RealPlane
open GridPlane
abbrev scalePointRecord := ℕ × GPoint
instance scalePointRecord.instCountable : Countable scalePointRecord :=
  @instCountableProd _ _ inferInstance GPoint.instCountable
instance scalePointRecord.instInfinite : Infinite scalePointRecord :=
  inferInstance
noncomputable def scalePointRecord.equivNat : scalePointRecord ≃ ℕ :=
  _root_.equivNat
noncomputable def stdPoint (i : ℕ) : Point :=
  let ⟨s, p⟩ := scalePointRecord.equivNat.symm i
  scalePoint s p

def Map.partialRegion (m : Map) (n : ℕ) : Region :=
  {z | ∃i < n, m z (stdPoint i)}
def Map.partialMap (m : Map) (n : ℕ) (k : Map) : Map :=
  fun z1 z2 => k z1 z2 ∧ z1 ∈ m.partialRegion n ∧ z2 ∈ m.partialRegion n
theorem mem_partialRegion_iff {m : Map} {n : ℕ} {z : Point}
  : z ∈ m.partialRegion n ↔ ∃i < n, m z (stdPoint i) := by rfl
@[simp] theorem partialRegion_zero {m : Map} : m.partialRegion 0 = ∅ := by{
  ext x
  simp[Map.partialRegion]
}
@[simp] theorem partialMap_zero {m k : Map} : m.partialMap 0 k = ⊥ := by{
  apply funext₂
  intro a b
  simp only [Map.partialMap, partialRegion_zero, Set.mem_empty_iff_false, and_self, and_false,
    Pi.bot_apply, Set.bot_eq_empty, eq_iff_iff, false_iff]
  change b ∉ (∅ : Set Point)
  simp
}
theorem partialRegion_succ {m : Map} {n : ℕ}
: m.partialRegion (n + 1) = m.partialRegion n ∪ (m · (stdPoint n)) := by{
  ext x
  simp only [Map.partialRegion, Set.mem_setOf_eq, Set.mem_union, Nat.lt_succ_iff]
  constructor
  · {
    intro ⟨i, hin, hmi⟩
    rcases lt_or_eq_of_le hin with hin | hin
    · left; exact ⟨i, hin, hmi⟩
    · right; exact hin ▸ hmi
  }
  · {
    intro h
    rcases h with ⟨i, hin, hmi⟩ | h
    · exact ⟨i, le_of_lt hin, hmi⟩
    · exact ⟨n, le_refl _, h⟩
  }
}

theorem exists_stdPoint_of_cover {m : Map} [IsSimpleMap m] {z : Point}
  (mz : m.cover z) : ∃i, m z (stdPoint i) := by{
    have ⟨rr, rrz, m0rr⟩:=IsSimpleMap.map_open _ _ mz
    have ⟨⟨s, r⟩, ⟨p, p_z, h⟩, rr_b⟩:=approx_rect rrz
    rw[←GRectangle.mem_iff_toRegion] at h
    have h':=GRectangle.inner_subset h
    use scalePointRecord.equivNat ⟨s, p⟩
    rw[stdPoint]
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    apply m0rr
    apply rr_b
    rw[ScaleGRect.toRegion]
    rw[scalePoint_mem_scaleRegion_iff]
    rw[←GRectangle.mem_iff_toRegion]
    apply h'
  }

theorem stdPoint_mem_partialRegion_of_mem_partialRegion_of_lt
  {m : Map} [IsPlainMap m] {n1 i n2 : ℕ} (lt_i_n1 : i < n1)
  (h : stdPoint i ∈ m.partialRegion n2)
  : stdPoint i ∈ m.partialRegion n1 := by{
    rw[mem_partialRegion_iff] at *
    have ⟨j, hjn, hj⟩:=h
    refine ⟨i, lt_i_n1, ?_⟩
    rw[←congr_right_of_rel hj] at hj
    exact hj
  }

theorem partialRegion_subset_of_le {m : Map} {n1 n2 : ℕ} (h12 : n1 ≤ n2)
  : m.partialRegion n1 ⊆ m.partialRegion n2 := by{
    intro z
    simp only [mem_partialRegion_iff]
    intro ⟨i, hin, hi⟩
    refine ⟨i, lt_of_lt_of_le hin h12, hi⟩
  }

theorem partialMap_cover {m : Map} [IsPlainMap m] {n : ℕ}
  : (m.partialMap n m).cover = m.partialRegion n := by{
    ext z
    unfold Map.cover
    change m.partialMap n m z z ↔ _
    rw[Map.partialMap, mem_partialRegion_iff, and_self]
    constructor
    · apply And.right
    intro ⟨i, hin, hi⟩
    refine ⟨?_, ⟨i, hin, hi⟩⟩
    apply (refl_of_rel hi).left
  }

theorem map_apply_subset_of_mem_partialRegion {m : Map} [IsPlainMap m]
{n : ℕ} {z : Point} : z ∈ m.partialRegion n → m z ⊆ m.partialRegion n := by{
    rw[mem_partialRegion_iff]
    intro ⟨i, ltin, m0zi⟩ t m0zt
    refine ⟨i, ltin, ?_⟩
    have m0zt':=eq_of_rel m0zt
    exact m0zt' ▸ m0zi
  }

theorem partialMap_apply_eq_of_mem_partialRegion {m : Map} [IsPlainMap m]
{n : ℕ} {z : Point} (hz : z ∈ m.partialRegion n)
: m.partialMap n m z = m z := by{
  ext t
  change m.partialMap n m z t ↔ m z t
  simp only [Map.partialMap, hz, true_and]
  have ih:=map_apply_subset_of_mem_partialRegion hz
  constructor
  · apply And.left
  · intro h; exact ⟨h, ih h⟩
}

theorem exists_partialMap_of_mem_partialRegion {m : Map} [IsPlainMap m]
{n : ℕ} {z : Point} (n_z : z ∈ m.partialRegion n)
: ∃i < n, m.partialMap n m z (stdPoint i) := by{
  have ⟨i, hin, hi⟩:=n_z
  refine ⟨i, hin, hi, n_z, ?_⟩
  apply map_apply_subset_of_mem_partialRegion n_z hi
  }

theorem partialMap_submap {m0 m : Map} {n : ℕ} : (m0.partialMap n m).submap m := by{
  intro z1 z2
  intro ⟨h, _⟩
  exact h
}
theorem partialMap_submap_of_le {m0 m : Map} {n1 n2 : ℕ} (hn12 : n1 ≤ n2) :
  (m0.partialMap n1 m).submap (m0.partialMap n2 m) := by{
    intro z1 z2
    intro ⟨h, hz1, hz2⟩
    refine ⟨h, ?_, ?_⟩
    · apply partialRegion_subset_of_le hn12 hz1
    · apply partialRegion_subset_of_le hn12 hz2
  }

@[implicit_reducible] def partialMap_isPlainMap {m0 m : Map} [IsPlainMap m]
  {n : ℕ} : IsPlainMap (m0.partialMap n m) := by{
    apply IsPlainMap.mk
    · {
      simp only [Map.mem_map_apply_iff, Map.partialMap, map_comm]
      tauto
    }
    · {
      simp only [Map.mem_map_apply_iff, Map.partialMap, Set.subset_def]
      intro p1 p2 ⟨h12, hp1, hp2⟩ p3 ⟨h23, _, hp3⟩
      exact ⟨map_trans' h12 h23, hp1, hp3⟩
    }
  }

@[implicit_reducible] def partialMap_isSimpleMap {m : Map} [IsSimpleMap m]
  {n : ℕ} : IsSimpleMap (m.partialMap n m) where
  toIsPlainMap := partialMap_isPlainMap
  map_open := by{
    intro z1 z2 ⟨m0z12, n_z1, n_z2⟩
    have ⟨r, r_z2, m0_r⟩:=IsSimpleMap.map_open _ _ m0z12
    refine ⟨r, r_z2, ?_⟩
    rw[partialMap_apply_eq_of_mem_partialRegion n_z1]
    apply m0_r
  }
  map_connected := by{
    intro z R1 R2 hR1o hR2o hrR12 hrmR1 hrmR2
    have ⟨z1, ⟨hz1m, hz1R1⟩⟩:=hrmR1
    have ⟨z2, ⟨hz2m, hz2R2⟩⟩:=hrmR2
    have hz1m' := partialMap_submap _ hz1m
    have hz2m' := partialMap_submap _ hz2m
    have ih:=(IsSimpleMap.map_connected (m:=m) z R1 R2 hR1o hR2o ·
    ⟨z1, hz1m', hz1R1⟩ ⟨z2, hz2m', hz2R2⟩)
    have ⟨hzz1, hz, hz1⟩:=hz1m
    have h : m.partialMap n m z = m z := partialMap_apply_eq_of_mem_partialRegion hz
    apply ih
    rw[←h]
    apply hrR12
  }

@[implicit_reducible] def partialMap_isFiniteSimpleMap {m : Map} [IsSimpleMap m]
  {n : ℕ} : IsFiniteSimpleMap (m.partialMap n m) where
  toIsSimpleMap := partialMap_isSimpleMap
  map_finite := by{
    use n
    rw[Map.at_most_regions]
    use fun i => stdPoint i.val
    intro p hp
    change m.partialMap n m p p at hp
    rw[Map.partialMap, and_self, mem_partialRegion_iff] at hp
    have ⟨i, hin, hi⟩ := hp.right
    use ⟨i, hin⟩
    simp only
    rw[Map.partialMap]
    refine ⟨map_symm hi, ?_⟩
    rw[mem_partialRegion_iff, mem_partialRegion_iff]
    constructor
    · refine ⟨i, hin, ?_⟩; apply (refl_of_rel hi).right
    · refine ⟨i, hin, hi⟩
  }

theorem size_partialMap (m : Map) {nc : ℕ} {k : Map} (n : ℕ)
  [IsPlainMap k] : k.at_most_regions nc → (m.partialMap n k).at_most_regions nc := by{
    simp only [Map.at_most_regions_eq_at_most_regions']
    intro ⟨f, f_k⟩
    let kfn (i : ℕ) := k (f i) ∩ m.partialRegion n
    have ⟨g, g_k⟩ : ∃g : ℕ → Point, ∀i < nc, kfn i ⊆ m.partialMap n k (g i)
      := exists_lemma
    use g
    intro z ⟨hz, n_z⟩
    rw[and_self] at n_z
    have ⟨i, hi, hiz⟩:=f_k z hz
    use i
    refine ⟨hi, ?_⟩
    apply g_k _ hi
    exact ⟨hiz, n_z⟩
  }
where exists_lemma {m : Map} {nc : ℕ} {k : Map} {n : ℕ}
  [IsPlainMap k] {f : ℕ → Point}
  : ∃g : ℕ → Point, ∀i < nc, k (f i) ∩ m.partialRegion n
    ⊆ m.partialMap n k (g i) := by{
  set kfn := fun i => k (f i) ∩ m.partialRegion n
  induction nc with
  | zero => simp
  | succ nc' ih => {
    rcases em (∃x, x ∈ kfn nc') with ⟨t, kfi, n_t⟩ | kfn'i
    · {
      have ⟨g, g_k⟩:=ih
      let g' := fun x => if x < nc' then g x else t
      use g'
      intro i hi
      rw[Nat.lt_succ_iff] at hi
      rcases lt_or_eq_of_le hi with hi | hi
      · {
        have gi : g' i = g i := by{
          unfold g'
          simp[hi]
        }
        exact gi ▸ g_k _ hi
      }
      · {
        unfold g'
        simp only [hi, lt_irrefl, ↓reduceIte]
        intro z ⟨hz0, hz1⟩
        simp only [Map.mem_map_apply_iff, Map.partialMap, n_t, hz1, and_true]
        apply map_trans (map_symm kfi) hz0
      }
    }
    · {
      have ⟨g, g_k⟩:=ih
      use g
      simp only [not_exists] at kfn'i
      have hfn'i' := Set.eq_empty_of_forall_notMem kfn'i
      unfold kfn at hfn'i'
      simp only [Nat.lt_succ_iff]
      intro i hi
      rcases lt_or_eq_of_le hi with hi | hi
      · exact g_k _ hi
      · simp [hi, hfn'i']
    }
  }
}

@[simp] theorem bot_partialRegion {n : ℕ} : Map.partialRegion ⊥ n = ∅ := by{
  ext a
  simp only [Map.partialRegion, Pi.bot_apply, Set.bot_eq_empty, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  change ∀x < n, stdPoint x ∉ (∅ : Set Point)
  simp
}
@[simp] theorem bot_partialMap {n : ℕ} {k : Map} : Map.partialMap ⊥ n k = ⊥ := by{
  ext a b
  simp[Map.mem_map_apply_iff, Map.partialMap]
}

theorem partialMap_eq_bot_iff_partialRegion_eq_empty {m : Map} [IsPlainMap m] {n : ℕ}
  : m.partialMap n m = ⊥ ↔ m.partialRegion n = ∅ := by{
    constructor
    · {
      intro h
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      have h':=congrFun₂ h a a
      simp only [Pi.bot_apply, Set.bot_eq_empty, eq_iff_iff, Map.partialMap] at h'
      intro ha
      change _ ↔ a ∈ (∅ : Set Point) at h'
      simp only [ha, and_self, and_true, Set.mem_empty_iff_false, iff_false] at h'
      apply h'
      rw[mem_partialRegion_iff] at ha
      have ⟨_, _, ha'⟩ := ha
      exact (refl_of_rel ha').left
    }
    · {
      intro h
      ext a b
      simp only [Pi.bot_apply, Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
      rw[Map.mem_map_apply_iff, Map.partialMap]
      simp[h]
    }
  }

def partialEqOn (m : Map) (n : ℕ) (k k' : Map) :=
  ∀z1 z2, z1 ∈ m.partialRegion n → z2 ∈ m.partialRegion n
  → (k z1 z2 ↔ k' z1 z2)
@[simp] theorem partialEqOn_zero {m : Map}
  : partialEqOn m 0 = ⊤ := by{
    ext k k'
    simp[partialEqOn]
  }
theorem partialEqOn_refl {m : Map} {n : ℕ} :
  ∀k, partialEqOn m n k k := by{simp[partialEqOn]}
theorem partialEqOn_symm {m : Map} {n : ℕ} {k k' : Map}
  (h : partialEqOn m n k k') : partialEqOn m n k' k := by{
    simp only [partialEqOn]
    simp only [iff_comm]
    apply h
  }
theorem partialEqOn_trans {m : Map} {n : ℕ} {k1 k2 k3 : Map}
  (h12 : partialEqOn m n k1 k2) (h23 : partialEqOn m n k2 k3)
  : partialEqOn m n k1 k3 := by{
    intro z1 z2 hz1 hz2
    have h12':=h12 z1 z2 hz1 hz2
    have h23':=h23 z1 z2 hz1 hz2
    exact h12'.trans h23'
  }
@[implicit_reducible] def partialEqOn.instEquivalence {m : Map} {n : ℕ}
  : Equivalence (partialEqOn m n) where
  refl := partialEqOn_refl
  symm := partialEqOn_symm
  trans := partialEqOn_trans
theorem partialEqOn_partialMap {m : Map} {n : ℕ} {k : Map}
  : partialEqOn m n k (m.partialMap n k) := by{
    intro z1 z2 hz1 hz2
    rw[Map.partialMap]
    constructor
    · {
      intro h
      apply And.intro h
      exact ⟨hz1, hz2⟩
    }
    · apply And.left
  }

theorem partialMap_partialMap {m : Map} {n : ℕ} {k : Map}
  : m.partialMap n (m.partialMap n k) = m.partialMap n k := by{
    apply funext₂
    intro z1 z2
    rw[Map.partialMap, Map.partialMap]
    ext
    tauto
  }

theorem partialMap_submap_partialMap_partialMap {m : Map} {n : ℕ}
  {k : Map} : (m.partialMap n k).submap (m.partialMap n (m.partialMap n k)) := by{
    rw[partialMap_partialMap]
    apply submap_refl
  }

theorem partialEqOn_of_partialEqOn_of_ge {m : Map} {n1 n2 : ℕ}
  {k k' : Map} (hn12 : n1 ≤ n2) (h2 : partialEqOn m n2 k k')
  : partialEqOn m n1 k k' := by{
    rw[partialEqOn] at *
    intro z1 z2 hz1 hz2
    apply h2
    · exact partialRegion_subset_of_le hn12 hz1
    · exact partialRegion_subset_of_le hn12 hz2
  }

end RealPlane
