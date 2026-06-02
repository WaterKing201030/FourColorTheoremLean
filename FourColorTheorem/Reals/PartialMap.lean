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
def Map.partialMap (m : Map) (n : ℕ) : Map :=
  fun z1 z2 => m z1 z2 ∧ z1 ∈ m.partialRegion n ∧ z2 ∈ m.partialRegion n
theorem mem_partialRegion_iff {m : Map} {n : ℕ} {z : Point}
  : z ∈ m.partialRegion n ↔ ∃i < n, m z (stdPoint i) := by rfl

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
  {m : Map} [IsPlainMap m] {n1 n2 i : ℕ} (lt_i_n1 : i < n1)
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

theorem partialRegion_cover {m : Map} [IsPlainMap m] {n : ℕ}
  : (m.partialMap n).cover = m.partialRegion n := by{
    ext z
    unfold Map.cover
    change m.partialMap n z z ↔ _
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
: m.partialMap n z = m z := by{
  ext t
  change m.partialMap n z t ↔ m z t
  simp only [Map.partialMap, hz, true_and]
  have ih:=map_apply_subset_of_mem_partialRegion hz
  constructor
  · apply And.left
  · intro h; exact ⟨h, ih h⟩
}

theorem exists_pmap_of_mem_partialRegion {m : Map} [IsPlainMap m]
{n : ℕ} {z : Point} (n_z : z ∈ m.partialRegion n)
: ∃i < n, m.partialMap n z (stdPoint i) := by{
  have ⟨i, hin, hi⟩:=n_z
  refine ⟨i, hin, hi, n_z, ?_⟩
  apply map_apply_subset_of_mem_partialRegion n_z hi
  }

theorem partialMap_submap {m : Map} {n : ℕ} : (m.partialMap n).submap m := by{
  intro z1 z2
  intro ⟨h, _⟩
  exact h
}
theorem partialMap_submap_of_le {m : Map} {n1 n2 : ℕ} (hn12 : n1 ≤ n2) :
  (m.partialMap n1).submap (m.partialMap n2) := by{
    intro z1 z2
    intro ⟨h, hz1, hz2⟩
    refine ⟨h, ?_, ?_⟩
    · apply partialRegion_subset_of_le hn12 hz1
    · apply partialRegion_subset_of_le hn12 hz2
  }

@[implicit_reducible] def partialMap_isPlainMap {m : Map} [IsPlainMap m]
  {n : ℕ} : IsPlainMap (m.partialMap n) := by{
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
  {n : ℕ} : IsSimpleMap (m.partialMap n) where
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
    have h : m.partialMap n z = m z := partialMap_apply_eq_of_mem_partialRegion hz
    apply ih
    rw[←h]
    apply hrR12
  }

@[implicit_reducible] def partialMap_isFiniteSimpleMap {m : Map} [IsSimpleMap m]
  {n : ℕ} : IsFiniteSimpleMap (m.partialMap n) where
  toIsSimpleMap := partialMap_isSimpleMap
  map_finite := by{
    use n
    rw[Map.at_most_regions]
    use fun i => m (stdPoint i.val)
    intro p hp
    change m.partialMap n p p at hp
    rw[Map.partialMap, and_self, mem_partialRegion_iff] at hp
    have ⟨i, hin, hi⟩ := hp.right
    use ⟨i, hin⟩
    simp only
    exact map_symm hi
  }

end RealPlane
