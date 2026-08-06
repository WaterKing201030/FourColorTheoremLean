import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

noncomputable def GMring (hgp : GridMapProper ab0 cm0) (i : Fin n) : List hgp.GMDart :=
  (hgp.extendCMatte i).ring.filterMap (fun d =>
    if hd : d ∈ hgp.GMGrid then some ⟨d, hd⟩ else none
  )
theorem GMring_map_val {hgp : GridMapProper ab0 cm0} {i : Fin n}
: (hgp.GMring i).map Subtype.val = (hgp.extendCMatte i).ring := by{
  unfold GMring
  rw[List.map_filterMap]
  simp only [apply_dite, Option.map_none, Option.map_some]
  nth_rw 2 [← List.filterMap_some (l:=(hgp.extendCMatte i).ring)]
  apply List.filterMap_congr
  intro x hx
  rw[dite_eq_left_iff]
  simp only [reduceCtorEq, imp_false, Decidable.not_not]
  rw[Matte.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  rw[mem_GMGrid_iff]
  left
  exact CM_subset_CMBBox hx.left
}
theorem GMring_length {hgp : GridMapProper ab0 cm0} {i : Fin n}
: (hgp.GMring i).length = (hgp.extendCMatte i).ring.length := by{
  rw[← GMring_map_val, List.length_map]
}
theorem mem_GMring_iff_val_mem_ring {hgp : GridMapProper ab0 cm0} {i : Fin n}
  {u : hgp.GMDart} : u ∈ hgp.GMring i ↔ u.val ∈ (hgp.extendCMatte i).ring := by{
    rw[GMring, List.mem_filterMap]
    constructor
    · {
      intro ⟨a, h0, h1⟩
      simp only [Option.dite_none_right_eq_some, Option.some.injEq, exists_subtype_mk_eq_iff] at h1
      exact h1 ▸ h0
    }
    · {
      intro h
      refine ⟨_, h, ?_⟩
      simp only [Subtype.coe_eta, dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false,
        Decidable.not_not]
      rw[Matte.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at h
      rw[mem_GMGrid_iff]
      left
      exact CM_subset_CMBBox h.left
    }
  }
theorem GMring_ne_nil {hgp : GridMapProper ab0 cm0} {i : Fin n}
: hgp.GMring i ≠ [] := by{
  intro h
  have ih := hgp.GMring_map_val (i:=i)
  rw[h] at ih
  have ih' := (hgp.extendCMatte i).ring_ne_nil
  simp at ih
  simp[ih] at ih'
}
theorem GMring_subset_GMInner {hgp : GridMapProper ab0 cm0} {i : Fin n}
{u : hgp.GMDart} (hu : u ∈ hgp.GMring i)
  : u ∈ hgp.GMInner := by{
    rw[mem_GMInner_iff]
    rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border] at hu
    exact CM_subset_CMBBox hu.left
  }
theorem GMring_simpleCycle {hgp : GridMapProper ab0 cm0} {i : Fin n}
: hgp.GMDartHypermap.simpleCycle
  hgp.GMDartHypermap.rlink (hgp.GMring i)
  := by{
    unfold Hypermap.simpleCycle Hypermap.rlink List.IsCycleChain
    simp only [GMring_ne_nil, ↓ reduceDIte]
    change (_ ∧ funReflTransGen GMface _ _) ∧ _
    rw[GMDartHypermap_fsetoid_iff_end0, GMDartHypermap_edge_val_eq, edge_end0]
    rw[← List.getLast_map (l:=hgp.GMring i) (f := Subtype.val) (by{
      rw[List.ne_nil_iff_length_pos]
      simp[List.length_pos_iff_ne_nil, hgp.GMring_ne_nil]
    }), ← List.head_map (l:=hgp.GMring i) (f := Subtype.val) (by{
      rw[List.ne_nil_iff_length_pos]
      simp[List.length_pos_iff_ne_nil, hgp.GMring_ne_nil]
    })]
    have hc := (hgp.extendCMatte i).ring_cycle
    unfold List.IsCycleChain at hc
    simp only [(hgp.extendCMatte i).ring_ne_nil, ↓ reduceDIte, mrlink] at hc
    simp only [GMring_map_val, hc.right, and_true]
    constructor
    · {
      nth_rw 1 [← GMring_map_val, List.isChain_map] at hc
      apply (Eq.mp · hc.left)
      congr
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw[mrlink]
      change _ ↔ funReflTransGen GMface _ _
      rw[GMDartHypermap_fsetoid_iff_end0, GMDartHypermap_edge_val_eq, edge_end0]
    }
    · {
      have hs := (hgp.extendCMatte i).ring_simple
      rw[Hypermap.simpleList]
      rw[List.nodup_iff_getElem_ne_getElem] at hs
      rw[List.nodup_iff_getElem_ne_getElem]
      intro i j hij hjl
      simp only [List.length_map, hgp.GMring_length] at hjl
      specialize hs i j hij (by{simp[hjl]})
      simp only [List.getElem_map, ne_eq]
      simp only [List.getElem_map, ne_eq] at hs
      rw[Quotient.eq_iff_equiv]
      change ¬funReflTransGen GMface _ _
      simp only [← GMring_map_val, List.getElem_map] at hs
      rw[GMDartHypermap_fsetoid_iff_end0]
      exact hs
    }
  }

end GridMapProper
end GridPlane
