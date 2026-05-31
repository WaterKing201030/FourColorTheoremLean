import FourColorTheorem.Reals.Grid.Matte.Basic
import FourColorTheorem.Reals.Grid.Matte.CoarseIn

namespace GridPlane
namespace Matte

def toRegion (m : Matte) : GRegion := {p | p ∈ m}
theorem mem_toRegion_iff_mem {m : Matte} {p : GPoint} : p ∈ m.toRegion ↔ p ∈ m := by rfl
theorem toRegion_subset_iff_disk_subset {m1 m2 : Matte} :
  m1.toRegion ⊆ m2.toRegion ↔ m1.disk ⊆ m2.disk := by{
  simp only [toRegion, mem_iff]
  constructor
  · exact fun h1 x h2 => Set.mem_setOf.mp (h1 (Set.mem_setOf.mpr h2))
  · exact fun h1 x h2 => Set.mem_setOf.mpr (h1 (Set.mem_setOf.mp h2))
}

theorem toRegion_disjoint_iff_disk_disjoint {m1 m2 : Matte} :
  Disjoint m1.toRegion m2.toRegion ↔ m1.disk.Disjoint m2.disk := by{
  simp only [toRegion, Set.disjoint_iff_forall_ne]
  constructor
  · {
    intro h x h1 h2
    have h':=h (Set.mem_setOf.mpr h1) (Set.mem_setOf.mpr h2)
    exact h' rfl
  }
  · {
    intro h a ha b hb hab
    rw[←hab] at hb
    rw[Set.mem_setOf] at ha hb
    exact h ha hb
  }
}

theorem extend_adj {m m1 : Matte} {r : GRectangle} (rEmh : m.coarseIn r.toRegion)
  (hm_r : ∃ q ∈ r, q ∈ m) (hm_ri : ∃ q ∈ r.inner, q ∈ m1) (hm_m1 : m.disk.Disjoint m1.disk)
  : ∃xm : Matte, m.disk ⊆ xm.disk ∧ xm.toRegion ⊆ (r.toRegion ∪ m.toRegion) \ m1.toRegion
  ∧ m1.adj xm := by{
    have ⟨p, hp_ri, hp_m1⟩:=hm_ri
    have ⟨xm, xmP, sxmr, xm_p⟩:=coarse_extendsIn rEmh hm_r p hp_ri
    have m1_xm : ∃q ∈ m1, q ∈ xm := ⟨p, hp_m1, xm_p⟩
    apply extend_adj' rEmh hm_r hm_ri hm_m1 xmP sxmr m1_xm
  }
where extend_adj'{m m1 : Matte} {r : GRectangle} (rEmh : coarseIn r.toRegion m)
(hm_r : ∃ q ∈ r, q ∈ m) (hm_ri : ∃ q ∈ r.inner, q ∈ m1)
(hm_m1 : m.disk.Disjoint m1.disk) {xm : Matte} (xmP : m.Extension xm)
(sxmr : xm.disk ⊆ r.enum ∪ m.disk) (m1_xm : ∃ q ∈ m1, q ∈ xm)
: ∃xm : Matte, m.disk ⊆ xm.disk
∧ xm.toRegion ⊆ (r.toRegion ∪ m.toRegion) \ m1.toRegion
∧ m1.adj xm := by{
  induction xmP with
  | refl => {
    have ⟨q, h0, h1⟩:=m1_xm
    exfalso
    exact hm_m1 h1 h0
  }
  | step d xm0 xm' xm0P xm0ep Dxm IHxm => {
    have sxm0r : xm0.toRegion ⊆ r.toRegion ∪ m.toRegion := by{
      intro x hx
      rw[Set.mem_union]
      have hx':x ∈ xm'.disk := by{
        simp only [←mem_iff, Dxm, extDisk, List.mem_cons, ←mem_toRegion_iff_mem]
        apply Or.inr hx
      }
      have hx'':=sxmr hx'
      rw[List.mem_union_iff, GRectangle.mem_enum_iff, GRectangle.mem_iff_toRegion] at hx''
      rw[mem_toRegion_iff_mem]
      assumption
    }
    have sxm0r' : xm0.disk ⊆ r.enum ∪ m.disk := by{
      intro x hx
      rw[List.mem_union_iff, GRectangle.mem_enum_iff]
      have hx':=sxm0r (Set.mem_setOf.mpr hx)
      rw[Set.mem_union, ←GRectangle.mem_iff_toRegion, mem_toRegion_iff_mem] at hx'
      assumption
    }
    rcases em (∃x ∈ m1, x ∈ xm0) with m1_xm0 | m1'xm0
    · {
      apply IHxm sxm0r' m1_xm0
    }
    · {
      use xm0
      apply And.intro xm0P.subset
      rw[Set.subset_diff, and_assoc]
      apply And.intro sxm0r
      rw[toRegion_disjoint_iff_disk_disjoint]
      simp only [not_exists, not_and, mem_iff] at m1'xm0
      rw[←List.Disjoint] at m1'xm0
      apply And.intro m1'xm0.symm
      use edge d
      apply And.intro xm0ep
      rw[edge_2]
      rw[m1.mem_ring_iff_mem_disk_border, border, Set.mem_setOf]
      rw[xm0.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at xm0ep
      rw[edge_2] at xm0ep
      refine ⟨?_, m1'xm0.symm xm0ep.left⟩
      have ⟨q, h0, h1⟩:=m1_xm
      simp only [Dxm, extDisk, List.mem_cons] at h1
      apply (Or.resolve_right · (m1'xm0 h0)) at h1
      rw[←h1]
      exact h0
    }
  }
}

end Matte
end GridPlane
