import FourColorTheorem.Hypermap.Actions.Patch
import FourColorTheorem.Hypermap.Properties.Plain.Basic

open Function
open Relation

namespace Hypermap

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]

namespace Patch

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]
variable {G : Hypermap α} {Gd : Hypermap αd} {Gr : Hypermap αr}
variable {hd : αd → α} {hr : αr → α} {bGd : List αd} {bGr : List αr}
variable (patchG : Patch G Gd Gr hd hr bGd bGr)
include patchG

theorem plain_iff : G.plain ↔ Gd.plainSubset {x | x ∉ bGd} ∧ Gr.plain := by{
  change _ ↔ _ ⊆ _ ∧ _
  rw[Set.setOf_subset_setOf, plain_iff_edge_edge, plain_iff_edge_edge]
  simp only [minimalPeriod_eq_two_iff]
  constructor
  · {
    intro h
    constructor
    · {
      intro x hx
      specialize h (hd x)
      rw[← patchG.disk_edge_morph _ hx, patchG.disk_hom_injective.ne_iff, ← patchG.disk_edge_morph,
      patchG.disk_hom_injective.eq_iff] at h
      · exact h
      revert hx; rw[not_imp_not]
      intro hx
      rw[← patchG.disk_border_cedge_close hx]
      apply Gd.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      intro x
      specialize h (hr x)
      rw[← patchG.rem_edge_morph, patchG.rem_hom_injective.ne_iff, ← patchG.rem_edge_morph,
      patchG.rem_hom_injective.eq_iff] at h
      exact h
    }
  }
  · {
    intro ⟨hd, hr⟩ x
    rcases patchG.disk_not_border_rem_hom_surj x with ⟨x', hx', hx'x⟩ | ⟨x', hx'⟩
    · {
      specialize hd _ hx'
      rw[← hx'x, ← patchG.disk_edge_morph _ hx', patchG.disk_hom_injective.ne_iff]
      refine ⟨?_, hd.right⟩
      rw[← patchG.disk_edge_morph, hd.left]
      revert hx'; rw[not_imp_not]
      intro hx
      rw[← patchG.disk_border_cedge_close hx]
      apply Gd.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      specialize hr x'
      rw[← hx', ← patchG.rem_edge_morph, patchG.rem_hom_injective.ne_iff, ← patchG.rem_edge_morph,
      patchG.rem_hom_injective.eq_iff]
      exact hr
    }
  }
}

end Patch
end Hypermap
