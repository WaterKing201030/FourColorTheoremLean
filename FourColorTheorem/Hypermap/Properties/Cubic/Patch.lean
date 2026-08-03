import FourColorTheorem.Hypermap.Actions.Patch
import FourColorTheorem.Hypermap.Properties.Cubic.Basic

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

theorem cubic_iff : G.cubic ↔ Gd.cubic ∧ Gr.cubicSubset {x | x ∉ bGr} := by{
  change _ ↔ _ ∧ _ ⊆ _
  simp only [Set.setOf_subset_setOf, cubic_iff_period_three, minimalPeriod_eq_three_iff]
  constructor
  · {
    intro h
    constructor
    · {
      intro x
      specialize h (hd x)
      rw[← patchG.disk_node_morph, patchG.disk_hom_injective.ne_iff, ← patchG.disk_node_morph,
      ← patchG.disk_node_morph, patchG.disk_hom_injective.eq_iff] at h
      exact h
    }
    · {
      intro x hx
      specialize h (hr x)
      rw[← patchG.rem_node_morph _ hx, patchG.rem_hom_injective.ne_iff, ← patchG.rem_node_morph,
      ← patchG.rem_node_morph, patchG.rem_hom_injective.eq_iff] at h
      · exact h
      · revert hx; rw[not_imp_not]
        intro hx
        rw[← patchG.rem_border_cnode_close hx]
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.tail (b:=node x)
        · apply funReflTransGen.single
        · rfl
      · revert hx; rw[not_imp_not]
        intro hx
        rw[← patchG.rem_border_cnode_close hx]
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.single
    }
  }
  · {
    intro ⟨hd, hr⟩ x
    rcases patchG.disk_rem_not_border_hom_surj x with ⟨x', hx'⟩ | ⟨x', hx', hx'x⟩
    · {
      specialize hd x'
      rw[← hx', ← patchG.disk_node_morph, patchG.disk_hom_injective.ne_iff,
      ← patchG.disk_node_morph, ← patchG.disk_node_morph, patchG.disk_hom_injective.eq_iff]
      exact hd
    }
    · {
      specialize hr _ hx'
      rw[← hx'x, ← patchG.rem_node_morph _ hx', patchG.rem_hom_injective.ne_iff]
      refine ⟨?_, hr.right⟩
      rw[← patchG.rem_node_morph]
      · {
        rw[← patchG.rem_node_morph, hr.left]
        revert hx'; rw[not_imp_not]
        intro hx'
        rw[← patchG.rem_border_cnode_close hx']
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.tail (b:=node x')
        · apply funReflTransGen.single
        · rfl
      }
      revert hx'; rw[not_imp_not]
      intro hx'
      rw[← patchG.rem_border_cnode_close hx']
      apply Gr.cnode_equivalence.symm
      apply funReflTransGen.single
    }
  }
}

end Patch
end Hypermap
