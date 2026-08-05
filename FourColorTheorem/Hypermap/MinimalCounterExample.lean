import FourColorTheorem.Hypermap.Properties
import FourColorTheorem.Hypermap.Coloring

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

class IsMinimalCounterExample {α : Type u} [Fintype α]
  [DecidableEq α] (H : Hypermap α) : Prop
  extends H.PlanarBridgelessPlainPrecubic where
  non_colorable : ¬H.fourColorable
  minimal {α' : Type u} [Fintype α'] [DecidableEq α']
    {H' : Hypermap α'} : H'.PlanarBridgelessPlainPrecubic →
    Fintype.card α' < Fintype.card α → H'.fourColorable

theorem MinimalCounterExample.cubic (Hm : H.IsMinimalCounterExample) :
  H.Cubic := by{
  have Hc := Hm.toPrecubic
  have Hb := Hm.toBridgeless
  have Hp := Hm.toPlain
  have Hb' := Hb.node_period_ge_two
  simp only [cubic_def]
  simp only [precubic_def] at Hc
  have Hbc : ∀x, minimalPeriod H.node x = 2 ∨ minimalPeriod H.node x = 3 := by{
    intro x
    specialize Hb' x
    specialize Hc x
    omega
  }
  intro x
  specialize Hbc x
  apply Hbc.resolve_left
  clear Hbc
  intro Hbc
  rw[minimalPeriod_eq_two_iff] at Hbc
  rcases Hbc with ⟨hn2, hn1⟩
  let H1 := H.WalkupE x
  let H2 := H1.WalkupE ⟨node x, hn1⟩
  have H2c' := Hm.minimal (H' := H2) (by{
    apply PlanarBridgelessPlainPrecubic.concatEdge
    · exact Hm.toPlanarBridgelessPlainPrecubic
    · exact ⟨hn2, hn1⟩
  }) (by{
    simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique]
    rw[Nat.sub_sub]
    apply Nat.sub_lt ?_ (by{simp})
    rw[Fintype.card_pos_iff]
    apply Nonempty.intro x
  })
  apply Hm.non_colorable
  apply fourColorable_of_concatEdge_fourColorable Hp Hb ⟨hn2, hn1⟩ H2c'
}

end Hypermap
