import FourColorTheorem.Hypermap.Properties
import FourColorTheorem.Hypermap.Coloring

open Relation
open Function

namespace Hypermap

universe u
variable {α : Type u}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

structure IsMinimalCounterExample {α : Type u} [Fintype α]
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

lemma exists_minimal_counterexample_of_exists_noncolorable
    (ex : ∃ β : Type u, ∃ _ : Fintype β, ∃ _ : DecidableEq β,
    ∃ H' : Hypermap β,
          H'.PlanarBridgelessPlainPrecubic ∧ ¬H'.fourColorable) :
    ∃ β : Type u, ∃_ : Fintype β, ∃_: DecidableEq β,
    ∃H' : Hypermap β,
      IsMinimalCounterExample H' := by
  -- 定义基数集合
  let S : Set ℕ := { n |
                ∃ β : Type u, ∃_ : Fintype β, ∃_: DecidableEq β,
                ∃H' : Hypermap β,
                H'.PlanarBridgelessPlainPrecubic ∧ ¬H'.fourColorable ∧ Fintype.card β = n }
  -- S 非空
  let P (n : ℕ) := ∃ β : Type u, ∃_ : Fintype β, ∃_: DecidableEq β,
          ∃H' : Hypermap β,
          H'.PlanarBridgelessPlainPrecubic ∧ ¬H'.fourColorable ∧ Fintype.card β = n
  have nonempty_P : ∃ n, P n := by
    obtain ⟨β, instF, instD, H', hpp, hnot⟩ := ex
    use Fintype.card β
    exact ⟨β, instF, instD, H', hpp, hnot, rfl⟩
  classical
  -- 取最小的 n 满足 P
  let n0 := Nat.find nonempty_P
  have n0_spec : P n0 := Nat.find_spec nonempty_P
  -- 从 P n0 中取出对应的 hypermap
  obtain ⟨β0, instF0, instD0, H0, hpp0, hnot0, card_eq0⟩ := n0_spec
  -- 证明 H0 是最小反例
  refine ⟨β0, instF0, instD0, H0, ?_⟩
  constructor
  · exact hpp0
  · exact hnot0
  · intro β' instF' instD' H' hpp' hnot'
    by_contra hnot_color
    -- 若 H' 非四色，则其基数也在 P 中
    have card_in_P : P (Fintype.card β') := by{
      use β', instF', instD', H'
    }
    -- 由 n0 的最小性，n0 ≤ Fintype.card β'
    have le := Nat.find_min nonempty_P (m:=Fintype.card β')
    apply swap at le
    specialize le card_in_P
    apply le
    unfold n0 at card_eq0
    rwa[← card_eq0]

section no_counterexample

variable (no_counterexample : ∀ {β : Type u} [Fintype β]
  [DecidableEq β] {H : Hypermap β}, H.PlanarBridgelessPlainPrecubic
  → ¬H.IsMinimalCounterExample)
include no_counterexample
variable {α : Type u}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

theorem planarBridgelessPlainPrecubic_fourColorable_of_no_counterexample
  (Hp : H.PlanarBridgelessPlainPrecubic)
  : H.fourColorable := by{
  by_contra Hc
  have IH := exists_minimal_counterexample_of_exists_noncolorable (by{
    use α, (by infer_instance), (by infer_instance), H
  })
  have ⟨_, _, _, H', hH'⟩ := IH
  specialize no_counterexample (H := H') hH'.toPlanarBridgelessPlainPrecubic
  contradiction
}

theorem planarBridgeless_fourColorable_of_no_counterexample
  (Hp : H.PlanarBridgeless)
  : H.fourColorable := by{
  have Hp' := Hp.cube_planarBridgelessPlainPrecubic
  have IH := planarBridgelessPlainPrecubic_fourColorable_of_no_counterexample no_counterexample
    (H := H.cube) Hp'
  exact fourColorable_of_cube_fourColorable IH
}

end no_counterexample

end Hypermap
