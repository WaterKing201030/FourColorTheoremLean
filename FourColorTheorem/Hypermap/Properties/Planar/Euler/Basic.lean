import FourColorTheorem.Hypermap.Properties.Planar.Euler.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem euler_lhs_ge3_intro (x : α) : H.euler_lhs ≥ 3:=by{
  unfold euler_lhs
  have hgp:=H.gcomp_pos_intro x
  rw[mul_two, ←two_add_one_eq_three, ←one_add_one_eq_two]
  apply add_le_add
  · {
    apply add_le_add
    all_goals
    exact hgp
  }
  apply Nat.succ_le_of_lt
  rw[Fintype.card_pos_iff]
  apply Nonempty.intro x
}
theorem euler_rhs_ge3_intro (x : α) : H.euler_rhs ≥ 3:=by{
  unfold euler_rhs
  have hep:=H.ecomp_pos_intro x
  have hnp:=H.ncomp_pos_intro x
  have hfp:=H.fcomp_pos_intro x
  rw[←two_add_one_eq_three, ←one_add_one_eq_two, ←Nat.add_assoc]
  apply add_le_add
  · apply add_le_add hep hnp
  exact hfp
}

end Hypermap
