import FourColorTheorem.Hypermap.Properties.Cubic.Basic
import FourColorTheorem.Hypermap.Actions.Walkup.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem walkupe_precubic_of_precubic (Hc : H.precubic) (x : α) : (H.WalkupE x).precubic := by{
  rw[precubic_def] at *
  intro x'
  have Hc' := Hc x'.val
  apply le_trans ?_ Hc'
  apply Finite.skip_minimalPeriod_le
}

end Hypermap
