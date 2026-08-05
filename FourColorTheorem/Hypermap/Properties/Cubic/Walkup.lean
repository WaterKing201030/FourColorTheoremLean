import FourColorTheorem.Hypermap.Properties.Cubic.Basic
import FourColorTheorem.Hypermap.Actions.Walkup.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem Precubic.walkupe (Hc : H.Precubic) (x : α) : (H.WalkupE x).Precubic := by{
  rw[precubic_def] at *
  intro x'
  have Hc' := Hc x'.val
  apply le_trans ?_ Hc'
  apply Finite.skip_minimalPeriod_le
}

end Hypermap
