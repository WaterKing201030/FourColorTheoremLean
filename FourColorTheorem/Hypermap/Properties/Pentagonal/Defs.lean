import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def arity (H : Hypermap α) (x : α) := minimalPeriod' H.face x
def pentagonal (H : Hypermap α) := ∀x, 4 < H.arity x
theorem arity_def {x : α} : H.arity x = minimalPeriod H.face x := by{
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
}

end Hypermap
