import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def arity (H : Hypermap α) (x : α) := minimalPeriod' H.face x
theorem arity_def {x : α} : H.arity x = minimalPeriod H.face x := by{
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
}
structure Pentagonal (H : Hypermap α) where
  arity_ge_five : ∀x, H.arity x ≥ 5
theorem pentagonal_def : H.Pentagonal ↔ ∀x, H.arity x ≥ 5 := by{
  constructor
  · apply Pentagonal.arity_ge_five
  · apply Pentagonal.mk
}

end Hypermap
