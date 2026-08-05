import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def euler_lhs (H : Hypermap α) := H.gcomp * 2 + Fintype.card α
def euler_rhs (H : Hypermap α) := H.ecomp + (H.ncomp + H.fcomp)
def genus (H : Hypermap α) := (H.euler_lhs - H.euler_rhs) / 2

structure Planar (H : Hypermap α) where
  genus_zero : H.genus = 0
theorem planar_def : H.Planar ↔ H.genus = 0 := by{
  constructor
  · intro h
    exact h.genus_zero
  · intro h
    exact ⟨h⟩
}
end Hypermap
