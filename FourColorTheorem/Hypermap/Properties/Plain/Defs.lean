import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def plainSubset (H : Hypermap α) : Set (Set α) := {s | s ⊆ {x | minimalPeriod H.edge x = 2}}
def plain (H : Hypermap α) := Set.univ ∈ H.plainSubset
theorem plain_iff_edge_edge : H.plain ↔ ∀x, H.edge (H.edge x) = x ∧ H.edge x ≠ x:=by{
  unfold plain plainSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_two_iff]
}

end Hypermap
