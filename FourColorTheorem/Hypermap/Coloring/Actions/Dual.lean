import FourColorTheorem.Hypermap.Coloring.Basic
import FourColorTheorem.Hypermap.Actions.Dual

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

theorem isColoring_dual (k : α → FourColor)
: H.dual.isColoring k ↔ H.isGraphColoring k := by{
  unfold isColoring isGraphColoring
  simp only [dual_edge, dual_face]
  apply and_congr
  · {
    constructor
    · intro ih x; specialize ih (edge x); rw[edgeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.edgeinv x); rw[edgeinv_rightinv] at ih; exact ih.symm
  }
  · {
    constructor
    · intro ih x; specialize ih (node x); rw[nodeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.nodeinv x); rw[nodeinv_rightinv] at ih; exact ih.symm
  }
}
theorem fourColorable_dual_iff
: H.dual.fourColorable ↔ H.fourGraphColorable := by{
  unfold fourColorable
  simp only [isColoring_dual]
  rfl
}

end Hypermap
