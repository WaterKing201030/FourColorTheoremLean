import FourColorTheorem.Hypermap.Coloring.Basic
import FourColorTheorem.Hypermap.Actions.Mirror

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

theorem isColoring_mirror (k : α → FourColor)
: H.mirror.isColoring k ↔ H.isColoring k := by{
  unfold isColoring
  simp only [mirror_edge, comp_apply, mirror_face]
  have h0 : (∀ (x : α), k (H.faceinv x) = k x) ↔ (∀ (x : α), k (face x) = k x) := by{
    constructor
    · intro ih x; specialize ih (face x); rw[faceinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.faceinv x); rw[faceinv_rightinv] at ih; exact ih.symm
  }
  rw[h0]
  apply and_congr_left
  intro hkf
  simp only [hkf]
  have h1 : (∀ (x : α), k (H.nodeinv x) ≠ k x) ↔ (∀ (x : α), k (node x) ≠ k x) := by{
    constructor
    · intro ih x; specialize ih (node x); rw[nodeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.nodeinv x); rw[nodeinv_rightinv] at ih; exact ih.symm
  }
  simp only [nodeinv_apply, hkf] at h1
  rw[← h1]
}
theorem fourColorable_mirror_iff : H.mirror.fourColorable ↔ H.fourColorable := by{
  unfold fourColorable
  simp only [isColoring_mirror]
}

end Hypermap
