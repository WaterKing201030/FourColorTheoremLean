import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Color.FourColor
import FourColorTheorem.Color.Trace
import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Actions.Walkup

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

def isColoring (k : α → FourColor) :=
  (∀x y, H.cedge x y → k x ≠ k y) ∧ (∀x y, H.cface x y → k x = k y)
def isGraphColoring (k : α → FourColor) :=
  (∀x y, H.cedge x y → k x ≠ k y) ∧ (∀x y, H.cnode x y → k x = k y)
def fourColorable := ∃k, H.isColoring k
def fourGraphColorable := ∃k, H.isGraphColoring k

@[inline] instance isColoring.instDecidable : DecidablePred H.isColoring := by{
  intro k
  unfold isColoring
  infer_instance
}
@[inline] instance isGraphColoring.instDecidable : DecidablePred H.isGraphColoring := by{
  intro k
  unfold isGraphColoring
  infer_instance
}
@[inline] instance fourColorable.instDecidable : Decidable (H.fourColorable) := by{
  unfold fourColorable
  infer_instance
}
@[inline] instance fourGraphColorable.instDecidable : Decidable (H.fourGraphColorable) := by{
  unfold fourGraphColorable
  infer_instance
}

theorem fourColorable.bridgeless (hf : H.fourColorable) : H.bridgeless := by{
  rcases hf with ⟨f, hfe, hff⟩
  intro x hx
  specialize hfe x (edge x) (funReflTransGen.single _ _)
  specialize hff x (edge x) hx
  exact hfe hff
}
theorem isColoring_dual (k : α → FourColor)
: H.dual.isColoring k ↔ H.isGraphColoring k := by{
  unfold isColoring
  simp only [dual_cedge, dual_cface]
  rfl
}
theorem fourColorable_dual
: H.dual.fourColorable ↔ H.fourGraphColorable := by{
  unfold fourColorable
  simp only [isColoring_dual]
  rfl
}

theorem isColoring_mirror (k : α → FourColor)
: H.mirror.isColoring k ↔ H.isColoring k := by{
  unfold isColoring
  simp only [mirror_cedge, mirror_cface, InvImage]
  apply and_congr_left
  intro hf
  constructor
  · {
    intro ih x y hxy
    specialize ih (face x) (face y)
    have hf0 := hf x (face x) (funReflTransGen.single _ _)
    have hf1 := hf y (face y) (funReflTransGen.single _ _)
    rw[← hf0, ← hf1] at ih
    apply ih
    have hx (x : α) : H.cedge (H.edgeinv x) x := by{
      apply ReflTransGen.single
      exact edgeinv_rightinv _
    }
    simp only [edgeinv_eq, comp_apply] at hx
    exact (hx x).trans (hxy.trans (H.cedge_equivalence.symm (hx y)))
  }
  · {
    intro ih x y hxy
    have hxy' : H.cedge (edge (node x)) (edge (node y)) := by{
      apply (H.cedge_equivalence.symm (funReflTransGen.single H.edge (node x))).trans
      apply hxy.trans
      apply funReflTransGen.single
    }
    specialize ih _ _ hxy'
    have hf (x : α) := hf (edge (node x)) (face (edge (node x))) (funReflTransGen.single _ _)
    simp only [fen_cancel] at hf
    simp only [hf] at ih
    exact ih
  }
}
theorem fourColorable_mirror : H.mirror.fourColorable ↔ H.fourColorable := by{
  unfold fourColorable
  simp only [isColoring_mirror]
}

open FourColor
def satTrace (r : List α) (et : ColSeq)
  := ∃k, H.isColoring k ∧ et = ColSeq.trace (r.map k)
@[inline] instance satTrace.instDecidable {r : List α} {et : ColSeq}
: Decidable (H.satTrace r et) := by{
  unfold satTrace
  infer_instance
}

end Hypermap
