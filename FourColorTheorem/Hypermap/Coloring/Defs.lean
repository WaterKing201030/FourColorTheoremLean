import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Color.FourColor
import FourColorTheorem.Color.Trace

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

def isColoring (k : α → FourColor) :=
  (∀x, k (edge x) ≠ k x) ∧ (∀x, k (face x) = k x)
def isGraphColoring (k : α → FourColor) :=
  (∀x, k (edge x) ≠ k x) ∧ (∀x, k (node x) = k x)
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

end Hypermap
