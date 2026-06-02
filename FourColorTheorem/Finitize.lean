import FourColorTheorem.Reals.Approx
import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Reals.Grid.Matte

open Function
open Relation
open RealPlane
open GridPlane

def fin_colorable (nc : ℕ) : Prop :=
  ∀m, IsFiniteSimpleMap m → m.colorable_with nc


