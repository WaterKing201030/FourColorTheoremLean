import FourColorTheorem.Hypermap.Actions.Walkup
import FourColorTheorem.Hypermap.Coloring

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

class IsMinimalCounterExample {α : Type u} [Fintype α]
  [DecidableEq α] (H : Hypermap α) : Prop
  extends H.PlanarBridgelessPlainPrecubic where
  non_colorable : ¬H.fourColorable
  minimal {α' : Type v} [Fintype α'] [DecidableEq α']
    {H' : Hypermap α'} : H'.PlanarBridgelessPlainPrecubic →
    Fintype.card α' < Fintype.card α → H'.fourColorable

-- theorem MinimalCounterExample.cubic (Hm : H.IsMinimalCounterExample) :
--   H.cubic := by{

-- }

-- theorem MinimalCounterExample.connected (Hm : H.IsMinimalCounterExample) :
--   H.connected := by{

-- }

end Hypermap
