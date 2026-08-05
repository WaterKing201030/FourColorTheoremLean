import FourColorTheorem.Hypermap.Properties.Planar.Euler.Mirror
import FourColorTheorem.Hypermap.Properties.Planar.PlanarEquiv

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem mirror_jordan : H.mirror.jordan ↔ H.jordan := by{
  simp only [←planar_iff_jordan, mirror_planar_iff]
}

end Hypermap
