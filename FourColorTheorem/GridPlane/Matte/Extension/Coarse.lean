import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.GridPlane.Matte.Constructors.Zoom
import FourColorTheorem.GridPlane.Matte.Extension.Extend
import FourColorTheorem.GridPlane.Matte.Coarse

open Function
open Relation

namespace GridPlane
namespace Matte

theorem canExtendIn_of_coarseIn {m : Matte} {r : GRectangle}
  (r0Emh : m.coarseIn r) (m_r : ∃ p ∈ r, p ∈ m)
  : ∀p, p ∈ r.inner → m.canExtendIn r p
  := by{
  sorry
}

end Matte
end GridPlane
