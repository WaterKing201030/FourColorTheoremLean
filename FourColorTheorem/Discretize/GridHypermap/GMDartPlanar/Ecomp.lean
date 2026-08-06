import FourColorTheorem.Discretize.GridHypermap.GMInner
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Card

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

section edgecard
theorem GMDartHypermap_ecomp {hgp : GridMapProper ab0 cm0}
  : hgp.GMDartHypermap.ecomp =
    hgp.extendBBox.area * 2 + hgp.extendBBox.width + hgp.extendBBox.height
  := by{
    have ih := hgp.GMDart_card
    rw[hgp.GMDartHypermap_plain.ecomp_double] at ih
    change _ = _ * (2 * 2) + _ at ih
    rw[← mul_assoc, ← add_mul] at ih
    simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at ih
    rwa[add_assoc]
  }
end edgecard

end GridMapProper
end GridPlane
