import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Card
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Ncomp
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Ecomp
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Fcomp
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Gcomp
import FourColorTheorem.Hypermap.Properties.Planar.Euler.Basic

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

theorem GMDartHypermap_planar {hgp : GridMapProper ab0 cm0}
: hgp.GMDartHypermap.Planar := by{
  rw[Hypermap.planar_def, Hypermap.genus, Hypermap.euler_rhs, Hypermap.euler_lhs]
  have hg : hgp.GMDartHypermap.gcomp = 1 := GMDartHypermap_connected
  rw[hg, Hypermap.Plain.ecomp_double GMDartHypermap_plain]
  simp only [one_mul, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, gt_iff_lt]
  rw[mul_two, ← add_assoc, ← Nat.sub_sub, Nat.add_sub_cancel]
  rw[add_comm (Hypermap.ncomp _), ← Nat.sub_sub]
  apply Nat.lt_of_le_of_lt (Nat.sub_le_sub_left GMDartHypermap_ncomp_ge _)
  rw[GMDartHypermap_ecomp, mul_two, Nat.sub_right_comm]
  rw[add_assoc, add_right_comm, ← add_assoc]
  rw[Nat.add_sub_cancel, GMDartHypermap_fcomp, GRectangle.area]
  ring_nf
  omega
}
end GridMapProper
end GridPlane
