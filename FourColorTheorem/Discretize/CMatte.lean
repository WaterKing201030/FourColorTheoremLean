import FourColorTheorem.GridPlane.Matte
import FourColorTheorem.Discretize.AdjBox

namespace GridPlane

structure CMatte (n : ℕ) where
  cm : Fin n → Matte
  cm_injOn : ∀i j p, p ∈ cm i → p ∈ cm j → i = j

def abCmProper {n : ℕ} (AB : AdjBox n) (CM : CMatte n)
  (e : AdjIndex n) (i : Fin n) : Prop :=
  (AB.ab e).proper → ((i ∈ e → ∃p ∈ (AB.ab e).inner, p ∈ CM.cm i)
  ∧ (∀p ∈ AB.ab e, p ∈ CM.cm i → i ∈ e))

structure ABCMatte (n : ℕ) extends CMatte n, AdjBox n where
  ab_cm_injOn : ∀e i, abCmProper toAdjBox toCMatte e i

end GridPlane
