import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def bridgeless (H : Hypermap α) := ∀x, ¬H.cface x (H.edge x)
def loopless (H : Hypermap α) := ∀x, ¬H.cnode x (H.edge x)

end Hypermap
