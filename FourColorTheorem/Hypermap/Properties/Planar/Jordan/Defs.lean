import FourColorTheorem.Hypermap.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def moebius_path (H : Hypermap α) (p : List α) : Prop :=
  if hp: p = [] then False
  else p.Nodup ∧ p.IsChain H.clink
  ∧ H.node (p.head hp) ∈ p.tail.drop (p.tail.idxOf (H.nodeinv (p.getLast hp)))
def jordan (H : Hypermap α) := ∀q, ¬H.moebius_path q

end Hypermap
