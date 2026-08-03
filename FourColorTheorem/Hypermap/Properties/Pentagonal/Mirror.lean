import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Properties.Pentagonal.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem mirror_arity : H.mirror.arity = H.arity :=by{
  unfold arity
  rw[mirror_face]
  unfold faceinv
  rw[Fintype.bijInv_minimalPeriod' H.face_bijective]
}

end Hypermap
