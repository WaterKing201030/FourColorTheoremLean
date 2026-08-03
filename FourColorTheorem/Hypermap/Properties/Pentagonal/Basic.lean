import FourColorTheorem.Hypermap.Properties.Pentagonal.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem cface_arity {x y : α} (hxy : H.cface x y) : H.arity x = H.arity y := by{
  unfold cface at hxy
  rw[funReflTransGen_iff_iterate_bounded] at hxy
  have ⟨n, hn, hxy'⟩:=hxy
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
  rw[←hxy']
  rw[minimalPeriod_eq_minimalPeriod_iff]
  intro n'
  unfold IsPeriodicPt IsFixedPt
  rw[←iterate_add_apply, add_comm, iterate_add_apply]
  symm
  apply Injective.eq_iff
  apply Injective.iterate
  exact H.face_injective
}
theorem iter_face_arity {x : α} : H.face^[H.arity x] x = x:=by{
  unfold arity
  rw[minimalPeriod'_eq_minimalPeriod]
  exact isPeriodicPt_minimalPeriod H.face x
}

end Hypermap
