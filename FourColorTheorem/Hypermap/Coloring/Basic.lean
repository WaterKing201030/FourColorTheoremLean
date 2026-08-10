import FourColorTheorem.Hypermap.Coloring.Defs
import FourColorTheorem.Hypermap.Properties

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

theorem isColoring.cface_invariant' {k : α → FourColor}
  (hk : ∀ x, k (face x) = k x) : ∀ x y, H.cface x y → k x = k y := by{
  intro x y hxy
  rw[cface, funReflTransGen_iff_iterate] at hxy
  rcases hxy with ⟨n, hn⟩
  induction n generalizing y with
  | zero => simp at hn; simp[hn]
  | succ n' ih => {
    specialize ih (face^[n'] x) rfl
    rw[iterate_succ_apply'] at hn
    rw[ih, ← hk, hn]
  }
}
theorem isColoring.cface_invariant {k : α → FourColor}
  (hk : H.isColoring k) : ∀ x y, H.cface x y → k x = k y := by{
  apply cface_invariant'
  exact hk.right
}
theorem isGraphColoring.cnode_invariant' {k : α → FourColor}
  (hk : ∀ x, k (node x) = k x) : ∀ x y, H.cnode x y → k x = k y := by{
  intro x y hxy
  rw[cnode, funReflTransGen_iff_iterate] at hxy
  rcases hxy with ⟨n, hn⟩
  induction n generalizing y with
  | zero => simp at hn; simp[hn]
  | succ n' ih => {
    specialize ih (node^[n'] x) rfl
    rw[iterate_succ_apply'] at hn
    rw[ih, ← hk, hn]
  }
}
theorem isGraphColoring.cnode_invariant {k : α → FourColor}
  (hk : H.isGraphColoring k) : ∀ x y, H.cnode x y → k x = k y := by{
  apply cnode_invariant'
  exact hk.right
}

theorem fourColorable.bridgeless (hf : H.fourColorable) : H.Bridgeless
:= by{
  rcases hf with ⟨f, hf⟩
  have hff' := hf.cface_invariant
  rcases hf with ⟨hfe, hff⟩
  rw[bridgeless_def]
  intro x hx
  specialize hfe x
  specialize hff' x (edge x) hx
  exact hfe hff'.symm
}

end Hypermap
