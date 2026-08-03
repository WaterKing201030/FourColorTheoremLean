import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Color.FourColor
import FourColorTheorem.Color.Trace
import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Actions.Mirror
import FourColorTheorem.Hypermap.Actions.Walkup

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

def isColoring (k : α → FourColor) :=
  (∀x, k (edge x) ≠ k x) ∧ (∀x, k (face x) = k x)
def isGraphColoring (k : α → FourColor) :=
  (∀x, k (edge x) ≠ k x) ∧ (∀x, k (node x) = k x)
def fourColorable := ∃k, H.isColoring k
def fourGraphColorable := ∃k, H.isGraphColoring k

@[inline] instance isColoring.instDecidable : DecidablePred H.isColoring := by{
  intro k
  unfold isColoring
  infer_instance
}
@[inline] instance isGraphColoring.instDecidable : DecidablePred H.isGraphColoring := by{
  intro k
  unfold isGraphColoring
  infer_instance
}
@[inline] instance fourColorable.instDecidable : Decidable (H.fourColorable) := by{
  unfold fourColorable
  infer_instance
}
@[inline] instance fourGraphColorable.instDecidable : Decidable (H.fourGraphColorable) := by{
  unfold fourGraphColorable
  infer_instance
}

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

theorem fourColorable.bridgeless (hf : H.fourColorable) : H.bridgeless
:= by{
  rcases hf with ⟨f, hf⟩
  have hff' := hf.cface_invariant
  rcases hf with ⟨hfe, hff⟩
  intro x hx
  specialize hfe x
  specialize hff' x (edge x) hx
  exact hfe hff'.symm
}
theorem isColoring_dual (k : α → FourColor)
: H.dual.isColoring k ↔ H.isGraphColoring k := by{
  unfold isColoring isGraphColoring
  simp only [dual_edge, dual_face]
  apply and_congr
  · {
    constructor
    · intro ih x; specialize ih (edge x); rw[edgeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.edgeinv x); rw[edgeinv_rightinv] at ih; exact ih.symm
  }
  · {
    constructor
    · intro ih x; specialize ih (node x); rw[nodeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.nodeinv x); rw[nodeinv_rightinv] at ih; exact ih.symm
  }
}
theorem fourColorable_dual
: H.dual.fourColorable ↔ H.fourGraphColorable := by{
  unfold fourColorable
  simp only [isColoring_dual]
  rfl
}

theorem isColoring_mirror (k : α → FourColor)
: H.mirror.isColoring k ↔ H.isColoring k := by{
  unfold isColoring
  simp only [mirror_edge, comp_apply, mirror_face]
  have h0 : (∀ (x : α), k (H.faceinv x) = k x) ↔ (∀ (x : α), k (face x) = k x) := by{
    constructor
    · intro ih x; specialize ih (face x); rw[faceinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.faceinv x); rw[faceinv_rightinv] at ih; exact ih.symm
  }
  rw[h0]
  apply and_congr_left
  intro hkf
  simp only [hkf]
  have h1 : (∀ (x : α), k (H.nodeinv x) ≠ k x) ↔ (∀ (x : α), k (node x) ≠ k x) := by{
    constructor
    · intro ih x; specialize ih (node x); rw[nodeinv_leftinv] at ih; exact ih.symm
    · intro ih x; specialize ih (H.nodeinv x); rw[nodeinv_rightinv] at ih; exact ih.symm
  }
  simp only [nodeinv_apply, hkf] at h1
  rw[← h1]
}
theorem fourColorable_mirror : H.mirror.fourColorable ↔ H.fourColorable := by{
  unfold fourColorable
  simp only [isColoring_mirror]
}

open FourColor
def satTrace (r : List α) (et : ColSeq)
  := ∃k, H.isColoring k ∧ et = ColSeq.trace (r.map k)
@[inline] instance satTrace.instDecidable {r : List α} {et : ColSeq}
: Decidable (H.satTrace r et) := by{
  unfold satTrace
  infer_instance
}

end Hypermap
