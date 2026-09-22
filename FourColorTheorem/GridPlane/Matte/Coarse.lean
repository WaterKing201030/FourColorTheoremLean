import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.GridPlane.Matte.Constructors.Zoom

/-! 一个Matte在某个长方形内是光滑的，是指在这个长方形内的部分(含只重叠了一个像素的部分)都可以被拆成2x2的正方形 -/

open Function
open Relation

namespace GridPlane

namespace Matte
def coarseIn (m : Matte) (R : GRegion) :=
  ∀p q, p ∈ R → q.half = p.half → (q ∈ m ↔ p ∈ m)
theorem coarseIn_def {m : Matte} {R : GRegion} :
  m.coarseIn R ↔ ∀p q, p ∈ R → q.half = p.half → (q ∈ m ↔ p ∈ m)
  := Iff.rfl
theorem coarseIn_def' {m : Matte} {R : GRegion} :
  m.coarseIn R ↔ ∀p ∈ R, ∀q, q.half = p.half → (q ∈ m ↔ p ∈ m)
  := by{
  unfold coarseIn
  constructor
  · intro ih p hp q; exact ih p q hp
  · intro ih p q hp; exact ih p hp q
}

theorem coarseIn_of_subset {r0 r1 : GRegion} {m : Matte}
  (hr : r0 ⊆ r1) : m.coarseIn r1 → m.coarseIn r0 := by{
  intro h p q hpr hqp
  have h0 := hr hpr
  apply h <;> assumption
}

theorem coarseIn_zoom {r : GRegion} {m : Matte} :
  m.zoom.coarseIn r := by{
    rw[coarseIn]
    simp only [mem_zoom_iff]
    intro _ _ _ hqp
    rw[hqp]
  }

end Matte

end GridPlane
