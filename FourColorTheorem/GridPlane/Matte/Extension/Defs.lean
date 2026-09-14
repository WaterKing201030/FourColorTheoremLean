import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.Utils.List

open Function
open Relation

namespace GridPlane
namespace Matte

inductive canExtendTo (m : Matte) : Matte → Prop
| refl : canExtendTo m m
| step (d : GDart) (xm0 xm : Matte) (hme : canExtendTo m xm0)
  (hdr : edge d ∈ xm0.ring) (hdisk : ∀ x, x ∈ xm ↔ x ∈ d.half :: xm0.disk)
  : canExtendTo m xm

namespace canExtendTo

theorem subset {m xm : Matte} (h : canExtendTo m xm) : m.disk ⊆ xm.disk := by{
  induction h with
  | refl => apply List.Subset.refl
  | step _ _ _ hme hdr hdisk ih => {
    apply ih.trans
    intro x
    simp only [mem_def] at hdisk
    simp only [hdisk, List.mem_cons]
    apply Or.inr
  }
}
theorem subset' {m xm : Matte} (h : canExtendTo m xm) : ∀x ∈ m, x ∈ xm := by{
  intro
  rw[mem_def, mem_def]
  apply h.subset
}
theorem trans {m0 m1 m2 : Matte} (h01 : canExtendTo m0 m1)
  (h12 : canExtendTo m1 m2) : canExtendTo m0 m2 := by{
  induction h12 generalizing m0 with
  | refl => exact h01
  | step d _ _ _ hdr hdisk ih => exact .step d _ _ (ih h01) hdr hdisk
}

end canExtendTo

def canExtendIn (m : Matte) (r : GRectangle) (p : GPixel) : Prop :=
  ∃xm, canExtendTo m xm ∧ xm.disk ⊆ r.enum ++ m.disk ∧ p ∈ xm
theorem canExtendIn_of_subset {m : Matte} {r1 r2 : GRectangle} (hr : r1 ⊆ r2)
  : ∀p, canExtendIn m r1 p → canExtendIn m r2 p := by{
    intro p h
    let ⟨xm, ext, sub, con⟩ := h
    refine ⟨xm, ext, fun q hq => (List.mem_append.mp (sub hq)).elim
      (fun hr1 => by{
        apply List.mem_append_left
        rw[GRectangle.mem_enum_iff]
        rw[GRectangle.mem_enum_iff] at hr1
        exact hr hr1
      }) (by{
        intro h
        apply List.mem_append_right
        exact h
      }), con⟩
  }
theorem canExtendIn_of_mem {m : Matte} (r : GRectangle) {p : GPixel} (hp : p ∈ m)
  : canExtendIn m r p := by{
    use m
    apply And.intro canExtendTo.refl
    apply And.intro (List.subset_append_right _ _)
    exact hp
  }

end Matte
end GridPlane
