import FourColorTheorem.Pixelate.Approx.ScaledPoint
import FourColorTheorem.Pixelate.Approx.ScaledRectangle
import FourColorTheorem.GridPlane.Matte

/-! 把Matte放进实平面 -/

namespace RealPlane
open GridPlane

abbrev ScaledMatte := ℕ × Matte

namespace ScaledMatte

@[inline] instance instCoeRegion : Coe ScaledMatte Region where
  coe := fun b => {p | approxPoint b.1 p ∈ b.2}
theorem coe_def {b : ScaledMatte}
: (b : Region) = {p | approxPoint b.1 p ∈ b.2} := rfl
theorem coe_eq {b : ScaledMatte}
: (b : Region) = scaledRegion b.1 (b.2 : GRegion)
:= by{
  ext p
  simp[scaledRegion, Matte.mem_def]
}

@[inline] instance instMembership : Membership Point ScaledMatte where
  mem := fun b p => p ∈ (b : Region)
theorem mem_def {p : Point} {b : ScaledMatte}
: p ∈ b ↔ p ∈ (b : Region) := Iff.rfl

def refine (b : ScaledMatte) : ScaledMatte :=
  ⟨b.1 + 1, b.2.zoom⟩

@[simp] theorem refine_coe (b : ScaledMatte) :
  (b.refine : Region) = b := by
  ext z
  change approxPoint (b.1 + 1) z ∈ b.2.zoom ↔
    approxPoint b.1 z ∈ b.2
  rw [Matte.mem_zoom_iff, approxPoint_half]
@[simp] theorem mem_refine {p : Point} {b : ScaledMatte} :
  p ∈ b.refine ↔ p ∈ b := by{
  rw[mem_def]
  rw[refine_coe]
  rfl
}

def refineBy (t : ℕ) (b : ScaledMatte) : ScaledMatte := (refine^[t]) b
@[simp] theorem refineBy_fst (t : ℕ) (b : ScaledMatte) :
    (b.refineBy t).1 = b.1 + t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [refineBy, Function.iterate_succ_apply']
    change (b.refineBy t).1 + 1 = b.1 + (t + 1)
    rw [ih, Nat.add_assoc]

@[simp] theorem refineBy_snd (t : ℕ) (b : ScaledMatte) :
    (b.refineBy t).2 = Matte.zoom^[t] b.2 := by{
    induction t with
    | zero => rfl
    | succ t ih => {
      rw[refineBy, Function.iterate_succ_apply', refine]
      rw[refineBy] at ih
      simp only[ih, ← Function.iterate_succ_apply']
    }
  }

@[simp] theorem refineBy_coe (t : ℕ) (b : ScaledMatte) :
    (b.refineBy t : Region) = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    ext p
    rw[Set.mem_ofPred, Set.mem_ofPred, refineBy_fst, refineBy_snd]
    rw[Function.iterate_succ_apply', Matte.mem_zoom_iff]
    rw[← add_assoc, approxPoint_half]
    rw[refineBy_fst, refineBy_snd, Set.ext_iff] at ih
    simp at ih
    simp[ih]
@[simp] theorem mem_refineBy {p : Point} {b : ScaledMatte} {s : ℕ} :
  p ∈ b.refineBy s ↔ p ∈ b := by{
  rw[mem_def]
  rw[refineBy_coe]
  rfl
}

end ScaledMatte

theorem Region.exists_scaledMatte_of_open {U : Region} (hU : IsOpen U)
    {z : Point} (hz : z ∈ U) :
    ∃ m : ScaledMatte, z ∈ m ∧ (m : Region) ⊆ U := by
  obtain ⟨b, hzb, hbU⟩ := exists_open_region_approx hU hz
  let p := approxPoint b.1 z
  let m : ScaledMatte := ⟨b.1, Matte.ofGPixel p⟩
  have hzm : z ∈ m := Matte.mem_ofGPixel_iff.mpr rfl
  refine ⟨m, hzm, ?_⟩
  intro t ht
  have ht' : approxPoint b.1 t = p := Matte.mem_ofGPixel_iff.mp ht
  apply hbU
  change approxPoint b.1 t ∈ b.2
  rw [ht']
  exact b.inner_subset hzb

end RealPlane
