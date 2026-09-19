import FourColorTheorem.RealPlane.Defs.Topology
import FourColorTheorem.GridPlane.Defs.Rectangle
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[simp] lemma exp2_pos (s : ℕ) : (2 : ℝ) ^ s > 0 := by{simp}

noncomputable def approx (s : ℕ) (x : ℝ) : ℤ := ⌊2 ^ s * x⌋

theorem approx_eq_iff {s : ℕ} {x : ℝ} {m : ℤ} :
    approx s x = m ↔ (m : ℝ) ≤ 2 ^ s * x ∧ 2 ^ s * x < m + 1 :=
  Int.floor_eq_iff
theorem approx_le (s : ℕ) (x : ℝ) : (approx s x : ℝ) ≤ 2 ^ s * x :=
  Int.floor_le _
theorem lt_approx_add_one (s : ℕ) (x : ℝ) : 2 ^ s * x < (approx s x : ℝ) + 1 :=
  Int.lt_floor_add_one _

theorem exists_precision {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∃ s, a < 2 ^ s * ε := by
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (a / ε) (by norm_num : (1 : ℝ) < 2)
  exact ⟨s, (div_lt_iff₀ hε).mp hs⟩

noncomputable def scale (s : ℕ) (m : ℤ) : ℝ := m / 2 ^ s

@[simp] theorem approx_scale (s : ℕ) (m : ℤ) : approx s (scale s m) = m := by {
  simp only [approx, scale]
  rw[mul_comm]
  simp
}

theorem approx_half (s : ℕ) (x : ℝ) : approx (s + 1) x / 2 = approx s x := by {
  change ⌊2 ^ (s + 1) * x⌋ / (2 : ℕ) = approx s x
  rw [← Int.floor_div_natCast _ 2]
  congr 1
  ring
}

namespace RealPlane
open GridPlane

noncomputable def approxPoint (s : ℕ) (x : Point) : GPoint :=
  ⟨approx s x.1, approx s x.2⟩
noncomputable def scalePoint (s : ℕ) (m : GPoint) : Point :=
  ⟨scale s m.1, scale s m.2⟩
@[simp] theorem approxPoint_scalePoint (s : ℕ) (p : GPoint) :
    approxPoint s (scalePoint s p) = p := by
  simp [approxPoint, scalePoint]
theorem approxPoint_half (s : ℕ) (z : Point) :
    (approxPoint (s + 1) z).half = approxPoint s z := by
  simp [GPoint.half, approxPoint, approx_half]

def scaledRegion (s : ℕ) (R : GRegion) : Region :=
  {p | approxPoint s p ∈ R}
@[simp] theorem scalePoint_mem_scaleRegion {s : ℕ} {U : GRegion} {p : GPoint} :
    scalePoint s p ∈ scaledRegion s U ↔ p ∈ U := by
  simp [scaledRegion]
theorem scaledRegion_mono {s : ℕ} {U V : GRegion} (h : U ⊆ V) :
    scaledRegion s U ⊆ scaledRegion s V := fun _ hz => h hz
theorem scaledRegion_mono_iff {s : ℕ} {U V : GRegion} :
  scaledRegion s U ⊆ scaledRegion s V ↔ U ⊆ V := by{
  refine ⟨?_, scaledRegion_mono⟩
  intro h p hp
  rw[← scalePoint_mem_scaleRegion (s := s)] at hp
  apply h at hp
  rw[scalePoint_mem_scaleRegion] at hp
  exact hp
}
theorem scaledRegion_succ_zoom (s : ℕ) (U : GRegion) :
  scaledRegion (s + 1) U.zoom = scaledRegion s U := by{
  ext p
  simp[scaledRegion, GRegion.mem_zoom_iff, approxPoint_half]
}

end RealPlane
