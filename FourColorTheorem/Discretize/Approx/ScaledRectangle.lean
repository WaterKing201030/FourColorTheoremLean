import FourColorTheorem.Discretize.Approx.ScaledPoint

/-! 把整长方形放进实平面 -/

namespace RealPlane
open GridPlane

abbrev ScaledRectangle := ℕ × GRectangle

namespace ScaledRectangle

@[inline] instance instCoeRegion : Coe ScaledRectangle Region where
  coe := fun b => {p | approxPoint b.1 p ∈ b.2}
theorem coe_def {b : ScaledRectangle}
: (b : Region) = {p | approxPoint b.1 p ∈ b.2} := rfl
theorem coe_eq {b : ScaledRectangle}
: (b : Region) = scaledRegion b.1 (b.2 : GRegion)
:= by{
  ext p
  simp[scaledRegion, GRectangle.mem_iff]
}

@[inline] instance instMembership : Membership Point ScaledRectangle where
  mem := fun b p => p ∈ (b : Region)
theorem mem_def {p : Point} {b : ScaledRectangle}
: p ∈ b ↔ p ∈ (b : Region) := Iff.rfl

def inner (b : ScaledRectangle) : ScaledRectangle :=
  ⟨b.1, b.2.inner⟩

def refine (b : ScaledRectangle) : ScaledRectangle :=
  ⟨b.1 + 1, b.2.zoom⟩

theorem inner_subset (b : ScaledRectangle) : (inner b : Region) ⊆ (b : Region) :=
  scaledRegion_mono b.2.inner_subset
theorem inner_subset' (b : ScaledRectangle) : ∀p ∈ b.inner, p ∈ b := by{
  intro p; apply inner_subset
}
@[simp] theorem refine_coe (b : ScaledRectangle) :
  (b.refine : Region) = b := by
  ext z
  change approxPoint (b.1 + 1) z ∈ b.2.zoom ↔
    approxPoint b.1 z ∈ b.2
  rw [GRectangle.mem_zoom_iff, approxPoint_half]

theorem inner_subset_refine_inner (b : ScaledRectangle)
: (b.inner : Region) ⊆ b.refine.inner := by
  intro z hz
  have h : approxPoint b.1 z ∈ b.2.inner := hz
  have hzoom : approxPoint (b.1 + 1) z ∈ b.2.inner.zoom := by
    rwa [GRectangle.mem_zoom_iff, approxPoint_half]
  exact GRectangle.inner_zoom_subset_zoom_inner hzoom
theorem inner_subset_refine_inner' (b : ScaledRectangle)
: ∀p ∈ b.inner, p ∈ b.refine.inner := by{
  intro p; apply inner_subset_refine_inner
}
@[simp] theorem refine_proper_iff (b : ScaledRectangle) :
    b.refine.2.proper ↔ b.2.proper := GRectangle.zoom_proper_iff

def refineBy (t : ℕ) (b : ScaledRectangle) : ScaledRectangle := (refine^[t]) b
@[simp] theorem refineBy_fst (t : ℕ) (b : ScaledRectangle) :
    (b.refineBy t).1 = b.1 + t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [refineBy, Function.iterate_succ_apply']
    change (b.refineBy t).1 + 1 = b.1 + (t + 1)
    rw [ih, Nat.add_assoc]

@[simp] theorem refineBy_snd (t : ℕ) (b : ScaledRectangle) :
    (b.refineBy t).2 = GRectangle.zoom^[t] b.2 := by{
    induction t with
    | zero => rfl
    | succ t ih => {
      rw[refineBy, Function.iterate_succ_apply', refine]
      rw[refineBy] at ih
      simp only[ih, ← Function.iterate_succ_apply']
    }
  }

@[simp] theorem refineBy_coe (t : ℕ) (b : ScaledRectangle) :
    (b.refineBy t : Region) = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    ext p
    rw[Set.mem_ofPred, Set.mem_ofPred, refineBy_fst, refineBy_snd]
    rw[Function.iterate_succ_apply', GRectangle.mem_zoom_iff]
    rw[← add_assoc, approxPoint_half]
    rw[refineBy_fst, refineBy_snd, Set.ext_iff] at ih
    simp at ih
    simp[ih]

theorem inset_subset_refineBy_inset (t : ℕ) (b : ScaledRectangle) :
    (b.inner : Region) ⊆ (b.refineBy t).inner := by
  induction t with
  | zero => exact Set.Subset.refl _
  | succ t ih =>
    rw [refineBy, Function.iterate_succ_apply']
    apply ih.trans
    apply inner_subset_refine_inner

@[simp] theorem refineBy_proper_iff (t : ℕ) (b : ScaledRectangle) :
    (b.refineBy t).2.proper ↔ b.2.proper := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [refineBy, Function.iterate_succ_apply', refine_proper_iff]
    exact ih

def touch (s : ℕ) (p : GPoint) : ScaledRectangle :=
  ⟨s, GRectangle.touch p⟩

theorem approx_mem_touch_inner (s : ℕ) (z : Point) :
    z ∈ (touch s (approxPoint s z)).inner := by
  change approxPoint s z ∈ (touch s (approxPoint s z)).2.inner
  simp only [touch, GRectangle.inner, GridPlane.Ico.inner, GRectangle.mem_iff]
  simp only [GRectangle.touch, Ico.touch]
  omega

end ScaledRectangle

theorem Rectangle.exists_rect_approx {R : Rectangle} {z : Point} (hz : z ∈ R) :
    ∃ b : ScaledRectangle, z ∈ b.inner ∧ (b : Region) ⊆ R := by
  obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := (Rectangle.mem_iff R z).mp hz
  let ε := min (z.1 - R.hspan.inf)
    (min (R.hspan.sup - z.1) (min (z.2 - R.vspan.inf) (R.vspan.sup - z.2)))
  have hε : 0 < ε := by
    dsimp [ε]
    simp only [lt_min_iff]
    exact ⟨sub_pos.mpr hx₀, sub_pos.mpr hx₁, sub_pos.mpr hy₀, sub_pos.mpr hy₁⟩
  obtain ⟨s, hs⟩ := exists_precision hε 3
  have hbounds : ε ≤ z.1 - R.hspan.inf ∧ ε ≤ R.hspan.sup - z.1 ∧
      ε ≤ z.2 - R.vspan.inf ∧ ε ≤ R.vspan.sup - z.2 := by
    dsimp [ε]
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have margins : 3 < 2 ^ s * (z.1 - R.hspan.inf) ∧
      3 < 2 ^ s * (R.hspan.sup - z.1) ∧
      3 < 2 ^ s * (z.2 - R.vspan.inf) ∧
      3 < 2 ^ s * (R.vspan.sup - z.2) :=
    ⟨hs.trans_le (mul_le_mul_of_nonneg_left hbounds.1 (by{simp} : (2 : ℝ) ^ s > 0).le),
      hs.trans_le (mul_le_mul_of_nonneg_left hbounds.2.1 (by{simp} : (2 : ℝ) ^ s > 0).le),
      hs.trans_le (mul_le_mul_of_nonneg_left hbounds.2.2.1 (by{simp} : (2 : ℝ) ^ s > 0).le),
      hs.trans_le (mul_le_mul_of_nonneg_left hbounds.2.2.2 (by{simp} : (2 : ℝ) ^ s > 0).le)⟩
  refine ⟨ScaledRectangle.touch s (approxPoint s z), ScaledRectangle.approx_mem_touch_inner s z, ?_⟩
  intro t ht
  rw [Set.mem_ofPred] at ht
  simp only [ScaledRectangle.touch, approxPoint,
  GRectangle.touch, GRectangle.mem_iff, Ico.touch] at ht
  change (R.hspan.inf < t.1 ∧ t.1 < R.hspan.sup) ∧
    (R.vspan.inf < t.2 ∧ t.2 < R.vspan.sup)
  have hxlo := approx_le s z.1
  have hxhi := lt_approx_add_one s z.1
  have hylo := approx_le s z.2
  have hyhi := lt_approx_add_one s z.2
  have htxlo := approx_le s t.1
  have htxhi := lt_approx_add_one s t.1
  have htylo := approx_le s t.2
  have htyhi := lt_approx_add_one s t.2
  have hxmin : (approx s z.1 : ℝ) - 1 ≤ approx s t.1 := by
    exact_mod_cast ht.1.1
  have hxmax : (approx s t.1 : ℝ) < approx s z.1 + 2 := by
    exact_mod_cast ht.1.2
  have hymin : (approx s z.2 : ℝ) - 1 ≤ approx s t.2 := by
    exact_mod_cast ht.2.1
  have hymax : (approx s t.2 : ℝ) < approx s z.2 + 2 := by
    exact_mod_cast ht.2.2
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  constructor
  · constructor <;>
      nlinarith [margins.1, margins.2.1, hxmin, hxmax, htxlo, htxhi]
  · constructor <;>
      nlinarith [margins.2.2.1, margins.2.2.2, hymin, hymax, htylo, htyhi]

theorem Region.exists_open_region_approx {U : Region} (hU : IsOpen U)
    {z : Point} (hz : z ∈ U) :
    ∃ b : ScaledRectangle, z ∈ b.inner ∧ (b : Region) ⊆ U := by
  obtain ⟨R, hzR, hRU⟩ := (Region.isOpen_iff_isOpen' U).mp hU z hz
  obtain ⟨b, hzb, hbR⟩ := Rectangle.exists_rect_approx hzR
  exact ⟨b, hzb, hbR.trans hRU⟩

theorem exists_nhd_rect_subset_ltouch (s : ℕ) (z : Point) :
    ∃ R : Rectangle, z ∈ R ∧
      (R : Region) ⊆ scaledRegion s (GRectangle.ltouch (approxPoint s z)) := by
  let interval (m : ℤ) : RealPlane.Ioo := ⟨scale s (m - 1), scale s (m + 1)⟩
  let R : Rectangle := ⟨interval (approx s z.1), interval (approx s z.2)⟩
  have mem_interval (x : ℝ) : x ∈ interval (approx s x) := by
    change (approx s x - 1 : ℤ) / 2 ^ s < x ∧ x < (approx s x + 1 : ℤ) / 2 ^ s
    rw [div_lt_iff₀ (exp2_pos s), lt_div_iff₀ (exp2_pos s)]
    push_cast
    constructor <;> nlinarith [approx_le s x, lt_approx_add_one s x]
  refine ⟨R, ⟨mem_interval z.1, mem_interval z.2⟩, ?_⟩
  intro t ht
  change (scale s (approx s z.1 - 1) < t.1 ∧ t.1 < scale s (approx s z.1 + 1)) ∧
    (scale s (approx s z.2 - 1) < t.2 ∧ t.2 < scale s (approx s z.2 + 1)) at ht
  change approxPoint s t ∈ GRectangle.ltouch (approxPoint s z)
  simp only [GRectangle.ltouch, GRectangle.mem_iff, GridPlane.Ico.ltouch, approxPoint]
  simp only [approx, Int.le_floor, Int.floor_lt]
  dsimp [scale] at ht
  rw [div_lt_iff₀ (exp2_pos s), lt_div_iff₀ (exp2_pos s)] at ht
  rw [div_lt_iff₀ (exp2_pos s), lt_div_iff₀ (exp2_pos s)] at ht
  push_cast at ht ⊢
  dsimp [approx] at ht
  constructor <;> constructor <;> nlinarith [ht.1.1, ht.1.2, ht.2.1, ht.2.2]

theorem exists_nhd_rect_subset_refined_inner {b : ScaledRectangle} {z : Point}
    (hz : z ∈ b.inner) :
    ∃ R : Rectangle, z ∈ R ∧ (R : Region) ⊆ b.refine.inner := by
  obtain ⟨R, hzR, hR⟩ := exists_nhd_rect_subset_ltouch (b.1 + 1) z
  refine ⟨R, hzR, hR.trans (scaledRegion_mono ?_)⟩
  intro p hp
  have hparent : (approxPoint (b.1 + 1) z).half ∈ b.2.inner := by
    rw [approxPoint_half]
    exact hz
  change p ∈ b.2.zoom.inner
  simp only [GRectangle.ltouch, Set.mem_prod, Set.mem_Ico, GridPlane.Ico.ltouch] at hp
  simp only [GRectangle.inner, GRectangle.zoom, GRectangle.mem_iff, GridPlane.Ico.inner,
    GridPlane.Ico.zoom, GPoint.half] at hparent ⊢
  omega

end RealPlane
