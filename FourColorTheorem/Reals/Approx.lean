import FourColorTheorem.Reals.Basic
import FourColorTheorem.Reals.Grid.Matte
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import FourColorTheorem.Utils.Nat

open Function
open Relation

def exp2R (s : ℕ) : ℝ := (2 : ℝ) ^ s
noncomputable def scale (s : ℕ) (m : ℤ) : ℝ := m / exp2R s
theorem exp2R_eq_nat_pow (s : ℕ) : exp2R s = (2 ^ s : ℕ) := by
  rw[exp2R]
  exact_mod_cast rfl
def scale' (s : ℕ) (m : ℤ) : ℚ := m / (2 : ℚ) ^ s
theorem scale_eq_scale' (s : ℕ) (m : ℤ) : scale s m = scale' s m := by
  simp [scale, scale', exp2R]
theorem exp2R_zero : exp2R 0 = 1 := by
  simp [exp2R]
theorem exp2R_succ (s : ℕ) : exp2R (s + 1) = 2 * exp2R s := by
  simp [exp2R, pow_succ']
theorem exp2R_pos {s : ℕ} : 0 < exp2R s := by
  simp [exp2R, pow_pos]
theorem exp2R_add (s t : ℕ) : exp2R (s + t) = exp2R s * exp2R t := by
  simp [exp2R, pow_add]
theorem exp2R_le_exp2R {s t : ℕ} (h : s ≤ t) : exp2R s ≤ exp2R t := by
  apply pow_le_pow_right₀ (by{simp}) h
theorem exp2R_lt_exp2R {s t : ℕ} (h : s < t) : exp2R s < exp2R t := by
  apply pow_lt_pow_right₀ (by{simp}) h
theorem one_lt_exp2R_pos {s : ℕ} (h : 0 < s) : 1 < exp2R s := by
  rw[←exp2R_zero]
  apply exp2R_lt_exp2R h
theorem one_lt_exp2R_succ (s : ℕ) : 1 < exp2R (s + 1) := by
  rw[←exp2R_zero]
  apply exp2R_lt_exp2R (Nat.succ_pos s)

def approx (s : ℕ) (x : ℝ) (m : ℤ) : Prop :=
  m ≤ x * exp2R s ∧ x * exp2R s < (m + 1 : ℤ)
theorem approx_iff_scale {s : ℕ} {x : ℝ} {m : ℤ}
: approx s x m ↔ scale s m ≤ x ∧ x < scale s (m + 1) := by
  simp only [approx, scale, Int.cast_add, Int.cast_one]
  rw[div_le_iff₀ exp2R_pos, lt_div_iff₀ exp2R_pos]
theorem approx_scale {s : ℕ} {m : ℤ} : approx s (scale s m) m := by
  simp only [approx, scale, div_mul_cancel₀ _ (ne_of_gt exp2R_pos)]
  exact ⟨le_refl _, by simp⟩
theorem approx_injective' {s : ℕ} {x : ℝ} {m n : ℤ}
(h₁ : approx s x m) (h₂ : approx s x n) : m = n := by
  rw[approx] at h₁ h₂
  rw[←Int.le_floor, ←Int.floor_lt] at h₁ h₂
  omega
theorem approx_exists (s : ℕ) (x : ℝ) : ∃m : ℤ, approx s x m := by
  simp only [approx, ←Int.le_floor, ←Int.floor_lt]
  use ⌊x * exp2R s⌋
  omega
theorem approx_exists_unique (s : ℕ) (x : ℝ) : ∃! m : ℤ, approx s x m := by
  have ⟨m, hm⟩:=approx_exists s x
  refine ⟨m, hm, ?_⟩
  intro n hn
  exact approx_injective' hn hm
theorem scale_inv_achimedean {x : ℝ} (hx : x > 0)
  : ∃s : ℕ, exp2R s * x > 1 := by
  have ⟨n, hn⟩:=Real.instArchimedean.arch 2 hx
  have ⟨m, hm⟩:=Nat.exists_le_pow (a:=2) (by{simp}) n
  use m
  simp only [gt_iff_lt]
  apply lt_of_lt_of_le (by{simp}:(1 : ℝ) < 2)
  rw[exp2R_eq_nat_pow]
  simp only [nsmul_eq_mul] at hn
  have hm':(n:ℝ) ≤  (2 ^ m : ℕ) := by{
    exact_mod_cast hm
  }
  apply le_trans hn
  apply mul_le_mul_of_nonneg_right hm' (le_of_lt hx)
theorem approx_halfz_of_approx_succ {s : ℕ} {x : ℝ} {m : ℤ}
  (h : approx (s + 1) x m) : approx s x (m / 2) := by{
  have ⟨h0, h1⟩:=h
  rw[approx, ←Int.le_floor, ←Int.floor_lt]
  rw[exp2R_succ, mul_left_comm] at h0 h1
  rw[←div_le_iff₀' (by{simp})] at h0
  rw[←lt_div_iff₀' (by{simp})] at h1
  apply Int.floor_le_floor at h0
  have h0':⌊↑m / (2 : ℝ)⌋ = m / 2 := by{
    nth_rw 2 [←Int.floor_intCast (R:=ℝ) m]
    rw[←Int.floor_div_cast_of_nonneg (by{simp})]
    congr
  }
  apply And.intro (h0' ▸ h0)
  have h1': ⌊x * exp2R s⌋ ≤ m / 2 := by{
    have h1':=lt_of_le_of_lt (Int.floor_le _) h1
    rw[←mul_lt_mul_iff_left₀ (a:=2) (by{simp})] at h1'
    rw[div_mul_cancel₀ _ (by{simp})] at h1'
    have h' : (2 : ℝ) = (2 : ℤ) := rfl
    rw[h', ←Int.cast_mul, Int.cast_lt] at h1'
    rw[Int.lt_add_one_iff] at h1'
    apply Int.le_ediv_of_mul_le (by{simp}) h1'
  }
  rw[h0'] at h0
  have h2':=le_antisymm h0 h1'
  simp[←h2']
}
theorem approx_between {s : ℕ} {x1 x2 : ℝ} {m1 m2 : ℤ}
  (h1 : approx (s + 1) x1 m1) (h2 : approx (s + 1) x2 m2)
  (h12 : 1 < exp2R s * (x2 - x1))
  : ∃m, m1 < m ∧ m < m2 := by{
    have ⟨m, hm⟩:=approx_exists s (x2 + x1)
    rw[approx] at hm h1 h2
    rw[exp2R_succ, mul_left_comm, ←mul_assoc, mul_right_comm] at h1 h2
    set s2 := exp2R s with hs2
    set y := (x2 + x1) * s2 with hy
    rw[mul_comm] at h12
    set z := (x2 - x1) * s2 with hz
    have hsyz : 2 * s2 * x1 = y - z := by{
      rw[hy, hz]
      ring
    }
    have hayz : 2 * s2 * x2 = y + z := by{
      rw[hy, hz]
      ring
    }
    rw[hsyz] at h1
    rw[hayz] at h2
    use m
    constructor
    · {
      rw[←Int.add_lt_add_iff_right 1]
      rw[←Int.cast_lt (R:=ℝ)]
      refine lt_of_le_of_lt ?_ hm.right
      rw[le_sub_iff_add_le] at h1
      refine le_trans ?_ h1.left
      simp only [Int.cast_add, Int.cast_one, add_le_add_iff_left]
      apply le_of_lt h12
    }
    · {
      rw[←Int.cast_lt (R:=ℝ)]
      apply lt_of_le_of_lt hm.left
      rw[←lt_sub_iff_add_lt] at h2
      apply lt_of_lt_of_le h2.right
      simp only [Int.cast_add, Int.cast_one,
      tsub_le_iff_right, add_le_add_iff_left]
      apply le_of_lt h12
    }
  }
theorem approx_double_cases {s : ℕ} {x : ℝ} {m : ℤ}
  (h : approx s x m) : approx (s + 1) x (2 * m)
  ∨ approx (s + 1) x (2 * m + 1) := by{
    rw[approx] at h
    rw[←mul_le_mul_iff_right₀ (by{simp} : (0 : ℝ) < 2)] at h
    rw[←mul_lt_mul_iff_right₀ (by{simp} : (0 : ℝ) < 2)] at h
    rw[approx, approx, exp2R_succ, mul_left_comm, add_assoc, ←two_mul,
    ←mul_add]
    simp only [Int.cast_mul, Int.cast_ofNat, h, true_and, and_true]
    apply lt_or_ge
  }
theorem approx_between3 {s : ℕ} {x1 x2 : ℝ} {m1 m2 : ℤ}
  (h1 : approx (s + 1) x1 m1) (h2 : approx (s + 1) x2 m2)
  (h12 : 2 < exp2R s * (x2 - x1))
  : ∃m m' m'', m1 < m ∧ m < m' ∧ m' < m'' ∧ m'' < m2 := by{
    set x3 := (x2 + x1) / 2 with hx3
    have h12':=(one_lt_div₀ (by{simp})).mpr h12
    rw[mul_div_assoc] at h12'
    have hx23 : x2 - x3 = (x2 - x1) / 2:=by{
      simp[hx3]
      ring
    }
    have hx31 : x3 - x1 = (x2 - x1) / 2:=by{
      simp[hx3]
      ring
    }
    have h12'2 := hx23 ▸ h12'
    have h12'1 := hx31 ▸ h12'
    have ⟨m3, hm3⟩:=approx_exists (s + 1) x3
    have ⟨m, hm⟩:=approx_between h1 hm3 h12'1
    have ⟨m', hm'⟩:=approx_between hm3 h2 h12'2
    use m, m3, m'
    simp[hm, hm']
  }

namespace RealPlane
open GridPlane
def approxPoint (s : ℕ) : Point → GPoint → Prop
| ⟨x, y⟩, ⟨mx, my⟩ => approx s x mx ∧ approx s y my
theorem approxPoint_injective' {s : ℕ} {p : Point} {gp1 gp2 : GPoint}
(h₁ : approxPoint s p gp1) (h₂ : approxPoint s p gp2) : gp1 = gp2 := by
  rw[approxPoint] at h₁ h₂
  rw[GPoint.ext_iff]
  exact ⟨approx_injective' h₁.left h₂.left, approx_injective' h₁.right h₂.right⟩
theorem approxPoint_exists (s : ℕ) (p : Point)
: ∃gp : GPoint, approxPoint s p gp := by
  simp only [approxPoint]
  have ⟨mx, hmx⟩:=approx_exists s p.x
  have ⟨my, hmy⟩:=approx_exists s p.y
  use ⟨mx, my⟩
noncomputable def scalePoint (s : ℕ) : GPoint → Point
| ⟨mx, my⟩ => ⟨scale s mx, scale s my⟩
def scalePoint' (s : ℕ) : GPoint → Point
| ⟨mx, my⟩ => ⟨scale' s mx, scale' s my⟩
theorem scalePoint_eq_scalePoint' {s : ℕ} {gp : GPoint}
: scalePoint s gp = scalePoint' s gp := by
  simp only [scalePoint, scalePoint', scale_eq_scale']
theorem approxPoint_scalePoint {s : ℕ} {gp : GPoint}
: approxPoint s (scalePoint s gp) gp := by
  simp[approxPoint, scalePoint, approx_scale]
theorem approxPoint_half_of_approxPoint_succ {s : ℕ} {p : Point} {gp : GPoint}
  (h : approxPoint (s + 1) p gp) : approxPoint s p gp.half := by
  simp only [approxPoint, GPoint.half]
  simp only [approxPoint] at h
  exact ⟨approx_halfz_of_approx_succ h.left, approx_halfz_of_approx_succ h.right⟩

def scaleRegion (s : ℕ) (gr : GRegion) : Region :=
  {p : Point | ∃gp : GPoint, approxPoint s p gp ∧ gp ∈ gr}
theorem scaleRegion_subset_of_subset {s : ℕ} {gr1 gr2 : GRegion}
(h : gr1 ⊆ gr2) : scaleRegion s gr1 ⊆ scaleRegion s gr2 := by
  simp only [scaleRegion, Set.setOf_subset_setOf, forall_exists_index, and_imp]
  intro z p hzp hpgr1
  refine ⟨p, hzp, h hpgr1⟩
theorem scalePoint_mem_scaleRegion_iff {s : ℕ} {gr : GRegion} {p : GPoint}
: scalePoint s p ∈ scaleRegion s gr ↔ p ∈ gr := by
  simp only [scaleRegion, Set.mem_setOf_eq]
  constructor
  · {
    intro ⟨gp, hgp, hgpgr⟩
    have hp := approxPoint_scalePoint (s:=s) (gp:=p)
    have hp':=approxPoint_injective' hp hgp
    exact hp' ▸ hgpgr
  }
  · intro h; use p; simp[approxPoint_scalePoint, h]
theorem scaleRegion_succ_zoom {s : ℕ} {gr : GRegion}
  : scaleRegion (s + 1) gr.zoom = scaleRegion s gr := by{
    rw[scaleRegion, scaleRegion]
    ext x
    simp only [Set.mem_setOf_eq, GRegion.zoom]
    constructor
    · {
      intro ⟨gp, h0, h1⟩
      have h0':=approxPoint_half_of_approxPoint_succ h0
      use gp.half
    }
    · {
      intro ⟨gp, h0, h1⟩
      rw[approxPoint] at h0
      have h0l:=approx_double_cases h0.left
      have h0r:=approx_double_cases h0.right
      simp only [approxPoint]
      cases h0l with
      | inl h0l => cases h0r with
        | inl h0r => {
          use ⟨2 * gp.x, 2*gp.y⟩
          simp[GPoint.half, h0l, h0r, h1]
        }
        | inr h0r => {
          use ⟨2 * gp.x, 2*gp.y + 1⟩
          simp[GPoint.half, h0l, h0r, Int.mul_add_ediv_left, h1]
        }
      | inr h0l => cases h0r with
        | inl h0r => {
          use ⟨2 * gp.x + 1, 2*gp.y⟩
          simp[GPoint.half, h0l, h0r, Int.mul_add_ediv_left, h1]
        }
        | inr h0r => {
          use ⟨2 * gp.x + 1, 2*gp.y + 1⟩
          simp[GPoint.half, h0l, h0r, Int.mul_add_ediv_left, h1]
        }
    }
  }

theorem scaledRegion_inner_subset_scaledRegion_succ_zoom_inner
  {s : ℕ} {r : GRectangle} : scaleRegion s r.inner.toRegion ⊆
  scaleRegion (s + 1) r.zoom.inner.toRegion := by{
    rw[←scaleRegion_succ_zoom, ←GRectangle.zoom_toRegion]
    apply scaleRegion_subset_of_subset
    rw[←GRectangle.subset_iff_region_subset]
    apply GRectangle.inner_zoom_subset_zoom_inner
  }

abbrev ScaleGRect := ℕ × GRectangle
abbrev ScaleMatte := ℕ × Matte

namespace ScaleGRect
def toRegion : ScaleGRect → Region
| ⟨s, r⟩ => scaleRegion s r.toRegion
def refine (s : ℕ := 1) : ScaleGRect → ScaleGRect
| ⟨s', r⟩ => ⟨s' + s, GRectangle.zoom^[s] r⟩
def inner : ScaleGRect → ScaleGRect
| ⟨s, r⟩ => ⟨s, r.inner⟩
def Mem (b : ScaleGRect) (p : Point) : Prop := p ∈ b.toRegion
@[inline] instance instMembership :
  Membership Point ScaleGRect where mem := Mem
theorem mem_iff {R : ScaleGRect} {x : Point}
: x ∈ R ↔ x ∈ R.toRegion := by{rfl}
def subset (R1 R2 : ScaleGRect) : Prop :=
  ∀ {x : Point}, x ∈ R1 → x ∈ R2
@[inline] instance instHasSubset : HasSubset ScaleGRect :=
  ⟨subset⟩
theorem subset_iff {R1 R2 : ScaleGRect}
  : R1 ⊆ R2 ↔ ∀ {x : Point}, x ∈ R1 → x ∈ R2 := by{rfl}
theorem subset_iff_region_subset {R1 R2 : ScaleGRect}
  : R1 ⊆ R2 ↔ R1.toRegion ⊆ R2.toRegion
:= by{
  rw[subset_iff]
  simp[mem_iff, toRegion, Set.subset_def]
}

theorem refine_zero {b : ScaleGRect} : b.refine 0 = b := by{
  simp[refine]
}
theorem refine_succ {s : ℕ} {b : ScaleGRect}
: b.refine (s + 1) = (b.refine s).refine := by{
  simp only [refine, iterate_succ', comp_apply, iterate_zero, id, Prod.mk.injEq]
  ring_nf
  simp
}
theorem refine_eq_iterate {s : ℕ} {b : ScaleGRect}
: b.refine s = refine^[s] b := by{
  induction s with
  | zero => simp[refine_zero]
  | succ s' ih => {
    rw[refine_succ, iterate_succ_apply', ih]
  }
}
theorem refine_add {s s' : ℕ} {b : ScaleGRect}
: b.refine (s + s') = (b.refine s).refine s':= by{
  rw[refine_eq_iterate, add_comm, iterate_add_apply]
  rw[refine_eq_iterate, refine_eq_iterate]
}
theorem refine_toRegion {s : ℕ} {b : ScaleGRect}
 : (b.refine s).toRegion = b.toRegion := by{
    induction s with
    | zero => rw[refine_zero]
    | succ s' ih => {
      match b with
      | ⟨k, r⟩ => {
        rw[refine, toRegion, ←add_assoc, toRegion]
        rw[refine, toRegion, toRegion] at ih
        rw[←ih, iterate_succ_apply', GRectangle.zoom_toRegion]
        rw[scaleRegion_succ_zoom]
      }
    }
  }
theorem mem_refine_iff {s : ℕ} {b : ScaleGRect} {p : Point}
  : p ∈ b.refine s ↔ p ∈ b := by{
    rw[mem_iff, refine_toRegion, ←mem_iff]
  }
theorem refine_inner_subset_inner {s : ℕ} {b : ScaleGRect}
  : b.inner ⊆ (b.refine s).inner := by{
    match b with | ⟨k, r⟩ => {
      rw[inner, refine, inner, subset_iff_region_subset]
      rw[toRegion, toRegion]
      induction s with
      | zero => simp
      | succ s' ih => {
        rw[←add_assoc, iterate_succ_apply']
        apply ih.trans
        apply scaledRegion_inner_subset_scaledRegion_succ_zoom_inner
      }
    }
  }
end ScaleGRect

theorem approx_rect {z : Point} {r : Rectangle}
  (hrz : z ∈ r) : ∃b : ScaleGRect, z ∈ b.inner ∧ b.toRegion ⊆ r.toRegion
  := by{
    match z, r with
    | ⟨x, y⟩, ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ => {
      simp only [Rectangle.mem_iff, Interval.mem_iff] at hrz
      have ⟨s, hs1, hs2, hs3, hs4⟩ :
        ∃s, 1 < exp2R s * (x - x0) ∧ 1 < exp2R s * (x1 - x)
        ∧ 1 < exp2R s * (y - y0) ∧ 1 < exp2R s * (y1 - y) := by{
          have ⟨s1, hs1⟩:=scale_inv_achimedean (sub_pos_of_lt hrz.1.1)
          have ⟨s2, hs2⟩:=scale_inv_achimedean (sub_pos_of_lt hrz.1.2)
          have ⟨s3, hs3⟩:=scale_inv_achimedean (sub_pos_of_lt hrz.2.1)
          have ⟨s4, hs4⟩:=scale_inv_achimedean (sub_pos_of_lt hrz.2.2)
          use max (max s1 s2) (max s3 s4)
          constructor
          · {
            apply lt_of_lt_of_le hs1
            rw[mul_le_mul_iff_left₀ (sub_pos_of_lt hrz.1.1)]
            apply exp2R_le_exp2R
            simp
          }
          constructor
          · {
            apply lt_of_lt_of_le hs2
            rw[mul_le_mul_iff_left₀ (sub_pos_of_lt hrz.1.2)]
            apply exp2R_le_exp2R
            simp
          }
          constructor
          · {
            apply lt_of_lt_of_le hs3
            rw[mul_le_mul_iff_left₀ (sub_pos_of_lt hrz.2.1)]
            apply exp2R_le_exp2R
            simp
          }
          · {
            apply lt_of_lt_of_le hs4
            rw[mul_le_mul_iff_left₀ (sub_pos_of_lt hrz.2.2)]
            apply exp2R_le_exp2R
            simp
          }
        }
      have ⟨⟨mx0, my0⟩, ⟨hmx0, hmy0⟩⟩:=approxPoint_exists (s + 1) ⟨x0, y0⟩
      have ⟨⟨mx1, my1⟩, ⟨hmx1, hmy1⟩⟩:=approxPoint_exists (s + 1) ⟨x1, y1⟩
      have ⟨⟨mx, my⟩, ⟨hmx, hmy⟩⟩:=approxPoint_exists (s + 1) ⟨x, y⟩
      have ⟨xm0, hxm0⟩:=approx_between hmx0 hmx hs1
      have ⟨xm1, hxm1⟩:=approx_between hmx hmx1 hs2
      have ⟨ym0, hym0⟩:=approx_between hmy0 hmy hs3
      have ⟨ym1, hym1⟩:=approx_between hmy hmy1 hs4
      use ⟨s + 1, ⟨⟨xm0, xm1 + 1⟩, ⟨ym0, ym1 + 1⟩⟩⟩
      simp only [ScaleGRect.inner, GRectangle.inner, ScaleGRect.mem_iff, ScaleGRect.toRegion,
        scaleRegion, GRectangle.toRegion, GInterval.mem_iff, Set.mem_setOf_eq, Rectangle.toRegion,
        Set.setOf_subset_setOf, forall_exists_index, and_imp]
      constructor
      · {
        use ⟨mx, my⟩
        constructor
        · exact ⟨hmx, hmy⟩
        · {
          simp only [add_sub_cancel_right]
          omega
        }
      }
      · {
        simp only [Interval.mem_iff, Int.lt_add_one_iff]
        intro a q ⟨⟨h4, h5⟩, ⟨h6, h7⟩⟩ h0 h1 h2 h3
        have ⟨hmx0l, hmx0r⟩:=hmx0
        have ⟨hmx1l, hmx1r⟩:=hmx1
        have ⟨hmy0l, hmy0r⟩:=hmy0
        have ⟨hmy1l, hmy1r⟩:=hmy1
        have ⟨hmxl, hmxr⟩:=hmx
        have ⟨hmyl, hmyr⟩:=hmy
        constructor
        · {
          constructor
          · {
            rw[←mul_lt_mul_iff_left₀ (exp2R_pos (s:=s + 1))]
            apply lt_of_lt_of_le hmx0r
            apply le_trans ?_ h4
            rw[Int.cast_le]
            omega
          }
          · {
            rw[←mul_lt_mul_iff_left₀ (exp2R_pos (s:=s + 1))]
            apply lt_of_lt_of_le h5
            apply le_trans ?_ hmx1l
            rw[Int.cast_le]
            omega
          }
        }
        · {
          constructor
          · {
            rw[←mul_lt_mul_iff_left₀ (exp2R_pos (s:=s + 1))]
            apply lt_of_lt_of_le hmy0r
            apply le_trans ?_ h6
            rw[Int.cast_le]
            omega
          }
          · {
            rw[←mul_lt_mul_iff_left₀ (exp2R_pos (s:=s + 1))]
            apply lt_of_lt_of_le h7
            apply le_trans ?_ hmy1l
            rw[Int.cast_le]
            omega
          }
        }
      }
    }
  }
theorem rect_approx {s : ℕ} {z : Point} {p : GPoint}
  (ha : approxPoint s z p) : ∃r : Rectangle, z ∈ r
  ∧ r.toRegion ⊆ ScaleGRect.toRegion ⟨s, p.gtouch⟩ := by{
    match z, p, ha with
    | ⟨x, y⟩, ⟨mx, my⟩, ⟨⟨lbx, ubx⟩, ⟨lby, uby⟩⟩ => {
      use ⟨⟨(mx - 1) / exp2R s, (mx + 1) / exp2R s⟩,
        ⟨(my - 1) / exp2R s, (my + 1) / exp2R s⟩⟩
      constructor
      · {
        simp only [Rectangle.mem_iff, Interval.mem_iff,
        div_lt_iff₀ exp2R_pos, lt_div_iff₀ exp2R_pos]
        constructor
        · {
          constructor
          · apply lt_of_lt_of_le ?_ lbx; simp
          · simp only [Int.cast_add, Int.cast_one] at ubx; exact ubx
        }
        · {
          constructor
          · apply lt_of_lt_of_le ?_ lby; simp
          · simp only [Int.cast_add, Int.cast_one] at uby; exact uby
        }
      }
      intro ⟨x', y'⟩
      have ⟨px, hpxl, hpxr⟩ := approx_exists s x'
      have ⟨py, hpyl, hpyr⟩ := approx_exists s y'
      simp only [Rectangle.toRegion, Set.mem_setOf, Interval.mem_iff,
      div_lt_iff₀ exp2R_pos, lt_div_iff₀ exp2R_pos, ←Int.cast_one (R:=ℝ),
      ←Int.cast_add]
      intro ⟨⟨hmxl, hmxr⟩, ⟨hmyl, hmyr⟩⟩
      simp only [ScaleGRect.toRegion, scaleRegion, GRectangle.toRegion, GPoint.gtouch,
        GInterval.mem_iff, tsub_le_iff_right, Set.mem_setOf_eq]
      rw[←Int.cast_sub] at hmxl hmyl
      cases lt_or_ge (x' * exp2R s) ↑mx with
      | inl hmxl' => cases lt_or_ge (y' * exp2R s) ↑my with
        | inl hmyl' => {
          use ⟨mx - 1, my - 1⟩
          constructor
          · {
            simp only [approxPoint, approx, le_of_lt hmxl, le_of_lt hmyl,
            sub_add_cancel, hmxl', hmyl', and_true]
          }
          · simp; omega
        }
        | inr hmyr' => {
          use ⟨mx - 1, my⟩
          constructor
          · {
            simp only [approxPoint, approx, le_of_lt hmxl,
            sub_add_cancel, hmxl', hmyr', hmyr, and_true]
          }
          · simp; omega
        }
      | inr hmxr' => cases lt_or_ge (y' * exp2R s) ↑my with
        | inl hmyl' => {
          use ⟨mx, my - 1⟩
          constructor
          · {
            simp only [approxPoint, approx, le_of_lt hmyl,
            sub_add_cancel, hmxr', hmxr, hmyl', and_true]
          }
          · simp; omega
        }
        | inr hmyr' => {
          use ⟨mx, my⟩
          constructor
          · {
            simp only [approxPoint, approx, hmxr', hmxr, hmyr', hmyr, and_true]
          }
          · simp
        }
    }
  }

namespace ScaleMatte
def toRegion : ScaleMatte → Region
| ⟨s, m⟩ => scaleRegion s m.toRegion
def Mem (b : ScaleMatte) (p : Point) : Prop := p ∈ b.toRegion
@[inline] instance instMembership :
  Membership Point ScaleMatte where mem := Mem
theorem mem_iff {R : ScaleMatte} {x : Point}
: x ∈ R ↔ x ∈ R.toRegion := by{rfl}
def subset (R1 R2 : ScaleMatte) : Prop :=
  ∀ {x : Point}, x ∈ R1 → x ∈ R2
@[inline] instance instHasSubset : HasSubset ScaleMatte :=
  ⟨subset⟩
theorem subset_iff {R1 R2 : ScaleMatte}
  : R1 ⊆ R2 ↔ ∀ {x : Point}, x ∈ R1 → x ∈ R2 := by{rfl}
theorem subset_iff_region_subset {R1 R2 : ScaleMatte}
  : R1 ⊆ R2 ↔ R1.toRegion ⊆ R2.toRegion
:= by{
  rw[subset_iff]
  simp[mem_iff, toRegion, Set.subset_def]
}

def refine (s : ℕ := 1) : ScaleMatte → ScaleMatte
| ⟨s', m⟩ => ⟨s' + s, Matte.zoom^[s] m⟩
theorem refine_zero {b : ScaleMatte} : b.refine 0 = b := by{
  simp[refine]
}
theorem refine_succ {s : ℕ} {b : ScaleMatte}
: b.refine (s + 1) = (b.refine s).refine := by{
  simp only [refine, iterate_succ', comp_apply, iterate_zero, id, Prod.mk.injEq]
  ring_nf
  simp
}
theorem refine_eq_iterate {s : ℕ} {b : ScaleMatte}
: b.refine s = refine^[s] b := by{
  induction s with
  | zero => simp[refine_zero]
  | succ s' ih => {
    rw[refine_succ, iterate_succ_apply', ih]
  }
}
theorem refine_add {s s' : ℕ} {b : ScaleMatte}
: b.refine (s + s') = (b.refine s).refine s':= by{
  rw[refine_eq_iterate, add_comm, iterate_add_apply]
  rw[refine_eq_iterate, refine_eq_iterate]
}
theorem refine_toRegion {s : ℕ} {b : ScaleMatte}
 : (b.refine s).toRegion = b.toRegion := by{
    induction s with
    | zero => rw[refine_zero]
    | succ s' ih => {
      match b with
      | ⟨k, r⟩ => {
        rw[refine, toRegion, ←add_assoc, toRegion]
        rw[refine, toRegion, toRegion] at ih
        rw[←ih, iterate_succ_apply', Matte.zoom_toRegion]
        rw[scaleRegion_succ_zoom]
      }
    }
  }
theorem mem_refine_iff {s : ℕ} {b : ScaleMatte} {p : Point}
  : p ∈ b.refine s ↔ p ∈ b := by{
    rw[mem_iff, refine_toRegion, ←mem_iff]
  }
end ScaleMatte

end RealPlane
