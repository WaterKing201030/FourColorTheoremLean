import FourColorTheorem.GridPlane.Matte.Constructors.Zoom
import FourColorTheorem.GridPlane.Matte.Coarse
import FourColorTheorem.GridPlane.Matte.Extension.Coarse

open Function
open Relation

namespace GridPlane
namespace Matte

/-- Weighted count of the missing pixels incident to a grid corner.
The diagonal has weight one; the two side pixels have weight two. -/
def mcorner (m : Matte) (q : GPoint) : ℕ :=
  m'q 2 + (m'q 1 + m'q 3) * 2
where m'q (i : ℕ) := if q - GPoint.ccw^[i] 0 ∉ m then 1 else 0

/-- A corner in the matte with count zero has all four incident pixels in the matte. -/
theorem mcorner0 {m : Matte} {q : GPoint}
  (mq : q ∈ m) (heq : m.mcorner q = 0)
  : ∀p ∈ GRectangle.ltouch q, p ∈ m := by{
  intro ⟨px, py⟩
  unfold mcorner at heq
  have h2 : mcorner.m'q m q 2 = 0 := by omega
  have h1 : mcorner.m'q m q 1 = 0 := by omega
  have h3 : mcorner.m'q m q 3 = 0 := by omega
  unfold mcorner.m'q at h1 h2 h3
  split_ifs at h1 h2 h3 with hn2 hn1 hn3
  intro hp
  rcases q with ⟨qx, qy⟩
  rw[GPoint.zero_def] at hn2 hn1 hn3
  simp only [iterate_succ, comp_apply, GPoint.ccw, sub_zero,
    sub_self, iterate_zero_apply] at hn1 hn2 hn3
  simp only [GRectangle.ltouch, Ico.ltouch, GRectangle.mem_iff, tsub_le_iff_right] at hp
  have hx : px = qx - 1 ∨ px = qx := by omega
  have hy : py = qy - 1 ∨ py = qy := by omega
  simp only [Prod.mk_sub_mk, sub_zero] at hn1 hn2 hn3
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simpa[hx, hy]
}

/-- Express the corner count using its three nontrivial incident pixels. -/
private theorem mcorner_eq (m : Matte) (q : GPoint) :
    m.mcorner q = (if q - (1, 1) ∈ m then 0 else 1) +
      ((if q - (1, 0) ∈ m then 0 else 1) +
        (if q - (0, 1) ∈ m then 0 else 1)) * 2 := by
  simp [mcorner, mcorner.m'q, GPoint.zero_def, GPoint.ccw,
    iterate_succ_apply]

-- The geometric construction below only needs to retain the old pixels and
-- fill one chosen pixel. All corner arithmetic is isolated in this lemma.
private theorem mcorner_lt_of_fill {m xm : Matte} {q d : GPoint}
    (hm : q.half ∈ m) (hpos : 0 < m.mcorner q.half)
    (hparent : ∀ c : GPoint, q.half + (q.mod2 - c).half ∈ m → q - c ∈ xm)
    (hfill : q - d.mod2 ∈ xm)
    (hd : if q.mod2 = 0 then d.mod2 ≠ 0 ∧ q.half - d.mod2 ∉ m
      else d.mod2 = q.mod2.ccw.ccw) :
    xm.mcorner q < m.mcorner q.half := by
  have h10 := hparent (1, 0)
  have h11 := hparent (1, 1)
  have h01 := hparent (0, 1)
  clear hparent
  rw [mcorner_eq] at hpos ⊢
  rw [mcorner_eq]
  rcases q.mod2_cases with hq | hq | hq | hq
  · rcases d.mod2_cases with he | he | he | he
    all_goals
      simp_all only [GPoint.half, sub_eq_add_neg, Prod.neg_mk, Int.reduceNeg,
        Prod.mk_add_mk, neg_zero, add_zero, add_pos_iff, Nat.ofNat_pos,
        mul_pos_iff_of_pos_right, ← GPoint.zero_def, ↓reduceIte, ne_eq,
        not_true_eq_false, and_self, Prod.mk_eq_zero, one_ne_zero, and_true,
        not_false_eq_true, true_and, Prod.fst_zero, zero_add, Int.reduceDiv,
        Prod.snd_zero, Int.zero_ediv, implies_true, ite_mul, zero_mul,
        one_mul, gt_iff_lt, zero_lt_one, true_or, or_true, and_false] <;>
        (split_ifs at * <;> simp_all)
  all_goals
    simp_all only [GPoint.half, sub_eq_add_neg, Prod.neg_mk, Int.reduceNeg,
      Prod.mk_add_mk, neg_zero, add_zero, add_pos_iff, Nat.ofNat_pos,
      mul_pos_iff_of_pos_right, Prod.mk_eq_zero, one_ne_zero, and_true, ↓reduceIte,
      GPoint.ccw, Int.zero_ediv, zero_add, Int.reduceDiv, gt_iff_lt, and_self, and_false]
    split_ifs at * <;> simp_all

/-- Extend the zoomed matte inside the zoomed rectangle, decreasing its corner count.
This is `refine_mcorner` in `matte.v`. -/
theorem zoom_mcorner {m : Matte} {r : GRectangle} {q : GPoint}
    (m_p : q.half ∈ m) (r_p : q.half ∈ r.inner) (mp_gt0 : m.mcorner q.half > 0) :
    ∃ xm : Matte, ((∀ p, p.half ∈ m → p ∈ xm) ∧
      (∀ p ∈ xm, p.half ∈ (r : GRegion) ∪ m)) ∧
      xm.mcorner q < m.mcorner q.half := by
  classical
  -- At remainder zero, fill a missing parent; otherwise fill the opposite pixel.
  obtain ⟨d, hd⟩ : ∃ d : GPoint,
      if q.mod2 = 0 then d.mod2 ≠ 0 ∧ q.half - d.mod2 ∉ m
      else d.mod2 = q.mod2.ccw.ccw := by
    by_cases hq : q.mod2 = 0
    · simp only [hq, if_true]
      have hmissing : q.half - (1, 1) ∉ m ∨ q.half - (1, 0) ∉ m ∨
          q.half - (0, 1) ∉ m := by
        rw [mcorner_eq] at mp_gt0
        by_contra h
        push Not at h
        simp [h.1, h.2.1, h.2.2] at mp_gt0
      rcases hmissing with h | h | h
      · exact ⟨(1, 1), by decide, by simpa [GPoint.mod2] using h⟩
      · exact ⟨(1, 0), by decide, by simpa [GPoint.mod2] using h⟩
      · exact ⟨(0, 1), by decide, by simpa [GPoint.mod2] using h⟩
    · exact ⟨q.mod2.ccw.ccw, by simp [hq, GPoint.mod2_ccw, GPoint.mod2_mod2]⟩
  have hinner : q - d.mod2 ∈ r.zoom.inner := by
    rw [GRectangle.mem_inner_iff_touch_subset]
    intro p hp
    rw [← GPoint.double_half_add_mod2 (d := q)] at hp
    match q, d, p, r with
    | ⟨qx, qy⟩, ⟨dx, dy⟩, ⟨px, py⟩, ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ =>
      simp [GRectangle.zoom, Ico.zoom] at *
      simp [GRectangle.touch, Ico.touch, GPoint.half, GPoint.mod2] at hp
      simp only [GRectangle.inner, GPoint.half, GRectangle.mem_iff, Ico.inner] at r_p
      omega
  have hmeet : ∃ p ∈ r.zoom, p ∈ m.zoom :=
    ⟨q, GRectangle.mem_zoom_iff.mpr (GRectangle.inner_subset r_p), mem_zoom_iff.mpr m_p⟩
  obtain ⟨xm, hext, hbounds, hfill⟩ :=
    canExtendIn_of_coarseIn coarseIn_zoom hmeet _ hinner
  have hretain : ∀ p, p.half ∈ m → p ∈ xm :=
    fun p hp => hext.subset' p (mem_zoom_iff.mpr hp)
  refine ⟨xm, ⟨hretain, ?_⟩, mcorner_lt_of_fill m_p mp_gt0 ?_ hfill hd⟩
  · intro p hp
    have hb := hbounds ((mem_def xm p).mp hp)
    rw [List.mem_append, GRectangle.mem_enum_iff, ← mem_def,
      GRectangle.mem_zoom_iff, mem_zoom_iff] at hb
    exact hb
  · intro c hc
    apply hretain
    rw [← GPoint.double_half_add_mod2 (d := q), add_sub_assoc, GPoint.half_add_double]
    exact hc


end Matte
end GridPlane
