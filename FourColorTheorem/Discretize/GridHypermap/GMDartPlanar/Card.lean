import FourColorTheorem.Discretize.GridHypermap.GMInner

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

section
noncomputable def GMLU (hgp : GridMapProper ab0 cm0) :=
  (List.range (hgp.extendBBox.hspan.width)).map
    (fun i => 2 • GPoint.mk (hgp.extendBBox.hspan.lb + Int.ofNat i)
      (hgp.extendBBox.vspan.ub) + ⟨0, 0⟩)
noncomputable def GMLD (hgp : GridMapProper ab0 cm0):=
  (List.range (hgp.extendBBox.hspan.width)).map
    (fun i => 2 • GPoint.mk (hgp.extendBBox.hspan.lb + Int.ofNat i)
      (hgp.extendBBox.vspan.lb - 1) + ⟨1, 1⟩)
noncomputable def GMLR (hgp : GridMapProper ab0 cm0) :=
  (List.range (hgp.extendBBox.vspan.width)).map
    (fun i => 2 • GPoint.mk (hgp.extendBBox.hspan.ub)
      (hgp.extendBBox.vspan.lb + Int.ofNat i) + ⟨0, 1⟩)
noncomputable def GMLL (hgp : GridMapProper ab0 cm0) :=
  (List.range (hgp.extendBBox.vspan.width)).map
    (fun i => 2 • GPoint.mk (hgp.extendBBox.hspan.lb - 1)
      (hgp.extendBBox.vspan.lb + Int.ofNat i) + ⟨1, 0⟩)
theorem lu_len {hgp : GridMapProper ab0 cm0}
  : hgp.GMLU.length =(hgp.extendBBox.hspan.width) := by{simp[GMLU]}
theorem ld_len {hgp : GridMapProper ab0 cm0}
  : hgp.GMLD.length = (hgp.extendBBox.hspan.width) := by{simp[GMLD]}
theorem lr_len {hgp : GridMapProper ab0 cm0}
  : hgp.GMLR.length = (hgp.extendBBox.vspan.width) := by{simp[GMLR]}
theorem ll_len {hgp : GridMapProper ab0 cm0}
  : hgp.GMLL.length = (hgp.extendBBox.vspan.width) := by{simp[GMLL]}
theorem lu_nodup {hgp : GridMapProper ab0 cm0} : hgp.GMLU.Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem ld_nodup {hgp : GridMapProper ab0 cm0} : hgp.GMLD.Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem lr_nodup {hgp : GridMapProper ab0 cm0} : hgp.GMLR.Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem ll_nodup {hgp : GridMapProper ab0 cm0} : hgp.GMLL.Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem mod2_of_lu {hgp : GridMapProper ab0 cm0} {d : GDart}
  (hd : d ∈ hgp.GMLU) : d.mod2 = ⟨0, 0⟩ := by{
  rw[GMLU, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_ld {hgp : GridMapProper ab0 cm0} {d : GDart}
  (hd : d ∈ hgp.GMLD) : d.mod2 = ⟨1, 1⟩ := by{
  rw[GMLD, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_lr {hgp : GridMapProper ab0 cm0} {d : GDart}
  (hd : d ∈ hgp.GMLR) : d.mod2 = ⟨0, 1⟩ := by{
  rw[GMLR, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_ll {hgp : GridMapProper ab0 cm0} {d : GDart}
  (hd : d ∈ hgp.GMLL) : d.mod2 = ⟨1, 0⟩ := by{
  rw[GMLL, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem lu_disjoint_lr {hgp : GridMapProper ab0 cm0}
: (hgp.GMLU).Disjoint (hgp.GMLR) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_lr hb] at hab
  simp at hab
}
theorem lu_disjoint_ld {hgp : GridMapProper ab0 cm0}
: (hgp.GMLU).Disjoint (hgp.GMLD) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_ld hb] at hab
  contradiction
}
theorem lu_disjoint_ll {hgp : GridMapProper ab0 cm0}
: (hgp.GMLU).Disjoint (hgp.GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_ll hb] at hab
  contradiction
}
theorem lr_disjoint_ld {hgp : GridMapProper ab0 cm0}
: (hgp.GMLR).Disjoint (hgp.GMLD) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lr ha, mod2_of_ld hb] at hab
  contradiction
}
theorem lr_disjoint_ll {hgp : GridMapProper ab0 cm0}
: (hgp.GMLR).Disjoint (hgp.GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lr ha, mod2_of_ll hb] at hab
  contradiction
}
theorem ld_disjoint_ll {hgp : GridMapProper ab0 cm0}
: (hgp.GMLD).Disjoint (hgp.GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_ld ha, mod2_of_ll hb] at hab
  contradiction
}
theorem ll_disjoint_ld {hgp : GridMapProper ab0 cm0}
: (hgp.GMLL).Disjoint (hgp.GMLD) := by{
  symm
  apply ld_disjoint_ll
}
theorem ll_disjoint_lr {hgp : GridMapProper ab0 cm0}
: (hgp.GMLL).Disjoint (hgp.GMLR) := by{
  symm
  apply lr_disjoint_ll
}
theorem ld_disjoint_lr {hgp : GridMapProper ab0 cm0}
: (hgp.GMLD).Disjoint (hgp.GMLR) := by{
  symm
  apply lr_disjoint_ld
}
theorem half_y_of_lu {hgp : GridMapProper ab0 cm0} {d : GDart}
(hd : d ∈ hgp.GMLU) : d.half.y = hgp.extendBBox.vspan.ub := by{
  rw[GMLU, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.y_half]
}
theorem half_y_of_ld {hgp : GridMapProper ab0 cm0} {d : GDart}
(hd : d ∈ hgp.GMLD) : d.half.y = hgp.extendBBox.vspan.lb - 1 := by{
  rw[GMLD, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.y_half]
}
theorem half_x_of_lr {hgp : GridMapProper ab0 cm0} {d : GDart}
(hd : d ∈ hgp.GMLR) : d.half.x = hgp.extendBBox.hspan.ub := by{
  rw[GMLR, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.x_half]
}
theorem half_x_of_ll {hgp : GridMapProper ab0 cm0} {d : GDart}
(hd : d ∈ hgp.GMLL) : d.half.x = hgp.extendBBox.hspan.lb - 1 := by{
  rw[GMLL, List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.x_half]
}
theorem half_x_of_lu {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLU)
: hgp.extendBBox.hspan.lb ≤ d.half.x ∧ d.half.x < hgp.extendBBox.hspan.ub := by{
  rw[GMLU, List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.x_half, Int.zero_ediv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.width_eq_sub_of_proper hgp.extendBBox_proper]
  unfold GRectangle.width
  simpa
}
theorem half_x_of_ld {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLD)
: hgp.extendBBox.hspan.lb ≤ d.half.x ∧ d.half.x < hgp.extendBBox.hspan.ub := by{
  rw[GMLD, List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.x_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.width_eq_sub_of_proper hgp.extendBBox_proper]
  unfold GRectangle.width
  simpa
}
theorem half_y_of_lr {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLR)
: hgp.extendBBox.vspan.lb ≤ d.half.y ∧ d.half.y < hgp.extendBBox.vspan.ub := by{
  rw[GMLR, List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.y_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.height_eq_sub_of_proper hgp.extendBBox_proper]
  unfold GRectangle.height
  simpa
}
theorem half_y_of_ll {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLL)
: hgp.extendBBox.vspan.lb ≤ d.half.y ∧ d.half.y < hgp.extendBBox.vspan.ub := by{
  rw[GMLL, List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.y_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.height_eq_sub_of_proper hgp.extendBBox_proper]
  unfold GRectangle.height
  simpa
}
theorem lu_subset_GMGrid {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLU)
: d ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_lu hd
  have hy := half_y_of_lu hd
  rw[edge_half, mod2_of_lu hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx, Int.le_sub_one_iff,
  GRectangle.vspan_lt_of_proper hgp.extendBBox_proper]
}
theorem ld_subset_GMGrid {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLD)
: d ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_ld hd
  have hy := half_y_of_ld hd
  rw[edge_half, mod2_of_ld hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx,
  GRectangle.vspan_lt_of_proper hgp.extendBBox_proper]
}
theorem lr_subset_GMGrid {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLR)
: d ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_lr hd
  have hy := half_y_of_lr hd
  rw[edge_half, mod2_of_lr hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx, Int.le_sub_one_iff,
  GRectangle.hspan_lt_of_proper hgp.extendBBox_proper]
}
theorem ll_subset_GMGrid {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLL)
: d ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_ll hd
  have hy := half_y_of_ll hd
  rw[edge_half, mod2_of_ll hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx,
  GRectangle.hspan_lt_of_proper hgp.extendBBox_proper]
}
theorem lu_disjoint_inner {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLU)
: ⟨d, lu_subset_GMGrid hd⟩ ∉ hgp.GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_y_of_lu hd]
}
theorem ld_disjoint_inner {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLD)
: ⟨d, ld_subset_GMGrid hd⟩ ∉ hgp.GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_y_of_ld hd]
}
theorem lr_disjoint_inner {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLR)
: ⟨d, lr_subset_GMGrid hd⟩ ∉ hgp.GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_x_of_lr hd]
}
theorem ll_disjoint_inner {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMLL)
: ⟨d, ll_subset_GMGrid hd⟩ ∉ hgp.GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_x_of_ll hd]
}
noncomputable def GMOuter (hgp : GridMapProper ab0 cm0)
:= hgp.GMLU ++ hgp.GMLL ++ hgp.GMLD ++ hgp.GMLR
theorem outer_nodup {hgp : GridMapProper ab0 cm0} : hgp.GMOuter.Nodup := by{
  unfold GMOuter
  simp only [List.nodup_append', List.disjoint_append_left]
  simp only [ll_nodup, lr_nodup, lu_nodup, ld_nodup, true_and]
  simp[lu_disjoint_lr, lu_disjoint_ld, lu_disjoint_ll,
    ll_disjoint_ld, ll_disjoint_lr, ld_disjoint_lr]
}
theorem outer_length {hgp : GridMapProper ab0 cm0}
: hgp.GMOuter.length = ((hgp.extendBBox).width + (hgp.extendBBox).height) * 2 := by{
  unfold GMOuter
  unfold GRectangle.width GRectangle.height
  simp[lu_len, lr_len, ld_len, ll_len]
  ring
}
theorem outer_subset_GMGrid {hgp : GridMapProper ab0 cm0} {d : GDart} (hd : d ∈ hgp.GMOuter)
: d ∈ hgp.GMGrid := by{
  simp only [GMOuter, List.mem_append] at hd
  rcases hd with ((hd | hd) | hd) | hd
  · exact lu_subset_GMGrid hd
  · exact ll_subset_GMGrid hd
  · exact ld_subset_GMGrid hd
  · exact lr_subset_GMGrid hd
}
theorem outer_disjoint_GMInner {hgp : GridMapProper ab0 cm0} {d : GDart}
(hd : d ∈ hgp.GMOuter)
  : ⟨d, outer_subset_GMGrid hd⟩ ∉ hgp.GMInner := by{
    simp only [GMOuter, List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact lu_disjoint_inner hd
    · exact ll_disjoint_inner hd
    · exact ld_disjoint_inner hd
    · exact lr_disjoint_inner hd
  }
theorem not_inner_in_outer {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
(hu : u ∉ hgp.GMInner) : u.val ∈ hgp.GMOuter := by{
  match u with | ⟨d, hd⟩ => {
    rw[mem_GMGrid_iff] at hd
    rw[mem_GMInner_iff] at hu
    simp only at hu
    apply (Or.resolve_left · hu) at hd
    simp only
    simp only [GMOuter, List.mem_append]
    simp only [GRectangle.mem_iff, GInterval.mem_iff, edge_half] at hd hu
    simp only [not_and, not_lt, and_imp] at hu
    rw[← GPoint.double_half_add_mod2 (d:=d)]
    rcases GPoint.mod2_cases (p:=d) with hdm | hdm | hdm | hdm
    · {
      left; left; left
      simp only [GPoint.ccw, hdm, sub_zero, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right, Int.le_sub_one_iff, Int.sub_one_lt_iff] at hd
      simp only [hd, le_of_lt, forall_const] at hu
      rw[GMLU, List.mem_map]
      have hu' := le_antisymm (by{simp[hd]}) hu
      use (d.half.x - hgp.extendBBox.hspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.left.left)]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.left.left), hdm, hu']
      simp[GRectangle.width_eta]
      simp[GRectangle.width_eq_sub_of_proper hgp.extendBBox_proper, hd]
    }
    · {
      left; left; right
      simp only [GPoint.ccw, hdm, sub_zero, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right] at hd
      have hd' := lt_trans (a:=d.half.x) (by{simp}) hd.left.right
      simp only [hd, not_le_of_gt hd.right.right, imp_false, not_true_eq_false, not_lt,
        not_le_of_gt hd', not_le] at hu
      rw[GMLL, List.mem_map]
      have hu' : d.half.x = hgp.extendBBox.hspan.lb - 1 := by{
        rw[Int.le_add_one_iff] at hd
        simp only [not_le_of_gt hu, false_or] at hd
        rw[hd.left.left]
        ring
      }
      use (d.half.y - hgp.extendBBox.vspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.right.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.right.left)]
      simp[GRectangle.height_eta]
      simp[GRectangle.height_eq_sub_of_proper hgp.extendBBox_proper, hd]
    }
    · {
      left; right
      simp only [GPoint.ccw, hdm, sub_self, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right] at hd
      have hd' := lt_trans (a:=d.half.y) (by{simp}) hd.right.right
      simp only [hd, not_le_of_gt hd', imp_false, not_le, forall_const] at hu
      rw[GMLD, List.mem_map]
      have hu' : d.half.y = hgp.extendBBox.vspan.lb - 1 := by{
        rw[Int.le_add_one_iff] at hd
        simp only [not_le_of_gt hu, false_or] at hd
        rw[hd.right.left]
        ring
      }
      use (d.half.x - hgp.extendBBox.hspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.left.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.left.left)]
      simp[GRectangle.width_eta]
      simp[GRectangle.width_eq_sub_of_proper hgp.extendBBox_proper, hd]
    }
    · {
      right
      simp only [GPoint.ccw, hdm, sub_self, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right, Int.le_sub_one_iff, Int.sub_one_lt_iff] at hd
      simp only [hd, le_of_lt, not_le_of_gt hd.right.right, imp_false, not_true_eq_false, not_lt,
        forall_const] at hu
      rw[GMLR, List.mem_map]
      have hu' := le_antisymm (by{simp[hd]}) hu
      use (d.half.y - hgp.extendBBox.vspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.right.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.right.left)]
      simp[GRectangle.height_eta]
      simp[GRectangle.height_eq_sub_of_proper hgp.extendBBox_proper, hd]
    }
  }
}

theorem GMOuterDart_card {hgp : GridMapProper ab0 cm0}
: Fintype.card hgp.GMOuterDart = (hgp.extendBBox.width + hgp.extendBBox.height) * 2 := by{
  rw[← outer_length, ← List.Subtype.fintype_card_eq_length_of_nodup outer_nodup]
  apply Fintype.card_congr
  let f : hgp.GMOuterDart → { x // x ∈ hgp.GMOuter } := fun ⟨⟨d, hd⟩, hu⟩ =>
    ⟨d, not_inner_in_outer hu⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro u1 u2 hu12
    match u1, u2 with | ⟨⟨d1, hd1⟩, hu1⟩, ⟨⟨d2, hd2⟩, hu2⟩ => {
      simp[f] at hu12
      simp[hu12]
    }
  }
  · {
    intro ⟨d, hd⟩
    use ⟨_, outer_disjoint_GMInner hd⟩
  }
}

theorem GMDart_card {hgp : GridMapProper ab0 cm0}
: Fintype.card hgp.GMDart = (hgp.extendBBox).area * 4
+ ((hgp.extendBBox).width + (hgp.extendBBox).height) * 2
:= by{
  rw[← Fintype.ofEquiv_card hgp.GMDart_equiv_GMInnerDart_sum_GMOuterDart]
  have h:=@Fintype.card_sum hgp.GMInnerDart hgp.GMOuterDart
    _ _
  rw[GMInnerDart_card, GMOuterDart_card] at h
  rw[← h]
  apply congrArg
  apply Subsingleton.elim
}
end
end GridMapProper
end GridPlane
