import FourColorTheorem.GridPlane.Defs.Point
import FourColorTheorem.GridPlane.Defs.Ico
import FourColorTheorem.Utils.Nat

/-! 整长方形相关定义 -/

open Function
open Relation

namespace GridPlane

open Set

@[ext] structure GRectangle where
  hspan : Ico
  vspan : Ico
namespace GRectangle
@[inline] instance instCoeRegion : Coe GRectangle GRegion where
  coe R := (R.hspan : Set ℤ) ×ˢ (R.vspan : Set ℤ)
theorem coe_iff (R : GRectangle) : R = (R.hspan : Set ℤ) ×ˢ (R.vspan : Set ℤ) := rfl

def inter (R1 R2 : GRectangle) : GRectangle :=
  ⟨R1.hspan ∩ R2.hspan, R1.vspan ∩ R2.vspan⟩
@[inline] instance instInter : Inter GRectangle := ⟨inter⟩
instance inter.instCommutative
: Std.Commutative (α := GRectangle) (· ∩ ·) := ⟨by{
  change ∀a b, inter a b = inter b a
  intro ⟨a0, a1⟩ ⟨b0, b1⟩
  simp[inter, Ico.inter_comm]
}⟩
instance inter.instAssociative
: Std.Associative (α := GRectangle) (· ∩ ·) := ⟨by{
  change ∀a b c, inter (inter a b) c = inter a (inter b c)
  intro ⟨a0, a1⟩ ⟨b0, b1⟩ ⟨c0, c1⟩
  simp[inter, Ico.inter_assoc]
}⟩
theorem inter_comm (I0 I1 : GRectangle) : I0 ∩ I1 = I1 ∩ I0 :=
  inter.instCommutative.comm _ _
theorem inter_assoc (I0 I1 I2 : GRectangle) : (I0 ∩ I1) ∩ I2 = I0 ∩ (I1 ∩ I2) :=
  inter.instAssociative.assoc _ _ _
theorem inter_hspan (I0 I1 : GRectangle) : (I0 ∩ I1).hspan = I0.hspan ∩ I1.hspan := rfl
theorem inter_vspan (I0 I1 : GRectangle) : (I0 ∩ I1).vspan = I0.vspan ∩ I1.vspan := rfl
theorem inter_def (I0 I1 : GRectangle) : I0 ∩ I1 = ⟨I0.hspan ∩ I1.hspan, I0.vspan ∩ I1.vspan⟩ := rfl
theorem inter_coe (I0 I1 : GRectangle) : ↑(I0 ∩ I1) = (I0 : Set GPoint) ∩ I1 := by{
  ext x
  simp only [mem_prod, mem_Ico, Set.mem_inter_iff, inter_def,
    Ico.inter_def, lt_min_iff]
  aesop
}

@[inline] instance : Membership GPoint GRectangle where
  mem R x := x ∈ (R : Set GPoint)
theorem mem_def (I : GRectangle) x : x ∈ I ↔ x ∈ (I : Set GPoint) := Iff.rfl
theorem mem_iff' (I : GRectangle) x : x ∈ I ↔ x.1 ∈ I.hspan ∧ x.2 ∈ I.vspan := Iff.rfl
theorem mem_iff (I : GRectangle) x : x ∈ I ↔ (I.hspan.inf ≤ x.1 ∧ x.1 < I.hspan.sup)
  ∧ (I.vspan.inf ≤ x.2 ∧ x.2 < I.vspan.sup) := Iff.rfl

theorem mem_inter_iff {I1 I2 : GRectangle} {x : GPoint}
  : x ∈ I1 ∩ I2 ↔ x ∈ I1 ∧ x ∈ I2 := by{
  simp[mem_def, Ico.inter_def, inter_def]
  aesop
}

instance : HasSubset GRectangle where
  Subset I1 I2 := (I1 : Set GPoint) ⊆ (I2 : Set GPoint)
theorem subset_def (I1 I2 : GRectangle) : I1 ⊆ I2 ↔ (I1 : Set GPoint) ⊆ (I2 : Set GPoint) := Iff.rfl
theorem subset_iff (I1 I2 : GRectangle) : I1 ⊆ I2 ↔ ∀ x, x ∈ I1 → x ∈ I2 := Iff.rfl
instance subset.instIsTrans : IsTrans GRectangle (· ⊆ ·) := ⟨by{
  intro a b c
  simp only [subset_def]
  apply Set.Subset.trans
}⟩
instance subset.instRefl : Std.Refl (α := GRectangle) (· ⊆ ·) := ⟨fun _ => Set.Subset.refl _⟩
theorem subset_trans {I1 I2 I3 : GRectangle} (h1 : I1 ⊆ I2) (h2 : I2 ⊆ I3) : I1 ⊆ I3 :=
  subset.instIsTrans.trans _ _ _ h1 h2
theorem subset_refl (I : GRectangle) : I ⊆ I :=
  subset.instRefl.refl _

def subrect (I1 I2 : GRectangle) := I1.hspan <+ I2.hspan ∧ I1.vspan <+ I2.vspan
infix:50 " <+ " => subrect
theorem subrect_def (I1 I2 : GRectangle) : I1 <+ I2 ↔ I1.hspan <+ I2.hspan ∧ I1.vspan <+ I2.vspan
  := Iff.rfl
theorem subrect_iff (I1 I2 : GRectangle) : I1 <+ I2 ↔
  (I1.hspan.inf ≥ I2.hspan.inf ∧ I1.hspan.sup ≤ I2.hspan.sup)
  ∧ (I1.vspan.inf ≥ I2.vspan.inf ∧ I1.vspan.sup ≤ I2.vspan.sup) :=
  Iff.rfl
theorem subrect.subset {I1 I2 : GRectangle} (h : I1 <+ I2) : I1 ⊆ I2 := by{
  rw[subset_iff]
  intro x hx
  rw[mem_iff'] at *
  rw[subrect_def] at h
  apply hx.imp
  · apply h.1.subset
  · apply h.2.subset
}
instance subrect.instIsTrans : IsTrans GRectangle (· <+ ·) := ⟨by{
  intro a b c hab hbc
  rw[subrect_iff] at *
  split_ands <;> linarith
}⟩
instance subrect.instRefl : Std.Refl (α := GRectangle) (· <+ ·) := ⟨by{
  intro ⟨h, v⟩
  rw[subrect_def]
  simp only
  split_ands <;> rfl
}⟩
instance subrect.instAntisymm : Std.Antisymm (α := GRectangle) (· <+ ·) := ⟨by{
  intro R1 R2 h1 h2
  rw[subrect_iff] at h1 h2
  ext <;> linarith
}⟩
theorem subrect_trans {R1 R2 R3 : GRectangle} (h1 : R1 <+ R2) (h2 : R2 <+ R3) : R1 <+ R3 :=
  subrect.instIsTrans.trans _ _ _ h1 h2
theorem subrect_refl (R : GRectangle) : R <+ R :=
  subrect.instRefl.refl _
theorem subrect_antisymm {R1 R2 : GRectangle} (h1 : R1 <+ R2) (h2 : R2 <+ R1) : R1 = R2 :=
  subrect.instAntisymm.antisymm _ _ h1 h2

theorem subrect_inter_left {R1 R2 : GRectangle} (h : R1 <+ R2) : R1 ∩ R2 = R1 := by{
  simp only [subrect_def] at h
  rw[GRectangle.ext_iff]
  rw[inter_hspan, inter_vspan]
  apply h.imp <;> apply Ico.subico_inter_left
}
theorem subrect_inter_right {R1 R2 : GRectangle} (h : R1 <+ R2) : R2 ∩ R1 = R1 := by{
  rw[inter_comm]
  apply subrect_inter_left h
}

def width (R : GRectangle) : ℕ := R.hspan.width
def height (R : GRectangle) : ℕ := R.vspan.width
def area (R : GRectangle) : ℕ := R.width * R.height
def proper (R : GRectangle) : Prop := R.hspan.proper ∧ R.vspan.proper

theorem proper_def {R : GRectangle} : R.proper ↔ R.hspan.proper ∧ R.vspan.proper :=
  Iff.rfl
theorem proper_iff {R : GRectangle} : R.proper ↔
  R.hspan.inf < R.hspan.sup ∧ R.vspan.inf < R.vspan.sup := Iff.rfl
theorem proper_iff_pos {R : GRectangle} : R.proper ↔
  R.width > 0 ∧ R.height > 0 := by{
  rw[proper, width, height]
  apply and_congr <;> rw[Ico.proper_iff_width_pos]
}
theorem proper_iff_area_pos {R : GRectangle} : R.proper ↔ R.area > 0 := by{
  simp only [area, Nat.mul_pos_iff, proper_iff_pos]
}
theorem proper_iff_ne_empty {R : GRectangle} : R.proper ↔ (R : Set GPoint) ≠ ∅ := by{
  rw[ne_eq, Set.eq_empty_iff_forall_notMem]
  simp only [mem_prod, mem_Ico, not_and, not_lt, and_imp, Prod.forall, not_forall,
    not_le]
  simp only [exists_prop, exists_and_left]
  rw[proper_iff]
  constructor
  · {
    intro
    use R.hspan.inf
    split_ands <;> try omega
    use R.vspan.inf
    omega
  }
  · {
    intro ⟨_, _, _, _, _, _⟩
    omega
  }
}
theorem proper_iff_nonempty {I : GRectangle} : I.proper ↔ (I : Set GPoint).Nonempty := by{
  rw[nonempty_iff_ne_empty, proper_iff_ne_empty]
}
theorem proper_of_mem {I : GRectangle} {x : GPoint} (hx : x ∈ I) : I.proper :=
  proper_iff_nonempty.mpr ⟨x, hx⟩
theorem proper_iff_exists_mem {I : GRectangle} : I.proper ↔ ∃x, x ∈ I := by{
  rw[proper_iff_nonempty]
  change Set.Nonempty (I : GRegion) ↔ ∃x, x ∈ (I : GRegion)
  rw[Set.nonempty_def]
}
theorem subrect_iff_subset_of_proper {I1 I2 : GRectangle} (hI1 : I1.proper) :
  I1 <+ I2 ↔ I1 ⊆ I2 := by{
  apply Iff.intro subrect.subset
  intro h
  rw[subrect_iff]
  rw[proper_iff] at hI1
  have h1 := h (by{simp[mem_iff]; omega} : (I1.hspan.inf, I1.vspan.inf) ∈ I1)
  have h2 := h (by{simp[mem_iff]; omega} : (I1.hspan.sup - 1, I1.vspan.sup - 1) ∈ I1)
  simp only [mem_prod, mem_Ico] at h1 h2
  omega
}
theorem proper_of_subset {I1 I2 : GRectangle} (h : I1 ⊆ I2) : I1.proper → I2.proper := by{
  intro h1
  have ⟨x, hx⟩ := proper_iff_nonempty.mp h1
  apply h at hx
  exact proper_of_mem hx
}
theorem proper_of_subrect {I1 I2 : GRectangle} (h : I1 <+ I2) : I1.proper → I2.proper := by{
  apply proper_of_subset
  exact h.subset
}


theorem empty_iff_any_empty {R : GRectangle} : (R : Set GPoint) = ∅
  ↔ (R.hspan : Set ℤ) = ∅ ∨ (R.vspan : Set ℤ) = ∅ :=
  Set.prod_eq_empty_iff

def enum (R : GRectangle) : List GPixel := R.hspan.enum ×ˢ R.vspan.enum
theorem enum_length {R : GRectangle} : R.enum.length = R.area := by{
  simp[enum, area, List.length_product, width, height, Ico.enum_length]
}
theorem enum_nodup {R : GRectangle} : R.enum.Nodup := by{
  rw[enum]
  apply List.Nodup.product
  · exact Ico.enum_nodup
  · exact Ico.enum_nodup
}
theorem mem_enum_iff {R : GRectangle} {p : GPoint} : p ∈ R.enum ↔ p ∈ R := by{
  simp only [enum]
  rw[List.mem_product]
  rw[mem_iff']
  simp[Ico.mem_enum_iff]
}
theorem subset_iff_enum {R1 R2 : GRectangle} : R1 ⊆ R2 ↔ R1.enum ⊆ R2.enum := by{
  simp[subset_iff, List.subset_def, mem_enum_iff]
}
theorem proper_iff_ne_nil {R : GRectangle} : R.proper ↔ R.enum ≠ [] := by{
  rw[enum, List.product_ne_nil_iff, proper_def]
  simp only [Ico.proper_iff_ne_nil]
}

theorem width_eq_sub_of_proper {R : GRectangle} (hR : R.proper) :
  R.width = R.hspan.sup - R.hspan.inf := by{
    have h := (proper_iff_pos.mp hR).left
    rw[width, Ico.width]
    rw[width, Ico.width] at h
    have h' := Int.pos_iff_toNat_pos.mpr h
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact le_of_lt h'
  }
theorem height_eq_sub_of_proper {R : GRectangle} (hR : R.proper) :
  R.height = R.vspan.sup - R.vspan.inf := by{
    have h := (proper_iff_pos.mp hR).right
    rw[height, Ico.width]
    rw[height, Ico.width] at h
    have h' := Int.pos_iff_toNat_pos.mpr h
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact le_of_lt h'
  }
theorem hspan_lt_of_proper {R : GRectangle} (hR : R.proper) :
  R.hspan.inf < R.hspan.sup := by{
    apply Int.lt_of_sub_pos
    rw[← width_eq_sub_of_proper hR]
    simp[proper_iff_pos.mp hR]
  }
theorem vspan_lt_of_proper {R : GRectangle} (hR : R.proper) :
  R.vspan.inf < R.vspan.sup := by{
    apply Int.lt_of_sub_pos
    rw[← height_eq_sub_of_proper hR]
    simp[proper_iff_pos.mp hR]
  }
theorem width_pos_of_proper {R : GRectangle} (hR : R.proper) :
  R.width > 0 := by{
    apply hspan_lt_of_proper at hR
    simpa[width, Ico.width]
  }
theorem height_pos_of_proper {R : GRectangle} (hR : R.proper) :
  R.height > 0 := by{
    apply vspan_lt_of_proper at hR
    simpa[height, Ico.width]
  }

theorem exists_ld_corner_of_proper {R : GRectangle} (hR : R.proper) :
  ∃p0, (∀x y : ℤ, p0 + ⟨x, y⟩ ∈ R ↔ (0 ≤ x ∧ x < R.width) ∧ (0 ≤ y ∧ y < R.height))
    ∧ ∀p ∈ R, ∃x y : ℕ, p = p0 + ⟨x, y⟩ ∧ x < R.width ∧ y < R.height := by{
  rw[proper_iff_pos] at hR
  match R with | ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ => {
    simp only [width, height, Ico.width, ← Int.pos_iff_toNat_pos, Int.sub_pos] at hR
    use ⟨x0, y0⟩
    simp only [Prod.mk_add_mk, mem_iff, le_add_iff_nonneg_right, width, Ico.width, Int.ofNat_toNat,
      lt_sup_iff, height, Int.lt_toNat, and_imp, Prod.forall, Prod.mk.injEq]
    constructor
    · {
      intro x y
      omega
    }
    · {
      intro x y hx0 hx1 hy0 hy1
      use (x - x0).toNat, (y - y0).toNat
      simp[hx0, hy0]
      omega
    }
  }
}

def zoom (I : GRectangle) : GRectangle := ⟨I.hspan.zoom, I.vspan.zoom⟩
def inner (I : GRectangle) : GRectangle := ⟨I.hspan.inner, I.vspan.inner⟩
def touch (I : GPoint) : GRectangle := ⟨Ico.touch I.1, Ico.touch I.2⟩
def ltouch (I : GPoint) : GRectangle := ⟨Ico.ltouch I.1, Ico.ltouch I.2⟩

theorem inner_subrect {I : GRectangle} : I.inner <+ I := by{
  rw[subrect_def]
  exact ⟨Ico.inner_subico, Ico.inner_subico⟩
}
theorem inner_subset {I : GRectangle} : I.inner ⊆ I :=
  I.inner_subrect.subset
theorem ltouch_subrect_touch {x : GPoint} : ltouch x <+ touch x := by{
  simp only [ltouch, touch, subrect_def]
  exact ⟨Ico.ltouch_subico_touch, Ico.ltouch_subico_touch⟩
}
theorem ltouch_subset_touch {x : GPoint} : ltouch x ⊆ touch x :=
  ltouch_subrect_touch.subset
theorem zoom_proper_iff {I : GRectangle} : I.zoom.proper ↔ I.proper := by{
  rw[proper_def, proper_def]
  apply and_congr <;> rw[zoom, Ico.zoom_proper_iff]
}
theorem mem_zoom_iff {x : GPoint} {R : GRectangle} : x ∈ R.zoom ↔ x.half ∈ R := by{
  match x, R with | ⟨xx, xy⟩, ⟨⟨Rhl, Rhu⟩, ⟨Rvl, Rvu⟩⟩ => {
    simp[mem_iff, zoom, Ico.zoom, GPoint.half]
    omega
  }
}
theorem ltouch_proper {x : GPoint} : (ltouch x).proper := by{
  rw[proper_def]
  exact ⟨Ico.ltouch_proper, Ico.ltouch_proper⟩
}
theorem touch_proper {x : GPoint} : (touch x).proper := by{
  apply proper_of_subset ltouch_subset_touch ltouch_proper
}
theorem mem_ltouch {x : GPoint} : x ∈ ltouch x := by{
  simp only [ltouch, mem_iff']
  exact ⟨Ico.mem_ltouch, Ico.mem_ltouch⟩
}
theorem mem_touch {x : GPoint} : x ∈ touch x :=
  ltouch_subset_touch mem_ltouch
theorem zoom_width {I : GRectangle} : I.zoom.width = 2 * I.width := by{
  simp[zoom, width, Ico.zoom_width]
}
theorem zoom_height {I : GRectangle} : I.zoom.height = 2 * I.height := by{
  simp[zoom, height, Ico.zoom_width]
}
theorem zoom_area {I : GRectangle} : I.zoom.area = 4 * I.area := by{
  simp[area, zoom_width, zoom_height]
  ring
}
theorem inner_zoom_subset_zoom_inner {r : GRectangle}
  : r.inner.zoom ⊆ r.zoom.inner := by{
  intro z
  simp only [Set.mem_prod]
  apply And.imp <;> apply Ico.inner_zoom_subset_zoom_inner
}
theorem mem_inner_iff_touch_subrect {x : GPoint} {I : GRectangle}
: x ∈ I.inner ↔ touch x <+ I := by{
  rw[subrect_def, mem_iff']
  apply and_congr <;> simp only[touch, inner, Ico.mem_inner_iff_touch_subico]
}
theorem mem_inner_iff_touch_subset {x : GPoint} {I : GRectangle} : x ∈ I.inner ↔ touch x ⊆ I := by{
  rw[← subrect_iff_subset_of_proper touch_proper, mem_inner_iff_touch_subrect]
}
theorem inner_subset_inner_of_subset {R1 R2 : GRectangle} (h : R1 ⊆ R2)
: R1.inner ⊆ R2.inner := by{
  intro x
  change x ∈ R1.inner → x ∈ R2.inner
  simp only [mem_inner_iff_touch_subset]
  apply swap subset_trans
  exact h
}

theorem area_le_area_of_subset {I1 I2 : GRectangle} (h : I1 ⊆ I2) : I1.area ≤ I2.area := by{
    rw[←enum_length, ←enum_length]
    apply List.length_le_length_of_nodup_of_subset
    · apply enum_nodup
    rw[←subset_iff_enum]
    exact h
  }
theorem coe_eq_of_subset_of_area_eq {I1 I2 : GRectangle} (h1 : I1 ⊆ I2) (h3 : I1.area = I2.area)
: (I1 : Set GPoint) = I2 := by
  have hperm := (enum_nodup (R := I1)).subperm (subset_iff_enum.mp h1)
  have hlength : I1.enum.length = I2.enum.length := by
    simpa only [enum_length] using h3
  ext p
  have hmem := (hperm.perm_of_length_le hlength.ge).mem_iff (a := p)
  exact (mem_enum_iff (R := I1)).symm.trans (hmem.trans (mem_enum_iff (R := I2)))

theorem area_lt_of_missing {s r : GRectangle} (hs : s ⊆ r)
    {q : GPixel} (hqr : q ∈ r) (hqs : q ∉ s) : s.area < r.area := by{
  have hle := GRectangle.area_le_area_of_subset hs
  apply lt_of_le_of_ne hle
  intro heq
  have hcoe := GRectangle.coe_eq_of_subset_of_area_eq hs heq
  apply hqs
  change q ∈ (s : GRegion)
  rw [hcoe]
  exact hqr
}

def extend (R : GRectangle) (p : GPoint) : GRectangle :=
  ⟨R.hspan.extend p.1, R.vspan.extend p.2⟩
theorem mem_extend {R : GRectangle} {p : GPoint} : p ∈ R.extend p := by{
  simp[extend, mem_iff', Ico.mem_extend]
}
theorem subrect_extend {R : GRectangle} {p : GPoint} : R <+ R.extend p := by{
  simp[extend, subrect_def, Ico.subico_extend]
}
theorem subset_extend {R : GRectangle} {p : GPoint} : R ⊆ R.extend p :=
  subrect_extend.subset

end GRectangle

end GridPlane
