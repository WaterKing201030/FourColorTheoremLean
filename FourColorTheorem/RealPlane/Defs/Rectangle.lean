import FourColorTheorem.RealPlane.Defs.Point
import FourColorTheorem.RealPlane.Defs.Ioo
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold

/-! 实平面上的开长方形 -/

namespace RealPlane

open Set

@[ext] structure Rectangle where
  hspan : Ioo
  vspan : Ioo
namespace Rectangle
@[inline] instance instCoeRegion : Coe Rectangle Region where
  coe R := (R.hspan : Set ℝ) ×ˢ (R.vspan : Set ℝ)
theorem coe_iff (R : Rectangle) : R = (R.hspan : Set ℝ) ×ˢ (R.vspan : Set ℝ) := rfl

def inter (R1 R2 : Rectangle) : Rectangle :=
  ⟨R1.hspan ∩ R2.hspan, R1.vspan ∩ R2.vspan⟩
@[inline] instance instInter : Inter Rectangle := ⟨inter⟩
instance inter.instCommutative
: Std.Commutative (α := Rectangle) (· ∩ ·) := ⟨by{
  change ∀a b, inter a b = inter b a
  intro ⟨a0, a1⟩ ⟨b0, b1⟩
  simp[inter, Ioo.inter_comm]
}⟩
instance inter.instAssociative
: Std.Associative (α := Rectangle) (· ∩ ·) := ⟨by{
  change ∀a b c, inter (inter a b) c = inter a (inter b c)
  intro ⟨a0, a1⟩ ⟨b0, b1⟩ ⟨c0, c1⟩
  simp[inter, Ioo.inter_assoc]
}⟩
theorem inter_comm (I0 I1 : Rectangle) : I0 ∩ I1 = I1 ∩ I0 :=
  inter.instCommutative.comm _ _
theorem inter_assoc (I0 I1 I2 : Rectangle) : (I0 ∩ I1) ∩ I2 = I0 ∩ (I1 ∩ I2) :=
  inter.instAssociative.assoc _ _ _
theorem inter_hspan (I0 I1 : Rectangle) : (I0 ∩ I1).hspan = I0.hspan ∩ I1.hspan := rfl
theorem inter_vspan (I0 I1 : Rectangle) : (I0 ∩ I1).vspan = I0.vspan ∩ I1.vspan := rfl
theorem inter_def (I0 I1 : Rectangle) : I0 ∩ I1 = ⟨I0.hspan ∩ I1.hspan, I0.vspan ∩ I1.vspan⟩ := rfl
theorem inter_coe (I0 I1 : Rectangle) : ↑(I0 ∩ I1) = (I0 : Set Point) ∩ I1 := by{
  ext x
  simp only [mem_prod, mem_Ioo, Set.mem_inter_iff, inter_def,
    Ioo.inter_def, max_lt_iff, lt_min_iff]
  aesop
}

@[inline] instance : Membership Point Rectangle where
  mem R x := x ∈ (R : Set Point)
theorem mem_def (I : Rectangle) x : x ∈ I ↔ x ∈ (I : Set Point) := Iff.rfl
theorem mem_iff' (I : Rectangle) x : x ∈ I ↔ x.1 ∈ I.hspan ∧ x.2 ∈ I.vspan := Iff.rfl
theorem mem_iff (I : Rectangle) x : x ∈ I ↔ (I.hspan.inf < x.1 ∧ x.1 < I.hspan.sup)
  ∧ (I.vspan.inf < x.2 ∧ x.2 < I.vspan.sup) := Iff.rfl

theorem mem_inter_iff {I1 I2 : Rectangle} {x : Point}
  : x ∈ I1 ∩ I2 ↔ x ∈ I1 ∧ x ∈ I2 := by{
  simp[mem_def, Ioo.inter_def, inter_def]
  aesop
}

instance : HasSubset Rectangle where
  Subset I1 I2 := (I1 : Set Point) ⊆ (I2 : Set Point)
theorem subset_def (I1 I2 : Rectangle) : I1 ⊆ I2 ↔ (I1 : Set Point) ⊆ (I2 : Set Point) := Iff.rfl
theorem subset_iff (I1 I2 : Rectangle) : I1 ⊆ I2 ↔ ∀ x, x ∈ I1 → x ∈ I2 := Iff.rfl
instance subset.instIsTrans : IsTrans Rectangle (· ⊆ ·) := ⟨by{
  intro a b c
  simp only [subset_def]
  apply Set.Subset.trans
}⟩
instance subset.instRefl : Std.Refl (α := Rectangle) (· ⊆ ·) := ⟨fun _ => Set.Subset.refl _⟩
theorem subset_trans {I1 I2 I3 : Rectangle} (h1 : I1 ⊆ I2) (h2 : I2 ⊆ I3) : I1 ⊆ I3 :=
  subset.instIsTrans.trans _ _ _ h1 h2
theorem subset_refl (I : Rectangle) : I ⊆ I :=
  subset.instRefl.refl _

def subrect (I1 I2 : Rectangle) := I1.hspan <+ I2.hspan ∧ I1.vspan <+ I2.vspan
infix:50 " <+ " => subrect
theorem subrect_def (I1 I2 : Rectangle) : I1 <+ I2 ↔ I1.hspan <+ I2.hspan ∧ I1.vspan <+ I2.vspan
  := Iff.rfl
theorem subrect_iff (I1 I2 : Rectangle) : I1 <+ I2 ↔
  (I1.hspan.inf ≥ I2.hspan.inf ∧ I1.hspan.sup ≤ I2.hspan.sup)
  ∧ (I1.vspan.inf ≥ I2.vspan.inf ∧ I1.vspan.sup ≤ I2.vspan.sup) :=
  Iff.rfl
theorem subrect.subset {I1 I2 : Rectangle} (h : I1 <+ I2) : I1 ⊆ I2 := by{
  rw[subset_iff]
  intro x hx
  rw[mem_iff'] at *
  rw[subrect_def] at h
  apply hx.imp
  · apply h.1.subset
  · apply h.2.subset
}
instance subrect.instIsTrans : IsTrans Rectangle (· <+ ·) := ⟨by{
  intro a b c hab hbc
  rw[subrect_iff] at *
  split_ands <;> linarith
}⟩
instance subrect.instRefl : Std.Refl (α := Rectangle) (· <+ ·) := ⟨by{
  intro ⟨h, v⟩
  rw[subrect_def]
  simp only
  split_ands <;> rfl
}⟩
instance subrect.instAntisymm : Std.Antisymm (α := Rectangle) (· <+ ·) := ⟨by{
  intro R1 R2 h1 h2
  rw[subrect_iff] at h1 h2
  ext <;> linarith
}⟩
theorem subrect_trans {R1 R2 R3 : Rectangle} (h1 : R1 <+ R2) (h2 : R2 <+ R3) : R1 <+ R3 :=
  subrect.instIsTrans.trans _ _ _ h1 h2
@[refl] theorem subrect_refl (R : Rectangle) : R <+ R :=
  subrect.instRefl.refl _
theorem subrect_antisymm {R1 R2 : Rectangle} (h1 : R1 <+ R2) (h2 : R2 <+ R1) : R1 = R2 :=
  subrect.instAntisymm.antisymm _ _ h1 h2

theorem subrect_inter_left {R1 R2 : Rectangle} (h : R1 <+ R2) : R1 ∩ R2 = R1 := by{
  simp only [subrect_def] at h
  rw[Rectangle.ext_iff]
  rw[inter_hspan, inter_vspan]
  apply h.imp <;> apply Ioo.subioo_inter_left
}
theorem subrect_inter_right {R1 R2 : Rectangle} (h : R1 <+ R2) : R2 ∩ R1 = R1 := by{
  rw[inter_comm]
  apply subrect_inter_left h
}
theorem inter_subrect_left {R1 R2 : Rectangle} : R1 ∩ R2 <+ R1 := by{
  match R1, R2 with
  | ⟨⟨R1xl, R1xu⟩, ⟨R1yl, R1yu⟩⟩, ⟨⟨R2xl, R2xu⟩, ⟨R2yl, R2yu⟩⟩ => {
    simp[inter_def, Ioo.inter_def, subrect_iff]
  }
}
theorem inter_subrect_right {R1 R2 : Rectangle} : R1 ∩ R2 <+ R2 := by{
  match R1, R2 with
  | ⟨⟨R1xl, R1xu⟩, ⟨R1yl, R1yu⟩⟩, ⟨⟨R2xl, R2xu⟩, ⟨R2yl, R2yu⟩⟩ => {
    simp[inter_def, Ioo.inter_def, subrect_iff]
  }
}
theorem subrect_inter_of_subrect {R1 R2 R3 : Rectangle}
  (h12 : R1 <+ R2) (h13 : R1 <+ R3) : R1 <+ R2 ∩ R3 := by{
  match R1, R2, R3 with
  | ⟨⟨R1xl, R1xu⟩, ⟨R1yl, R1yu⟩⟩,
    ⟨⟨R2xl, R2xu⟩, ⟨R2yl, R2yu⟩⟩,
    ⟨⟨R3xl, R3xu⟩, ⟨R3yl, R3yu⟩⟩ => {
    simp only [subrect_iff, ge_iff_le, inter_def, Ioo.inter_def, sup_le_iff, le_inf_iff] at *
    split_ands <;> linarith
  }
}

instance : SemilatticeInf Rectangle where
  le := (· <+ ·)
  le_refl := subrect_refl
  le_trans := fun _ _ _ => subrect_trans
  le_antisymm := fun _ _ => subrect_antisymm
  inf := (· ∩ ·)
  inf_le_left := fun _ _ => inter_subrect_left
  inf_le_right := fun _ _ => inter_subrect_right
  le_inf := fun _ _ _ => subrect_inter_of_subrect

def Nonempty (R : Rectangle) : Prop :=
  R.hspan.Nonempty ∧ R.vspan.Nonempty
theorem nonempty_def {R : Rectangle}
: R.Nonempty ↔ R.hspan.Nonempty ∧ R.vspan.Nonempty := by rfl
theorem nonempty_iff {R : Rectangle}
: R.Nonempty ↔ R.hspan.inf < R.hspan.sup ∧ R.vspan.inf < R.vspan.sup := by rfl
theorem nonempty_iff_coe {R : Rectangle}
: R.Nonempty ↔ Set.Nonempty (R : Region) := by{
  simp[nonempty_iff]
}
theorem nonempty_of_mem {I : Rectangle} {x : Point}
  (hx : x ∈ I) : I.Nonempty := by{
  rw[nonempty_iff_coe]
  apply Set.nonempty_of_mem hx
}
theorem nonempty_iff_exists_mem {R : Rectangle}
: R.Nonempty ↔ ∃x, x ∈ R := by{
  simp only [Rectangle.mem_def, Prod.exists]
  simp only [mem_prod, exists_and_left, exists_and_right]
  simp only [nonempty_def, Ioo.nonempty_iff_exists_mem, Ioo.mem_def]
}

def null : Rectangle := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
theorem null_coe : (null : Region) = ∅ := by{
  simp[null]
}
theorem notMem_null {p : Point} : p ∉ null := by{
  simp[null, mem_def]
}
theorem null_not_nonempty : ¬null.Nonempty := by{
  simp[nonempty_iff_coe, null]
}

def iInter' {α : Type _} {s : Finset α} (hs : s.Nonempty) (f : α → Rectangle) : Rectangle :=
  s.inf' hs f
theorem mem_iInter'_iff {α : Type _} {s : Finset α} (hs : s.Nonempty)
  {f : α → Rectangle} {p : Point} :
  p ∈ iInter' hs f ↔ ∀i ∈ s, p ∈ f i := by{
  unfold iInter'
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i s his ih => {
    rcases em' (s.Nonempty) with hs' | hs'
    · {
      simp only [Finset.not_nonempty_iff_eq_empty] at hs'
      simp[hs']
    }
    rw[Finset.inf'_insert hs']
    simp only [Finset.mem_insert, forall_eq_or_imp]
    specialize ih hs'
    rw[← ih]
    change p ∈ f i ∩ _ ↔ _
    simp[mem_inter_iff]
  }
}
theorem iInter'_subrect_of_subrect {α : Type _} {s : Finset α} (hs : s.Nonempty)
  {f : α → Rectangle} {R : Rectangle}
  (hfR : ∀ i ∈ s, f i <+ R) :
  iInter' hs f <+ R:= by{
  unfold iInter'
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i s his ih => {
    rcases em' (s.Nonempty) with hs' | hs'
    · {
      simp only [Finset.not_nonempty_iff_eq_empty] at hs'
      simp[hs'] at hfR
      simp[hs', hfR]
    }
    rw[Finset.inf'_insert hs']
    change f i ∩ _ <+ R
    apply subrect_trans inter_subrect_left
    apply hfR
    simp
  }
}

theorem disjoint_of_hspan_disjoint {R1 R2 : Rectangle}
  (H : ∀ x, x ∈ R1.hspan → x ∉ R2.hspan) :
  ∀p, p ∈ R1 → p ∉ R2 := by{
  intro ⟨x, y⟩ h
  rw[mem_iff'] at h
  specialize H _ h.1
  rw[mem_iff']
  simp[H]
}
theorem disjoint_of_vspan_disjoint {R1 R2 : Rectangle}
  (H : ∀ x, x ∈ R1.vspan → x ∉ R2.vspan) :
  ∀p, p ∈ R1 → p ∉ R2 := by{
  intro ⟨x, y⟩ h
  rw[mem_iff'] at h
  specialize H _ h.2
  rw[mem_iff']
  simp[H]
}
end Rectangle

theorem exists_rect_to_mem (p : Point) :
  ∃R : Rectangle, p ∈ R := by{
  use ⟨⟨p.1 - 1, p.1 + 1⟩, ⟨p.2 - 1, p.2 + 1⟩⟩
  simp[Rectangle.mem_def]
}

noncomputable def sepRectangle (p q : Point) : Rectangle
  := ⟨sepIoo p.1 q.1, sepIoo p.2 q.2⟩
theorem right_mem_sepRectangle {p1 p2 : Point}
  : p2 ∈ sepRectangle p1 p2 := by{
    match p1, p2 with | ⟨x1, y1⟩, ⟨x2, y2⟩ => {
      rw[sepRectangle, Rectangle.mem_iff]
      exact ⟨right_mem_sepIoo, right_mem_sepIoo⟩
    }
  }
theorem left_notMem_sepRectangle_of_ne {p1 p2 : Point}
  (h12 : p1 ≠ p2) : p1 ∉ sepRectangle p1 p2 := by{
    match p1, p2 with | ⟨x1, y1⟩, ⟨x2, y2⟩ => {
      simp only [ne_eq, Prod.mk.injEq, not_and] at h12
      rw[sepRectangle, Rectangle.mem_iff, not_and]
      intro h
      apply left_notMem_sepIoo_of_ne
      apply h12
      apply of_not_not
      intro h'
      have h'':=left_notMem_sepIoo_of_ne h'
      contradiction
    }
  }
theorem sepRectangle_antisymm' {p0 p1 t : Point} (htxy : t ∈ sepRectangle p0 p1)
  (htyx : t ∈ sepRectangle p1 p0) : p0 = p1 := by{
    match t, p0, p1 with
    | ⟨tx, ty⟩, ⟨x0, y0⟩, ⟨x1, y1⟩ => {
      rw[sepRectangle, Rectangle.mem_iff] at htxy htyx
      have h0:=sepIoo_antisymm' htxy.left htyx.left
      have h1:=sepIoo_antisymm' htxy.right htyx.right
      simp only at h0 h1
      rw[h0, h1]
    }
  }

end RealPlane
