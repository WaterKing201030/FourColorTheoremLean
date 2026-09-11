import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

namespace RealPlane

open Set

@[ext] structure Ioo where
  inf : ℝ
  sup : ℝ

namespace Ioo
@[inline] instance instCoeSet : Coe Ioo (Set ℝ) where
  coe I := Set.Ioo I.inf I.sup

theorem coe_iff (I : Ioo) : I = Set.Ioo I.inf I.sup := rfl

def inter : Ioo → Ioo → Ioo
| ⟨x0, x1⟩, ⟨y0, y1⟩ => ⟨max x0 y0, min x1 y1⟩
@[inline] instance instInter : Inter Ioo := ⟨inter⟩
instance inter.instCommutative
: Std.Commutative (α := Ioo) (· ∩ ·) := ⟨by{
  change ∀a b, inter a b = inter b a
  intro ⟨a0, a1⟩ ⟨b0, b1⟩
  simp[inter, max_comm, min_comm]
}⟩
instance inter.instAssociative
: Std.Associative (α := Ioo) (· ∩ ·) := ⟨by{
  change ∀a b c, inter (inter a b) c = inter a (inter b c)
  intro ⟨a0, a1⟩ ⟨b0, b1⟩ ⟨c0, c1⟩
  simp[inter, max_assoc, min_assoc]
}⟩
theorem inter_comm (I0 I1 : Ioo) : I0 ∩ I1 = I1 ∩ I0 :=
  inter.instCommutative.comm _ _
theorem inter_assoc (I0 I1 I2 : Ioo) : (I0 ∩ I1) ∩ I2 = I0 ∩ (I1 ∩ I2) :=
  inter.instAssociative.assoc _ _ _
theorem inter_inf (I0 I1 : Ioo) : (I0 ∩ I1).inf = max I0.inf I1.inf := rfl
theorem inter_sup (I0 I1 : Ioo) : (I0 ∩ I1).sup = min I0.sup I1.sup := rfl
theorem inter_def (I0 I1 : Ioo) : I0 ∩ I1 = ⟨max I0.inf I1.inf, min I0.sup I1.sup⟩ := rfl
theorem inter_coe (I0 I1 : Ioo) : ↑(I0 ∩ I1) = (I0 : Set ℝ) ∩ I1 := by{
  ext x
  simp only [Set.mem_Ioo, Set.mem_inter_iff, inter_def, max_lt_iff, lt_min_iff]
  aesop
}

@[inline] instance : Membership ℝ Ioo where
  mem I x := x ∈ (I : Set ℝ)
theorem mem_def (I : Ioo) (x : ℝ) : x ∈ I ↔ x ∈ (I : Set ℝ) :=  Iff.rfl
theorem mem_iff (I : Ioo) (x : ℝ) : x ∈ I ↔ I.inf < x ∧ x < I.sup := Iff.rfl
theorem mem_inter_iff {I1 I2 : Ioo} {x : ℝ}
  : x ∈ I1 ∩ I2 ↔ x ∈ I1 ∧ x ∈ I2 := by{
  rw[mem_def, inter_coe, mem_iff, mem_iff, Set.mem_inter_iff, mem_Ioo, mem_Ioo]
}

instance : HasSubset Ioo where
  Subset I1 I2 := (I1 : Set ℝ) ⊆ (I2 : Set ℝ)
theorem subset_def (I1 I2 : Ioo) : I1 ⊆ I2 ↔ (I1 : Set ℝ) ⊆ (I2 : Set ℝ) := Iff.rfl
theorem subset_iff (I1 I2 : Ioo) : I1 ⊆ I2 ↔ ∀ x, x ∈ I1 → x ∈ I2 := Iff.rfl
instance subset.instIsTrans : IsTrans Ioo (· ⊆ ·) := ⟨by{
  intro a b c
  simp only [subset_def]
  apply Set.Subset.trans
}⟩
instance subset.instRefl : Std.Refl (α := Ioo) (· ⊆ ·) := ⟨fun _ => Set.Subset.refl _⟩
theorem subset_trans {I1 I2 I3 : Ioo} (h1 : I1 ⊆ I2) (h2 : I2 ⊆ I3) : I1 ⊆ I3 :=
  subset.instIsTrans.trans _ _ _ h1 h2
@[refl] theorem subset_refl (I : Ioo) : I ⊆ I :=
  subset.instRefl.refl _

def subioo (I1 I2 : Ioo) := I1.inf ≥ I2.inf ∧ I1.sup ≤ I2.sup
infix:50 " <+ " => subioo
theorem subioo_def (I1 I2 : Ioo) : I1 <+ I2 ↔ I1.inf ≥ I2.inf ∧ I1.sup ≤ I2.sup := Iff.rfl
theorem subioo.subset {I1 I2 : Ioo} (h : I1 <+ I2) : I1 ⊆ I2 := by{
  intro x hx
  rw[mem_Ioo] at *
  rw[subioo_def] at h
  split_ands <;> linarith
}
instance subioo.instIsTrans : IsTrans Ioo (· <+ ·) := ⟨by{
  intro a b c hab hbc
  rw[subioo_def] at *
  split_ands <;> linarith
}⟩
instance subioo.instRefl : Std.Refl (α := Ioo) (· <+ ·) := ⟨fun _ => ⟨le_refl _, le_refl _⟩⟩
instance subioo.instAntisymm : Std.Antisymm (α := Ioo) (· <+ ·) := ⟨by{
  intro I1 I2 h1 h2
  rw[subioo_def] at h1 h2
  ext <;> linarith
}⟩
theorem subioo_trans {I1 I2 I3 : Ioo} (h1 : I1 <+ I2) (h2 : I2 <+ I3) : I1 <+ I3 :=
  subioo.instIsTrans.trans _ _ _ h1 h2
@[refl] theorem subioo_refl (I : Ioo) : I <+ I :=
  subioo.instRefl.refl _
theorem subioo_antisymm {I1 I2 : Ioo} (h1 : I1 <+ I2) (h2 : I2 <+ I1) : I1 = I2 :=
  subioo.instAntisymm.antisymm _ _ h1 h2

theorem subioo_inter_left {I1 I2 : Ioo} (h : I1 <+ I2) : I1 ∩ I2 = I1 := by{
  simp only [subioo_def] at h
  ext
  · rw[inter_inf, max_eq_left]; linarith
  · rw[inter_sup, min_eq_left]; linarith
}
theorem subioo_inter_right {I1 I2 : Ioo} (h : I1 <+ I2) : I2 ∩ I1 = I1 := by{
  rw[inter_comm]
  apply subioo_inter_left h
}

end Ioo

noncomputable def sepIoo (x1 x2 : ℝ) : Ioo :=
  let w := (x1 + x2) / 2
  ⟨if x2 ≤ w then x2 - 1 else w, if x2 ≥ w then x2 + 1 else w⟩
theorem right_mem_sepIoo {x1 x2 : ℝ}
  : x2 ∈ sepIoo x1 x2 := by{
    rcases lt_trichotomy x2 ((x1 + x2) / 2) with h | h | h
    all_goals
    simp[sepIoo, Ioo.mem_iff]
    try simp[le_of_lt h, not_le_of_gt h]
    try simp[h.symm]
    try simp[h]
  }
theorem left_notMem_sepIoo_of_ne {x1 x2 : ℝ}
  (h12 : x1 ≠ x2) : x1 ∉ sepIoo x1 x2 := by{
    rcases lt_trichotomy x2 ((x1 + x2) / 2) with h | h | h
    · {
      simp only [sepIoo, ge_iff_le, Ioo.mem_iff, not_and, not_lt]
      simp only [le_of_lt h, ↓reduceIte, not_le_of_gt h]
      rw[lt_div_iff₀ (by{simp}), mul_two, add_lt_add_iff_right] at h
      rw[div_le_iff₀ (by{simp}), mul_two, add_le_add_iff_left]
      simp[le_of_lt h]
    }
    · {
      rw[eq_div_iff (by{simp}), mul_two, add_right_cancel_iff, Eq.comm] at h
      contradiction
    }
    · {
      simp only [sepIoo, ge_iff_le, Ioo.mem_iff, not_and, not_lt]
      simp only [le_of_lt h, ↓reduceIte, not_le_of_gt h]
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_right] at h
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_left]
      simp[not_lt_of_gt h]
    }
  }
theorem sepIoo_antisymm' {x y t : ℝ} (htxy : t ∈ sepIoo x y)
  (htyx : t ∈ sepIoo y x) : x = y := by{
    apply of_not_not
    intro h
    wlog hxy : x < y with H
    · exact H htyx htxy (Ne.symm h) ((lt_or_gt_of_ne h).resolve_left hxy)
    have hxw : x < (y + x) / 2 := by{
      rw[lt_div_iff₀ (by{simp}), mul_two, add_lt_add_iff_right]
      exact hxy
    }
    have hwy : (x + y) / 2 < y := by{
      rw[div_lt_iff₀ (by{simp}), mul_two, add_lt_add_iff_right]
      exact hxy
    }
    simp only [sepIoo, not_le_of_gt hwy, ↓reduceIte, ge_iff_le, le_of_lt hwy,
      Ioo.mem_iff] at htxy
    simp only [sepIoo, not_le_of_gt hxw, ↓reduceIte, le_of_lt hxw,
      Ioo.mem_iff] at htyx
    rw[add_comm] at htyx
    apply lt_asymm htyx.2 htxy.1
  }

end RealPlane
