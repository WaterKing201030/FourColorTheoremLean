import Mathlib.Order.Interval.Set.Basic
import FourColorTheorem.Utils.Int
import FourColorTheorem.Utils.List

open Function
open Relation

namespace GridPlane

open Set

@[ext] structure Ico where
  inf : ℤ
  sup : ℤ

namespace Ico
@[inline] instance instCoeSet : Coe Ico (Set ℤ) where
  coe I := Set.Ico I.inf I.sup
theorem coe_iff (I : Ico) : I = Set.Ico I.inf I.sup := rfl

def inter : Ico → Ico → Ico
| ⟨x0, x1⟩, ⟨y0, y1⟩ => ⟨max x0 y0, min x1 y1⟩
@[inline] instance instInter : Inter Ico := ⟨inter⟩
instance inter.instCommutative
: Std.Commutative (α := Ico) (· ∩ ·) := ⟨by{
  change ∀a b, inter a b = inter b a
  intro ⟨a0, a1⟩ ⟨b0, b1⟩
  simp[inter, max_comm, min_comm]
}⟩
instance inter.instAssociative
: Std.Associative (α := Ico) (· ∩ ·) := ⟨by{
  change ∀a b c, inter (inter a b) c = inter a (inter b c)
  intro ⟨a0, a1⟩ ⟨b0, b1⟩ ⟨c0, c1⟩
  simp[inter, max_assoc, min_assoc]
}⟩
theorem inter_comm (I0 I1 : Ico) : I0 ∩ I1 = I1 ∩ I0 :=
  inter.instCommutative.comm _ _
theorem inter_assoc (I0 I1 I2 : Ico) : (I0 ∩ I1) ∩ I2 = I0 ∩ (I1 ∩ I2) :=
  inter.instAssociative.assoc _ _ _
theorem inter_inf (I0 I1 : Ico) : (I0 ∩ I1).inf = max I0.inf I1.inf := rfl
theorem inter_sup (I0 I1 : Ico) : (I0 ∩ I1).sup = min I0.sup I1.sup := rfl
theorem inter_def (I0 I1 : Ico) : I0 ∩ I1 = ⟨max I0.inf I1.inf, min I0.sup I1.sup⟩ := rfl
theorem inter_coe (I0 I1 : Ico) : ↑(I0 ∩ I1) = (I0 : Set ℤ) ∩ I1 := by{
  ext x
  simp only [Set.mem_Ico, Set.mem_inter_iff, inter_def]
  aesop
}

@[inline] instance : Membership ℤ Ico where
  mem I x := x ∈ (I : Set ℤ)
theorem mem_def (I : Ico) (x : ℤ) : x ∈ I ↔ x ∈ (I : Set ℤ) :=  Iff.rfl
theorem mem_iff (I : Ico) (x : ℤ) : x ∈ I ↔ I.inf ≤ x ∧ x < I.sup := Iff.rfl
theorem mem_inter_iff {I1 I2 : Ico} {x : ℤ}
  : x ∈ I1 ∩ I2 ↔ x ∈ I1 ∧ x ∈ I2 := by{
  rw[mem_def, inter_coe, mem_iff, mem_iff, Set.mem_inter_iff, mem_Ico, mem_Ico]
}

instance : HasSubset Ico where
  Subset I1 I2 := (I1 : Set ℤ) ⊆ (I2 : Set ℤ)
theorem subset_def (I1 I2 : Ico) : I1 ⊆ I2 ↔ (I1 : Set ℤ) ⊆ (I2 : Set ℤ) := Iff.rfl
theorem subset_iff (I1 I2 : Ico) : I1 ⊆ I2 ↔ ∀ x, x ∈ I1 → x ∈ I2 := Iff.rfl
instance subset.instIsTrans : IsTrans Ico (· ⊆ ·) := ⟨by{
  intro a b c
  simp only [subset_def]
  apply Set.Subset.trans
}⟩
instance subset.instRefl : Std.Refl (α := Ico) (· ⊆ ·) := ⟨fun _ => Set.Subset.refl _⟩
theorem subset_trans {I1 I2 I3 : Ico} (h1 : I1 ⊆ I2) (h2 : I2 ⊆ I3) : I1 ⊆ I3 :=
  subset.instIsTrans.trans _ _ _ h1 h2
@[refl] theorem subset_refl (I : Ico) : I ⊆ I :=
  subset.instRefl.refl _

def subico (I1 I2 : Ico) := I1.inf ≥ I2.inf ∧ I1.sup ≤ I2.sup
infix:50 " <+ " => subico
theorem subico_def (I1 I2 : Ico) : I1 <+ I2 ↔ I1.inf ≥ I2.inf ∧ I1.sup ≤ I2.sup := Iff.rfl
theorem subico.subset {I1 I2 : Ico} (h : I1 <+ I2) : I1 ⊆ I2 := by{
  intro x hx
  rw[mem_Ico] at *
  rw[subico_def] at h
  split_ands <;> omega
}
instance subico.instIsTrans : IsTrans Ico (· <+ ·) := ⟨by{
  intro a b c hab hbc
  rw[subico_def] at *
  split_ands <;> omega
}⟩
instance subico.instRefl : Std.Refl (α := Ico) (· <+ ·) := ⟨fun _ => ⟨le_refl _, le_refl _⟩⟩
instance subico.instAntisymm : Std.Antisymm (α := Ico) (· <+ ·) := ⟨by{
  intro I1 I2 h1 h2
  rw[subico_def] at h1 h2
  ext <;> omega
}⟩
theorem subico_trans {I1 I2 I3 : Ico} (h1 : I1 <+ I2) (h2 : I2 <+ I3) : I1 <+ I3 :=
  subico.instIsTrans.trans _ _ _ h1 h2
@[refl] theorem subico_refl (I : Ico) : I <+ I :=
  subico.instRefl.refl _
theorem subico_antisymm {I1 I2 : Ico} (h1 : I1 <+ I2) (h2 : I2 <+ I1) : I1 = I2 :=
  subico.instAntisymm.antisymm _ _ h1 h2

theorem subico_inter_left {I1 I2 : Ico} (h : I1 <+ I2) : I1 ∩ I2 = I1 := by{
  simp only [subico_def] at h
  ext
  · rw[inter_inf, max_eq_left]; omega
  · rw[inter_sup, min_eq_left]; omega
}
theorem subico_inter_right {I1 I2 : Ico} (h : I1 <+ I2) : I2 ∩ I1 = I1 := by{
  rw[inter_comm]
  apply subico_inter_left h
}

def width (I : Ico) : ℕ := (I.sup - I.inf).toNat

def proper (I : Ico) : Prop := I.inf < I.sup
theorem proper_iff_width_pos {I : Ico} : I.proper ↔ I.width > 0 := by{
  rw[proper, width]
  omega
}
theorem proper_iff_ne_empty {I : Ico} : I.proper ↔ (I : Set ℤ) ≠ ∅ := by{
  rw[proper, ne_eq, Set.eq_empty_iff_forall_notMem]
  simp only [mem_Ico, not_and, not_lt, not_forall, not_le]
  simp only [exists_prop]
  constructor
  · intro h; use I.inf
  · intro ⟨_, _, _⟩; omega
}
theorem proper_iff_nonempty {I : Ico} : I.proper ↔ (I : Set ℤ).Nonempty := by{
  rw[nonempty_iff_ne_empty, proper_iff_ne_empty]
}
theorem proper_of_mem {I : Ico} {x : ℤ} (hx : x ∈ I) : I.proper :=
  proper_iff_nonempty.mpr ⟨x, hx⟩
theorem inf_mem_of_proper {I : Ico} (h : I.proper) : I.inf ∈ I := by{
  simpa[mem_iff]
}
theorem sup_not_mem {I : Ico} : I.sup ∉ I := by{
  simp[mem_iff]
}
theorem sup_sub_one_mem_of_proper {I : Ico} (h : I.proper) : I.sup - 1 ∈ I := by{
  rw[proper] at h
  simp[mem_iff]
  omega
}
theorem subico_iff_subset_of_proper {I1 I2 : Ico} (hI1 : I1.proper) :
  I1 <+ I2 ↔ I1 ⊆ I2 := by{
  apply Iff.intro subico.subset
  intro h
  rw[subset_iff] at h
  rw[subico_def]
  rw[proper] at hI1
  have h1 := h I1.inf (inf_mem_of_proper hI1)
  have h2 := h _ (sup_sub_one_mem_of_proper hI1)
  rw[mem_iff] at h1 h2
  omega
}
theorem proper_of_subset {I1 I2 : Ico} (h : I1 ⊆ I2) : I1.proper → I2.proper := by{
  intro h1
  have ⟨x, hx⟩ := proper_iff_nonempty.mp h1
  apply h at hx
  exact proper_of_mem hx
}
theorem proper_of_subico {I1 I2 : Ico} (h : I1 <+ I2) : I1.proper → I2.proper := by{
  apply proper_of_subset
  exact h.subset
}

def enum (I : Ico) : List ℤ := (List.range I.width).map (Int.ofNat · + I.inf)
theorem enum_length {I : Ico} : I.enum.length = I.width := by{simp[enum]}
theorem enum_nodup {I : Ico} : I.enum.Nodup := by{
  rw[enum]
  rw[List.nodup_map_iff]
  · exact List.nodup_range
  apply Injective.comp (g:=(· + I.inf)) ?_ Int.ofNat_injective
  exact fun _ _ => (Int.add_left_inj I.inf).mp
}
theorem mem_enum_iff {I : Ico} {x : ℤ} : x ∈ I.enum ↔ x ∈ I := by{
  rw[enum, List.mem_map, mem_iff]
  simp only [List.mem_range, width]
  simp only [Int.lt_toNat, Int.ofNat_eq_natCast]
  constructor
  · {
    intro ⟨a, ha0, ha1⟩
    constructor
    · simp[←ha1]
    · {
      rw[←ha1]
      apply lt_of_lt_of_le (add_lt_add_left ha0 I.inf)
      rw[sub_add_cancel]
    }
  }
  · {
    intro ⟨h0, h1⟩
    simp only [←eq_sub_iff_add_eq]
    use (x - I.inf).toNat
    simp[h0, h1]
  }
}
theorem subset_iff_enum {R1 R2 : Ico} : R1 ⊆ R2 ↔ R1.enum ⊆ R2.enum := by{
  simp[subset_iff, List.subset_def, mem_enum_iff]
}
theorem proper_iff_ne_nil {I : Ico} : I.proper ↔ I.enum ≠ [] := by{
  rw[enum]
  simp only [Int.ofNat_eq_natCast, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  rw[← ne_eq, Nat.ne_zero_iff_zero_lt]
  rw[proper_iff_width_pos]
}

def zoom (I : Ico) : Ico := ⟨I.inf * 2, I.sup * 2⟩
def inner (I : Ico) : Ico := ⟨I.inf + 1, I.sup - 1⟩
def touch (I : ℤ) : Ico := ⟨I - 1, I + 2⟩
def ltouch (I : ℤ) : Ico := ⟨I - 1, I + 1⟩

theorem inner_subico {I : Ico} : I.inner <+ I := by{
  rw[subico_def]
  simp[inner]
}
theorem inner_subset {I : Ico} : I.inner ⊆ I :=
  I.inner_subico.subset
theorem ltouch_subico_touch {x : ℤ} : ltouch x <+ touch x := by{
  simp[subico_def, touch, ltouch]
}
theorem ltouch_subset_touch {x : ℤ} : ltouch x ⊆ touch x :=
  ltouch_subico_touch.subset
theorem zoom_proper_iff {I : Ico} : I.zoom.proper ↔ I.proper := by{
  simp[zoom, proper]
}
theorem ltouch_proper {x : ℤ} : (ltouch x).proper := by{
  simp[ltouch, proper]; omega
}
theorem touch_proper {x : ℤ} : (touch x).proper := by{
  apply proper_of_subset ltouch_subset_touch ltouch_proper
}
theorem mem_ltouch {x : ℤ} : x ∈ ltouch x := by{
  simp[ltouch, mem_iff]
}
theorem mem_touch {x : ℤ} : x ∈ touch x :=
  ltouch_subset_touch mem_ltouch
theorem zoom_width {I : Ico} : I.zoom.width = 2 * I.width := by{
  simp[zoom, width]
  omega
}
theorem inner_zoom_subico_zoom_inner {r : Ico}
  : r.inner.zoom <+ r.zoom.inner := by{
  rw[subico_def]
  simp[inner, zoom]
  omega
}
theorem inner_zoom_subset_zoom_inner {r : Ico}
  : r.inner.zoom ⊆ r.zoom.inner :=
  inner_zoom_subico_zoom_inner.subset

theorem mem_inner_iff_touch_subset {x : ℤ} {I : Ico} : x ∈ I.inner ↔ touch x ⊆ I := by{
  simp only [inner, mem_iff, touch, subset_iff, tsub_le_iff_right, and_imp]
  constructor
  · intro h y; omega
  intro ih
  have ih1 := ih (x - 1) (by{omega}) (by{omega})
  have ih2 := ih (x + 1) (by{omega}) (by{omega})
  omega
}
theorem mem_inner_iff_touch_subico {x : ℤ} {I : Ico} : x ∈ I.inner ↔ touch x <+ I := by{
  rw[subico_iff_subset_of_proper touch_proper, mem_inner_iff_touch_subset]
}
theorem inner_subset_inner_of_subset {I1 I2 : Ico} (h : I1 ⊆ I2) : I1.inner ⊆ I2.inner := by{
  intro x
  change x ∈ I1.inner → x ∈ I2.inner
  simp only [mem_inner_iff_touch_subset]
  apply swap subset_trans
  exact h
}

theorem width_le_width_of_subset {I1 I2 : Ico} (h : I1 ⊆ I2) : I1.width ≤ I2.width := by{
  rw[← enum_length, ← enum_length]
  apply List.length_le_length_of_nodup_of_subset
  · apply enum_nodup
  · apply enum_nodup
  · rwa[← subset_iff_enum]
}
theorem coe_eq_of_subset_of_width_eq {I1 I2 : Ico} (h1 : I1 ⊆ I2) (h3 : I1.width = I2.width)
: (I1 : Set ℤ) = I2 := by{
  simp only [width] at h3
  simp only [subset_def, Set.subset_def, Set.mem_Ico] at h1
  ext x
  simp only [mem_Ico]
  apply Iff.intro (h1 x)
  intro h2
  have h3' : ((I1.sup - I1.inf).toNat : ℤ) = (I2.sup - I2.inf).toNat := by{
    rw[h3]
  }
  simp only [Int.ofNat_toNat,
    max_eq_left_of_lt
        (by { omega
        } : 0 < I2.sup - I2.inf)] at h3'
  have h3'' : I1.inf < I1.sup := by{
    apply lt_of_sub_pos
    apply lt_of_not_ge
    intro h
    rw[max_eq_right h] at h3'
    omega
  }
  rw[max_eq_left_of_lt (by { omega } : 0 < I1.sup - I1.inf)] at h3'
  have h1' := h1 I1.inf (by{omega})
  have h1'' := h1 (I1.sup - 1) (by{omega})
  omega
}

def extend (I : Ico) (x : ℤ) : Ico :=
  ⟨min I.inf x, max I.sup (x + 1)⟩
theorem mem_extend {I : Ico} {x : ℤ} : x ∈ I.extend x := by{
  match I with | ⟨inf, sup⟩ => {
    simp[Ico.mem_iff, extend]
  }
}
theorem subico_extend {I : Ico} {x : ℤ} : I <+ I.extend x := by{
  simp[extend, subico_def]
}
theorem subset_extend {I : Ico} {x : ℤ} : I ⊆ I.extend x :=
  subico_extend.subset

end Ico

end GridPlane
