import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Order.Ring.Int

theorem Int.mul_le_zero_of_neg_of_nonneg {a b : ℤ} (ha : a < 0) (hb : b ≥ 0) : a * b ≤ 0 := by{
  have h:=@mul_le_mul_left_of_neg ℤ _ _ _ _ _ _ b 0 a ha
  simp[hb] at h
  simp[h]
}

theorem Int.toNat_mul_right_nonneg {a b : ℤ} (hb : b ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by{
  cases lt_or_ge a 0 with
  | inl ha => {
    simp only [toNat_eq_zero.mpr (le_of_lt ha), zero_mul, toNat_eq_zero]
    exact mul_le_zero_of_neg_of_nonneg ha hb
  }
  | inr ha => {
    exact toNat_mul ha hb
  }
}

theorem Int.toNat_mul_left_nonneg {a b : ℤ} (ha : a ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by{
  rw[mul_comm, Nat.mul_comm]
  apply toNat_mul_right_nonneg
  exact ha
}

theorem Int.emod_ediv_pos {a b : ℤ} (hb : b > 0) : a % b / b = 0 := by{
  apply ediv_eq_zero_of_lt
  · apply emod_nonneg _ (Int.ne_of_gt hb)
  · apply emod_lt_of_pos _ hb
}

theorem Int.one_add_emod_two {a : ℤ} : (1 + a) % 2 = 1 - a % 2 := by{
  cases emod_two_eq a with
  | inl ha | inr ha => simp[ha, add_emod]
}
theorem Int.one_sub_emod_two {a : ℤ} : (1 - a) % 2 = 1 - a % 2 := by{
  cases emod_two_eq a with
  | inl ha | inr ha => simp[ha, sub_emod]
}
theorem Int.add_one_emod_two {a : ℤ} : (a + 1) % 2 = 1 - a % 2 := by{
  cases emod_two_eq a with
  | inl ha | inr ha => simp[ha, add_emod]
}
theorem Int.sub_one_emod_two {a : ℤ} : (a - 1) % 2 = 1 - a % 2 := by{
  cases emod_two_eq a with
  | inl ha | inr ha => simp[ha, sub_emod]
}

theorem Int.add_one_ediv_two_of_mod_zero {a : ℤ} (ha : a % 2 = 0) : (a + 1) / 2 = a / 2 := by{
  rw[Int.add_ediv (by{simp})]
  simp[ha]
}
theorem Int.sub_one_ediv_two_of_mod_one {a : ℤ} (ha : a % 2 = 1) : (a - 1) / 2 = a / 2 := by{
  symm
  nth_rw 1 [←sub_add_cancel a 1]
  apply add_one_ediv_two_of_mod_zero
  rw[sub_one_emod_two]
  simp[ha]
}
theorem Int.add_one_ediv_two_of_mod_one {a : ℤ} (ha : a % 2 = 1) : (a + 1) / 2 = a / 2 + 1 := by{
  rw[Int.add_ediv (by{simp})]
  simp[ha]
}
theorem Int.sub_one_ediv_two_of_mod_zero {a : ℤ} (ha : a % 2 = 0) : (a - 1) / 2 = a / 2 - 1 := by{
  symm
  nth_rw 1 [←sub_add_cancel a 1]
  rw[sub_eq_iff_eq_add]
  apply add_one_ediv_two_of_mod_one
  rw[sub_one_emod_two]
  simp[ha]
}
