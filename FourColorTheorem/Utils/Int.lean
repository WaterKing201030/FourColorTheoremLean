import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Order.Ring.Int

theorem Int.mul_le_zero_of_neg_of_nonneg {a b : ℤ} (ha : a < 0) (hb : b ≥ 0) : a * b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) hb

theorem Int.toNat_mul_right_nonneg {a b : ℤ} (hb : b ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by
  cases lt_or_ge a 0 with
  | inl ha => simp only [toNat_eq_zero.mpr (le_of_lt ha), zero_mul,
    toNat_eq_zero, mul_le_zero_of_neg_of_nonneg ha hb]
  | inr ha => exact toNat_mul ha hb

theorem Int.toNat_mul_left_nonneg {a b : ℤ} (ha : a ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by
  rw [mul_comm, Nat.mul_comm, toNat_mul_right_nonneg ha]

theorem Int.emod_ediv_pos {a b : ℤ} (hb : b > 0) : a % b / b = 0 := by
  apply ediv_eq_zero_of_lt (emod_nonneg _ (Int.ne_of_gt hb)) (emod_lt_of_pos _ hb)

theorem Int.one_add_emod_two {a : ℤ} : (1 + a) % 2 = 1 - a % 2 := by omega
theorem Int.one_sub_emod_two {a : ℤ} : (1 - a) % 2 = 1 - a % 2 := by omega
theorem Int.add_one_emod_two {a : ℤ} : (a + 1) % 2 = 1 - a % 2 := by omega
theorem Int.sub_one_emod_two {a : ℤ} : (a - 1) % 2 = 1 - a % 2 := by omega

theorem Int.add_one_ediv_two_of_mod_zero {a : ℤ} (ha : a % 2 = 0) : (a + 1) / 2 = a / 2
:= by omega
theorem Int.sub_one_ediv_two_of_mod_one {a : ℤ} (ha : a % 2 = 1) : (a - 1) / 2 = a / 2
:= by omega
theorem Int.add_one_ediv_two_of_mod_one {a : ℤ} (ha : a % 2 = 1) : (a + 1) / 2 = a / 2 + 1
:= by omega
theorem Int.sub_one_ediv_two_of_mod_zero {a : ℤ} (ha : a % 2 = 0) : (a - 1) / 2 = a / 2 - 1
:= by omega
