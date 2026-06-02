import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Basic

instance Nat.instMulArchimedean : MulArchimedean ℕ where
  arch := by{
    intro x y hy
    use log y x + 1
    apply le_of_lt
    apply Nat.lt_pow_of_log_lt hy
    omega
  }

theorem Nat.exists_lt_pow {a : ℕ} (ha : 1 < a) (n : ℕ)
: ∃ m : ℕ, n < a ^ m := by
  use log a n + 1
  apply Nat.lt_pow_of_log_lt ha
  omega
theorem Nat.exists_le_pow {a : ℕ} (ha : 1 < a) (n : ℕ)
: ∃ m : ℕ, n ≤ a ^ m := by
  have ⟨m, hm⟩:=exists_lt_pow ha n
  exact ⟨m, le_of_lt hm⟩
