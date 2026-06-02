import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Basic

noncomputable def equivNat {α : Sort _} [Infinite α] [Countable α]
: α ≃ ℕ :=
  -- 1. 使用 Mathlib 中的基数理论：类型的基数由 #α 表示
  -- 我们的目标是证明 #α = #ℕ，从而推导出 α ≃ ℕ
  have h_card : Cardinal.mk α = Cardinal.mk ℕ := by
    -- 2. 利用可数且无限的性质，说明其基数就是 aleph_0 (ℵ₀)
    simp[Cardinal.mk_eq_aleph0]
  -- 3. Mathlib 中定理：如果两个类型的基数相等，则它们之间存在等价关系
  (Cardinal.eq.mp h_card).some
