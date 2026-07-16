import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Basic

noncomputable def equivNat {α : Sort _} [Infinite α] [Countable α]
: α ≃ ℕ :=
  have h_card : Cardinal.mk α = Cardinal.mk ℕ := by
    simp[Cardinal.mk_eq_aleph0]
  (Cardinal.eq.mp h_card).some
