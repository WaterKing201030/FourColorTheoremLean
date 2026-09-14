import Mathlib.Data.Nat.Find

theorem Classical.propDecidable_eq_inferInstance {p : Prop} [Decidable p]
  : propDecidable p = (inferInstance : Decidable p) :=
  Subsingleton.elim _ _

theorem Classical.propDecidableEq_eq_inferInstance {α : Type _} [DecidableEq α] {a b : α}
  : propDecidable (a = b) = (inferInstance:DecidableEq α) a b:=
  propDecidable_eq_inferInstance
