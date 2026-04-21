import Mathlib.Data.Nat.Find

theorem Classical.propDecidable_eq_inferInstance {p : Prop} [Decidable p]
  : propDecidable p = (inferInstance : Decidable p):=by{
    match (inferInstance:Decidable p), propDecidable p with
    | isTrue hp, isTrue hq
    | isFalse hp, isFalse hq => simp
    | isTrue hp, isFalse hq
    | isFalse hp, isTrue hq => contradiction
  }

theorem Classical.propDecidableEq_eq_inferInstance {α : Type _} [DecidableEq α] {a b : α}
  : propDecidable (a = b) = (inferInstance:DecidableEq α) a b:=
  propDecidable_eq_inferInstance
