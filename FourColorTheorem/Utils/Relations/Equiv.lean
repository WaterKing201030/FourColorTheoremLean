import FourColorTheorem.Utils.Relations.Basic

open Relation
open Function

variable {α : Type _}

@[inline] instance InvImage.instDecidableRel {β : Sort _} {ra : α → α → Prop} [DecidableRel ra]
  (e : β → α) : DecidableRel (InvImage ra e) :=
  fun a b => (inferInstance:DecidableRel ra) (e a) (e b)
@[inline] instance Equiv.instDecidableRel {β : Sort _} {ra : α → α → Prop} [DecidableRel ra]
  (e : α ≃ β) : DecidableRel (InvImage ra e.symm) := by infer_instance

@[reducible] def Equiv.decidableRel_of_iff {α β : Sort _}
    {ra : α → α → Prop} {rb : β → β → Prop}
    [DecidableRel ra] (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    DecidableRel rb :=
    fun b₁ b₂ =>
    let := (inferInstance:DecidableRel ra) (e.invFun b₁) (e.invFun b₂)
    by{
      rw[eq] at this
      rw[←Equiv.toFun_as_coe, e.right_inv, e.right_inv] at this
      exact this
    }

theorem Equiv.ofBijective_coe {β : Type _} {f : α → β} (hf : Bijective f)
  : ofBijective _ hf = f := rfl

@[inline] def Equivalence.ofSubtype {p : α → Prop} {r : α → α → Prop}
  (e : Equivalence r) : Equivalence (α:={a // p a}) (InvImage r Subtype.val)
  where
    refl:=fun ⟨x, _⟩ => e.refl x
    symm:=e.symm
    trans:=e.trans
@[inline] def Setoid.ofSubtype (s : Setoid α) (p : α → Prop) : Setoid {a // p a} :=
  Setoid.mk _ s.iseqv.ofSubtype
@[inline] instance Setoid.ofSubtype.decidable {p : α → Prop} {s : Setoid α} [DecidableRel s]
  : DecidableRel (s.ofSubtype p):=by{
    unfold ofSubtype
    simp only
    apply InvImage.instDecidableRel
  }
theorem Setoid.ofSubtype_iff {p : α → Prop} {s : Setoid α} {u v : {a // p a}} :
  s.ofSubtype p u v ↔ s u v:=by{
    unfold ofSubtype
    simp[InvImage]
  }

theorem Equivalence.pred_eq_iff {r : α → α → Prop} (e : Equivalence r) {a b : α}
  : (r a = r b) ↔ r a b := by{
    constructor
    · {
      intro h
      rw[h]
      apply e.refl
    }
    · {
      intro h
      ext c
      constructor
      · apply e.trans (e.symm h)
      · apply e.trans h
    }
  }
theorem Equivalence.comm {r : α → α → Prop} (e : Equivalence r) {a b : α}
  : r a b = r b a := by{
    ext
    constructor
    all_goals
    apply e.symm
  }

theorem Setoid.equivalence {r : Setoid α} : Equivalence r := r.iseqv
