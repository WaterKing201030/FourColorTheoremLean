import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.CompleteField

/- Axiomatic definition of the real numbers -/

class RealStructure (α : Type _) extends
  Field α, ConditionallyCompleteLinearOrder α, IsStrictOrderedRing α

@[inline] noncomputable instance Real.instRealStructure : RealStructure ℝ where
  toField := inferInstance
  toConditionallyCompleteLinearOrder := inferInstance
  add_le_add_left:=Real.instIsStrictOrderedRing.add_le_add_left
  le_of_add_le_add_left:=Real.instIsStrictOrderedRing.le_of_add_le_add_left
  zero_le_one:=Real.instIsStrictOrderedRing.zero_le_one
  mul_lt_mul_of_pos_left:=Real.instIsStrictOrderedRing.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right:=Real.instIsStrictOrderedRing.mul_lt_mul_of_pos_right

/- Proof that the real axiomatization is categorical -/

@[implicit_reducible] def RealStrucutre.uniqueOrderRingHom (α : Type _) (β : Type _)
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] [RealStructure β] :
  Unique (α →+*o β) :=
  ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom α β

@[implicit_reducible] def RealStructure.uniqueOrderRingIso (α : Type _) (β : Type _)
  [RealStructure α] [RealStructure β] : Unique (α ≃+*o β) :=
  ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso α β
