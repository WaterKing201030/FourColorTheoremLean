import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Order.Minimal
import Mathlib.Dynamics.PeriodicPts.Lemmas
import FourColorTheorem.Utils.Chain

open Relation
open Function


variable {α : Type _}

def Relation.fromFun (f : α → α) : α → α → Prop := fun a b => f a = b
theorem Relation.fromFun_iff {f : α → α} {a b : α} : fromFun f a b ↔ f a = b := by rfl
theorem Relation.fromFun_of_fun (f : α → α) (a : α) : fromFun f a (f a) := by rfl
@[inline] instance Relation.fromFun.dec [DecidableEq α] {f : α → α} : DecidableRel (fromFun f) :=
  let inst : DecidableEq α := inferInstance
  fun a b => inst (f a) b

def Relation.union (r1 r2 : α → α → Prop) : α → α → Prop := fun a b => r1 a b ∨ r2 a b
@[inline] instance Relation.instUnion : Union (α → α → Prop) where union := union
theorem Relation.union_iff {r1 r2 : α → α → Prop} {a b : α}
  : (r1 ∪ r2) a b ↔ r1 a b ∨ r2 a b := by rfl
@[inline] instance Relation.instHasSubset : HasSubset (α → α → Prop) where Subset := Subrelation
theorem Relation.subrelation_symbol {r1 r2 : α → α → Prop} : r1 ⊆ r2 ↔ Subrelation r1 r2 := by rfl
theorem Relation.union_left_sub {r1 r2 : α → α → Prop} : r1 ⊆ r1 ∪ r2 :=
  union_iff.mpr ∘ Or.inl
theorem Relation.union_right_sub {r1 r2 : α → α → Prop} : r2 ⊆ r1 ∪ r2 :=
  union_iff.mpr ∘ Or.inr
theorem Relation.union_assoc {r1 r2 r3 : α → α → Prop} : (r1 ∪ r2) ∪ r3 = r1 ∪ (r2 ∪ r3) := by{
  ext a b
  rw[union_iff, union_iff, union_iff, union_iff, or_assoc]
}
theorem Relation.union_comm {r1 r2 : α → α → Prop} : r1 ∪ r2 = r2 ∪ r1 := by{
  ext a b
  rw[union_iff, union_iff, or_comm]
}
@[inline] instance Relation.union.dec {r1 r2 : α → α → Prop} [DecidableRel r1] [DecidableRel r2]
  : DecidableRel (r1 ∪ r2) :=
  fun _ _ => instDecidableOr

theorem Relation.union_Symm_of_Symm {r1 r2 : α → α → Prop} (hr1 : Std.Symm r1) (hr2 : Std.Symm r2) :
  Std.Symm (r1 ∪ r2) := by{
  apply Std.Symm.mk
  intro a b h
  rw[union_iff] at h
  cases h with
  | inl hr1ab => exact union_iff.mpr (Or.inl (hr1.symm _ _ hr1ab))
  | inr hr2ab => exact union_iff.mpr (Or.inr (hr2.symm _ _ hr2ab))
}
