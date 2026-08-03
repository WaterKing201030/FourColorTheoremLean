import FourColorTheorem.Utils.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic

open Function
open Relation

inductive FourColor where
| color0 | color1 | color2 | color3
deriving DecidableEq, Fintype

namespace FourColor

abbrev select {α : Sort _} (c0 c1 c2 c3 : α) : FourColor → α
  := fun c => match c with
  | color0 => c0
  | color1 => c1
  | color2 => c2
  | color3 => c3

def toBits : FourColor → Bool × Bool
:= select ⟨false, false⟩ ⟨false, true⟩ ⟨true, false⟩ ⟨true, true⟩

def bit0 (c : FourColor) := c.toBits.2
def bit1 (c : FourColor) := c.toBits.1

def ofBits : Bool → Bool → FourColor
| false, false => color0
| false, true => color1
| true, false => color2
| true, true => color3

def ofBits' (p : Bool × Bool) : FourColor :=
  ofBits p.1 p.2
theorem toBits_leftInverse : LeftInverse toBits ofBits' := by{
  intro ⟨b1, b0⟩
  match b1, b0 with
  | false, false | false, true
  | true, false | true, true => rfl
}
theorem toBits_rightInverse : RightInverse toBits ofBits' := by{
  intro c
  match c with | color0 | color1 | color2 | color3 => rfl
}
theorem bit0_eq_select : bit0 = select false true false true
  := by{
    ext c
    match c with | color0 | color1 | color2 | color3 => rfl
  }
theorem bit1_eq_select : bit1 = select false false true true
  := by{
    ext c
    match c with | color0 | color1 | color2 | color3 => rfl
  }
@[simp] theorem ofBits_eta {c : FourColor} : ofBits c.bit1 c.bit0 = c := by{
  match c with | color0 | color1 | color2 | color3 => simp[bit0_eq_select, bit1_eq_select, ofBits]
}
@[simp] theorem ofBits_bit1 {b1 b0 : Bool} : (ofBits b1 b0).bit1 = b1 := by{
  match b1, b0 with
  | false, false | false, true
  | true, false | true, true => rfl
}
@[simp] theorem ofBits_bit0 {b1 b0 : Bool} : (ofBits b1 b0).bit0 = b0 := by{
  match b1, b0 with
  | false, false | false, true
  | true, false | true, true => rfl
}

theorem ofBits_injective {b : Bool} : Injective (ofBits b) := by{
  intro b'
  match b, b' with
  | false, false | false, true
  | true, false | true, true => simp[ofBits]
}

def add : FourColor → FourColor → FourColor :=
  select id
    (select color1 color0 color3 color2)
    (select color2 color3 color0 color1)
    (select color3 color2 color1 color0)

@[inline] instance instZero : Zero FourColor where
  zero := color0
@[inline] instance instAdd : Add FourColor where
  add := add
@[inline] instance instNeg : Neg FourColor where
  neg := id

@[inline] instance instAddCommGroup : AddCommGroup FourColor where
  zero_add := by{
    change ∀_, add color0 _ = _
    simp[add]
  }
  add_comm := by{
    intro a b
    change add a b = add b a
    cases a <;> cases b <;> rfl
  }
  add_assoc := by{
    intro a b c
    change add (add a b) c = add a (add b c)
    cases a <;> cases b <;> cases c <;> rfl
  }
  neg_add_cancel := by{
    intro a
    change add a a = color0
    cases a <;> rfl
  }
  add_zero := by{
    intro a
    change add a color0 = a
    cases a <;> rfl
  }
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem neg_id {c : FourColor} : -c = c := rfl
theorem sub_eq_add {a b : FourColor} : a - b = a + b := by{
  rw[sub_eq_add_neg, neg_id]
}
theorem add_eq_zero_iff {a b : FourColor} : a + b = 0 ↔ a = b := by{
  rw[← sub_eq_add, sub_eq_zero]
}
theorem add_eq_color0_iff {a b : FourColor} : a + b = color0 ↔ a = b := by{
  change a + b = 0 ↔ _; exact add_eq_zero_iff
}
theorem add_bit0 {a b : FourColor} : (a + b).bit0 = (a.bit0 ^^ b.bit0) := by{
  change (add a b).bit0 = _
  cases a <;> cases b <;> rfl
}
theorem add_bit1 {a b : FourColor} : (a + b).bit1 = (a.bit1 ^^ b.bit1) := by{
  change (add a b).bit1 = _
  cases a <;> cases b <;> rfl
}

end FourColor
