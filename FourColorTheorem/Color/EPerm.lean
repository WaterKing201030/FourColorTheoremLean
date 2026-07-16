import FourColorTheorem.Color.FourColor

open Function
open Relation

namespace FourColor

inductive EPerm where
| eperm123 | eperm132 | eperm213 | eperm231 | eperm312 | eperm321
deriving DecidableEq, Fintype
abbrev EPerm.select {α : Sort _} (e123 e132 e213 e231 e312 e321 : α) : EPerm → α
  := fun e => match e with
  | eperm123 => e123
  | eperm132 => e132
  | eperm213 => e213
  | eperm231 => e231
  | eperm312 => e312
  | eperm321 => e321
abbrev EPerm.toFun : EPerm → FourColor → FourColor :=
  select
    id
    (FourColor.select color0 color1 color3 color2)
    (FourColor.select color0 color2 color1 color3)
    (FourColor.select color0 color2 color3 color1)
    (FourColor.select color0 color3 color1 color2)
    (FourColor.select color0 color3 color2 color1)

@[inline] instance EPerm.instCoeFun : CoeFun EPerm (fun _ => FourColor → FourColor) where
  coe:=toFun

def EPerm.inv : EPerm → EPerm :=
  select eperm123 eperm132 eperm213 eperm312 eperm231 eperm321

def EPerm.mul : EPerm → EPerm → EPerm :=
  select
    id
    (select eperm132 eperm123 eperm312 eperm321 eperm213 eperm231)
    (select eperm213 eperm231 eperm123 eperm132 eperm321 eperm312)
    (select eperm231 eperm213 eperm321 eperm312 eperm123 eperm132)
    (select eperm312 eperm321 eperm132 eperm123 eperm231 eperm213)
    (select eperm321 eperm312 eperm231 eperm213 eperm132 eperm123)

@[inline] instance EPerm.instGroup : Group EPerm where
  mul := mul
  one := eperm123
  inv := inv
  mul_assoc := by{
    intro a b c
    change mul (mul a b) c = mul a (mul b c)
    cases a <;> cases b <;> cases c <;> rfl
  }
  one_mul := by{
    intro a
    change mul eperm123 a = _
    cases a <;> rfl
  }
  mul_one := by{
    intro a
    change mul a eperm123 = _
    cases a <;> rfl
  }
  inv_mul_cancel := by{
    intro a
    cases a <;> rfl
  }

theorem EPerm.mul_eq_comp {e1 e2 : EPerm} :
  (e1 * e2 : FourColor → FourColor) = (e1 ∘ e2) := by{
    change (mul e1 e2).toFun = _
    ext c
    rw[comp_apply]
    cases e1 <;> cases e2 <;> cases c <;> rfl
  }

@[simp] theorem eperm_color0 {e : EPerm} : e color0 = color0 := by{
  cases e <;> rfl
}
theorem eperm_0 {e : EPerm} : e 0 = 0 := eperm_color0

def smul (e : EPerm) (c : FourColor) := e c

@[inline] instance instDistribMulAction : DistribMulAction EPerm FourColor where
  smul := smul
  mul_smul := by{
    intro x y b
    change (x * y) b = x (y b)
    rw[EPerm.mul_eq_comp]
    simp
  }
  one_smul := by{
    intro b
    change EPerm.eperm123 b = b
    rfl
  }
  smul_zero := by{
    intro e
    change e 0 = 0
    exact eperm_0
  }
  smul_add := by{
    intro e c1 c2
    change e (add c1 c2) = add (e c1) (e c2)
    cases e <;> cases c1 <;> cases c2 <;> rfl
  }

def EPerm.ofFun (f : FourColor → FourColor)
  : EPerm :=
  FourColor.select
    eperm123
    (FourColor.select eperm123 eperm123 eperm123 eperm132 (f color2))
    (FourColor.select eperm123 eperm213 eperm123 eperm231 (f color2))
    (FourColor.select eperm123 eperm312 eperm321 eperm123 (f color2))
  (f color1)

theorem EPerm.ofFun_eq {f : FourColor → FourColor}
(hfi : Injective f) (hf0 : f color0 = color0)
: ofFun f = f := by{
  ext c
  have hf10 : f color1 ≠ color0 := by{rw[← hf0, hfi.ne_iff]; simp}
  have hf20 : f color2 ≠ color0 := by{rw[← hf0, hfi.ne_iff]; simp}
  have hf30 : f color3 ≠ color0 := by{rw[← hf0, hfi.ne_iff]; simp}
  have hf12 : f color1 ≠ f color2 :=by{rw[hfi.ne_iff]; simp}
  have hf13 : f color1 ≠ f color3 :=by{rw[hfi.ne_iff]; simp}
  have hf23 : f color2 ≠ f color3 :=by{rw[hfi.ne_iff]; simp}
  cases c <;> cases hf1 : f color1 <;> cases hf2 : f color2 <;> cases hf3 : f color3
  all_goals
  simp[hf1, hf2, hf3] at hf10 hf20 hf30 hf12 hf13 hf23
  try simp[ofFun, toFun, hf0, hf1, hf2]
}
theorem EPerm.exists_of_fun {f : FourColor → FourColor}
(hfi : Injective f) (hf0 : f color0 = color0)
  : ∃e : EPerm, f = e := by{
    use ofFun f
    simp [EPerm.ofFun_eq hfi hf0]
  }

open EPerm

theorem color_eperm_cases {c : FourColor} (hc : c ≠ color0) (d : FourColor)
  : d = color0 ∨ d = c ∨ d = eperm312 c ∨ d = eperm231 c := by{
    cases d <;> cases c
    all_goals
    simp[toFun]
    try simp at hc
  }

theorem eperm123_id {c : FourColor} : eperm123 c = c := rfl
theorem EPerm.eq_zero_iff {e : EPerm} {c : FourColor} : (e c = color0) ↔ (c = color0) := by{
  cases e <;> cases c <;> simp[toFun]
}

end FourColor
