import FourColorTheorem.Color.EPerm
import FourColorTheorem.Utils.List

open Function
open Relation

namespace FourColor
open EPerm

def ERot : FourColor → EPerm := select eperm123 eperm123 eperm312 eperm231
@[simp] theorem erot_self (a : FourColor) : ERot a a = if a = color0 then color0 else color1 := by{
  cases a <;> rfl
}

abbrev ColSeq := List FourColor
namespace ColSeq
abbrev headColor (l : ColSeq) := l.headD color0
-- 似乎最后可约性证明是写一个函数输出布尔值判断
-- 如果是这样的话命题写起来会比较吐血（因为不只有True和False）
-- 那这里边染色我就使用布尔值来定义，而不是通常的谓词
def proper (et : ColSeq) : Bool := et.headColor != color0
def pTrace (lc : ColSeq) : ColSeq :=
  List.pairmap (· + ·) lc
def permt (lc : ColSeq) (e : EPerm) : ColSeq := lc.map e
def sumt (lc : ColSeq) : FourColor := lc.foldr (· + ·) color0
def cTrace (et : ColSeq) := et ++ [et.sumt]
def trace (lc : ColSeq) : ColSeq :=
  if lc = [] then [] else lc.pTrace.cTrace
def urtrace (lc : ColSeq) : ColSeq := (lc.getLastD color0::lc).pairmap (· + ·)
def untrace (c0 : FourColor) (et : ColSeq) : ColSeq :=
  (color0 :: et).dropLast.scanl (· + ·) c0

@[simp] theorem nil_headColor : headColor [] = color0 := rfl
@[simp] theorem nil_not_proper : ¬proper [] := by{simp[proper]}
@[simp] theorem singleton_headColor {a : FourColor} : headColor [a] = a := rfl
@[simp] theorem singleton_proper {a : FourColor} : proper [a] = (a != color0)
  := by{simp[proper]}
@[simp] theorem cons_headColor {a : FourColor} {lc : ColSeq}
  : headColor (a :: lc) = a := rfl
@[simp] theorem cons_proper {a : FourColor} {lc : ColSeq}
  : proper (a :: lc) = (a != color0) := by{simp[proper]}
@[simp] theorem permt_nil {e : EPerm} : permt [] e = [] := rfl
theorem permt_cons {a : FourColor} {lc : ColSeq} {e : EPerm} :
  permt (a :: lc) e = e a :: lc.permt e := rfl
theorem permt_123 {lc : ColSeq} : lc.permt eperm123 = lc := by{
  induction lc with
  | nil => rfl
  | cons a lc' ih => rw[permt_cons, eperm123_id, ih]
}
theorem permt_permt {lc : ColSeq} {e1 e2 : EPerm}
: (lc.permt e1).permt e2 = lc.permt (e2 * e1) := by{
  induction lc with
  | nil => simp
  | cons a lc' ih => {
    simp only [permt_cons, EPerm.mul_eq_comp, comp_apply, ih]
  }
}

-- 以下将边色列表标准化
-- ttail首先要求最开头一项必须是color1，使用3色轮换对称作用
def tTail (et : ColSeq) : ColSeq :=
  if et.proper then
    permt et.tail (ERot et.headColor)
  else [color0]
@[simp] theorem nil_ttail : tTail [] = [color0] := by{simp[tTail]}
@[simp] theorem singleton_ttail {a : FourColor} :
  tTail [a] = if a = color0 then [color0] else [] := by{
  cases a <;> rfl
}
theorem cons_ttail {a : FourColor} {et : ColSeq}
  : tTail (a :: et) = if a = color0 then [color0] else et.permt (ERot a) := by{
  unfold tTail
  simp only [cons_proper, cons_headColor, List.tail_cons]
  rcases eq_or_ne a color0 with h0 | h0 <;> simp[h0]
}
def evenTail (et : ColSeq) : Bool :=
  -- 对于一个列表，每一个出现的color3之前都有一个color2关门
  -- 也就是说第一次出现的color2比第一次出现的color3更早
  et.foldr (fun c b => select b b true false c) true
@[simp] theorem nil_eventail : evenTail [] := by{trivial}
@[simp] theorem singleton_eventail {a : FourColor} : evenTail [a] = (a != color3) := by{
  cases a <;> simp[evenTail]
}
@[inline] instance evenTail.instDecidable {et : ColSeq} : Decidable et.evenTail := by{
  apply instDecidableEqBool
}
where loop {et : ColSeq} {flag : Bool}
: Decidable (et.foldr (fun c b => select b b True False c) flag) := by{
  induction et generalizing flag with
  | nil =>{
    simp only [List.foldr_nil]
    cases flag <;> simp only [Bool.false_eq_true]
    · exact instDecidableFalse
    · exact instDecidableTrue
  }
  | cons a et' ih => {
    rw[List.foldr_cons]
    match a with
    | color0 | color1 => {
      change Decidable (List.foldr _ _ _)
      apply ih
    }
    | color2 => exact instDecidableTrue
    | color3 => exact instDecidableFalse
  }
}
def evenTrace (et : ColSeq) : Bool :=
  et.tTail.evenTail
@[simp] theorem nil_eventrace : evenTrace [] := by{trivial}
@[simp] theorem singleton_eventrace {a : FourColor} : evenTrace [a] := by{
  cases a <;> simp[evenTrace]
}
def eTracePerm (et : ColSeq) : EPerm := if et.evenTrace then eperm123 else eperm132
-- eTrace再将23颜色互换，使得2总比3早
-- 这样操作之后获得的eTrace是所有等价et中字典序最小的
def eTrace (et : ColSeq) := et.permt et.eTracePerm
def eTail (et : ColSeq) := et.tTail.permt et.eTracePerm
def ePTrace (lc : ColSeq) := lc.pTrace.eTail

theorem color0_mem_permt_iff {et : ColSeq} {e : EPerm}
: color0 ∈ et.permt e ↔ color0 ∈ et := by{
  induction et with
  | nil => simp
  | cons a et' ih => {
    rw[permt_cons, List.mem_cons, List.mem_cons, Eq.comm, EPerm.eq_zero_iff, Eq.comm, ih]
  }
}
theorem permt_proper_iff {et : ColSeq} {e : EPerm} : (et.permt e).proper = et.proper := by{
  induction et with
  | nil => simp
  | cons a et ih =>
    rw[permt_cons, cons_proper, cons_proper]
    cases e <;> cases a <;> rfl
}
theorem color0_mem_ttail_iff {et : ColSeq}
  : color0 ∈ et.tTail ↔ et.proper = false ∨ color0 ∈ et := by{
  induction et with
  | nil => simp
  | cons a et ih => {
    rw[cons_ttail, cons_proper, apply_ite (color0 ∈ ·)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, color0_mem_permt_iff,
      if_true_left, bne_eq_false_iff_eq]
    cases a <;> simp
  }
}

theorem even_etail (et : ColSeq) : et.eTail.evenTail := by{
  unfold eTail eTracePerm evenTrace
  generalize et.tTail = ett
  rcases eq_or_ne ett.evenTail true with hett | hett
  · simp only [hett, ↓reduceIte, permt_123]
  simp only [hett]
  simp only [Bool.false_eq_true, ↓reduceIte]
  induction ett with
  | nil => simp
  | cons a ett' ih => {
    rw[permt_cons]
    match a with
    | color0 | color1 => {
      simp only [evenTail, List.foldr_cons, ne_eq] at hett
      change List.foldr _ _ _ ≠ true at hett
      change evenTail _ ≠ true at hett
      specialize ih hett
      simp only [toFun, EPerm.select, select]
      unfold evenTail
      rw[List.foldr_cons]
      exact ih
    }
    | color2 => simp[evenTail] at hett
    | color3 => simp[evenTail, toFun]
  }
}
theorem ttail_etrace (et : ColSeq) : et.eTrace.tTail = et.eTail := by{
  unfold eTrace eTail tTail eTracePerm
  simp only [permt_proper_iff]
  match hetet : et.evenTrace with
  | true => simp only[↓reduceIte, permt_123]
  | false => {
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw[apply_ite (permt · eperm132)]
    change _ = if _ then _ else [color0]
    congr 1
    match et with
    | [] => simp
    | color0 :: et' | color1 :: et' => {
      rw[permt_cons]
      simp only [toFun, EPerm.select, select, cons_headColor,
        List.tail_cons, ERot, permt_123]
    }
    | color2 :: et' | color3 :: et' => {
      rw[permt_cons]
      simp only [toFun, EPerm.select, select, cons_headColor, ERot,
        List.tail_cons, permt_permt]
      congr 1
    }
  }
}
theorem exists_color1_cons_tTail_of_proper {et : ColSeq} (het : et.proper) :
  ∃e, permt et e = color1 :: et.tTail := by{
  unfold tTail
  simp only [het, ↓reduceIte]
  use et.headColor.ERot
  match et with
  | [] => simp at het
  | a :: et' => {
    rw[cons_proper] at het
    simp only [bne_iff_ne, ne_eq] at het
    rw[cons_headColor, List.tail_cons, permt_cons, erot_self]
    simp[het]
  }
}
theorem exists_color1_cons_eTail_of_proper {et : ColSeq} (het : et.proper) :
  ∃e, permt et e = color1 :: et.eTail := by{
  have ⟨e, he⟩ := exists_color1_cons_tTail_of_proper het
  unfold eTail eTracePerm
  use (if et.evenTrace = true then eperm123 else eperm132) * e
  rw[← permt_permt, he, permt_cons]
  congr 1
  rw[apply_ite (toFun · color1)]
  simp
}
theorem etail_permt (et : ColSeq) (e : EPerm) : (et.permt e).eTail = et.eTail := by{
  match hetp : et.proper with
  | false => {
    unfold eTail tTail eTracePerm evenTrace tTail
    simp [permt_proper_iff, hetp]
  }
  | true => {
    have ⟨g, hg⟩:=exists_color1_cons_eTail_of_proper hetp
    have ⟨g', hg'⟩:=
      exists_color1_cons_eTail_of_proper (permt_proper_iff (e := e) ▸ hetp)
    rw[permt_permt] at hg'
    rw[← mul_one (g' * e), ← inv_mul_cancel g, ← mul_assoc, ← permt_permt,
    hg, permt_cons] at hg'
    simp only [List.cons.injEq] at hg'
    rw[← hg'.right]
    match hgeg : g' * e * g⁻¹ with
    | eperm213 | eperm231 | eperm312 | eperm321 => simp[hgeg] at hg'
    | eperm123 => rw[permt_123]
    | eperm132 => {
      simp only [hgeg, true_and] at hg'
      have ih : color2 ∉ et.eTail ∧ color3 ∉ et.eTail := by{
        generalize et.permt e = et' at *
        have het' := even_etail et'
        have het := even_etail et
        generalize et.eTail = ett at *
        generalize et'.eTail = et't at *
        clear! et
        rw[← hg'] at het'
        clear! et't
        induction ett with
        | nil => simp
        | cons a ett' ih => {
          match a with
          | color3 => simp[evenTail] at het
          | color2 => simp[evenTail, permt] at het'
          | color0 | color1 => {
            change evenTail ett' = true at het
            change (permt ett' eperm132).evenTail = true at het'
            specialize ih het het'
            simp[ih]
          }
        }
      }
      clear hg' hg hetp
      generalize et.eTail = ett at *
      induction ett with
      | nil => simp
      | cons a ett' ih' => {
        match a with
        | color2 | color3 => simp at ih
        | color0 | color1 => {
          rw[permt_cons]
          congr 1
          apply ih'
          simp at ih
          simp[ih]
        }
      }
    }
  }
}

end ColSeq
end FourColor
