import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Finite.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Inv
import Init.Data.Nat.Lemmas
import FourColorTheorem.Utils.Relations
import FourColorTheorem.Utils.Classical


open Relation
open Function


theorem Function.minimalPeriod_eq_two_iff {α : Type _} {f : α → α} {x : α} :
  minimalPeriod f x = 2 ↔ f (f x) = x ∧ f x ≠ x := by{
    rw[minimalPeriod_eq_prime_iff]
    rfl
  }
theorem Function.minimalPeriod_eq_three_iff {α : Type _} {f : α → α} {x : α} :
  minimalPeriod f x = 3 ↔ f (f (f x)) = x ∧ f x ≠ x := by{
    rw[minimalPeriod_eq_prime_iff]
    rfl
  }
theorem isEmpty_quotient_iff {α : Type _} {s : Setoid α}
  : IsEmpty (Quotient s) ↔ IsEmpty α := by{
    simp only [isEmpty_iff]
    constructor
    · exact fun ha a => ha (Quotient.mk s a)
    · exact fun ha a => ha a.out
  }
theorem Nat.card_gt_one_iff {α : Type _} [Finite α]
  : Nat.card α > 1 ↔ ∃x y:α, x ≠ y:=by{
    generalize hc : Nat.card α = k
    match k with
    | 0 => {
      let inst:Finite α:=inferInstance
      simp[card_eq_zero, not_infinite_iff_finite.mpr inst] at hc
      simp
    }
    | 1 => {
      simp[card_eq_one_iff_unique] at hc
      simp only [gt_iff_lt, lt_self_iff_false, ne_eq, false_iff, not_exists, not_not]
      exact hc.left.allEq
    }
    | n' + 2 => {
      simp only [gt_iff_lt, lt_add_iff_pos_left, Order.lt_add_one_iff, _root_.zero_le, ne_eq,
        true_iff]
      let e:=Nat.equivFinOfCardPos (α:=α) (by{simp[hc]})
      simp[hc] at e
      use e.symm 0, e.symm 1
      simp
    }
  }
theorem Nat.card_le_two_iff {α : Type _} [Finite α]
  : Nat.card α ≤ 2 ↔ IsEmpty α ∨ ∃x y:α, ∀z, z = x ∨ z = y:=by{
    generalize hc : Nat.card α = k
    match k with
    | 0 => {
      let inst:Finite α:=inferInstance
      simp[card_eq_zero, not_infinite_iff_finite.mpr inst] at hc
      simp[hc]
    }
    | 1 => {
      simp[card_eq_one_iff_unique] at hc
      simp only [one_le_ofNat, true_iff]
      apply Or.inr
      use hc.right.some
      use hc.right.some
      intro _
      simp only [or_self]
      apply hc.left.allEq
    }
    | 2 => {
      simp only [Std.le_refl, true_iff]
      rw[card_eq_two_iff] at hc
      have ⟨x, y, hxy, hexy⟩:=hc
      apply Or.inr
      use x
      use y
      intro z
      have hz:=Set.mem_univ z
      rw[←hexy] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      exact hz
    }
    | n' + 3 => {
      have h:=((card_pos_iff (α:=α)).mp (by{simp[hc]})).left
      simp only [reduceLeDiff, not_isEmpty_of_nonempty, false_or, false_iff]
      let e:=Nat.equivFinOfCardPos (α:=α) (by{simp[hc]})
      simp only [not_exists, not_forall, not_or]
      intro a b
      simp[hc] at e
      cases em (a = e.symm ⟨0, by{simp}⟩ ∨ a = e.symm ⟨1, by{simp}⟩) with
      | inl ha => cases em (b = e.symm ⟨0, by{simp}⟩ ∨ b = e.symm ⟨1, by{simp}⟩) with
        | inl hb => {
          use e.symm ⟨2, by{simp}⟩
          cases ha with | inl ha | inr ha =>
          cases hb with | inl hb | inr hb =>
            simp[ha, hb]
        }
        | inr hb => {
          simp only [not_or] at hb
          cases ha with
          | inl ha => {
            use e.symm ⟨1, by{simp}⟩
            simp only [ha, e.symm.injective.eq_iff, Fin.ext_iff]
            simp only [one_ne_zero, not_false_eq_true, true_and]
            exact Ne.symm hb.right
          }
          | inr ha => {
            use e.symm ⟨0, by{simp}⟩
            simp only [ha, e.symm.injective.eq_iff, Fin.ext_iff]
            simp only [zero_ne_one, not_false_eq_true, true_and]
            exact Ne.symm hb.left
          }
        }
      | inr ha =>
        simp only [not_or] at ha
        cases em (b = e.symm ⟨0, by{simp}⟩) with
        | inl hb => {
          use e.symm ⟨1, by{simp}⟩
          simp only [hb, e.symm.injective.eq_iff, Fin.ext_iff]
          simp only [one_ne_zero, not_false_eq_true, and_true]
          exact Ne.symm ha.right
        }
        | inr hb => {
          use e.symm ⟨0, by{simp}⟩
          exact ⟨Ne.symm ha.left, Ne.symm hb⟩
        }
    }
  }
section Fintype

variable {α : Type _} [Fintype α]

theorem Fintype.card_gt_one_iff :
  card α > 1 ↔ ∃x y:α, x ≠ y := by{
    rw[card_eq_nat_card]
    exact Nat.card_gt_one_iff
  }
theorem Fintype.card_le_two_iff :
  card α ≤ 2 ↔ IsEmpty α ∨ ∃x y:α, ∀z, z = x ∨ z = y := by{
    rw[card_eq_nat_card]
    exact Nat.card_le_two_iff
  }
def Fintype.nComp (r : Setoid α) [DecidableRel r] : ℕ :=
  let q := Quotient r
  Fintype.card q
theorem Fintype.ofEquivQuotient_eq {β : Type _}
  {ra : Setoid α} {rb : Setoid β}
  [DecidableRel ra]
  (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂))
  : @ofEquiv _ (Quotient ra) (Quotient.fintype ra) (Quotient.congr e eq)
  = @Quotient.fintype _ (ofEquiv α e) rb (Equiv.decidableRel_of_iff e eq) :=by{
    let dec_rb : DecidableRel rb := Equiv.decidableRel_of_iff e eq
    unfold ofEquiv ofBijective Quotient.fintype ofSurjective
    congr
    ext x
    rw[Finset.mem_map]
    rw[Finset.mem_image]
    simp only [Finset.mem_univ, Embedding.coeFn_mk, true_and]
    rw[Quotient.exists]
    simp only [Quotient.congr_mk]
    constructor
    · {
      intro ⟨a, ha⟩
      use e.toFun a
      exact ha
    }
    · {
      intro ⟨b, hb⟩
      use e.invFun b
      rw[←e.toFun_as_coe, e.right_inv]
      exact hb
    }
  }
theorem Fintype.nComp_equiv {β : Type _}
  {ra : Setoid α} {rb : Setoid β}
  [DecidableRel ra]
  (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂))
  : nComp ra = @nComp _ (ofEquiv α e) rb (Equiv.decidableRel_of_iff e eq) := by{
    unfold nComp
    simp only
    have h:=Eq.symm (ofEquiv_card (Quotient.congr e eq))
    simp only [h]
    congr
    exact ofEquivQuotient_eq e eq
  }
theorem Fintype.nComp_eq_zero_iff {r : Setoid α} [DecidableRel r]
  : nComp r = 0 ↔ IsEmpty α := by{
    unfold nComp
    rw[card_eq_zero_iff, isEmpty_quotient_iff]
}
theorem Fintype.nComp_eq_one_iff_nonempty_all {s : Setoid α} [DecidableRel s]
  : nComp s = 1 ↔ Nonempty α ∧ ∀x y, s x y := by{
    unfold nComp
    rw[card_eq_one_iff]
    constructor
    · {
      intro ⟨x, hx⟩
      apply And.intro (Nonempty.intro x.out)
      intro a b
      have hxa := hx ⟦a⟧
      have hxb := hx ⟦b⟧
      have hx':=hxa.trans hxb.symm
      rw[Quotient.eq_iff_equiv] at hx'
      exact hx'
    }
    · {
      intro ⟨hn, ha⟩
      use ⟦hn.some⟧
      intro y
      rw[Quotient.eq_mk_iff_out]
      simp[ha]
    }
  }
theorem Fintype.nComp_eq_one_iff_exists_all {s : Setoid α} [DecidableRel s]
  : nComp s = 1 ↔ ∃x, ∀y, s x y := by{
    unfold nComp
    rw[card_eq_one_iff]
    constructor
    · {
      intro ⟨x, hx⟩
      use x.out
      intro y
      have hx':=hx ⟦y⟧
      rw[Quotient.mk_eq_iff_out] at hx'
      exact s.iseqv.symm hx'
    }
    · {
      intro ⟨x, hx⟩
      use ⟦x⟧
      intro y
      rw[Quotient.eq_mk_iff_out]
      apply s.iseqv.symm
      simp[hx]
    }
  }
theorem Fintype.nComp_gt_one_iff {s : Setoid α} [DecidableRel s]
  : nComp s > 1 ↔ ∃x y, ¬s x y := by{
    unfold nComp
    simp only
    rw[card_gt_one_iff]
    simp[Quotient.exists, Quotient.eq_iff_equiv]
  }

end Fintype

section Pigeonhole
variable {α : Type _}
variable [Finite α]

theorem Finite.exists_ne_map_eq_of_card_lt {α : Type _} {β : Type _} [Finite α] [Finite β]
  (f : α → β) (h : Nat.card β < Nat.card α) : ∃ a1 a2 : α, a1 ≠ a2 ∧ f a1 = f a2 := by{
    let instA : Fintype α := Fintype.ofFinite α
    let instB : Fintype β := Fintype.ofFinite β
    exact Fintype.exists_ne_map_eq_of_card_lt f
      (by{rw[←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card]; exact h})
  }

theorem Finite.exists_fin_lt_map_eq_of_card_lt {n : ℕ} (f : Fin n → α) (h : Nat.card α < n) :
  ∃ i j : Fin n, i < j ∧ f i = f j := by{
    obtain ⟨i, j, h_lt, h_eq⟩ : ∃ i j : Fin n, i ≠ j ∧ f i = f j :=
      Finite.exists_ne_map_eq_of_card_lt f
      (by{rw[Nat.card_fin]; exact h})
    wlog h_ij : i < j generalizing i j with H
    · exact H j i h_lt.symm h_eq.symm (lt_of_le_of_ne (le_of_not_gt h_ij) (Ne.symm h_lt))
    exact ⟨i, j, h_ij, h_eq⟩
  }
end Pigeonhole
