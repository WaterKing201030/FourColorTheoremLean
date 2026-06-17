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

theorem List.Subtype.fintype_card_le_length {α : Type _} [DecidableEq α] {l : List α}
  : Fintype.card {x // x ∈ l} ≤ l.length := by{
  have h := Fintype.subtype_card (p:=(· ∈ l)) l.toFinset (by simp)
  have h' := List.toFinset_card_le l
  rw[← h] at h'
  apply (Eq.mp · h')
  congr
  apply Subsingleton.elim
}
theorem List.Subtype.fintype_card_eq_length_of_nodup {α : Type _} [DecidableEq α] {l : List α}
  (hl : l.Nodup) : Fintype.card {x // x ∈ l} = l.length := by{
  have h := Fintype.subtype_card (p:=(· ∈ l)) l.toFinset (by simp)
  rw[← List.toFinset_card_of_nodup hl]
  rw[← h]
  congr
  apply Subsingleton.elim
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
theorem Relation.ReflTransGen_iff_isChain_le_card_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, l.length ≤ Fintype.card α ∧ List.IsChain r l
    ∧ l.head? = some a ∧ l.getLast? = some b := by{
    constructor
    · {
      rw[ReflTransGen_iff_isChain_nodup_option]
      intro ⟨l, hp, hc, hh, hd⟩
      use l
      apply (And.intro · ⟨hc, hh, hd⟩)
      exact List.Nodup.length_le_card hp
    }
    · {
      intro ⟨l, hl, hc, hh, hd⟩
      rw[ReflTransGen_iff_isChain_option]
      exact ⟨l, hc, hh, hd⟩
    }
  }
theorem Relation.ReflTransGen_iff_isChain_le_card_subtype_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : { x : List α // x.length ≤ Fintype.card α }, List.IsChain r l
    ∧ l.val.head? = some a ∧ l.val.getLast? = some b := by{
    rw[ReflTransGen_iff_isChain_le_card_option]
    constructor
    · {
      intro ⟨l, hl, hc, hh, hd⟩
      use ⟨l, hl⟩
    }
    · {
      intro ⟨⟨l, hl⟩, hc, hh, hd⟩
      use l
    }
  }

@[inline] instance List.constLenFintype {n : ℕ} : Fintype { l : List α // l.length = n }
  := Vector.fintype
@[inline] instance List.boundedLenFintype {n : ℕ} : Fintype {l : List α // l.length ≤ n} := by{
  induction n with
  | zero => {
    simp only [nonpos_iff_eq_zero, length_eq_zero_iff]
    exact Fintype.subtypeEq []
  }
  | succ n' ih => {
    let set0 := Finset.univ (α:={l : List α // l.length ≤ n'})
    let set1 := Finset.univ (α:={l : List α // l.length = n' + 1})
    let set2 := set0.map ⟨Subtype.val, Subtype.val_injective⟩
    let set3 := set1.map ⟨Subtype.val, Subtype.val_injective⟩
    have h23: _root_.Disjoint (α:=Finset (List α)) set2 set3:=by{
      rw[Finset.disjoint_iff_ne]
      intro a ha b hb
      have ⟨⟨a', pa'⟩, ha'⟩:=Finset.mem_map.mp ha
      have ⟨⟨b', pb'⟩, hb'⟩:=Finset.mem_map.mp hb
      rw[←ha'.right, ←hb'.right]
      simp only [Embedding.coeFn_mk, ne_eq]
      intro hn
      rw[←hn] at pb'
      rw[pb'] at pa'
      simp at pa'
    }
    let set4 := Finset.disjUnion set2 set3 h23
    apply Fintype.ofFinset set4
    change ∀x, x∈ set4 ↔ x.length ≤ n' + 1
    intro x
    rw[Nat.le_succ_iff]
    rw[Finset.mem_disjUnion]
    rw[Finset.mem_map, Finset.mem_map]
    constructor
    · {
      intro h
      match h with
      | Or.inl ⟨a, ha, h⟩ => apply Or.inl; rw[←h]; simp[a.property]
      | Or.inr ⟨a, ha, h⟩ => apply Or.inr; rw[←h]; simp[a.property]
    }
    · {
      intro h
      match h with
      | Or.inl h => apply Or.inl; exact ⟨⟨x, h⟩, by{unfold set0; simp}⟩
      | Or.inr h => apply Or.inr; exact ⟨⟨x, h⟩, by{unfold set1; simp}⟩
    }
  }
}
@[inline] instance Relation.ReflTransGen.finDec [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
  : DecidableRel (ReflTransGen r) := by{
    intro a b
    rw[ReflTransGen_iff_isChain_le_card_subtype_option]
    exact Fintype.decidableExistsFintype
  }
@[inline] instance Relation.funReflTransGen.finDec [DecidableEq α] {f : α → α}
  : DecidableRel (funReflTransGen f) := by{
    unfold funReflTransGen
    apply ReflTransGen.finDec
}
theorem Fintype.bijInv_bijInv [DecidableEq α] {f : α → α} (hf : Bijective f)
  : bijInv (bijective_bijInv hf) = f:=by{
  ext x
  apply (bijective_bijInv hf).left
  rw[leftInverse_bijInv hf]
  rw[rightInverse_bijInv (bijective_bijInv hf)]
}
theorem Fintype.comp_bijInv [DecidableEq α] {f g : α → α} (hf : Bijective f) (hg : Bijective g)
  : bijInv (Function.Bijective.comp hf hg) = bijInv hg ∘ bijInv hf := by{
    ext x
    apply (Function.Bijective.comp hf hg).injective
    rw[rightInverse_bijInv (Function.Bijective.comp hf hg)]
    rw[comp_apply, comp_apply]
    rw[rightInverse_bijInv hg, rightInverse_bijInv hf]
  }
theorem Fintype.iterate_bijInv [DecidableEq α] {f : α → α} (hf : Bijective f) {n : ℕ}
  : bijInv (Bijective.iterate hf n) = (bijInv hf)^[n] := by{
    ext x
    rw[←(hf.left.iterate n).eq_iff]
    rw[rightInverse_bijInv (hf.iterate n)]
    induction n with
    | zero => simp
    | succ n' ih => {
      rw[iterate_succ, iterate_succ']
      simp only [comp_apply]
      rw[rightInverse_bijInv hf]
      exact ih
    }
  }

end Fintype

section Finite
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

theorem Relation.funReflTransGen_iff_iterate_bounded {f : α → α} {a b : α} :
  funReflTransGen f a b ↔ ∃ n < Nat.card α, (f^[n]) a = b := by{
    apply funReflTransGen_iff_iterate.trans
    constructor
    · {
      intro ⟨n, hn⟩
      induction n using Nat.strong_induction_on generalizing a with
      | h n ih => {
        by_cases hmn : n < Nat.card α
        · exact ⟨n, hmn, hn⟩
        · {
          have hmn:=le_of_not_gt hmn
          let instA : Fintype α := Fintype.ofFinite α
          obtain ⟨i, j, h_ij, h_eq⟩ : ∃ i j : Fin (n + 1), i < j ∧ (f^[i]) a = (f^[j]) a :=
          Finite.exists_fin_lt_map_eq_of_card_lt (fun i : Fin (n + 1) => (f^[i.val]) a)
            (Nat.lt_succ_of_le hmn)
          have h_eq' := congrArg f^[n - j] h_eq
          rw[←iterate_add_apply, ←iterate_add_apply] at h_eq'
          rw[Nat.sub_add_cancel j.is_le, hn] at h_eq'
          apply (ih (n - j + i) · h_eq')
          omega
        }
      }
    }
    · {
      intro ⟨n, hn, hnn⟩
      exact ⟨n, hnn⟩
    }
  }

theorem Relation.iterate_bounded_periodicpts (f : α → α) (a : α) :
  ∃ n < Nat.card α, (f^[n]) a ∈ periodicPts f := by{
    obtain ⟨i, j, hn, h_eq⟩ :=
      Finite.exists_fin_lt_map_eq_of_card_lt (fun k => f^[k] a) (Nat.lt_succ_self _)
    have hij:IsPeriodicPt f (j - i) (f^[i] a):=by{
      unfold IsPeriodicPt
      unfold IsFixedPt
      rw[←iterate_add_apply, Nat.sub_add_cancel (le_of_lt hn)]
      exact h_eq.symm
    }
    exact ⟨i, lt_of_lt_of_le hn j.is_le, mk_mem_periodicPts (Nat.sub_pos_of_lt hn) hij⟩
  }

theorem Relation.funReflTransGen_Symm_of_injective {f : α → α} (hf : Injective f) :
  Std.Symm (funReflTransGen f) := by{
    apply Std.Symm.mk
    intro a b h
    have ⟨n, hn⟩ := Relation.funReflTransGen_iff_iterate.mp h
    have hb := Function.Injective.mem_periodicPts hf a
    rw[mem_periodicPts] at hb
    have ⟨c, hcn, hcp⟩ := hb
    unfold IsPeriodicPt IsFixedPt at hcp
    let t:=n ⌈/⌉ c * c - n
    have ht : f^[t] b = a:=by{
      unfold t
      rw[←hn, ←iterate_add_apply, Nat.sub_add_cancel]
      · rw[mul_comm, iterate_mul, iterate_fixed hcp]
      · rw[Nat.mul_comm]; exact le_smul_ceilDiv hcn
    }
    rw[funReflTransGen_iff_iterate]
    exact ⟨t, ht⟩
  }

theorem Relation.funReflTransGen_symm_of_injective {f : α → α} (hf : Injective f) {a b : α} :
  funReflTransGen f a b → funReflTransGen f b a := by{
    intro h
    have ⟨n, hn⟩ := Relation.funReflTransGen_iff_iterate.mp h
    have hb := Function.Injective.mem_periodicPts hf a
    rw[mem_periodicPts] at hb
    have ⟨c, hcn, hcp⟩ := hb
    unfold IsPeriodicPt IsFixedPt at hcp
    let t:=n ⌈/⌉ c * c - n
    have ht : f^[t] b = a:=by{
      unfold t
      rw[←hn, ←iterate_add_apply, Nat.sub_add_cancel]
      · rw[mul_comm, iterate_mul, iterate_fixed hcp]
      · rw[Nat.mul_comm]; exact le_smul_ceilDiv hcn
    }
    rw[funReflTransGen_iff_iterate]
    exact ⟨t, ht⟩
  }
theorem Function.minimalPeriod_le_card' {f : α → α} {x : α}
  : minimalPeriod f x ≤ Nat.card α := by{
    let inst := Fintype.ofFinite α
    have h:=minimalPeriod_le_card (f:=f) (x:=x)
    rw[Fintype.card_eq_nat_card] at h
    exact h
  }
theorem Function.mem_periodicPts_iff_exists_le_card' {f : α → α} {x : α} :
  x ∈ periodicPts f ↔ ∃n > 0, n ≤ Nat.card α ∧ IsPeriodicPt f n x := by{
    rw[mem_periodicPts]
    constructor
    · {
      intro ⟨n, hn, hr⟩
      let t:=minimalPeriod f x
      use t
      apply And.intro (hr.minimalPeriod_pos hn)
      apply And.intro minimalPeriod_le_card'
      apply isPeriodicPt_minimalPeriod
    }
    · {
      intro ⟨n, hn, _, hr⟩
      exact ⟨n, hn, hr⟩
    }
  }
theorem Function.Injective.minimalPeriod_pos {f : α → α} (hf : Injective f)
  {x : α} : 0 < minimalPeriod f x := by{
    apply minimalPeriod_pos_of_mem_periodicPts
    apply hf.mem_periodicPts
  }
end Finite

section Fintype
variable {α : Type _}
variable [Fintype α]

theorem Function.mem_periodicPts_iff_exists_le_card {f : α → α} {x : α}
  : x ∈ periodicPts f ↔ ∃n > 0, n ≤ Fintype.card α ∧ IsPeriodicPt f n x := by{
    rw[Fintype.card_eq_nat_card]
    exact mem_periodicPts_iff_exists_le_card'
  }
@[inline] instance Function.instDecidableMemPeriodicPts [DecidableEq α] {f : α → α} {x : α}
  : Decidable (x ∈ periodicPts f) := by{
    rw[mem_periodicPts_iff_exists_le_card]
    simp only [and_left_comm]
    let p:=(fun n => n > 0 ∧ IsPeriodicPt f n x)
    let inst : DecidablePred p:=fun _ => instDecidableAnd
    exact Nat.decidableExistsLE (p:=p) (Fintype.card α)
  }

theorem Relation.fromFun_bijInv_iff [DecidableEq α]
  {f : α → α} (hf : Bijective f) {a b : α}
  : fromFun (Fintype.bijInv hf) a b ↔ fromFun f b a:=by{
    simp only [fromFun]
    rw[←Injective.eq_iff hf.left]
    rw[Fintype.rightInverse_bijInv hf]
    rw[Eq.comm]
  }

theorem Relation.funReflTransGen_bijInv [DecidableEq α] {f : α → α}
  (hf : Bijective f) {a b : α} (hab : funReflTransGen f a b)
  : funReflTransGen (Fintype.bijInv hf) a b := by{
    induction hab with
    | refl => exact ReflTransGen.refl
    | @tail c b hac hcb ih => {
      apply ih.trans
      rw[←fromFun_bijInv_iff hf] at hcb
      have hcb':=ReflTransGen.single hcb
      have hcb'':=funReflTransGen_symm_of_injective (Fintype.bijective_bijInv hf).left hcb'
      exact hcb''
    }
  }

theorem Relation.funReflTransGen_bijInv_iff [DecidableEq α] {f : α → α}
  (hf : Bijective f) : funReflTransGen (Fintype.bijInv hf) = funReflTransGen f := by{
    ext a b
    unfold funReflTransGen
    apply (Iff.intro · (funReflTransGen_bijInv hf))
    intro hab
    have hab':=funReflTransGen_bijInv (Fintype.bijective_bijInv hf) hab
    rw[Fintype.bijInv_bijInv hf] at hab'
    exact hab'
  }

def Function.minimalPeriod' [DecidableEq α] (f : α → α) (x : α) : ℕ :=
  if h : x ∈ periodicPts f then Nat.find h else 0
theorem Function.minimalPeriod'_eq_minimalPeriod [DecidableEq α] {f : α → α}
  : minimalPeriod' f = minimalPeriod f := by{
  funext x
  rw [minimalPeriod', minimalPeriod]
  split_ifs with h
  · congr
  · rfl
}
theorem Function.minimalPeriod'_pos_iff_mem_periodicPts [DecidableEq α] {f : α → α} {x : α} :
  0 < minimalPeriod' f x ↔ x ∈ periodicPts f := by{
    rw[minimalPeriod'_eq_minimalPeriod]
    exact minimalPeriod_pos_iff_mem_periodicPts
  }
theorem Function.minimalPeriod'_pos_of_mem_periodicPts [DecidableEq α] {f : α → α} {x : α}
  (hx : x ∈ periodicPts f) : 0 < minimalPeriod' f x
  := minimalPeriod'_pos_iff_mem_periodicPts.mpr hx
theorem Function.Injective.minimalPeriod'_pos [DecidableEq α] {f : α → α} (hf : Injective f)
  {x : α} : 0 < minimalPeriod' f x := by{
    apply minimalPeriod'_pos_of_mem_periodicPts
    apply hf.mem_periodicPts
  }
theorem Fintype.bijInv_IsFixedPt [DecidableEq α] {f : α → α} (hf : Bijective f)
  {x : α} : IsFixedPt (bijInv hf) x ↔ IsFixedPt f x:=by{
    unfold IsFixedPt
    rw[←hf.injective.eq_iff, rightInverse_bijInv hf, Eq.comm]
  }
theorem Fintype.bijInv_IsPeriodicPt [DecidableEq α] {f : α → α} (hf : Bijective f)
  {x : α} {n : ℕ} : IsPeriodicPt (bijInv hf) n x ↔ IsPeriodicPt f n x:=by{
    unfold IsPeriodicPt
    rw[←iterate_bijInv hf]
    exact bijInv_IsFixedPt (hf.iterate n)
  }
theorem Fintype.bijInv_minimalPeriod' [DecidableEq α] {f : α → α} (hf : Bijective f)
  : minimalPeriod' (bijInv hf) = minimalPeriod' f:=by{
    ext x
    rw[minimalPeriod'_eq_minimalPeriod]
    rw[minimalPeriod'_eq_minimalPeriod]
    rw[minimalPeriod_eq_minimalPeriod_iff]
    intro n
    exact bijInv_IsPeriodicPt hf
  }
theorem Fintype.bijInv_minimalPeriod [DecidableEq α] {f : α → α} (hf : Bijective f)
  : minimalPeriod (bijInv hf) = minimalPeriod f:=by{
    rw[←minimalPeriod'_eq_minimalPeriod]
    rw[←minimalPeriod'_eq_minimalPeriod]
    apply Fintype.bijInv_minimalPeriod' hf
  }
theorem Relation.funReflTransGen_conj [DecidableEq α] {f : α → α} (hf : Bijective f) (g : α → α)
  : funReflTransGen ((Fintype.bijInv hf) ∘ g ∘ f) = ReflTransGen (InvImage (fromFun g) f) := by{
    ext a b
    unfold funReflTransGen
    constructor
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hac hcb ih => {
        apply ih.tail
        simp only [InvImage, fromFun]
        simp only [fromFun, comp_apply] at hcb
        rw[←hf.injective.eq_iff] at hcb
        rw[Fintype.rightInverse_bijInv hf] at hcb
        exact hcb
      }
    }
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hac hcb ih => {
        apply ih.tail
        simp only [fromFun, comp_apply]
        simp only [fromFun, InvImage] at hcb
        rw[←hf.injective.eq_iff]
        rw[Fintype.rightInverse_bijInv hf]
        exact hcb
      }
    }
  }

theorem Finite.funReflTransGen_injective_equivalence {α : Type _} [Finite α]
  {f : α → α} (hf : Injective f)
  : Equivalence (funReflTransGen f) where
  refl:=fun _ => ReflTransGen.refl
  trans:=ReflTransGen.trans
  symm:=funReflTransGen_symm_of_injective hf
def Fintype.injective_setoid {f : α → α} (hf : Injective f):Setoid α where
  r:=funReflTransGen f
  iseqv:=Finite.funReflTransGen_injective_equivalence hf
@[inline] instance Fintype.injective_setoid.decidable [DecidableEq α] {f : α → α} (hf : Injective f)
  :DecidableRel (injective_setoid hf):=
  fun a b => by{
    unfold injective_setoid
    apply Relation.funReflTransGen.finDec
  }

theorem List.isChain_bijInv_iff_isChain_reverse [DecidableEq α] {l : List α} {f : α → α}
  (hf : Bijective f)
  : List.IsChain (fromFun (Fintype.bijInv hf)) l ↔ List.IsChain (fromFun f) l.reverse := by{
    match l with
    | [] | [_] => simp
    | a :: b :: t => {
      rw[List.isChain_cons_cons]
      rw[List.reverse_cons, List.reverse_cons]
      rw[List.isChain_concat_append]
      rw[←List.reverse_cons]
      rw[and_comm]
      apply and_congr
      · apply isChain_bijInv_iff_isChain_reverse hf
      · {
        simp only [fromFun, isChain_cons_cons, IsChain.singleton, and_true]
        rw[←hf.injective.eq_iff, Fintype.rightInverse_bijInv hf, Eq.comm]
      }
    }
  }
end Fintype
theorem Function.iterate_isPeriodicPt {α : Type _} {f : α → α}
  {x : α} {n : ℕ} (hp : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f n (f^[m] x) := by{
    rw[IsPeriodicPt, IsFixedPt] at *
    rw[←iterate_add_apply, add_comm, iterate_add_apply, hp]
  }
section Finite
variable {α : Type _}
variable [Finite α]
theorem Function.minimalPeriod_eq_of_funReflTransGen_injective {f : α → α} (hf : Injective f)
  {x y : α} (hxy : funReflTransGen f x y) : minimalPeriod f x = minimalPeriod f y := by{
    have hyx:=funReflTransGen_symm_of_injective hf hxy
    rw[funReflTransGen_iff_iterate] at hxy hyx
    have ⟨n, hxyn⟩:=hxy
    have ⟨m, hyxm⟩:=hyx
    rw[minimalPeriod_eq_minimalPeriod_iff]
    intro k
    constructor
    · {
      intro hkx
      rw[←hxyn]
      apply iterate_isPeriodicPt
      exact hkx
    }
    · {
      intro hky
      rw[←hyxm]
      apply iterate_isPeriodicPt
      exact hky
    }
  }
end Finite

-- skip

section Fintype
variable {α : Type _}
variable [DecidableEq α]
def Function.skip' (f : α → α) (x : α) : α → α:=
  fun z => if f z = x then f (f z) else f z
theorem Function.skip'_ne {f : α → α} {x y : α} (hf : Injective f) (hy : y ≠ x)
  : skip' f x y ≠ x := by{
    cases (inferInstance:DecidableEq α) (f y) x with
    | isTrue hfu => {
      unfold skip'
      simp only [ne_eq, hfu, ↓reduceIte]
      nth_grewrite 2 [←hfu]
      rw[Eq.comm, hf.eq_iff]
      exact hy
    }
    | isFalse hfu => {
      unfold skip'
      simp only [ne_eq, hfu, ↓reduceIte, not_false_eq_true]
    }
  }
theorem Function.skip'_eq_of_apply_eq {f : α → α} {x y : α} (hy : f y = x)
  : skip' f x y = f (f y) := by{simp[skip', hy]}
theorem Function.skip'_eq_of_apply_ne {f : α → α} {x y : α} (hy : f y ≠ x)
  : skip' f x y = f y := by{simp[skip', hy]}
theorem Relation.funReflTransGen_skip'_ne {f : α → α} {x y z : α}
  (hf : Injective f) (hy : y ≠ x) (hyz : funReflTransGen (skip' f x) y z) : z ≠ x:=by{
    rw[funReflTransGen_iff_iterate] at hyz
    have ⟨n, hn⟩:=hyz
    induction n generalizing z with
    | zero => simp at hn; simp[hn] at hy; simp[hy]
    | succ n' ih => {
      have ih':=@ih ((skip' f x)^[n'] y) ⟨n', rfl⟩ rfl
      rw[←hn, iterate_succ_apply']
      apply skip'_ne hf ih'
    }
  }
lemma Function.skip_proof {f : α → α} {x : α} {u : {a : α // a ≠ x}} (hf : Injective f)
  : skip' f x u.val ≠ x:=by{
    exact skip'_ne hf u.prop
  }
def Function.skip {f : α → α} (hf : Injective f) (x : α) :
  {a : α // a ≠ x} → {a : α // a ≠ x} :=
  fun u => ⟨skip' f x u.val, skip_proof hf⟩
theorem Function.skip_injective {f : α → α} (hf : Injective f) (x : α)
  :Injective (skip hf x):=by{
    intro u v huv
    unfold skip skip' at huv
    simp only [ne_eq, Subtype.mk.injEq] at huv
    cases (inferInstance:DecidableEq α) (f u) x with
    | isTrue hux => cases (inferInstance:DecidableEq α) (f v) x with
      | isTrue hvx => {
        have h:=hux.trans hvx.symm
        simp[hf.eq_iff] at h
        ext
        simp[h]
      }
      | isFalse hvx => {
        have hv:=v.prop.symm
        simp only [hux, ↓reduceIte, hvx, hf.eq_iff] at huv
        contradiction
      }
    | isFalse hux => cases (inferInstance:DecidableEq α) (f v) x with
      | isTrue hvx => {
        have hv:=u.prop
        simp only [hux, ↓reduceIte, hvx, hf.eq_iff] at huv
        contradiction
      }
      | isFalse hvx => {
        simp[hux, hvx] at huv
        simp[hf.eq_iff] at huv
        ext
        simp[huv]
      }
  }
theorem Function.skip_iff_skip' {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : skip hf x u = v ↔ skip' f x u = v:=by{
    unfold skip
    simp[Subtype.ext_iff]
  }

theorem Relation.funReflTransGen_skip_iff_skip' {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : funReflTransGen (skip hf x) u v
     ↔ funReflTransGen (skip' f x) u v:=by{
      unfold funReflTransGen
      constructor
      · exact ReflTransGen.lift Subtype.val fun _ _ => (skip_iff_skip' hf).mp
      · {
        intro h
        generalize h_u : u.val = u_val at h
        generalize h_v : v.val = v_val at h
        induction h generalizing u v with
        | refl =>
          change ReflTransGen (fromFun (skip hf x)) ⟨u.val, u.prop⟩ ⟨v.val, v.prop⟩
          simp only [h_u, h_v]
          rfl
        | @tail b c huw hwv ih => {
          have hb:b ≠ x:=by{
            apply funReflTransGen_skip'_ne hf u.prop
            rw[h_u]
            exact huw
          }
          have ih':=ih (v:=⟨b, hb⟩) h_u rfl
          apply ih'.tail
          unfold fromFun
          unfold fromFun at hwv
          rw[skip_iff_skip']
          simp[h_v, hwv]
        }
      }
  }
theorem Relation.funReflTransGen_skip {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : funReflTransGen (skip hf x) u v
  ↔ funReflTransGen f u v:=by{
    constructor
    · {
      unfold funReflTransGen
      intro h
      induction h with
      | refl => rfl
      | @tail c b hac hcb ih => {
        apply ih.trans
        unfold fromFun at hcb
        rw[skip_iff_skip'] at hcb
        unfold skip' at hcb
        match (inferInstance:DecidableEq α) (f c.val) x with
        | isTrue hfcx => {
          simp[hfcx] at hcb
          have hfcx':=ReflTransGen.single (r:=fromFun f) hfcx
          simp[hfcx'.tail hcb]
        }
        | isFalse hfcx => {
          simp[hfcx] at hcb
          apply ReflTransGen.single
          simp[fromFun, hcb]
        }
      }
    }
    · {
      rw[funReflTransGen_skip_iff_skip']
      intro h
      generalize hu : u.val = u_val at h
      generalize hv : v.val = v_val at h
      let inst':DecidableEq α:=inferInstance
      induction h generalizing u v with
      | refl => apply ReflTransGen.refl
      | @tail b c huw hwv ih => {
        cases inst' b x with
        | isTrue hb => {
          have huw':funReflTransGen f u_val b:=huw
          rw[funReflTransGen_iff_iterate_minimal] at huw'
          have ⟨n, hn, hn'⟩:=huw'
          unfold fromFun at hwv
          match n with
          | 0 => simp[←hu, hb, u.prop] at hn
          | n' + 1 => {
            rw[iterate_succ_apply'] at hn
            simp only [Nat.lt_succ_iff] at hn'
            apply ReflTransGen.tail (b:=f^[n'] u_val)
            · {
              have h_step : ∀ m < n', skip' f x (f^[m] u_val) = f (f^[m] u_val) := by
                intro m hm
                unfold skip'
                have h_not_x : f (f^[m] u_val) ≠ x := by
                  rw [←iterate_succ_apply' f m]
                  exact hb ▸ hn' m.succ (Nat.succ_le_of_lt hm)
                simp [h_not_x]
              have h_step'':∀m ≤ n', ReflTransGen (fromFun (skip' f x)) u_val (f^[m] u_val):=by{
                intro m hmn
                induction m with
                | zero => rfl
                | succ m' ihm => {
                  apply ReflTransGen.tail (b:=f^[m'] u_val)
                  · {
                    apply ihm
                    exact Nat.le_of_succ_le hmn
                  }
                  · {
                    unfold fromFun
                    rw[h_step _ (Nat.lt_of_succ_le hmn), iterate_succ_apply']
                  }
                }
              }
              exact h_step'' n' (by rfl)
            }
            · {
              unfold fromFun skip'
              simp[hn, hb]
              simp[←hb, hwv]
            }
          }
        }
        | isFalse hb => {
          have ih':=ih (v:=⟨b, hb⟩) hu rfl
          apply ih'.tail
          unfold skip'
          unfold fromFun at hwv
          simp[hwv, ←hv, v.prop]
        }
      }
    }
  }
theorem Function.skip_eq_of_apply_ne {f : α → α} {x : α} (hf : Injective f) {u : {a // a ≠ x}}
  (hu : f u ≠ x) : skip hf x u = ⟨f u, hu⟩ := by{
    unfold skip
    simp only [ne_eq, Subtype.mk.injEq]
    exact skip'_eq_of_apply_ne hu
  }
theorem Function.skip_eq_of_apply_eq {f : α → α} {x : α} (hf : Injective f) {u : {a // a ≠ x}}
  (hu : f u = x) : skip hf x u = ⟨f (f u), by{
    rw[hu]
    intro hn
    have hn':=hu.trans hn.symm
    rw[hf.eq_iff] at hn'
    exact u.prop hn'
  }⟩ := by{
    unfold skip
    simp only [ne_eq, Subtype.mk.injEq]
    exact skip'_eq_of_apply_eq hu
  }
theorem Function.skip_eq_of_eq {f : α → α} {x : α} (hf : Injective f)
  {u v : {a // a ≠ x}} (huv : f u = v) : skip hf x u = v:=by{
    have huv':=huv ▸ v.prop
    have huv'':=skip_eq_of_apply_ne hf huv'
    rw[huv'']
    simp[huv]
  }
theorem Function.skip_val {f : α → α} {x : α} (hf : Injective f)
  {u : {a // a ≠ x}} : (skip hf x u).val = skip' f x u:=by{
    unfold skip
    rfl
  }
variable [Fintype α]
theorem Finite.skip_bijective {α : Type _} [Finite α] [DecidableEq α] {f : α → α}
  (hf : Injective f) (x : α) : Bijective (skip hf x) :=
  let :Finite α:=inferInstance
  (skip_injective hf x).bijective_of_finite
def Fintype.skip_setoid {f : α → α} (hf : Injective f) (x : α)
  : Setoid {a // a ≠ x} :=
  Setoid.mk (funReflTransGen (skip hf x))
  (Finite.funReflTransGen_injective_equivalence (skip_injective hf x))
@[inline] instance Fintype.skip_setoid.finDec {f : α → α} (hf : Injective f) {x : α}
  : DecidableRel (skip_setoid hf x) :=
  fun _ _ => by{
    unfold skip_setoid
    apply funReflTransGen.finDec
  }
theorem Fintype.nComp_skip_setoid {f : α → α} {hf : Injective f} {x : α}
  : nComp (skip_setoid hf x) + (if f x = x then 1 else 0) = nComp (injective_setoid hf):= by{
    cases (inferInstance:DecidableEq α) (f x) x with
    | isTrue hx => {
      unfold nComp
      simp only [ne_eq, hx, ↓reduceIte]
      have e:Quotient (skip_setoid hf x) ⊕ Unit ≃ Quotient (injective_setoid hf):=by{
        have toFun_proof:∀ (a b : { a // a ≠ x }), (skip_setoid hf x) a b →
        (Quotient.mk (injective_setoid hf) ∘ Subtype.val) a =
        (Quotient.mk (injective_setoid hf) ∘ Subtype.val) b:=by{
          intro ⟨a, ha⟩ ⟨b, hb⟩ hab
          unfold skip_setoid at hab
          simp only [ne_eq, funReflTransGen_skip] at hab
          simp only [ne_eq, comp_apply, Quotient.eq_iff_equiv]
          exact hab
        }
        let toFun:Quotient (skip_setoid hf x) ⊕ Unit → Quotient (injective_setoid hf):=
          fun q => match q with
            | Sum.inl q' => Quotient.lift (Quotient.mk (injective_setoid hf) ∘ Subtype.val)
              toFun_proof q'
            | Sum.inr q' => Quotient.mk (injective_setoid hf) x
        have invFun_proof:∀ (a b : α), (injective_setoid hf) a b →
        (fun a ↦ if ha : a = x then Sum.inr () else Sum.inl ⟦Subtype.mk a ha⟧) a =
        (fun a ↦ if ha : a = x then Sum.inr () else Sum.inl ⟦(⟨a, ha⟩:{a // a ≠ x})⟧) b:=by{
          intro a b hab
          simp only [ne_eq, apply_dite, dite_eq_left_iff, reduceCtorEq, imp_false,
            Decidable.not_not]
          unfold injective_setoid at hab
          simp only at hab
          cases em (b = x) with
          | inl hbx => {
            simp[hbx]
            have hab':=funReflTransGen_symm_of_injective hf hab
            rw[hbx, funReflTransGen_idemp hx] at hab'
            simp[hab']
          }
          | inr hbx => {
            have hax:a ≠ x:=by{
              intro ha
              simp[ha, funReflTransGen_idemp hx] at hab
              simp[hab] at hbx
            }
            simp only [hax, ↓reduceDIte, Sum.inl.injEq, dite_then_false]
            simp only [Quotient.eq_iff_equiv, hbx, not_false_eq_true, exists_true_left]
            change (skip_setoid hf x) ⟨a, hax⟩ ⟨b, hbx⟩
            unfold skip_setoid
            simp[funReflTransGen_skip, hab]
          }
        }
        let invFun:Quotient (injective_setoid hf) → Quotient (skip_setoid hf x) ⊕ Unit:=
          Quotient.lift (fun a => if ha:a = x then Sum.inr () else
            Sum.inl (Quotient.mk (skip_setoid hf x) ⟨a, ha⟩)) invFun_proof
        have left_inv:LeftInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          match q with
          | Sum.inl q' => {
            simp only [ne_eq]
            rw[←Quotient.out_eq q', Quotient.lift_mk]
            simp[q'.out.prop]
          }
          | Sum.inr q' => simp
        }
        have right_inv:RightInverse invFun toFun:=by{
          intro q
          rw[←Quotient.out_eq q]
          unfold toFun invFun
          rw[Quotient.lift_mk]
          cases em (q.out = x) with
          | inl hqx | inr hqx => simp[hqx]
        }
        exact ⟨toFun, invFun, left_inv, right_inv⟩
      }
      have he:=ofEquiv_card e
      simp only [ne_eq, card_sum, card_unique] at he
      rw[Eq.comm] at he
      apply (Eq.mp · he)
      congr
      apply Subsingleton.elim
    }
    | isFalse hx => {
      simp only [ne_eq, hx, ↓reduceIte, add_zero]
      unfold nComp
      simp only
      have e:Quotient (skip_setoid hf x) ≃ Quotient (injective_setoid hf):=by{
        have toFun_proof:∀ (a b : { a // a ≠ x }), (skip_setoid hf x) a b →
          (Quotient.mk (injective_setoid hf) ∘ Subtype.val) a =
          (Quotient.mk (injective_setoid hf) ∘ Subtype.val) b :=by{
            intro a b hab
            unfold skip_setoid at hab
            simp only [ne_eq] at hab
            rw[funReflTransGen_skip] at hab
            simp only [ne_eq, comp_apply]
            rw[Quotient.eq_iff_equiv]
            exact hab
        }
        let toFun:Quotient (skip_setoid hf x) → Quotient (injective_setoid hf):=
          Quotient.lift (Quotient.mk (injective_setoid hf) ∘ Subtype.val) toFun_proof
        have invFun_proof:∀ (a b : α), (injective_setoid hf) a b →
        (Quotient.mk (skip_setoid hf x) ∘ fun a ↦ if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩) a =
        (Quotient.mk (skip_setoid hf x) ∘ fun a ↦ if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩) b:=by{
          intro a b hab
          unfold injective_setoid at hab
          simp only at hab
          simp only [ne_eq, comp_apply]
          rw[Quotient.eq_iff_equiv]
          change (skip_setoid hf x) (if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩)
            (if hb : b = x then ⟨f x, hx⟩ else ⟨b, hb⟩)
          unfold skip_setoid
          simp only [ne_eq]
          rw[funReflTransGen_skip]
          simp only [ne_eq, apply_dite, dite_eq_ite]
          rw[apply_ite (funReflTransGen f _)]
          simp only [apply_ite (funReflTransGen f), ite_apply]
          unfold funReflTransGen
          simp only [ReflTransGen.refl, if_true_left]
          unfold funReflTransGen at hab
          simp only [hab, if_true_right]
          cases em (b = x) with
          | inl hbx => {
            simp only [hbx, ↓reduceIte]
            simp only [← hbx]
            intro _
            apply ReflTransGen.tail hab
            rfl
          }
          | inr hbx => {
            simp only [hbx, ↓reduceIte]
            intro hax
            simp only [← hax]
            apply (ReflTransGen.trans · hab)
            apply (Finite.funReflTransGen_injective_equivalence hf).symm
            apply ReflTransGen.single
            rfl
          }
        }
        let invFun:Quotient (injective_setoid hf) → Quotient (skip_setoid hf x):=
          Quotient.lift (Quotient.mk (skip_setoid hf x) ∘
          (fun a => if ha:a = x then ⟨f x, hx⟩ else ⟨a, ha⟩)) invFun_proof
        have left_inv:LeftInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          rw[←Quotient.out_eq q]
          rw[Quotient.lift_mk]
          simp only [ne_eq, comp_apply, Quotient.lift_mk, Subtype.coe_eta, dite_eq_ite,
            Quotient.out_eq]
          rw[Eq.comm, ←Quotient.out_eq q]
          rw[Quotient.eq_iff_equiv]
          simp only [ne_eq, Quotient.out_eq, apply_ite, Setoid.refl, if_true_right]
          intro h
          change (skip_setoid hf x) q.out ⟨f x, hx⟩
          unfold skip_setoid
          simp only [ne_eq, funReflTransGen_skip]
          apply ReflTransGen.single
          exact h.symm ▸ rfl
        }
        have right_inv:RightInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          rw[←Quotient.out_eq q]
          rw[Quotient.lift_mk]
          simp only [ne_eq, comp_apply, Quotient.lift_mk, Quotient.out_eq]
          rw[Eq.comm, ←Quotient.out_eq q]
          rw[Quotient.eq_iff_equiv]
          rw[apply_dite Subtype.val]
          simp only [Quotient.out_eq, dite_eq_ite]
          simp only [apply_ite, Setoid.refl, if_true_right]
          intro h
          apply ReflTransGen.single
          exact h ▸ rfl
        }
        let e': Quotient (skip_setoid hf x) ≃ Quotient (injective_setoid hf) :={
          toFun:=toFun,
          invFun:=invFun,
          left_inv:=left_inv,
          right_inv:=right_inv
        }
        exact e'
      }
      have he:=ofEquiv_card e.symm
      apply (Eq.mp · he)
      congr
      apply Subsingleton.elim
    }
  }
theorem Fintype.bijInv_eq_iff_eq_apply {f : α → α} (hf : Bijective f) (x y : α)
  : bijInv hf x = y ↔ x = f y := by{
    nth_rw 1 [←hf.injective.eq_iff]
    rw[rightInverse_bijInv hf]
  }
theorem Fintype.eq_bijInv_iff_apply_eq {f : α → α} (hf : Bijective f) (x y : α)
  : x = bijInv hf y ↔ f x = y := by{
    rw[Eq.comm (a:=x), Eq.comm (b:=y)]
    exact bijInv_eq_iff_eq_apply hf y x
  }
theorem Fintype.skip_bijInv_comm {f : α → α} (hf : Bijective f) {x : α}
  : skip (bijective_bijInv hf).injective x = bijInv (Finite.skip_bijective hf.injective x) := by{
    apply funext
    intro u
    rw[eq_bijInv_iff_apply_eq]
    ext
    rw[skip_val, skip_val]
    unfold skip'
    simp only[bijInv_eq_iff_eq_apply]
    rw[apply_ite f]
    rw[rightInverse_bijInv hf]
    rw[rightInverse_bijInv hf]
    rw[apply_ite f]
    rw[rightInverse_bijInv hf]
    simp only [apply_ite (· = x), u.prop]
    simp only [ne_eq, if_false_right]
    cases em (u = f x) with
    | inl hux => {
      simp[hux]
      simp[leftInverse_bijInv hf x]
    }
    | inr hux => simp[hux]
  }
end Fintype
