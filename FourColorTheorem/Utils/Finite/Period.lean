import FourColorTheorem.Utils.Finite.Chain

open Relation
open Function

section Finite

end Finite
section Fintype
variable {α : Type _} [Finite α]
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
      apply IsPeriodicPt.apply_iterate
      exact hkx
    }
    · {
      intro hky
      rw[←hyxm]
      apply IsPeriodicPt.apply_iterate
      exact hky
    }
  }
end Fintype

section Fintype
variable {α : Type _} [Fintype α]
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
end Fintype
