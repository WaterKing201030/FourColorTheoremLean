import Mathlib.Data.Fintype.Vector
--import Mathlib.Logic.Embedding.Basic
--import FourColorTheorem.Utils.Relations
import FourColorTheorem.Utils.Finite.Basic

open Function
open Relation

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

section vector

variable {α : Type _} [Fintype α]

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

end vector
