import FourColorTheorem.Utils.Finite.Basic
import FourColorTheorem.Utils.Finite.List

open Relation
open Function

section Fintype
variable {α : Type _}
variable [Fintype α]
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
end Fintype

section Finite
variable {α : Type _}
variable [Finite α]

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
end Finite

section Fintype
variable {α : Type _}
variable [Fintype α]

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

end Fintype
