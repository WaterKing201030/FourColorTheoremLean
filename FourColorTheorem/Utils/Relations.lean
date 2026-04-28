import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Order.Minimal
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
def Relation.funReflTransGen (f : α → α) : α → α → Prop
  := ReflTransGen (fromFun f)
theorem Relation.funReflTransGen_iff {f : α → α} {a b : α} :
  Relation.funReflTransGen f a b ↔ ReflTransGen (fromFun f) a b := by rfl
theorem Relation.funReflTransGen.rfl {f : α → α} {a : α} : funReflTransGen f a a :=
  ReflTransGen.refl
theorem Relation.funReflTransGen.refl {f : α → α} (a : α) : funReflTransGen f a a :=
  funReflTransGen.rfl
theorem Relation.funReflTransGen.trans {f : α → α} {a b c : α} :
  funReflTransGen f a b → funReflTransGen f b c → funReflTransGen f a c
  := ReflTransGen.trans
theorem Relation.funReflTransGen.single (f : α → α) (a : α) :
  funReflTransGen f a (f a) := ReflTransGen.single (by{simp[fromFun]})
instance Relation.funReflTransGen.instRefl {f : α → α} : Std.Refl (funReflTransGen f) where
  refl := funReflTransGen.refl
instance Relation.funReflTransGen.instTrans {f : α → α} : IsTrans α (funReflTransGen f) where
  trans := fun _ _ _ =>funReflTransGen.trans
theorem Relation.funReflTransGen.tail {f : α → α} {a b c : α} :
  funReflTransGen f a b → f b = c → funReflTransGen f a c
  := ReflTransGen.tail
theorem Relation.funReflTransGen.head {f : α → α} {a b c : α} :
  f a = b → funReflTransGen f b c → funReflTransGen f a c
  := (ReflTransGen.head ·)
theorem Relation.funReflTransGen.ofFun (f : α → α) (a : α) : funReflTransGen f a (f a) :=
  ReflTransGen.single (fromFun_of_fun f a)
theorem Relation.funReflTransGen_iff_iterate {f : α → α} {a b : α} :
  funReflTransGen f a b ↔ ∃ n, (f^[n]) a = b := by{
    constructor
    · {
      intro h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail hab hbc ih => {
        have ⟨n, ih⟩ := ih
        use n + 1
        rw[iterate_succ_apply', ih, hbc]
      }
    }
    · {
      intro ⟨n, hn⟩
      induction n generalizing a with
      | zero => rw[←hn]; exact funReflTransGen.refl a
      | succ n ih => {
        rw[iterate_succ_apply] at hn
        have h := ih hn
        apply funReflTransGen.trans (funReflTransGen.ofFun f a) h
      }
    }
  }
theorem Relation.funReflTransGen_iff_iterate_minimal {f : α → α} {a b : α} :
  funReflTransGen f a b ↔ ∃ n, f^[n] a = b ∧ ∀m < n, f^[m] a ≠ b := by{
    rw[funReflTransGen_iff_iterate]
    constructor
    · {
      intro hn
      classical
      use Nat.find hn
      apply And.intro (Nat.find_spec hn)
      intro _
      exact Nat.find_min hn
    }
    · {
      intro ⟨n, hn, _⟩
      exact ⟨n, hn⟩
    }
  }
theorem Relation.funReflTransGen_idemp {f : α → α} {a b : α}
  (ha : f a = a) : funReflTransGen f a b ↔ a = b:=by{
    rw[funReflTransGen_iff_iterate]
    simp[iterate_fixed ha]
  }
theorem Relation.funReflTransGen.iterate {f : α → α} {a : α} {n : ℕ}
  : funReflTransGen f a (f^[n] a) := by{
    apply funReflTransGen_iff_iterate.mpr
    use n
  }
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

theorem Relation.ReflTranGen_Symm_of_Symm {r : α → α → Prop} (hr : Std.Symm r) :
  Std.Symm (ReflTransGen r) := by{
  apply Std.Symm.mk
  intro a b h
  induction h with
  | refl => exact ReflTransGen.refl
  | tail hab hbc ih => {
    have hba := hr.symm _ _ hbc
    exact ReflTransGen.head hba ih
  }
  }
theorem Relation.union_Symm_of_Symm {r1 r2 : α → α → Prop} (hr1 : Std.Symm r1) (hr2 : Std.Symm r2) :
  Std.Symm (r1 ∪ r2) := by{
  apply Std.Symm.mk
  intro a b h
  rw[union_iff] at h
  cases h with
  | inl hr1ab => exact union_iff.mpr (Or.inl (hr1.symm _ _ hr1ab))
  | inr hr2ab => exact union_iff.mpr (Or.inr (hr2.symm _ _ hr2ab))
}
theorem Relation.ReflTransGen_union_subset {r1 r2 : α → α → Prop}
  : ReflTransGen r1 ∪ ReflTransGen r2 ⊆ ReflTransGen (r1 ∪ r2) := by{
  intro a b h
  rw[union_iff] at h
  cases h with
  | inl hr1ab => {
    induction hr1ab with
    | refl => exact ReflTransGen.refl
    | tail hab hbc ih => exact ih.tail (Or.inl hbc)
  }
  | inr hr2ab => {
    induction hr2ab with
    | refl => exact ReflTransGen.refl
    | tail hab hbc ih => exact ih.tail (Or.inr hbc)
  }
  }
theorem Relation.ReflTransGen_subset {r1 r2 : α → α → Prop} (h : r1 ⊆ r2)
: ReflTransGen r1 ⊆ ReflTransGen r2 := by{
  intro a b h'
  induction h' with
  | refl => exact ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h hbc)
}
theorem Relation.ReflTransGen_union_eq_ReflTransGen_union_ReflTransGen {r1 r2 : α → α → Prop}
  : ReflTransGen (r1 ∪ r2) = ReflTransGen (ReflTransGen r1 ∪ ReflTransGen r2) := by{
  ext a b
  constructor
  · {
    intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail hab hbc ih => {
      rw[union_iff] at hbc
      apply ih.tail
      rw[union_iff]
      exact hbc.imp ReflTransGen.single ReflTransGen.single
    }
  }
  · {
    intro h
    rw[←Relation.reflTransGen_idem]
    exact ReflTransGen_subset ReflTransGen_union_subset h
  }
  }

theorem Relation.ReflTransGen_iff_isChain {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, List.IsChain r (a::l) ∧ l.getLastD a = b := by{
    constructor
    · {
      intro h
      induction h using ReflTransGen.head_induction_on with
      | refl => exact ⟨[], List.IsChain.singleton b, rfl⟩
      | @head a c hab hbc ih => {
        have ⟨l, hlc, hld⟩:=ih
        use c::l
        rw[List.isChain_cons_cons]
        rw[List.getLastD_cons]
        constructor
        · exact ⟨hab, hlc⟩
        · exact hld
      }
    }
    · {
      intro ⟨l, hl, hr⟩
      induction l generalizing a with
      | nil => rw[List.getLastD_nil] at hr; rw[hr]
      | cons c l' ih => {
        rw[List.getLastD_cons] at hr
        rw[List.isChain_cons_cons] at hl
        have ih':=ih hl.right hr
        exact ReflTransGen.head hl.left ih'
      }
    }
  }

theorem Relation.ReflTransGen_iff_isChain_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, List.IsChain r l ∧ l.head? = some a ∧ l.getLast? = some b
  := by{
    rw[ReflTransGen_iff_isChain]
    constructor
    · {
      intro ⟨l, hl, hr⟩
      use (a::l)
      rw[List.getLast?_cons_eq_getLastD, hr]
      simp[hl]
    }
    · {
      intro ⟨l, hl, hh, hd⟩
      have hl':l ≠ []:=by{intro hh; simp[hh] at hd}
      use l.tail
      match l with
      | a'::l' => {
        rw[List.tail_cons]
        rw[List.head?_cons] at hh
        rw[List.getLast?_cons_eq_getLastD] at hd
        rw[Option.some_inj] at hh hd
        rw[←hh]
        exact ⟨hl, hd⟩
      }
    }
  }


theorem Relation.ReflTransGen_iff_isChain_nodup_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, l.Nodup ∧ List.IsChain r l
  ∧ l.head? = some a ∧ l.getLast? = some b := by{
    rw[ReflTransGen_iff_isChain_option]
    constructor
    · {
      intro ⟨l, hc, hh, hd⟩
      have ⟨l', hs', hp', hc', hh', hd'⟩:=List.isChain_exists_shorterChain_option hc
      use l'
      apply And.intro hp'
      apply And.intro hc'
      apply And.intro (hh'.trans hh)
      exact hd'.trans hd
    }
    · {
      intro ⟨l, _, hc, hd⟩
      exact ⟨l, hc, hd⟩
    }
  }
theorem Relation.ReflTransGen_iff_isChain_nodup {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, (a::l).Nodup ∧ List.IsChain r (a::l)
  ∧ l.getLastD a = b := by{
    rw[ReflTransGen_iff_isChain_nodup_option]
    constructor
    · {
      intro ⟨l, hp, hc, hh, hd⟩
      have hl:l ≠ []:=by{intro hl; simp[hl] at hh}
      use l.tail
      have ha:l.head hl = a:=by{match l with | a'::_ => simp at hh; simp[hh]}
      rw[←ha, List.cons_head_tail hl]
      apply And.intro hp
      apply And.intro hc
      rw[←Option.some_inj]
      rw[←List.getLast?_cons_eq_getLastD]
      rw[List.cons_head_tail hl]
      exact hd
    }
    · {
      intro ⟨l, hp, hc, hd⟩
      use a::l
      apply And.intro hp
      apply And.intro hc
      apply And.intro rfl
      rw[List.getLast?_cons_eq_getLastD, hd]
    }
  }

theorem Relation.ReflTransGen_iff_isChain_minimal_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, List.IsChain r l
  ∧ l.head? = some a ∧ l.getLast? = some b ∧ ∀l':List α, List.IsChain r l' ∧ l'.head? = some a
  ∧ l'.getLast? = some b → l'.length ≥ l.length:=by{
    rw[ReflTransGen_iff_isChain_option]
    constructor
    · {
      intro ⟨l, hl⟩
      have h:∃n, ∃l:List α, l.length = n ∧ List.IsChain r l ∧ l.head? = some a
        ∧ l.getLast? = some b:=by{
        use l.length
        use l
      }
      have h':=exists_minimal_of_wellFoundedLT _ h
      unfold Minimal at h'
      simp only at h'
      have ⟨n', ⟨l', hl'⟩, hn'⟩:=h'
      use l'
      simp only [hl', true_and]
      intro l'' hl''
      have hn'':=hn' ⟨l'', rfl, hl''⟩
      have ht:=Nat.le_total l''.length n'
      exact ht.elim hn'' id
    }
    · {
      intro ⟨l, hl0, hl1, hl2, _⟩
      exact ⟨l, hl0, hl1, hl2⟩
    }
  }
theorem Relation.ReflTransGen_iff_isChain_minimal_nodup_option {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, l.Nodup ∧ List.IsChain r l
  ∧ l.head? = some a ∧ l.getLast? = some b ∧ ∀l':List α, List.IsChain r l' ∧ l'.head? = some a
  ∧ l'.getLast? = some b → l'.length ≥ l.length:=by{
    rw[ReflTransGen_iff_isChain_minimal_option]
    constructor
    · {
      intro ⟨l, h0, h1, h2, h3⟩
      use l
      apply (And.intro · ⟨h0, h1, h2, h3⟩)
      rw[List.nodup_iff_getElem?_ne_getElem?]
      intro i j hij hjl hlij
      let l':=l.take i ++ l.drop j
      have h0':List.IsChain r l':=by{
        unfold l'
        match i with
        | 0 => {
          simp only [List.take_zero, List.nil_append]
          apply List.isChain_drop
          exact h0
        }
        | i' + 1 => {
          have h:l.take (i' + 1) ≠ []:=by{
            simp[List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hjl)]
          }
          have h':l.drop j ≠ []:=by{simp[hjl]}
          let la:=l.take (i' + 1)
          generalize hlb: l.drop j = lb
          rw[hlb] at h'
          match lb with
          | b::lb' => {
            rw[List.isChain_append_cons]
            rw[←hlb]
            apply (And.intro · (List.isChain_drop h0))
            rw[List.isChain_concat_iff_of_ne_nil h]
            apply And.intro (List.isChain_take h0)
            rw[List.take_getLast h]
            have hb:b=l[j]'hjl:=by{
              have hlb':List.head _ (hlb.symm ▸ h') = List.head (b::lb') (by{simp}):=by{
                congr
              }
              simp at hlb'
              simp[hlb']
            }
            rw[hb]
            simp only [List.getElem?_eq_getElem hjl] at hlij
            simp only [List.getElem?_eq_getElem (Nat.lt_trans hij hjl), Option.some.injEq] at hlij
            rw[←hlij]
            have hm:min l.length (i' + 1) - 1 = i':=by{
              omega
            }
            simp only [hm]
            exact List.isChain_iff_getElem.mp h0 i' (Nat.lt_trans hij hjl)
          }
        }
      }
      have h1':l'.head? = some a:=by{
        unfold l'
        match i with
        | 0 => {
          simp only [List.take_zero, List.nil_append, List.head?_drop, ← hlij]
          match l with
          | _::_ => {
            simp at h1
            simp[h1]
          }
        }
        | _ + 1 => {
          match l with
          | _::_ => {
            simp at h1
            simp[h1]
          }
        }
      }
      have h2':l'.getLast? = some b:=by{
        unfold l'
        rw[←List.take_append_drop j l] at h2
        simp only [List.getLast?_append, Option.or_eq_some_iff,
        List.getLast?_eq_none_iff, List.drop_eq_nil_iff, Nat.not_le_of_gt hjl,
        false_and, or_false] at h2
        simp[h2]
      }
      have h3':=h3 l' ⟨h0', h1', h2'⟩
      unfold l' at h3'
      simp[min_eq_left_of_lt (Nat.lt_trans hij hjl), ←Nat.add_sub_assoc (Nat.le_of_lt hjl)] at h3'
      simp[Nat.le_sub_iff_add_le (Nat.le_add_left_of_le (Nat.le_of_lt hjl))] at h3'
      simp[Nat.add_comm _ j, Nat.not_le_of_gt hij] at h3'
    }
    · {
      intro ⟨l, _, h0⟩
      exact ⟨l, h0⟩
    }
  }

@[inline] instance InvImage.instDecidableRel {β : Type _} {ra : α → α → Prop} [DecidableRel ra]
  (e : β → α) : DecidableRel (InvImage ra e) :=
  fun a b => (inferInstance:DecidableRel ra) (e a) (e b)
@[inline] instance Equiv.instDecidableRel {β : Type _} {ra : α → α → Prop} [DecidableRel ra]
  (e : α ≃ β) : DecidableRel (InvImage ra e.symm) := by infer_instance

@[reducible] def Equiv.decidableRel_of_iff {α β : Type _}
    {ra : α → α → Prop} {rb : β → β → Prop}
    [DecidableRel ra] (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    DecidableRel rb :=
  fun b₁ b₂ =>
    let := (inferInstance:DecidableRel ra) (e.invFun b₁) (e.invFun b₂)
    by{
      rw[eq] at this
      rw[←Equiv.toFun_as_coe, e.right_inv, e.right_inv] at this
      exact this
    }


theorem Relation.ReflTransGen_InvImage_subset {β : Type _} {r : α → α → Prop} {f : β → α}
  : ReflTransGen (InvImage r f) ⊆ InvImage (ReflTransGen r) f := by{
    intro a b hab
    induction hab with
    | refl => unfold InvImage; rfl
    | tail hac hcb ih => exact ih.tail hcb
  }
theorem Relation.ReflTransGen_InvImage_Equiv {β : Type _} {r : α → α → Prop} {f : β ≃ α}
  : ReflTransGen (InvImage r f) = InvImage (ReflTransGen r) f := by{
    ext a b
    unfold InvImage
    constructor
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hac hcb ih => exact ih.tail hcb
    }
    · {
      intro h
      rw[ReflTransGen_iff_isChain] at *
      have ⟨l, hl⟩:=h
      use l.map f.invFun
      have h':=List.IsChain_map (r:=r) (f:=f) (l:=a::l.map f.invFun)
      unfold InvImage at h'
      rw[←h']
      simp only [List.map_cons]
      nth_rw 2 [←f.left_inv a]
      rw[List.getLastD_map]
      apply hl.imp
      · simp
      · {
        intro h''
        apply f.injective
        rw[←f.toFun_as_coe, f.right_inv]
        exact h''
      }
    }
  }

theorem Equiv.ofBijective_coe {β : Type _} {f : α → β} (hf : Bijective f)
  : ofBijective _ hf = f := rfl

@[inline] def Equivalence.ofSubtype {p : α → Prop} {r : α → α → Prop}
  (e : Equivalence r) : Equivalence (α:={a // p a}) (InvImage r Subtype.val)
  where
    refl:=fun ⟨x, _⟩ => e.refl x
    symm:=e.symm
    trans:=e.trans
@[inline] def Setoid.ofSubtype (s : Setoid α) (p : α → Prop) : Setoid {a // p a} :=
  Setoid.mk _ s.iseqv.ofSubtype
@[inline] instance Setoid.ofSubtype.decidable {p : α → Prop} {s : Setoid α} [DecidableRel s]
  : DecidableRel (s.ofSubtype p):=by{
    unfold ofSubtype
    simp only
    apply InvImage.instDecidableRel
  }
theorem Setoid.ofSubtype_iff {p : α → Prop} {s : Setoid α} {u v : {a // p a}} :
  s.ofSubtype p u v ↔ s u v:=by{
    unfold ofSubtype
    simp[InvImage]
  }
