import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Order.Minimal
import Mathlib.Dynamics.PeriodicPts.Lemmas
import FourColorTheorem.Utils.Chain
import FourColorTheorem.Utils.Relations.Basic
import FourColorTheorem.Utils.Relations.Equiv

open Relation
open Function

variable {α : Type _}

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
theorem Relation.ReflTransGen_subset {r1 r2 : α → α → Prop} (h : r1 ⊆ r2)
: ReflTransGen r1 ⊆ ReflTransGen r2 := by{
  intro a b h'
  induction h' with
  | refl => exact ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h hbc)
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
theorem Relation.ReflTransGen_iff_isChain_minimal_nodup {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, (a::l).Nodup ∧ List.IsChain r (a::l)
  ∧ l.getLastD a = b ∧ ∀l':List α, List.IsChain r (a::l') ∧ l'.getLastD a = b
  → l'.length ≥ l.length:=by{
    constructor
    · {
      rw[ReflTransGen_iff_isChain_minimal_nodup_option]
      intro ⟨l, h0, h1, h2, h3, h4⟩
      have h5 : l ≠ [] := by{intro h5; simp[h5] at h2}
      match l with
      | a' :: l' => {
        simp only [List.head?_cons, Option.some.injEq] at h2
        rw[List.getLast?_cons_eq_getLastD, Option.some.injEq, h2] at h3
        rw[h2] at h1 h0
        refine ⟨l', h0, h1, h3, ?_⟩
        intro l1'
        specialize h4 (a::l1')
        simp only [List.head?_cons, true_and, List.length_cons, ge_iff_le,
        add_le_add_iff_right] at h4
        rw[List.getLast?_cons_eq_getLastD, Option.some.injEq] at h4
        exact h4
      }
    }
    · {
      intro ⟨l, _, h0, h1, _⟩
      rw[ReflTransGen_iff_isChain]
      use l
    }
  }
theorem Relation.ReflTransGen_iff_isChain_minimal_nodup_last {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, (l ++ [b]).Nodup ∧ List.IsChain r (l ++ [b])
  ∧ l.headD b = a ∧ ∀l':List α, List.IsChain r (l' ++ [b]) ∧ l'.headD b = a
  → l'.length ≥ l.length:=by{
    constructor
    · {
      rw[ReflTransGen_iff_isChain_minimal_nodup_option]
      intro ⟨l, h0, h1, h2, h3, h4⟩
      have h5 : l ≠ [] := by{intro h5; simp[h5] at h2}
      have ⟨l', b', h6⟩:=List.ne_nil_iff_exists_concat.mp h5
      use l'
      simp only [← h6, List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at h3
      simp only [← h3, h6]
      rw[← h6, List.head?_concat_eq_headD, Option.some.injEq] at h2
      refine ⟨h0, h1, h2, ?_⟩
      intro l1'
      specialize h4 (l1' ++ [b])
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, and_true,
      List.length_append, List.length_cons, List.length_nil, zero_add, ge_iff_le] at h4
      rw[List.head?_concat_eq_headD, Option.some_inj, ← h6, ← h3] at h4
      simp only [List.length_append, List.length_cons, List.length_nil,
        zero_add, add_le_add_iff_right] at h4
      exact h4
    }
    · {
      intro ⟨l, _, h0, h1, _⟩
      match l with
      | [] => simp at h1; simp[h1]; rfl
      | a' :: l' => {
        rw[ReflTransGen_iff_isChain]
        use l' ++ [b]
        rw[List.cons_append] at h0
        simp at h1
        simp[h1] at h0
        simp[h0]
      }
    }
  }
theorem Relation.ReflTransGen_iff_isChain_last {r : α → α → Prop} {a b : α}
  : ReflTransGen r a b ↔ ∃ l : List α, List.IsChain r (l ++ [b]) ∧ l.headD b = a:=by{
    constructor
    · {
      rw[ReflTransGen_iff_isChain_minimal_nodup_last]
      intro ⟨l, _, h0, h1, _⟩
      use l
    }
    · {
      intro ⟨l, hl0, hl1⟩
      match l with
      | [] => simp at hl1; simp[hl1]; rfl
      | a' :: l' => {
        rw[ReflTransGen_iff_isChain]
        use l' ++ [b]
        simp at hl1
        simp[hl1] at hl0
        simp[hl0]
      }
    }
  }
theorem Relation.ReflTransGen_of_isChain_of_mem_drop [DecidableEq α]
  {r : α → α → Prop} {x y : α} {l : List α}
  (hl : l.IsChain r) (hxy : y ∈ l.drop (l.idxOf x)) : ReflTransGen r x y :=by{
    rw[List.mem_iff_getElem] at hxy
    have ⟨i, hi, hiy⟩:=hxy
    simp only [List.getElem_drop] at hiy
    have hx:x ∈ l:=by{
      apply of_not_not
      intro hx
      simp[List.idxOf_eq_length hx] at hi
    }
    have hx':=List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
    rw[ReflTransGen_iff_isChain_option]
    use (l.take (l.idxOf x + i + 1)).drop (l.idxOf x)
    simp only [List.head?_drop, List.getElem?_take, Option.ite_none_right_eq_some]
    rw[(iff_true _).mp (List.getElem?_eq_some_getElem_iff (List.idxOf_lt_length_of_mem hx))]
    rw[Option.some_inj, hx']
    simp only [and_true, Nat.add_assoc, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, true_and]
    apply And.intro (List.isChain_drop (List.isChain_take hl))
    rw[List.getLast?_drop]
    rw[ite_cond_eq_false]
    · {
      rw[List.getLast?_take]
      simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, ↓reduceIte, Nat.add_succ_sub_one,
        Option.or_eq_some_iff, getElem?_eq_none_iff, not_lt]
      left
      rw[(iff_true _).mp (List.getElem?_eq_some_getElem_iff _), hiy]
      simp only [List.length_drop] at hi
      exact Nat.add_lt_of_lt_sub' hi
    }
    simp[List.idxOf_lt_length_of_mem hx]
  }
theorem Relation.ReflTransGen_of_isChain_of_mem_of_symm
  {r : α → α → Prop} {x y : α} {l : List α} (hl : l.IsChain r)
  (hx : x ∈ l) (hy : y ∈ l) (hs : Std.Symm (ReflTransGen r)) : ReflTransGen r x y :=by{
    classical
    have hx':=List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
    have hy':=List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
    wlog h_ij : List.idxOf x l < List.idxOf y l with H
    · {
      apply le_of_not_gt at h_ij
      cases lt_or_eq_of_le h_ij with
      | inl h_ij => {
        apply hs.symm
        exact H hl hy hx hs hy' hx' h_ij
      }
      | inr h_ij => {
        simp only [h_ij, hx'] at hy'
        simp only [hy']
        rfl
      }
    }
    apply ReflTransGen_of_isChain_of_mem_drop hl
    rw[List.mem_drop_iff_getElem]
    use l.idxOf y - l.idxOf x
    simp only [Nat.add_sub_cancel' (Nat.le_of_lt h_ij), hy']
    simp only [exists_prop, and_true]
    rw[Nat.sub_add_cancel (Nat.le_of_lt h_ij)]
    exact List.idxOf_lt_length_of_mem hy
  }

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

theorem List.tail_eq_dropLast_map_of_isChain_fromFun {p : List α}
  {f : α → α} (hp : p.IsChain (fromFun f))
  : p.tail = p.dropLast.map f:=by{
    induction p with
    | nil => simp
    | cons x p' ih => {
      cases em (p' = []) with
      | inl hp' => simp[hp']
      | inr hp' => {
        rw[List.isChain_cons_iff_of_ne_nil hp'] at hp
        have ih':=ih hp.right
        rw[List.tail_cons, ←List.cons_head_tail hp', ih']
        rw[List.dropLast_cons₂, List.map_cons, hp.left]
        congr
        rw[←ih', List.cons_head_tail]
      }
    }
  }
theorem List.isChain_fromFun_injective_univ {p : List α} {f : α → α} (hf : Injective f)
  (hpn : p ≠ []) (hpc : p.IsChain (fromFun f)) (hplh : p.head hpn = f (p.getLast hpn))
  : ∀x, x ∈ p → f x ∈ p := by{
    intro x hx
    rw[←List.cons_head_tail hpn]
    rw[hplh, List.mem_cons, hf.eq_iff]
    rw[←List.concat_dropLast_getLast hpn] at hx
    rw[List.mem_append, List.mem_singleton, or_comm] at hx
    apply hx.imp_right
    intro h
    rw[tail_eq_dropLast_map_of_isChain_fromFun hpc]
    rw[mem_map]
    use x
  }
theorem List.isChain_fromFun_injective_refltransgen_univ {p : List α} {f : α → α} (hf : Injective f)
  (hpn : p ≠ []) (hpc : p.IsChain (fromFun f)) (hplh : p.head hpn = f (p.getLast hpn))
  : ∀x, funReflTransGen f (p.head hpn) x → x ∈ p := by{
    intro x hx
    rw[funReflTransGen_iff_iterate] at hx
    have ⟨n, hn⟩:=hx
    induction n generalizing x with
    | zero => simp at hn; simp[←hn]
    | succ n' ih => {
      have ih':=ih (f^[n'] (p.head hpn)) ⟨n', rfl⟩ rfl
      rw[←hn, iterate_succ_apply']
      apply isChain_fromFun_injective_univ hf hpn hpc hplh
      exact ih'
    }
  }
theorem List.isChain_fromFun_injective_refltransgen_univ_iff {p : List α} {f : α → α}
  (hf : Injective f)
  (hpn : p ≠ []) (hpc : p.IsChain (fromFun f)) (hplh : p.head hpn = f (p.getLast hpn))
  : ∀x, funReflTransGen f (p.head hpn) x ↔ x ∈ p := by{
    intro x
    constructor
    · exact isChain_fromFun_injective_refltransgen_univ hf hpn hpc hplh x
    intro h
    rw[funReflTransGen, ReflTransGen_iff_isChain_option]
    classical
    use p.take (p.idxOf x + 1)
    have hp'n:p.take (p.idxOf x + 1) ≠ []:=by{
      simp[hpn]
    }
    rw[head?_eq_some_head hp'n, Option.some_inj]
    rw[getLast?_eq_some_getLast hp'n, Option.some_inj]
    apply And.intro (List.isChain_take hpc)
    rw[head_take]
    apply And.intro rfl
    rw[getLast_take, Nat.add_sub_cancel]
    rw[List.getElem?_idxOf h, Option.getD_some]
  }
theorem List.prefix_isChain_fromFun_of_head_eq_of_mem_getLast_of_nodup {p l : List α} {f : α → α}
  (hpn : p ≠ []) (hln : l ≠ []) (hplh : p.head hpn = l.head hln)
  (hpll : p.getLast hpn ∈ l) (hpc : p.IsChain (fromFun f)) (hlc : l.IsChain (fromFun f))
  (hpd : p.Nodup)
  : p <+: l := by{
    match p, l with
    | [a], b::l' => {
      simp at hplh
      simp[hplh]
    }
    | a::a'::p', [b] => {
      exfalso
      simp only [head_cons] at hplh
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, mem_cons, not_mem_nil,
        or_false] at hpll
      rw[List.nodup_cons] at hpd
      apply hpd.left
      rw[hplh, ←hpll]
      apply List.getLast_mem
    }
    | a::a'::p', b::b'::l' => {
      simp only [head_cons] at hplh
      rw[List.cons_prefix_cons]
      apply And.intro (hplh)
      rw[List.isChain_cons_cons, fromFun] at hpc hlc
      rw[List.getLast_cons_cons, List.mem_cons] at hpll
      rw[List.nodup_cons] at hpd
      apply prefix_isChain_fromFun_of_head_eq_of_mem_getLast_of_nodup (by {simp}) (by {simp})
        (by{rw[List.head_cons, List.head_cons, ←hpc.left, ←hlc.left, hplh]})
        (by{
          apply hpll.resolve_left
          intro h
          rw[←hplh] at h
          apply hpd.left
          rw[←h]
          apply List.getLast_mem
        }) hpc.right hlc.right hpd.right
    }
  }
theorem List.isChain_fromFun_eq_of_length_eq_of_head_eq {p l : List α} {f : α → α}
  (hpn : p ≠ []) (hln : l ≠ []) (hpll : p.length = l.length)
  (hplh : p.head hpn = l.head hln) (hpc : p.IsChain (fromFun f)) (hlc : l.IsChain (fromFun f))
  : p = l := by{
    match p, l with
    | [a], [b] => {
      simp at hplh
      simp[hplh]
    }
    | a::a'::p', b::b'::l' => {
      rw[List.length_cons (as:=_::_)] at hpll
      rw[List.length_cons (as:=_::_)] at hpll
      rw[Nat.add_right_cancel_iff] at hpll
      rw[List.head_cons, List.head_cons] at hplh
      rw[List.isChain_cons_cons, fromFun] at hpc hlc
      rw[List.cons_eq_cons]
      apply And.intro hplh
      apply isChain_fromFun_eq_of_length_eq_of_head_eq (by{simp}) (by{simp}) hpll
        (by{rw[List.head_cons, List.head_cons, ←hpc.left, ←hlc.left, hplh]})
        hpc.right hlc.right
    }
  }
theorem List.isChain_fromFun_eq_of_length_eq_of_head?_eq {p l : List α} {f : α → α}
  (hpll : p.length = l.length) (hplh : p.head? = l.head?)
  (hpc : p.IsChain (fromFun f)) (hlc : l.IsChain (fromFun f))
  : p = l := by{
    match p, l with
    | [], [] => rfl
    | _::_, _::_ => {
      rw[head?_eq_some_head (by {simp})] at hplh
      rw[head?_eq_some_head (by {simp})] at hplh
      rw[Option.some_inj] at hplh
      apply List.isChain_fromFun_eq_of_length_eq_of_head_eq (by{simp}) (by{simp})
        hpll hplh hpc hlc
    }
  }
theorem List.suffix_isChain_fromFun_injective_of_getLast_eq_of_mem_head_of_nodup {p l : List α}
  {f : α → α} (hf : Injective f) (hpn : p ≠ []) (hln : l ≠ [])
  (hpll : p.getLast hpn = l.getLast hln) (hplh : p.head hpn ∈ l) (hpc : p.IsChain (fromFun f))
  (hlc : l.IsChain (fromFun f)) (hpd : p.Nodup) : p <:+ l := by{
    rw[←concat_dropLast_getLast hpn, ←concat_dropLast_getLast hln]
    rw[hpll]
    rw[append_suffix_append_right]
    cases em (p.dropLast = []) with
    | inl hp'n => simp[hp'n]
    | inr hp'n => {
      rw[←concat_dropLast_getLast hpn, ←concat_eq_append, nodup_concat] at hpd
      have h : p.head hpn ≠ p.getLast hpn:=by{
        intro h
        apply hpd.left
        rw[←h]
        have h':=head_dropLast hp'n
        rw[←h']
        apply head_mem
      }
      rw[←concat_dropLast_getLast hln, mem_append, mem_singleton, ←hpll] at hplh
      simp only [h, or_false] at hplh
      have hl'n := ne_nil_of_mem hplh
      rw[←concat_dropLast_getLast hpn, List.isChain_concat_iff_of_ne_nil hp'n] at hpc
      rw[←concat_dropLast_getLast hln, List.isChain_concat_iff_of_ne_nil hl'n] at hlc
      have : p.dropLast.length < p.length := by{
        rw[List.length_dropLast]
        apply Nat.pred_lt
        simp[hpn]
      }
      refine suffix_isChain_fromFun_injective_of_getLast_eq_of_mem_head_of_nodup hf hp'n hl'n
        ?_ ?_ hpc.left hlc.left hpd.right
      · {
        rw[fromFun] at hpc hlc
        rw[←hpll, ←hpc.right, hf.eq_iff] at hlc
        rw[hlc.right]
      }
      · {
        rw[head_dropLast hp'n]
        apply hplh
      }
    }
  }
termination_by p.length
theorem List.isChain_map_iterate_range_fromFun {n : ℕ} {f : α → α} {x : α} :
  ((List.range n).map (f^[·] x)).IsChain (fromFun f) := by{
    match n with
    | 0 | 1 => simp
    | n + 2 => {
      rw[range_succ, range_succ, List.map_append, List.map_append]
      rw[List.map_singleton, List.map_singleton, List.isChain_concat_append]
      rw[←List.map_singleton (f:=(f^[·] x)), ←List.map_append, ←List.range_succ]
      apply And.intro isChain_map_iterate_range_fromFun
      simp[fromFun, ←iterate_succ_apply']
    }
  }
theorem Relation.reflTransGen_of_isCycleChain
  {r : α → α → Prop} {x y : α} {l : List α}
  (hl : l.IsCycleChain r) (hx : x ∈ l) (hy : y ∈ l) : ReflTransGen r x y := by{
    have hln : l ≠ [] := List.ne_nil_of_mem hx
    classical
    have hl':=(hl.rotate (l.idxOf x)).isChain
    have h' : (l.rotate (List.idxOf x l)).idxOf x = 0 := by{
      rw[List.idxOf_eq_zero_iff_head_eq (by{simp[hln]})]
      rw[List.head_rotate_idxOf hx]
    }
    apply ReflTransGen_of_isChain_of_mem_drop hl'
    simp[h', hy]
  }
theorem List.isChain_fromFun_getElem {f : α → α} {l : List α} (hl : l.IsChain (fromFun f))
  {i : ℕ} (hi : i < l.length) : l[i] = f^[i] (l.head (ne_nil_of_length_pos (Nat.zero_lt_of_lt hi)))
  := by{
    match i, l with
    | 0, _::_ => simp
    | i' + 1, _::_ => {
      simp only [getElem_cons_succ, head_cons, iterate_succ, comp_apply]
      simp only [length_cons, Nat.add_lt_add_iff_right] at hi
      rw[isChain_fromFun_getElem hl.of_cons hi]
      rw[isChain_cons_iff_of_ne_nil (ne_nil_of_length_pos (Nat.zero_lt_of_lt hi))] at hl
      rw[hl.left]
    }
  }
theorem List.period_of_IsCycleChain {f : α → α} {l : List α} (hlk : l.IsCycleChain (fromFun f))
  {x : α} (hxl : x ∈ l) : IsPeriodicPt f l.length x := by{
    classical
    have hlk' := hlk.rotate (l.idxOf x)
    simp only [← List.length_rotate l (l.idxOf x)]
    have hln : l.rotate (idxOf x l) ≠ [] := by{simp[List.ne_nil_of_mem hxl]}
    have hxh : List.head _ hln = _ := List.head_rotate_idxOf hxl
    generalize hl' : l.rotate (l.idxOf x) = l'
    simp only [hl'] at hln hxh hlk'
    change List.head _ hln = _ at hxh
    clear! l
    have hlk'' := hlk'.isChain
    have hlk''' := isChain_fromFun_getElem hlk'' (i := l'.length - 1)
      (by{simp[length_pos_of_ne_nil hln]})
    unfold IsCycleChain at hlk'
    simp only [hln, ↓reduceDIte] at hlk'
    rw[fromFun, List.getLast_eq_getElem, hlk''', ← iterate_succ_apply' f] at hlk'
    simp only [Nat.sub_one, Nat.succ_pred (Nat.ne_zero_of_lt (length_pos_of_ne_nil hln)),
    hxh] at hlk'
    exact hlk'.right
  }
theorem List.forall_mem_of_isCycleChain {f : α → α} {l : List α} (hlk : l.IsCycleChain (fromFun f))
  {x : α} (hxl : x ∈ l) : ∀n, f^[n] x ∈ l := by{
    classical
    have hlk' := hlk.rotate (l.idxOf x)
    simp only [← List.mem_rotate (l:=l) (n:=l.idxOf x)]
    have hln : l.rotate (idxOf x l) ≠ [] := by{simp[List.ne_nil_of_mem hxl]}
    have hxh : List.head _ hln = _ := List.head_rotate_idxOf hxl
    generalize hl' : l.rotate (l.idxOf x) = l'
    simp only [hl'] at hln hxh hlk'
    change List.head _ hln = _ at hxh
    clear! l
    have hlk'' := hlk'.isChain
    intro n
    wlog hn : n < l'.length with H
    · {
      have hm := period_of_IsCycleChain hlk' (hxh ▸ head_mem hln)
      rw[← hm.iterate_mod_apply]
      apply H l' hln hlk' hxh hlk''
      apply Nat.mod_lt
      apply length_pos_of_ne_nil hln
    }
    rw[← hxh, ← isChain_fromFun_getElem hlk'' hn]
    simp
  }
theorem Relation.funReflTransGen_iff_mem_of_isCycleChain
  {f : α → α} {x y : α} {l : List α}
  (hl : l.IsCycleChain (fromFun f)) (hx : x ∈ l) : y ∈ l ↔ funReflTransGen f x y := by{
    constructor
    · apply reflTransGen_of_isCycleChain hl hx
    intro h'
    rw[funReflTransGen_iff_iterate] at h'
    have ⟨n, hn⟩:=h'
    rw[← hn]
    apply List.forall_mem_of_isCycleChain hl hx
  }
