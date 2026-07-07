import Mathlib.Data.List.Induction
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Cycle
import FourColorTheorem.Utils.List

open Relation
open Function

variable {α : Type _}
def List.shorterChain [DecidableEq α] : List α → List α
| [] => []
| x :: xs => let rest:=shorterChain xs
  if h:x ∈ rest then
    x :: rest.drop ((rest.idxOf? x).get (idxOf?_isSome_iff.mpr h) + 1)
  else
    x :: rest

theorem List.shorterChain_nil [DecidableEq α] : List.shorterChain ([] : List α) = []:=rfl
theorem List.shorterChain_cons [DecidableEq α] {x : α} {xs : List α}
  : (x::xs).shorterChain = let rest:=shorterChain xs
  if h:x ∈ rest then
    x :: rest.drop ((rest.idxOf? x).get (idxOf?_isSome_iff.mpr h) + 1)
  else
    x :: rest
  := rfl
theorem List.shorterChain_singleton [DecidableEq α] {x : α} : [x].shorterChain = [x]:=rfl
theorem List.shorterChain_cons_mem [DecidableEq α] {x : α} {xs : List α}
  (hx : x ∈ xs.shorterChain) : (x::xs).shorterChain =
    x :: xs.shorterChain.drop ((xs.shorterChain.idxOf? x).get (List.idxOf?_isSome_iff.mpr hx) + 1)
  := by{
    rw[List.shorterChain_cons]
    simp[hx]
  }
theorem List.shorterChain_cons_not_mem [DecidableEq α] {x : α} {xs : List α}
  (hx : x ∉ xs.shorterChain) : (x::xs).shorterChain = x::xs.shorterChain
  := by{
    rw[List.shorterChain_cons]
    simp[hx]
  }
theorem List.shorterChain_eq_nil_iff [DecidableEq α] {l : List α}
  : l.shorterChain = [] ↔ l = [] := by{
    match l with
    | [] => rfl
    | x::xs => {
      rw[shorterChain_cons]
      cases Decidable.em (x ∈ xs.shorterChain) with
      | inl hp | inr hp => simp[hp]
    }
  }
theorem List.shorterChain_ne_nil_iff [DecidableEq α] {l : List α}
  : l.shorterChain ≠ [] ↔ l ≠ [] :=
  not_iff_not.mpr shorterChain_eq_nil_iff
theorem List.nodup_drop {l : List α} {k : ℕ} (hl : l.Nodup) : (l.drop k).Nodup := by{
  match l, k with
  | [], _ => simp
  | _, 0 => simp[hl]
  | x::xs, n + 1 => {
    rw[nodup_cons] at hl
    rw[drop_succ_cons]
    exact nodup_drop hl.right
  }
}
theorem List.shorterChain_nodup [DecidableEq α] {l : List α} : l.shorterChain.Nodup := by{
  induction l with
  | nil => rw[shorterChain_nil]; exact nodup_nil
  | cons x xs ih => {
    rw[shorterChain_cons]
    cases Decidable.em (x ∈ xs.shorterChain) with
      | inl hp => {
        simp only [hp, ↓reduceDIte, nodup_cons]
        constructor
        · {
          have h0:=idxOf?_isSome_iff.mpr hp
          let k:=(idxOf? x xs.shorterChain).get h0
          have h1:=take_append_drop (k + 1) xs.shorterChain
          have h2:=congrArg (count x) h1
          rw[count_append] at h2
          rw[←count_eq_zero]
          have h3:count x xs.shorterChain = 1:=count_eq_one_of_mem ih hp
          have h4:count x (xs.shorterChain.take (k + 1)) = 1:=by{
            apply count_eq_one_of_mem (nodup_take ih)
            rw[mem_iff_get]
            have h5:(take (k + 1) xs.shorterChain).length = k + 1:=by{
              rw[length_take]
              apply Nat.min_eq_left
              apply Nat.succ_le_of_lt
              unfold k
              exact idxOf?_isSome_get_lt_length hp
            }
            use ⟨k, h5.symm ▸ Nat.lt_succ_self k⟩
            simp only [get_eq_getElem, getElem_take]
            unfold k
            exact idxOf?_isSome_getElem hp
          }
          rw[h3, h4] at h2
          simp only [Nat.add_eq_left] at h2
          exact h2
        }
        · exact nodup_drop ih
      }
      | inr hp => {
        simp only [hp, ↓reduceDIte, nodup_cons, not_false_eq_true, true_and]
        exact ih
      }
  }
}
theorem List.shorterChain_head [DecidableEq α] {l : List α} (hl : l ≠ [])
  : l.shorterChain.head (shorterChain_ne_nil_iff.mpr hl) = l.head hl
  := by{
    match l with
    | x::xs => {
      simp only [shorterChain_cons]
      cases Decidable.em (x ∈ xs.shorterChain) with
      | inl hp | inr hp => simp[hp]
    }
  }
theorem List.isChain_cons_iff_of_ne_nil {x : α} {l : List α} {r : α → α → Prop} (hl : l ≠ [])
  : IsChain r (x::l) ↔ r x (l.head hl) ∧ IsChain r l := by{
    match l with | y :: ys => simp
  }
theorem List.isChain_concat_iff_of_ne_nil {x : α} {l : List α} {r : α → α → Prop} (hl : l ≠ [])
  : IsChain r (l ++ [x]) ↔ IsChain r l ∧ r (l.getLast hl) x := by{
    match l with
    | [a] => simp
    | a::b::l' => {
      rw[isChain_cons_cons]
      rw[cons_append, cons_append, isChain_cons_cons, ←cons_append]
      rw[isChain_concat_iff_of_ne_nil (by{simp})]
      rw[getLast_cons_cons]
      rw[and_assoc]
    }
  }
theorem List.isChain_drop {l : List α} {r : α → α → Prop} {k : ℕ} (hl : IsChain r l)
  : IsChain r (l.drop k) := by{
  match l, k with
  | [], _ | [x], _ + 1 => simp
  | _, 0 => simp[hl]
  | x::y::xs, n + 1 => {
    rw[drop_succ_cons]
    rw[isChain_cons_cons] at hl
    exact isChain_drop hl.right
  }
}
theorem List.isChain_take {l : List α} {r : α → α → Prop} {k : ℕ} (hl : IsChain r l)
  : IsChain r (l.take k) := by{
  match l, k with
  | [], _ | [x], _ + 1 => simp
  | _, 0 => simp
  | _::_, 1 => simp
  | x::y::xs, n + 2 => {
    rw[take_succ_cons, take_succ_cons]
    rw[isChain_cons_cons] at hl
    rw[isChain_cons_cons]
    apply hl.imp_right
    intro h
    rw[←take_succ_cons]
    apply isChain_take h
  }
}
theorem List.shorterChain_isChain [DecidableEq α] {l : List α} {r : α → α → Prop} (h : IsChain r l)
  : IsChain r l.shorterChain := by{
    match l with
    | [] => exact IsChain.nil
    | [x] => exact IsChain.singleton _
    | x::y::xs => {
      have hs:(y::xs).shorterChain ≠ []:=shorterChain_ne_nil_iff.mpr (by{simp})
      rw[isChain_cons_cons] at h
      rw[shorterChain_cons]
      have ih:=shorterChain_isChain h.right
      by_cases hp : x ∈ (y::xs).shorterChain
      · {
        simp only [hp, ↓reduceDIte]
        have h0:=idxOf?_isSome_iff.mpr hp
        let k:=(idxOf? x (y::xs).shorterChain).get h0
        have hk:k + 1 ≤ (y::xs).shorterChain.length:=by{
          apply Nat.succ_le_of_lt
          exact idxOf?_isSome_get_lt_length hp
        }
        cases Nat.lt_or_eq_of_le hk with
        | inl hk => {
          have h1:drop (k + 1) (y::xs).shorterChain ≠ []:=by{
            rw[ne_nil_iff_length_pos]
            rw[length_drop]
            rw[Nat.sub_pos_iff_lt]
            exact hk
          }
          rw[List.isChain_cons_iff_of_ne_nil h1]
          constructor
          · {
            have h2:(drop (k + 1) (y :: xs).shorterChain).head h1
              = (y::xs).shorterChain[k + 1]'hk:=by{simp}
            rw[h2]
            have h3:=idxOf?_isSome_getElem hp
            rw[←h3]
            exact isChain_iff_getElem.mp ih k hk
          }
          · exact isChain_drop ih
        }
        | inr hk => {
          unfold k at hk
          simp[hk]
        }
      }
      · {
        simp only [hp, ↓reduceDIte]
        rw[List.isChain_cons_iff_of_ne_nil hs]
        rw[shorterChain_head (by{simp})]
        rw[head_cons]
        exact ⟨h.left, ih⟩
      }
    }
  }
theorem List.isChain_exists_shorterChain_option {l : List α} {r : α → α → Prop} (hc : IsChain r l)
  : ∃ l', List.Sublist l' l ∧ l'.Nodup ∧ List.IsChain r l'
  ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast?
  :=by{
    match l with
    | [] => {
      use []
      simp
    }
    | x::xs => {
      by_cases hx : x ∈ xs
      · {
        have ⟨k, hk, hxk⟩:=mem_iff_getElem.mp hx
        let l':=xs.drop k
        have hl't:l'.length < (x::xs).length:=by{
          unfold l'
          rw[length_drop, length_cons]
          exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
        }
        have hlc:IsChain r l':=isChain_drop hc (k:=k+1)
        have hln:l' ≠ []:=by{
          rw[ne_nil_iff_length_pos]
          unfold l'
          rw[length_drop]
          exact Nat.sub_pos_of_lt hk
        }
        have hln':=length_pos_of_ne_nil hln
        have hlx:l'[0]'hln' = x :=by{
          unfold l'
          rw[←hxk]
          simp
        }
        have hlx':l'.head? = some x:=by{
          match l' with
          | x'::_ => simp at hlx; simp[hlx]
        }
        have ⟨l'', hl'', hl''p, hl''c, hl''h, hl''d⟩:=isChain_exists_shorterChain_option hlc
        use l''
        constructor
        · exact hl''.trans (drop_sublist (k + 1) (x::xs))
        constructor
        · exact hl''p
        constructor
        · exact hl''c
        rw[hl''h, head?_cons]
        rw[hlx']
        constructor
        · rfl
        rw[hl''d]
        rw[getLast?_drop]
        have hxs':xs ≠ []:=ne_nil_of_mem hx
        have hxs:(x::xs).getLast? = xs.getLast?:=by{match xs with | _::_ => simp}
        rw[hxs]
        simp[Nat.not_le_of_gt hk]
      }
      · {
        have hc':=isChain_of_isChain_cons hc
        have ⟨l', hl', hl'c, hl'h, hl'd⟩:=isChain_exists_shorterChain_option hc'
        use x::l'
        rw[head?_cons, head?_cons]
        constructor
        · exact Sublist.cons_cons _ hl'
        constructor
        · exact Nodup.cons (fun hn => hx (hl'.subset hn)) hl'c
        rw[and_left_comm]
        constructor
        · rfl
        match l' with
        | [] => {
          simp[Eq.comm (a:=none), getLast?_eq_none_iff] at hl'd
          simp[hl'd]
        }
        | x'::l'' => {
          have hx:xs ≠ []:=ne_nil_iff_length_pos.mpr (Nat.lt_of_lt_of_le (by{simp}) hl'.length_le)
          match xs with
          | x''::xs' => {
            simp at hl'd
            simp only[isChain_cons_cons, getLast?_cons_cons, hl'd.right, hl'h]
            simp
            simp [isChain_cons_cons] at hc
            simp[hl'd.left, hc.left]
          }
        }
      }
    }
  }
termination_by l.length
theorem List.isChain_concat_append {l₁ l₂ : List α} {r : α → α → Prop} {x : α}
  : List.IsChain r (l₁ ++ [x] ++ l₂) ↔ List.IsChain r (l₁ ++ [x]) ∧ List.IsChain r (x :: l₂)
  :=by{
    induction l₁ with
    | nil => simp
    | cons x l₁' ih => {
      simp only [cons_append, append_assoc, nil_append]
      rw[List.isChain_cons_iff_of_ne_nil (by{simp})]
      simp at ih
      simp only [ih]
      rw[List.isChain_cons_iff_of_ne_nil (l:=l₁' ++ _) (by{simp})]
      rw[and_assoc]
      apply and_congr_left
      intros
      rw[←propext_iff]
      apply congrArg (r x)
      match l₁' with
      | [] | _::_ => simp
    }
  }
theorem List.isChain_append_cons {l₁ l₂ : List α} {r : α → α → Prop} {x : α}
  : List.IsChain r (l₁ ++ x::l₂) ↔ List.IsChain r (l₁ ++ [x]) ∧ List.IsChain r (x :: l₂)
  := by{
    have h:=isChain_concat_append (l₁:=l₁) (l₂:=l₂) (r:=r) (x:=x)
    simp at h
    simp[h]
}
theorem List.IsChain_map {β : Type _} {r : α → α → Prop} {f : β → α} {l : List β}
  : IsChain r (l.map f) ↔ IsChain (InvImage r f) l := by{
    match l with
    | [] | [_] => simp
    | a::b::as => simp[InvImage, ←IsChain_map (l:=b::as)]
  }

theorem List.isChain_attachWith_of_iff_getElem {p : List α} {P : α → Prop} (hP : ∀ x ∈ p, P x)
  {r : α → α → Prop} {r' : {x // P x} → {x // P x} → Prop}
  (h : ∀ i, (hi : i < p.length - 1) → r'
    ⟨p[i]'(Nat.lt_of_lt_pred hi), hP _ (List.getElem_mem (Nat.lt_of_lt_pred hi))⟩
    ⟨p[i + 1]'(Nat.succ_lt_of_lt_pred hi), hP _ (List.getElem_mem (Nat.succ_lt_of_lt_pred hi))⟩ ↔
    r p[i] p[i + 1])
  : (p.attachWith P hP).IsChain r' ↔ p.IsChain r := by{
    induction p using twoStepInduction with
    | nil | singleton _ => simp
    | cons_cons a b p' ih1 ih2 => {
      rw[attachWith_cons, attachWith_cons, isChain_cons_cons]
      have hP':∀x ∈ b::p', P x:=by{
        intro x hx
        apply hP _
        simp[hx]
      }
      rw[←attachWith_cons hP', isChain_cons_cons]
      have ih2':=ih2 b hP' (by{
        intro i hi
        have hi':=h (i + 1) (by{simp at hi; simp[hi]})
        simp only [getElem_cons_succ (as:=b::p')] at hi'
        exact hi'
      })
      apply (and_congr · ih2')
      have h':=h 0 (by{simp})
      simp at h'
      simp[h']
    }
  }
theorem List.isChain_attachWith_of_iff_mem {p : List α} {P : α → Prop} (hP : ∀ x ∈ p, P x)
  {r : α → α → Prop} {r' : {x // P x} → {x // P x} → Prop}
  (h : ∀ a b, (ha : a ∈ p) → (hb : b ∈ p) → r' ⟨a, hP a ha⟩ ⟨b, hP b hb⟩ ↔ r a b)
  : (p.attachWith P hP).IsChain r' ↔ p.IsChain r := by{
    apply isChain_attachWith_of_iff_getElem
    intro i hi
    apply h
    · apply getElem_mem
    · apply getElem_mem
  }

theorem List.isChain_attachWith_of_imp_getElem {p : List α} {P : α → Prop} (hP : ∀ x ∈ p, P x)
  {r : α → α → Prop} {r' : {x // P x} → {x // P x} → Prop}
  (h : ∀ i, (hi : i < p.length - 1) → r p[i] p[i + 1] →
  r' ⟨p[i]'(Nat.lt_of_lt_pred hi), hP _ (List.getElem_mem (Nat.lt_of_lt_pred hi))⟩
    ⟨p[i + 1]'(Nat.succ_lt_of_lt_pred hi), hP _ (List.getElem_mem (Nat.succ_lt_of_lt_pred hi))⟩)
  (hr : p.IsChain r) : (p.attachWith P hP).IsChain r':= by{
    induction p using twoStepInduction with
    | nil | singleton _ => simp
    | cons_cons a b p' ih1 ih2 => {
      rw[attachWith_cons, attachWith_cons, isChain_cons_cons]
      have hP':∀x ∈ b::p', P x:=by{
        intro x hx
        apply hP _
        simp[hx]
      }
      rw[←attachWith_cons hP']
      rw[isChain_cons_cons] at hr
      have ih2':=ih2 b hP' (by{
        intro i hi
        have hi':=h (i + 1) (by{simp at hi; simp[hi]})
        simp only [getElem_cons_succ (as:=b::p')] at hi'
        exact hi'
      }) hr.right
      apply (And.intro · ih2')
      have h':=h 0 (by{simp})
      simp at h'
      simp[h' hr.left]
    }
  }
theorem List.isChain_attachWith_of_imp_mem {p : List α} {P : α → Prop} (hP : ∀ x ∈ p, P x)
  {r : α → α → Prop} {r' : {x // P x} → {x // P x} → Prop}
  (h : ∀ a b, (ha : a ∈ p) → (hb : b ∈ p) → r a b → r' ⟨a, hP a ha⟩ ⟨b, hP b hb⟩)
  (hr : p.IsChain r) : (p.attachWith P hP).IsChain r':= by{
    apply (isChain_attachWith_of_imp_getElem _ · hr)
    intro i hi
    apply h
    · apply getElem_mem
    · apply getElem_mem
  }

def List.IsCycleChain (r : α → α → Prop) (l : List α) : Prop :=
  if hln : l = [] then True
  else l.IsChain r ∧ r (l.getLast hln) (l.head hln)
@[inline] instance List.IsCycleChain.instDecidable {r : α → α → Prop} [DecidableRel r]
  : DecidablePred (List.IsCycleChain r) := fun _ => instDecidableDite
theorem List.IsCycleChain.isChain {r : α → α → Prop} {l : List α}
  (hlr : l.IsCycleChain r) : l.IsChain r := by{
    rw[IsCycleChain] at hlr
    cases em (l = []) with
    | inl hln => simp[hln]
    | inr hln => {
      simp[hln] at hlr
      simp[hlr]
    }
  }
@[simp] theorem List.isCycleChain_nil {r : α → α → Prop}
  : IsCycleChain r [] := by{simp[IsCycleChain]}
theorem List.isCycleChain_iff_getElem {r : α → α → Prop} {l : List α} (hln : l ≠ [])
  : l.IsCycleChain r ↔ ∀i, r
  (l[i % l.length]'(by{apply Nat.mod_lt; apply length_pos_of_ne_nil hln}))
  (l[(i + 1) % l.length]'(by{apply Nat.mod_lt; apply length_pos_of_ne_nil hln}))
  := by{
    rw[IsCycleChain, dite_cond_eq_false (by{simp[hln]})]
    rw[isChain_iff_getElem, getLast_eq_getElem, head_eq_getElem]
    constructor
    · {
      intro ⟨hl, hr⟩ i
      have hi := Nat.mod_lt i (length_pos_of_ne_nil hln)
      have hi':=Nat.le_pred_of_lt hi
      have hln':=Nat.succ_pred (Nat.ne_zero_of_lt hi)
      have hln'':=Nat.succ_mod_succ_eq_zero_iff (a:=i) (b:=l.length.pred)
      simp only [Nat.pred_eq_sub_one, Nat.sub_add_cancel (Nat.zero_lt_of_lt hi)] at hln''
      rw[Nat.pred_eq_sub_one] at hi'
      rcases lt_or_eq_of_le hi' with hi' | hi'
      · {
        simp only [Nat.ne_of_lt hi', iff_false] at hln''
        have hln0 : l.length ≠ 1 :=by{
          intro hln0
          simp[hln0, Nat.mod_one] at hln''
        }
        have hln''':(i + 1) % l.length = i % l.length + 1 := by{
          rw[Nat.add_mod, Nat.one_mod_eq_one.mpr hln0]
          rw[Nat.mod_eq_of_lt]
          apply Nat.succ_lt_of_lt_pred
          exact hi'
        }
        simp only [hln''']
        apply hl
      }
      · {
        simp only [hi', iff_true] at hln''
        simp[hln'', hi', hr]
      }
    }
    · {
      intro h
      constructor
      · {
        intro i hi
        have h':=h i
        simp[Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hi)] at h'
        simp[h']
      }
      · {
        have h':=h (l.length - 1)
        simp[Nat.sub_add_cancel (length_pos_of_ne_nil hln)] at h'
        simp[h']
      }
    }
  }

theorem List.IsCycleChain.rotate {r : α → α → Prop} {l : List α} (hlk : l.IsCycleChain r)
  (k : ℕ) : (l.rotate k).IsCycleChain r := by{
    induction k generalizing l with
    | zero => simp[hlk]
    | succ k' ih => {
      rw[Nat.add_comm, rotate_add]
      apply ih
      match l with
      | [] => simp
      | [a] => simp[hlk]
      | a :: b :: l' => {
        rw[rotate_cons_succ, rotate_zero]
        rw[IsCycleChain, dite_cond_eq_false (by{simp})]
        rw[IsCycleChain, dite_cond_eq_false (by{simp})] at hlk
        rw[getLast_cons_cons, head_cons] at hlk
        rw[getLast_append_singleton]
        simp only [cons_append, head_cons]
        rw[List.isChain_cons_cons] at hlk
        refine ⟨?_, hlk.1.1⟩
        rw[←cons_append, isChain_append]
        simp only [IsChain.singleton, ne_eq, reduceCtorEq, not_false_eq_true,
          getLast?_eq_some_getLast, Option.mem_def, Option.some.injEq, head?_cons, forall_eq',
          true_and]
        apply And.intro hlk.1.2
        exact hlk.right
      }
    }
  }
theorem List.isCycleChain_iff_next_of_nodup [DecidableEq α] {r : α → α → Prop} {l : List α}
  (hl : l.Nodup) : l.IsCycleChain r ↔ ∀x, (hxl : x ∈ l) → r x (l.next x hxl) := by{
    rcases eq_or_ne l [] with hln | hln
    · simp[hln]
    rw[List.isCycleChain_iff_getElem hln]
    simp only [List.next_eq_getElem]
    constructor
    · {
      intro ih x hxl
      rw[mem_iff_getElem] at hxl
      have ⟨i, hi, hlix⟩:=hxl
      simp only [←hlix, hl.idxOf_getElem]
      specialize ih i
      simp only [Nat.mod_eq_of_lt hi] at ih
      exact ih
    }
    · {
      intro ih i
      specialize ih (l[i % l.length]'(Nat.mod_lt _ (length_pos_of_ne_nil hln))) (by{simp})
      simp[hl.idxOf_getElem] at ih
      simp[ih]
    }
  }
theorem List.isCycleChain_iff_prev_of_nodup [DecidableEq α] {r : α → α → Prop} {l : List α}
  (hl : l.Nodup) : l.IsCycleChain r ↔ ∀x, (hxl : x ∈ l) → r (l.prev x hxl) x := by{
    rw[isCycleChain_iff_next_of_nodup hl]
    constructor
    · {
      intro ih x hxl
      nth_rw 2 [← List.next_prev l hl x hxl]
      apply ih
    }
    · {
      intro ih x hxl
      nth_rw 1 [← List.prev_next l hl x hxl]
      apply ih
    }
  }
