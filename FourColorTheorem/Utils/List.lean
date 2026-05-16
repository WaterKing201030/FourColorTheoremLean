import Batteries.Data.List.Basic
import Init.Data.List.Pairwise
import Mathlib.Data.List.Nodup
import Mathlib.Order.Minimal

open Relation
open Function

variable {α : Type _}
theorem List.mem_take_of_mem_take_le {l : List α} {x : α} {n m : ℕ}
  (hlx : x ∈ l.take n) (hnm : n ≤ m) : x ∈ l.take m := by{
    apply List.take_subset_take_left _ hnm
    exact hlx
  }
theorem List.ne_nil_iff_exists_concat {l : List α}
  : l ≠ [] ↔ ∃l' x, l' ++ [x] = l:=by{
    induction l with
    | nil => simp
    | cons x l' ih => {
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
      cases em (l' = []) with
      | inl hl => {
        use [], x
        simp[hl]
      }
      | inr hl => {
        have ⟨l'', x', hl⟩:=ih.mp hl
        apply Exists.intro (x::l'')
        use x'
        simp[hl]
      }
    }
  }
theorem List.attach_concat {xs : List α} {x : α} :
  (xs ++ [x]).attach =
    List.map
      (fun x_1 ↦
        match x_1 with
        | ⟨y, h⟩ => ⟨y, by{simp[h]}⟩)
        xs.attach ++ [⟨x, by{simp}⟩]:=by{
          rw[List.attach_append]
          simp
        }

theorem List.getLast?_cons_eq_getLastD {a : α} {l : List α}
  : (a::l).getLast? = some (l.getLastD a):=by{
  induction l generalizing a with
  | nil => rfl
  | cons b bs ih => simp[ih]
}
theorem List.getLast?_cons_of_ne_nil {a : α} {l : List α} (hl : l ≠ [])
  : (a::l).getLast? = l.getLast? := by{
    match l with
    | _::_ => rw[getLast?_cons_cons]
  }
theorem List.getLast_cons_eq_getLastD {x : α} {l : List α}
  : (x::l).getLast (by{simp}) = l.getLastD x:=by{
    induction l generalizing x with
    | nil => simp
    | cons y l' ih => {
      rw[getLast_cons_cons, getLastD_cons]
      exact ih
    }
  }
theorem List.getLastD_append_cons {a : α} {l₁ : List α} {x : α} {l₂ : List α}
  : (l₁ ++ x::l₂).getLastD a = l₂.getLastD x := by{
    induction l₂ generalizing l₁ x with
    | nil => simp
    | cons x' l₂' ih => {
      have ih':=@ih (l₁ ++ [x]) x'
      rw[←concat_append, getLastD_cons]
      rw[List.concat_eq_append]
      exact ih'
    }
  }
theorem List.drop_idxOf_head [DecidableEq α] {x : α} {p : List α} (hxp : x ∈ p)
  : (p.drop (p.idxOf x)).head (by{simp[idxOf_lt_length_iff, hxp]}) = x:=by{
    simp
  }
theorem List.idxOf_head [DecidableEq α] {p : List α} (hp : p ≠ [])
  : p.idxOf (p.head hp) = 0 := by{
    match p with | _::_ => simp
  }
theorem List.idxOf?_isSome_iff [DecidableEq α] {x : α} {l : List α}
  : (l.idxOf? x).isSome ↔ x ∈ l:=by{
    induction l with
    | nil => simp
    | cons y ys ih => {
      rw[idxOf?_cons]
      match (inferInstance:DecidableEq α) x y with
      | isTrue hxy => simp[hxy]
      | isFalse hxy => {
        simp[Eq.comm (a:=y), hxy]
      }
    }
  }
theorem List.idxOf?_isSome_get_lt_length [DecidableEq α] {x : α} {l : List α} (hxl : x ∈ l)
  : (l.idxOf? x).get (idxOf?_isSome_iff.mpr hxl) < l.length:=by{
    induction l with
    | nil => contradiction
    | cons y ys ih => {
      simp only [idxOf?_cons, beq_iff_eq, length_cons]
      match (inferInstance:DecidableEq α) x y with
      | isTrue hxy => simp[hxy]
      | isFalse hxy => {
        simp only [Eq.comm (a := y), hxy, ↓reduceIte,
          Option.get_map, Nat.add_lt_add_iff_right, gt_iff_lt]
        simp only [mem_cons, hxy, false_or] at hxl
        exact ih hxl
      }
    }
  }
theorem List.idxOf?_isSome_getElem [DecidableEq α] {x : α} {l : List α} (hxl : x ∈ l)
  : l[(l.idxOf? x).get (idxOf?_isSome_iff.mpr hxl)]'(idxOf?_isSome_get_lt_length hxl) = x:=by{
    induction l with
    | nil => contradiction
    | cons y ys ih => {
      simp only [idxOf?_cons, beq_iff_eq]
      match (inferInstance:DecidableEq α) x y with
      | isTrue hxy => simp[hxy]
      | isFalse hxy => {
        simp only [Eq.comm (a := y), hxy, ↓reduceIte,
          Option.get_map]
        simp only [mem_cons, hxy, false_or] at hxl
        exact ih hxl
      }
    }
  }

theorem List.nodup_take {l : List α} {k : ℕ} (hl : l.Nodup) : (l.take k).Nodup := by{
  match l, k with
  | [], _ | _, 0 => simp
  | x::xs, n + 1 => {
    rw[nodup_cons] at hl
    rw[take_succ_cons]
    rw[nodup_cons]
    exact ⟨fun hx => hl.left (take_subset _ _ hx), nodup_take hl.right⟩
  }
}

theorem List.take_getLast {l : List α} {k : ℕ} (hlk : l.take k ≠ [])
  : (l.take k).getLast hlk = l[min l.length k - 1]'(by{
    simp at hlk
    match k, l with
    | k' + 1, x::l' => {
      simp only [length_cons, Nat.add_min_add_right, Nat.add_one_sub_one, gt_iff_lt]
      apply Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by{simp})
    }
  }):=by{
    simp at hlk
    match k, l with
    | k' + 1, [x] => simp
    | 1, x::y::l' => simp
    | k' + 2, x::y::l' => {
      simp only [take_succ_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, length_cons,
        Nat.add_min_add_right, Nat.add_one_sub_one, getElem_cons_succ]
      simp only [← take_succ_cons]
      rw[take_getLast]
      simp
    }
  }

theorem List.idxOf_map_eq_of_inj {β : Type _} [DecidableEq α] [DecidableEq β] {l : List α}
{f : α → β} (hf : Injective f) (a : α) : (l.map f).idxOf (f a) = l.idxOf a := by{
  induction l with
  | nil => simp
  | cons x l' ih => {
    rw[map_cons]
    cases em (x = a) with
    | inl hxa => {
      simp only [hxa, idxOf_cons_self]
    }
    | inr hxa => {
      have hxa':f x ≠ f a:=by{
        rw[hf.ne_iff]
        exact hxa
      }
      simp only [ne_eq, hxa', not_false_eq_true, idxOf_cons_ne, Nat.succ_eq_add_one, hxa,
        Nat.add_right_cancel_iff]
      exact ih
    }
  }
}

theorem List.concat_dropLast_getLast {p : List α} (hp : p ≠ [])
  : List.dropLast p ++ [p.getLast hp] = p:=by{
    match p with
    | [_] => simp
    | a::b::p' => {
      simp only [dropLast_cons₂, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_append,
        cons.injEq, true_and]
      apply concat_dropLast_getLast
    }
  }

theorem List.nodup_attachWith {p : List α} {P : α → Prop} (hp : ∀ x ∈ p, P x)
  : (p.attachWith P hp).Nodup ↔ p.Nodup := by{
    induction p with
    | nil => simp
    | cons x p' ih => {
      simp[ih]
    }
  }

theorem List.idxOf_getLast_of_nodup [DecidableEq α] {p : List α} (hp : p ≠ [])
  (hpd : p.Nodup) : p.idxOf (p.getLast hp) = p.length - 1 := by{
    rw[idxOf_getLast]
    rw[←List.concat_dropLast_getLast hp] at hpd
    rw[←List.concat_eq_append, List.nodup_concat] at hpd
    exact hpd.left
  }
theorem List.idxOf_drop_of_notMem [DecidableEq α] {p : List α} {x : α} {n : ℕ}
  (hpx : x ∉ p.take n) : (p.drop n).idxOf x = p.idxOf x - n := by{
    nth_rw 2 [←List.take_append_drop n p]
    rw[List.idxOf_append_of_notMem hpx]
    rw[Nat.add_comm, List.length_take]
    cases Nat.le_total n p.length with
    | inl hnp => rw[Nat.min_eq_left hnp, Nat.add_sub_cancel]
    | inr hnp => {
      rw[List.drop_of_length_le hnp]
      rw[Nat.min_eq_right hnp]
      simp[hnp]
    }
  }
theorem List.idxOf_ge_of_mem_drop_of_notMem_take [DecidableEq α] {p : List α} {x : α} {n : ℕ}
  (hpx : x ∈ p.drop n) (hpx' : x ∉ p.take n) : n ≤ p.idxOf x:= by{
    have ih:=idxOf_drop_of_notMem hpx'
    apply Nat.le_of_not_lt
    intro h
    simp only [Nat.le_of_lt h, Nat.sub_eq_zero_of_le] at ih
    rw[List.idxOf_eq_zero_iff_eq_nil_or_head_eq] at ih
    have h0:=ne_nil_of_mem hpx
    apply (Or.resolve_left · h0) at ih
    rw[head?_eq_some_head h0, Option.some_inj] at ih
    rw[←List.take_append_drop n p] at h
    rw[List.idxOf_append_of_notMem hpx', length_take] at h
    rw[ne_eq, drop_eq_nil_iff, Nat.not_le] at h0
    rw[Nat.min_eq_left (Nat.le_of_lt h0)] at h
    have h':=Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
    simp at h'
  }
theorem List.idxOf_ge_of_mem_drop_of_nodup [DecidableEq α] {p : List α} {x : α} {n : ℕ}
  (hpx : x ∈ p.drop n) (hpd : p.Nodup) : n ≤ p.idxOf x:= by{
    apply List.idxOf_ge_of_mem_drop_of_notMem_take hpx
    rw[←List.take_append_drop n p, List.nodup_append_comm, List.nodup_append'] at hpd
    apply hpd.right.right hpx
  }
def List.revInduction {C : List α → Sort _} (nil : C [])
  (concat : (xs : List α) → (x : α) → C xs → C (xs.concat x))
  (l : List α) : C l :=
  List.reverse_reverse l ▸ l.reverse.rec (motive:=C ∘ reverse) nil
    (fun h t ht => Eq.mp (id
      (Eq.mpr (id (congrArg (fun _a ↦ C (t.reverse.concat h) = C _a) (reverse_cons' h t)))
        (Eq.refl (C (t.reverse.concat h))))) (concat t.reverse h ht) :
    (h : α) → (t : List α) → (C ∘ reverse) t → (C ∘ reverse) (h::t))
theorem List.append_suffix_append_right {l₁ l₂ l : List α} : l₁ ++ l <:+ l₂ ++ l ↔ l₁ <:+ l₂ := by{
  rw[suffix_iff_eq_append]
  rw[suffix_iff_eq_append]
  simp[Nat.add_sub_add_right, List.take_append_of_le_length (Nat.sub_le _ _)]
  simp[←List.append_assoc]
}
theorem List.exists_mem_iff_exists_getElem_minimal {P : α → Prop} {l : List α} :
  (∃ x ∈ l, P x) ↔ ∃i, ∃(hi : i < l.length), P l[i] ∧ ∀j, (hj : j < i) → ¬P l[j]:=by{
    constructor
    · {
      intro h
      rw[List.exists_mem_iff_exists_getElem] at h
      have h':=exists_minimal_of_wellFoundedLT _ h
      unfold Minimal at h'
      have ⟨i, ⟨hi0, hi1⟩, hi'⟩:=h'
      use i
      use hi0
      apply And.intro hi1
      intro j hj hj'
      have hi'':=hi' ⟨Nat.lt_trans hj hi0, hj'⟩ (Nat.le_of_lt hj)
      apply Nat.not_le_of_gt hj hi''
    }
    · {
      intro ⟨i, _, hi, _⟩
      exact ⟨l[i], List.getElem_mem _, hi⟩
    }
  }
theorem List.nodup_iff_getElem?_ne_getElem?' {l : List α} :
  l.Nodup ↔ ∀ (i j : ℕ), i ≠ j → i < l.length → j < l.length → l[i]? ≠ l[j]?
  :=by{
    rw[nodup_iff_getElem?_ne_getElem?]
    constructor
    · {
      intro h i j hij hil hjl
      cases lt_or_gt_of_ne hij with
      | inl hij => {
        exact h _ _ hij hjl
      }
      | inr hij => {
        symm
        exact h _ _ hij hil
      }
    }
    · {
      intro h i j hij hjl
      exact h _ _ (ne_of_lt hij) (lt_trans hij hjl) hjl
    }
  }
theorem List.getElem?_eq_some_getElem {xs : List α} {i : ℕ} (h : i < xs.length) :
  xs[i]? = some xs[i] := by{simp[getElem?_eq_some_getElem_iff h]}
theorem List.nodup_iff_getElem_ne_getElem {l : List α} :
  l.Nodup ↔ ∀ (i j : ℕ), (hij:i < j) → (hjl:j < l.length) → l[i] ≠ l[j]
  :=by{
    rw[nodup_iff_getElem?_ne_getElem?]
    constructor
    · {
      intro h i j hij hjl
      have h':=h i j hij hjl
      rw[getElem?_eq_some_getElem (lt_trans hij hjl)] at h'
      rw[getElem?_eq_some_getElem hjl] at h'
      rw[ne_eq, Option.some_inj] at h'
      exact h'
    }
    · {
      intro h i j hij hjl
      rw[getElem?_eq_some_getElem (lt_trans hij hjl)]
      rw[getElem?_eq_some_getElem hjl]
      rw[ne_eq, Option.some_inj]
      exact h _ _ hij hjl
    }
  }
theorem List.nodup_iff_getElem_ne_getElem' {l : List α} :
  l.Nodup ↔ ∀ (i j : ℕ), (hij:i ≠ j) → (hil:i < l.length) → (hjl:j < l.length) → l[i] ≠ l[j]
  :=by{
    rw[nodup_iff_getElem_ne_getElem]
    constructor
    · {
      intro h i j hij hil hjl
      cases lt_or_gt_of_ne hij with
      | inl hij => {
        exact h _ _ hij hjl
      }
      | inr hij => {
        symm
        exact h _ _ hij hil
      }
    }
    · {
      intro h i j hij hjl
      exact h _ _ (ne_of_lt hij) (lt_trans hij hjl) hjl
    }
  }

