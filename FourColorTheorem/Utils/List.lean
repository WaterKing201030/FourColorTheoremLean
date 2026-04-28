import Batteries.Data.List.Basic
import Init.Data.List.Pairwise
import Mathlib.Data.List.Nodup

open Relation
open Function

variable {α : Type _}

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
