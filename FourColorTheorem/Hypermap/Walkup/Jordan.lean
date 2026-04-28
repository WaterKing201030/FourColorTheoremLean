import FourColorTheorem.Hypermap.Walkup.Skip

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem walkupe_moebius_path_head_ne_or_tail_ne_node {x : α} {p : List {a // a ≠ x}}
  (hp : (H.WalkupE x).moebius_path p) :
  p.head (moebius_path_ne_nil hp) ≠ H.nodeinv x ∨ p.getLast (moebius_path_ne_nil hp)
  ≠ H.node x :=by{
    cases em (p.head (moebius_path_ne_nil hp) = H.nodeinv x) with
    | inl hp0 => {
      right
      intro h
      have hp':=moebius_path_not_eq' hp
      rw[walkupe_node, ne_eq, Subtype.ext_iff, skip_val, hp0, h] at hp'
      apply hp'
      rw[skip'_eq_of_apply_eq, nodeinv_rightinv]
      rw[nodeinv_rightinv]
    }
    | inr hp0 => exact Or.inl hp0
  }
theorem skip'_nodup_cross_head_ne_or_tail_ne_node {x : α} {p : List α} (hp : p ≠ []) (hpd : p.Nodup)
  (hpm : skip' H.node x (p.head hp) ∈ p.tail.drop (p.tail.idxOf (skip' H.nodeinv x (p.getLast hp))))
  : p.head hp ≠ H.nodeinv x ∨ p.getLast hp ≠ H.node x := by{
    have hpm':=List.ne_nil_of_mem hpm
    simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
    rw[List.idxOf_lt_length_iff] at hpm'
    rw[←List.cons_head_tail hp, List.nodup_cons] at hpd
    symm
    apply (em (p.head hp = H.nodeinv x)).imp_left
    intro h0 h1
    rw[h1] at hpm'
    rw[skip'_eq_of_apply_eq (nodeinv_leftinv x), nodeinv_leftinv, ←h0] at hpm'
    exact hpd.left hpm'
  }

def clink1 (x : α) : α → α → Prop :=fromFun H.nodeinv ∪ fromFun (skip' H.face x)
def clink2 (x : α) : α → α → Prop :=fromFun (skip' H.nodeinv x) ∪ fromFun (skip' H.face x)

@[inline] instance cclink1.instDecidableRel : DecidableRel (H.clink1 x)
  := union.dec
@[inline] instance cclink2.instDecidableRel : DecidableRel (H.clink2 x)
  := union.dec
theorem walkupe_ischain_clink_iff_ischain_clink2 {x : α} {p : List {a // a ≠ x}}
  : List.IsChain (H.WalkupE x).clink p ↔ List.IsChain (H.clink2 x) (p.map Subtype.val) := by{
    match p with
    | [] | [_] => simp
    | a::b::p' => {
      rw[List.isChain_cons_cons]
      rw[List.map_cons, List.map_cons]
      rw[List.isChain_cons_cons]
      rw[←List.map_cons]
      apply and_congr
      · {
        unfold clink clink2
        simp only [union_iff, fromFun]
        apply or_congr
        · {
          rw[nodeinv_eq_iff_eq_node, walkupe_node]
          rw[nodeinv, ←skip_val]
          · {
            rw[Fintype.skip_bijInv_comm]
            rw[←Subtype.ext_iff]
            rw[Fintype.bijInv_eq_iff_eq_apply]
          }
          · {
            apply Bijective.injective ∘ Fintype.bijective_bijInv
            exact H.node_bijective
          }
        }
        · rw[walkupe_face, Subtype.ext_iff, skip_val]
      }
      · apply walkupe_ischain_clink_iff_ischain_clink2
    }
  }
theorem ischain_clink1_of_ischain_clink2_of_nodeinv_not_mem {x : α} {p : List α}
  (hp : List.IsChain (H.clink2 x) p) (hn : H.nodeinv x ∉ p) :
  List.IsChain (H.clink1 x) p := by{
    match p with
    | [] | [_] => simp
    | a::b::p' => {
      rw[List.isChain_cons_cons]
      rw[List.isChain_cons_cons] at hp
      rw[List.mem_cons, not_or] at hn
      apply hp.imp
      · {
        simp only [hp, forall_const]
        simp only [clink1, union_iff, fromFun]
        have hp':=hp.left
        simp only [clink2, union_iff, fromFun] at hp'
        cases em (skip' H.face x a = b) with
        | inl hf => exact Or.inr hf
        | inr hf => {
          apply (Or.resolve_right · hf) at hp'
          left
          rw[List.mem_cons, not_or] at hn
          apply of_not_not
          intro hab
          apply hn.right.left
          unfold skip' at hp'
          cases em (H.nodeinv a = x) with
          | inl hax => {
            simp only [hax, ↓reduceIte] at hp'
            exact hp'
          }
          | inr hax => {
            simp[hax] at hp'
            contradiction
          }
        }
      }
      · {
        apply (ischain_clink1_of_ischain_clink2_of_nodeinv_not_mem · hn.right)
      }
    }
  }
theorem ischain_clink1_of_ischain_clink2_of_node_not_mem {x : α} {p : List α}
  (hp : List.IsChain (H.clink2 x) p) (hn : H.node x ∉ p) :
  List.IsChain (H.clink1 x) p := by{
    match p with
    | [] | [_] => simp
    | a::b::p' => {
      rw[List.isChain_cons_cons]
      rw[List.isChain_cons_cons] at hp
      rw[List.mem_cons, not_or] at hn
      apply hp.imp
      · {
        simp only [hp, forall_const]
        simp only [clink1, union_iff, fromFun]
        have hp':=hp.left
        simp only [clink2, union_iff, fromFun] at hp'
        cases em (skip' H.face x a = b) with
        | inl hf => exact Or.inr hf
        | inr hf => {
          apply (Or.resolve_right · hf) at hp'
          left
          rw[List.mem_cons, not_or] at hn
          apply of_not_not
          intro hab
          apply hn.right.left
          unfold skip' at hp'
          cases em (H.nodeinv a = x) with
          | inl hax => {
            rw[nodeinv_eq_iff_eq_node] at hax
            simp[hax] at hn
          }
          | inr hax => {
            simp[hax] at hp'
            contradiction
          }
        }
      }
      · {
        apply (ischain_clink1_of_ischain_clink2_of_node_not_mem · hn.right)
      }
    }
  }
theorem ischain_clink_of_ischain_clink1_of_face_not_mem {x : α} {p : List α}
  (hp : List.IsChain (H.clink1 x) p) (hf : H.face x ∉ p) :
  List.IsChain H.clink p := by{
    match p with
    | [] | [_] => simp
    | a::b::p' => {
      rw[List.isChain_cons_cons]
      rw[List.isChain_cons_cons] at hp
      rw[List.mem_cons, not_or] at hf
      apply hp.imp
      · {
        simp only [hp, forall_const]
        simp only [clink, union_iff, fromFun]
        have hp':=hp.left
        simp only [clink1, union_iff, fromFun] at hp'
        cases em (H.nodeinv a = b) with
        | inl hn => exact Or.inl hn
        | inr hn => {
          apply (Or.resolve_left · hn) at hp'
          right
          rw[List.mem_cons, not_or] at hf
          apply of_not_not
          intro hab
          apply hf.right.left
          unfold skip' at hp'
          cases em (H.face a = x) with
          | inl hax => {
            simp only [hax, ↓reduceIte] at hp'
            exact hp'
          }
          | inr hax => {
            simp[hax] at hp'
            contradiction
          }
        }
      }
      · {
        apply (ischain_clink_of_ischain_clink1_of_face_not_mem · hf.right)
      }
    }
  }
theorem ischain_clink_of_ischain_clink1_of_faceinv_not_mem {x : α} {p : List α}
  (hp : List.IsChain (H.clink1 x) p) (hf : H.faceinv x ∉ p) :
  List.IsChain H.clink p := by{
    match p with
    | [] | [_] => simp
    | a::b::p' => {
      rw[List.isChain_cons_cons]
      rw[List.isChain_cons_cons] at hp
      rw[List.mem_cons, not_or] at hf
      apply hp.imp
      · {
        simp only [hp, forall_const]
        simp only [clink, union_iff, fromFun]
        have hp':=hp.left
        simp only [clink1, union_iff, fromFun] at hp'
        cases em (H.nodeinv a = b) with
        | inl hn => exact Or.inl hn
        | inr hn => {
          apply (Or.resolve_left · hn) at hp'
          right
          rw[List.mem_cons, not_or] at hf
          unfold skip' at hp'
          rw[faceinv_eq_iff_eq_face] at hf
          rw[Eq.comm (a:=x)] at hf
          simp[hf] at hp'
          simp[hp']
        }
      }
      · {
        apply (ischain_clink_of_ischain_clink1_of_faceinv_not_mem · hf.right)
      }
    }
  }
theorem exists_faceinv_face_of_clink1_of_not_clink {x : α} {p : List α}
  (hpc : List.IsChain (H.clink1 x) p) (hpc' : ¬List.IsChain H.clink p) :
  ∃ i, ∃ (h:i < p.length - 1), p[i]'(Nat.lt_of_lt_pred h)
  = H.faceinv x ∧ p[i + 1]'(Nat.succ_lt_of_lt_pred h) = H.face x:=by{
    match p with
    | [] | [_] => simp at hpc'
    | a::b::p' => {
      rw[List.isChain_cons_cons] at hpc hpc'
      rw[not_and] at hpc'
      cases em (H.clink a b) with
      | inl hab => {
        have hpc':=hpc' hab
        have ⟨i, hi, hfi, hfi'⟩:=exists_faceinv_face_of_clink1_of_not_clink hpc.right hpc'
        use i + 1
        simp only [List.length_cons, add_tsub_cancel_right] at hi
        simp only [List.getElem_cons_succ, List.length_cons, add_tsub_cancel_right,
          Order.lt_add_one_iff, Order.add_one_le_iff]
        use hi
        simp at hfi'
        simp[hfi, hfi']
      }
      | inr hab => {
        have hab':=hpc.left
        simp only [clink, union_iff, fromFun, not_or] at hab
        simp only [clink1, union_iff, fromFun] at hab'
        simp only [hab, false_or] at hab'
        unfold skip' at hab'
        cases em (H.face a = x) with
        | inl hfa => {
          simp only [hfa, ↓reduceIte] at hab'
          use 0
          simp only [List.getElem_cons_zero, zero_add, List.getElem_cons_succ, hab', and_true,
            List.length_cons, add_tsub_cancel_right, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le, exists_const]
          symm
          rw[faceinv_eq_iff_eq_face]
          simp[hfa]
        }
        | inr hfa => {
          simp only [hfa, ↓reduceIte] at hab'
          have hab:=hab.right
          contradiction
        }
      }
    }
  }
theorem exists_node_nodeinv_of_clink2_of_not_clink1 {x : α} {p : List α}
  (hpc : List.IsChain (H.clink2 x) p) (hpc' : ¬List.IsChain (H.clink1 x) p) :
  ∃ i, ∃ (h:i < p.length - 1), p[i]'(Nat.lt_of_lt_pred h) = H.node x
  ∧ p[i + 1]'(Nat.succ_lt_of_lt_pred h) = H.nodeinv x:=by{
    match p with
    | [] | [_] => simp at hpc'
    | a::b::p' => {
      rw[List.isChain_cons_cons] at hpc hpc'
      rw[not_and] at hpc'
      cases em (H.clink1 x a b) with
      | inl hab => {
        have hpc':=hpc' hab
        have ⟨i, hi, hfi, hfi'⟩:=exists_node_nodeinv_of_clink2_of_not_clink1 hpc.right hpc'
        use i + 1
        simp only [List.length_cons, add_tsub_cancel_right] at hi
        simp only [List.getElem_cons_succ, List.length_cons, add_tsub_cancel_right,
          Order.lt_add_one_iff, Order.add_one_le_iff]
        use hi
        simp at hfi'
        simp[hfi, hfi']
      }
      | inr hab => {
        have hab':=hpc.left
        simp only [clink1, union_iff, fromFun, not_or] at hab
        simp only [clink2, union_iff, fromFun] at hab'
        simp only [hab, or_false] at hab'
        unfold skip' at hab'
        cases em (H.nodeinv a = x) with
        | inl hfa => {
          simp only [hfa, ↓reduceIte] at hab'
          use 0
          simp only [List.getElem_cons_zero, zero_add, List.getElem_cons_succ, hab', and_true,
            List.length_cons, add_tsub_cancel_right, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le, exists_const]
          symm
          rw[nodeinv_eq_iff_eq_node] at hfa
          simp[hfa]
        }
        | inr hfa => {
          simp only [hfa, ↓reduceIte] at hab'
          have hab:=hab.left
          contradiction
        }
      }
    }
  }
theorem split_nodup_ischain_clink1_of_not_clink {x : α} {p : List α}
  (hpd : p.Nodup) (hpc : List.IsChain (H.clink1 x) p) (hpc' : ¬List.IsChain H.clink p)
  : ∃p₁ p₂, p₁ ++ p₂ = p ∧ List.IsChain H.clink (p₁ ++ [x] ++ p₂) ∧ p₁ ≠ [] ∧ p₂ ≠ []
  ∧ p₁.getLast? = some (H.faceinv x) ∧ p₂.head? = some (H.face x):=by{
    have ⟨i, hi, hfi, hfi'⟩:=exists_faceinv_face_of_clink1_of_not_clink hpc hpc'
    use p.take (i + 1)
    use p.drop (i + 1)
    rw[List.take_append_drop]
    apply And.intro rfl
    have hp:p ≠ []:=by{intro hp; simp[hp] at hpc'}
    have hfp1:p.take (i + 1) ≠ []:=by{simp[hp]}
    have hfp2:p.drop (i + 1) ≠ []:=by{
      simp only [ne_eq, List.drop_eq_nil_iff, not_le]
      exact Nat.succ_lt_of_lt_pred hi
    }
    simp only [List.head?_eq_some_head hfp2, List.head_drop, hfi', and_true]
    simp only [List.getLast?_eq_some_getLast hfp1, List.take_getLast hfp1]
    have h0:=Nat.succ_lt_of_lt_pred hi
    simp only [Nat.sub_eq, tsub_zero] at h0
    have h1:=min_eq_right_of_lt h0
    simp only [h1, ←Nat.pred_eq_sub_one, Nat.pred_succ, hfi, and_true]
    simp only [ne_eq, hfp1, not_false_eq_true,
      hfp2, and_self, and_true]
    rw[List.isChain_concat_append]
    constructor
    · {
      rw[List.isChain_concat_iff_of_ne_nil hfp1]
      constructor
      · {
        apply ischain_clink_of_ischain_clink1_of_face_not_mem (List.isChain_take hpc)
        rw[←List.take_append_drop (i + 1) p] at hpd
        rw[List.nodup_append] at hpd
        have hpd:=hpd.right.right
        have hpd:=Function.swap (hpd (a:=H.face x) (b:=H.face x))
          (List.mem_of_getElem (i:=0) (by{
            rw[List.getElem_drop]
            · simp[hfi']
            simp only [List.length_drop, tsub_pos_iff_lt]
            exact Nat.succ_lt_of_lt_pred hi
          }))
        simp at hpd
        simp[hpd]
      }
      · {
        simp [List.getLast_take, add_tsub_cancel_right,
        List.getElem?_eq_getElem (Nat.lt_of_lt_pred hi), hfi, clink, union_iff, fromFun,
        faceinv_eq, fen_cancel]
      }
    }
    · {
      rw[List.isChain_cons_iff_of_ne_nil hfp2]
      constructor
      · simp[hfi', clink, union_iff, fromFun]
      · {
        rw[←List.take_append_drop (i + 1) p] at hpd
        rw[List.nodup_append] at hpd
        have hpd:=hpd.right.right (H.faceinv x) (List.mem_of_getElem (i:=i) (by{
          rw[List.getElem_take]
          · simp[hfi]
          simp only [List.length_take, lt_inf_iff, lt_add_iff_pos_right, zero_lt_one, true_and]
          apply Nat.lt_of_lt_pred hi
        })) (H.faceinv x)
        simp only [ne_eq, not_true_eq_false, imp_false] at hpd
        apply ischain_clink_of_ischain_clink1_of_faceinv_not_mem (List.isChain_drop hpc) hpd
      }
    }
  }

theorem exists_moebius_path_of_not_mem_of_nodup_of_clink_of_walkupe_cross_nlink {x : α} {p : List α}
  (hp : p ≠ []) (hpx : x ∉ p) (hpd : p.Nodup) (hpc : p.IsChain H.clink)
  (hpm : skip' H.node x (p.head hp) ∈ p.tail.drop (p.tail.idxOf (skip' H.nodeinv x (p.getLast hp))))
  : ∃q, H.moebius_path q:=by{
    have h:=skip'_nodup_cross_head_ne_or_tail_ne_node hp hpd hpm
    cases em (H.node x = x) with
    | inl hnx => {
      have hnx':H.nodeinv x = x:=by{rw[nodeinv_eq_iff_eq_node, hnx]}
      have h0 : skip' H.node x (p.head hp) = H.node (p.head hp) :=by{
        apply skip'_eq_of_apply_ne
        rw[ne_eq, ←eq_nodeinv_iff_node_eq, hnx']
        intro h
        apply hpx
        rw[h] at hpm
        nth_rw 3 [←hnx'] at hpm
        rw[skip'_eq_of_apply_eq (nodeinv_rightinv _)] at hpm
        rw[nodeinv_rightinv, hnx] at hpm
        have hpm':=List.mem_of_mem_drop hpm
        exact List.mem_of_mem_tail hpm'
      }
      rw[h0] at hpm
      have h1 : skip' H.nodeinv x (p.getLast hp) = H.nodeinv (p.getLast hp):=by{
        apply skip'_eq_of_apply_ne
        intro h
        have hpm':=List.ne_nil_of_mem hpm
        simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
        rw[List.idxOf_lt_length_iff] at hpm'
        rw[skip'_eq_of_apply_eq h, h, hnx'] at hpm'
        apply hpx
        exact List.mem_of_mem_tail hpm'
      }
      rw[h1] at hpm
      use p
      unfold moebius_path
      simp only [hp, ↓reduceDIte, hpd, hpc, true_and]
      exact hpm
    }
    | inr hnx => {
      have hnx':H.nodeinv x ≠ x:=by{rw[ne_eq, nodeinv_eq_iff_eq_node, Eq.comm]; exact hnx}
      cases em (p.head hp = H.nodeinv x) with
      | inl hp0 => {
        have h:=h.neg_resolve_left hp0
        use x::p
        unfold moebius_path
        simp only [reduceCtorEq, ↓reduceDIte, List.nodup_cons, List.tail_cons, List.head_cons]
        simp only[hpx, hpd, not_false_eq_true, true_and]
        constructor
        · {
          rw[List.isChain_cons_iff_of_ne_nil hp]
          rw[hp0]
          simp[hpc]
          simp[clink, union_iff, fromFun]
        }
        · {
          rw[hp0, skip'_eq_of_apply_eq (nodeinv_rightinv x), nodeinv_rightinv] at hpm
          rw[List.getLast_cons hp]
          have h':H.nodeinv (p.getLast hp) ≠ H.nodeinv x:=by{
            rw[nodeinv_injective.ne_iff]
            intro h
            apply hpx
            rw[←h]
            apply List.getLast_mem
          }
          have h'':H.nodeinv (p.getLast hp) ≠ x:=by{
            rw[ne_eq, nodeinv_eq_iff_eq_node]
            exact h
          }
          rw[skip'_eq_of_apply_ne h''] at hpm
          nth_rw 2 3 [←List.cons_head_tail hp]
          rw[List.idxOf_cons_ne _ (by{rw[hp0]; exact h'.symm})]
          rw[List.drop_succ_cons]
          exact hpm
        }
      }
      | inr hp0 => {
        have hp0' : skip' H.node x (p.head hp) = H.node (p.head hp):=by{
          rw[skip'_eq_of_apply_ne]
          rw[ne_eq, ←eq_nodeinv_iff_node_eq]
          exact hp0
        }
        rw[hp0'] at hpm
        cases em (p.getLast hp = H.node x) with
        | inl hp1 => {
          use p++[x]
          unfold moebius_path
          simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceDIte, ne_eq,
            not_false_eq_true, List.getLast_append_of_ne_nil, List.getLast_singleton]
          simp only [←List.concat_eq_append, List.nodup_concat, hpx, hpd,
          not_false_eq_true, true_and]
          simp only [List.concat_eq_append]
          rw[List.isChain_concat_iff_of_ne_nil hp]
          constructor
          · {
            simp[hpc]
            simp[clink, hp1, union_iff, fromFun, nodeinv_leftinv]
          }
          rw[hp1, skip'_eq_of_apply_eq (nodeinv_leftinv _), nodeinv_leftinv _] at hpm
          rw[List.head_append_left hp]
          rw[List.tail_append_of_ne_nil hp]
          have hp2:=List.ne_nil_of_mem hpm
          simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hp2
          rw[List.idxOf_lt_length_iff] at hp2
          rw[List.idxOf_append_of_mem hp2]
          rw[List.drop_append_of_le_length List.idxOf_le_length]
          apply List.mem_append_left
          exact hpm
        }
        | inr hp1 => {
          have hp1' : skip' H.nodeinv x (p.getLast hp) = H.nodeinv (p.getLast hp):=by{
            rw[skip'_eq_of_apply_ne]
            rw[ne_eq, nodeinv_eq_iff_eq_node]
            exact hp1
          }
          rw[hp1'] at hpm
          use p
          unfold moebius_path
          simp only [hp, ↓reduceDIte, hpd, hpc, true_and]
          exact hpm
        }
      }
    }
  }
theorem exists_moebius_path_of_not_mem_of_nodup_of_clink1_of_walkupe_cross_nlink {x : α}
  {p : List α} (hp : p ≠ []) (hpx : x ∉ p) (hpd : p.Nodup) (hpc : p.IsChain (H.clink1 x))
  (hpm : skip' H.node x (p.head hp) ∈ p.tail.drop (p.tail.idxOf (skip' H.nodeinv x (p.getLast hp))))
  : ∃q, H.moebius_path q:=by{
    have h:=skip'_nodup_cross_head_ne_or_tail_ne_node hp hpd hpm
    cases em (p.IsChain H.clink) with
    | inl hpc' => {
      have ih:=exists_moebius_path_of_not_mem_of_nodup_of_clink_of_walkupe_cross_nlink hp hpx
        hpd hpc' hpm
      exact ih
    }
    | inr hpc' => {
      have ⟨q₁, q₂, hqp, hqc, hq₁, hq₂, hq₁l, hq₂h⟩:=split_nodup_ischain_clink1_of_not_clink
        hpd hpc hpc'
      rw[List.getLast?_eq_some_getLast hq₁, Option.some_inj] at hq₁l
      rw[List.head?_eq_some_head hq₂, Option.some_inj] at hq₂h
      have hq₁h : q₁.head hq₁ = p.head hp:=by{
        simp only [←hqp, List.head_append_left hq₁]
      }
      have hq₂l : q₂.getLast hq₂ = p.getLast hp:=by{
        simp only [←hqp, List.getLast_append_right hq₂]
      }
      have hqd:List.Nodup (q₁ ++ [x] ++ q₂):=by{
        rw[List.append_assoc, List.nodup_append_comm]
        rw[List.singleton_append, List.cons_append, List.nodup_cons]
        rw[List.mem_append, Or.comm, ←List.mem_append, hqp]
        rw[List.nodup_append_comm, hqp]
        exact ⟨hpx, hpd⟩
      }
      cases em (p.head hp = H.nodeinv x) with
      | inl hp0 => {
        have h:=h.neg_resolve_left hp0
        have h' : skip' H.nodeinv x (p.getLast hp) = H.nodeinv (p.getLast hp) := by{
          rw[skip'_eq_of_apply_ne]
          rw[ne_eq, nodeinv_eq_iff_eq_node]
          exact h
        }
        have h0:H.nodeinv (p.getLast hp) ∈ p.tail:=by{
          have hpm':=List.ne_nil_of_mem hpm
          simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
          rw[List.idxOf_lt_length_iff] at hpm'
          rw[h'] at hpm'
          exact hpm'
        }
        have h'':skip' H.node x (p.head hp) = H.node x:=by{
          rw[skip'_eq_of_apply_eq, hp0, nodeinv_rightinv]
          rw[hp0, nodeinv_rightinv]
        }
        rw[h'', h'] at hpm
        cases em (H.nodeinv (p.getLast hp) ∈ q₁) with
        | inl hqm => {
          use q₁ ++ [x] ++ q₂
          unfold moebius_path
          have hqm':H.nodeinv (p.getLast hp) ∈ q₁.tail :=by{
            match q₁ with
            | _::_ => {
              rw[List.tail_cons]
              rw[List.mem_cons] at hqm
              apply hqm.resolve_left
              simp only [←hqp, List.cons_append, List.head_cons] at hp0
              rw[hp0, nodeinv_injective.eq_iff]
              intro h
              apply hpx
              rw[←h]
              apply List.getLast_mem
            }
          }
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_eq_nil_iff,
            reduceCtorEq, and_false, ↓reduceDIte]
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hqd hqc
          apply And.intro hqd
          apply And.intro hqc
          rw[List.head_append_left hq₁, hq₁h, hp0, nodeinv_rightinv]
          rw[List.getLast_append_right (by{simp}), List.getLast_cons hq₂, hq₂l]
          rw[List.tail_append_of_ne_nil hq₁]
          rw[List.idxOf_append_of_mem hqm']
          rw[List.drop_append_of_le_length List.idxOf_le_length]
          simp
        }
        | inr hqm => {
          use [x] ++ q₂
          have hqd': List.Nodup ([x] ++ q₂) := by{
            rw[List.append_assoc] at hqd
            exact List.Nodup.of_append_right hqd
          }
          have hqc : List.IsChain H.clink ([x] ++ q₂) := by{
            rw[List.append_assoc] at hqc
            exact List.IsChain.right_of_append hqc
          }
          have h1:H.nodeinv (p.getLast hp) ∈ q₂:=by{
            have h0':=List.mem_of_mem_tail h0
            nth_rw 1 [←hqp] at h0'
            rw[List.mem_append] at h0'
            apply h0'.resolve_left
            exact hqm
          }
          nth_rw 2 3 [←hqp] at hpm
          rw[List.tail_append_of_ne_nil hq₁] at hpm
          have h2:=List.idxOf_append_of_notMem (fun h => hqm (List.mem_of_mem_tail h)) (l₂:=q₂)
          rw[h2, ←List.drop_drop, List.drop_append_length] at hpm
          unfold moebius_path
          simp only [hqd', hqc, true_and]
          simp only [List.cons_append, List.nil_append, reduceCtorEq, ↓reduceDIte, List.tail_cons,
            List.head_cons]
          rw[List.getLast_cons hq₂, hq₂l]
          exact hpm
        }
      }
      | inr hp0 => {
        have hp0':skip' H.node x (p.head hp) = H.node (p.head hp):=by{
          rw[skip'_eq_of_apply_ne]
          rw[ne_eq, ←eq_nodeinv_iff_node_eq]
          exact hp0
        }
        rw[hp0'] at hpm
        have hp0'': H.node (p.head hp) ∈ p.tail := by{
          apply List.mem_of_mem_drop hpm
        }
        cases em (p.getLast hp = H.node x) with
        | inl hp1 => {
          have hp1' : skip' H.nodeinv x (p.getLast hp) = H.nodeinv x:=by{
            rw[hp1, skip'_eq_of_apply_eq (nodeinv_leftinv _), nodeinv_leftinv]
          }
          rw[hp1'] at hpm
          nth_rw 1 [←hqp, List.tail_append_of_ne_nil hq₁, List.mem_append] at hp0''
          nth_rw 1 2 [←hqp] at hpm
          rw[List.tail_append_of_ne_nil hq₁] at hpm
          cases em (H.nodeinv x ∈ q₁.tail) with
          | inl h0 => {
            cases em (H.node (p.head hp) ∈ q₁.tail) with
            | inl h1 => {
              use q₁ ++ [x]
              unfold moebius_path
              rw[dite_cond_eq_false (by{simp})]
              apply And.intro (List.Nodup.of_append_left hqd)
              apply And.intro (List.IsChain.left_of_append hqc)
              rw[List.head_append_left hq₁, hq₁h]
              rw[List.tail_append_of_ne_nil hq₁, List.getLast_append_singleton]
              rw[List.idxOf_append_of_mem h0]
              rw[List.drop_append_of_le_length List.idxOf_le_length]
              rw[List.mem_append]
              left
              rw[List.idxOf_append_of_mem h0] at hpm
              rw[List.drop_append_of_le_length List.idxOf_le_length] at hpm
              rw[←hqp] at hpd
              rw[List.nodup_append'] at hpd
              have hpd':=hpd.right.right (List.mem_of_mem_tail h1)
              rw[List.mem_append] at hpm
              apply hpm.resolve_right
              exact hpd'
            }
            | inr h1 => {
              have h2:=List.mem_of_mem_drop hpm
              rw[List.mem_append] at h2
              have h2:=h2.resolve_left h1
              use q₁ ++ [x] ++ q₂
              unfold moebius_path
              rw[dite_cond_eq_false (by{simp})]
              simp only [hqd, hqc, true_and]
              simp only [List.append_assoc]
              rw[List.head_append_left hq₁]
              rw[List.tail_append_of_ne_nil hq₁]
              simp only [←List.append_assoc q₁]
              rw[List.getLast_append_right hq₂, hq₂l, hq₁h, hp1, nodeinv_leftinv]
              rw[List.idxOf_append_of_notMem (by{
                intro h; apply hpx; rw[←hqp];
                apply List.mem_append_left; apply List.mem_of_mem_tail h
              })]
              rw[List.drop_length_add_append]
              rw[List.singleton_append, List.idxOf_cons_eq _ rfl]
              rw[List.drop_zero]
              rw[List.mem_cons]
              right
              rw[List.idxOf_append_of_mem h0] at hpm
              rw[List.drop_append_of_le_length List.idxOf_le_length] at hpm
              rw[List.mem_append] at hpm
              apply hpm.resolve_left
              intro h
              apply h1
              exact List.mem_of_mem_drop h
            }
          }
          | inr h0 => {
            use q₁ ++ [x] ++ q₂
            unfold moebius_path
            simp only [hqd, hqc, true_and]
            rw[dite_cond_eq_false (by{simp})]
            simp only [List.append_assoc]
            rw[List.head_append_left hq₁]
            rw[List.tail_append_of_ne_nil hq₁]
            simp only [←List.append_assoc q₁]
            rw[List.getLast_append_right hq₂, hq₂l, hq₁h, hp1, nodeinv_leftinv]
            rw[List.idxOf_append_of_notMem (by{
              intro h; apply hpx; rw[←hqp];
              apply List.mem_append_left; apply List.mem_of_mem_tail h
            })]
            rw[List.drop_length_add_append]
            rw[List.singleton_append, List.idxOf_cons_eq _ rfl]
            rw[List.drop_zero]
            rw[List.mem_cons]
            right
            rw[List.idxOf_append_of_notMem h0] at hpm
            rw[List.drop_length_add_append] at hpm
            apply List.mem_of_mem_drop hpm
          }
        }
        | inr hp1 => {
          have hp1':skip' H.nodeinv x (p.getLast hp) = H.nodeinv (p.getLast hp):=by{
            rw[skip'_eq_of_apply_ne]
            rw[ne_eq, nodeinv_eq_iff_eq_node]
            exact hp1
          }
          rw[hp1'] at hpm
          use q₁ ++ [x] ++ q₂
          unfold moebius_path
          simp only [hqd, hqc, true_and]
          simp only [List.append_assoc]
          simp only [List.head_append_left hq₁, hq₁h]
          have h':[x] ++ q₂ ≠ []:=by{simp}
          simp only [List.getLast_append_right h']
          simp only [List.getLast_append_right hq₂, hq₂l]
          rw[dite_cond_eq_false (by{simp})]
          rw[List.tail_append_of_ne_nil hq₁]
          have h0:H.nodeinv (p.getLast hp) ∈ p.tail:=by{
            have hpm':=List.ne_nil_of_mem hpm
            simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
            rw[List.idxOf_lt_length_iff] at hpm'
            exact hpm'
          }
          nth_rw 1 [←hqp] at h0
          nth_rw 2 3 [←hqp] at hpm
          rw[List.tail_append_of_ne_nil hq₁, List.mem_append] at h0
          rw[List.tail_append_of_ne_nil hq₁] at hpm
          cases em (H.nodeinv (p.getLast hp) ∈ q₁.tail) with
          | inl h2 => {
            rw[List.idxOf_append_of_mem h2]
            rw[List.idxOf_append_of_mem h2] at hpm
            rw[List.drop_append_of_le_length List.idxOf_le_length]
            rw[List.drop_append_of_le_length List.idxOf_le_length] at hpm
            rw[List.mem_append] at hpm
            rw[List.mem_append]
            apply hpm.imp_right
            simp only [List.cons_append, List.nil_append, List.mem_cons]
            apply Or.inr
          }
          | inr h2 => {
            rw[List.idxOf_append_of_notMem h2]
            rw[List.idxOf_append_of_notMem h2] at hpm
            rw[List.drop_length_add_append] at hpm
            rw[List.drop_length_add_append]
            rw[List.singleton_append]
            rw[List.idxOf_cons_ne _ (by{symm; rw[ne_eq, nodeinv_eq_iff_eq_node]; exact hp1})]
            rw[List.drop_succ_cons]
            exact hpm
          }
        }
      }
    }
  }
theorem split_nodup_ischain_clink2_of_not_clink1 {x : α} {p : List α}
  (hpd : p.Nodup) (hpc : List.IsChain (H.clink2 x) p) (hpc' : ¬List.IsChain (H.clink1 x) p)
  : ∃p₁ p₂, p₁ ++ p₂ = p ∧ List.IsChain (H.clink1 x) (p₁ ++ [x] ++ p₂) ∧ p₁ ≠ [] ∧ p₂ ≠ []
  ∧ p₁.getLast? = some (H.node x) ∧ p₂.head? = some (H.nodeinv x):=by{
    have ⟨i, hi, hfi, hfi'⟩:=exists_node_nodeinv_of_clink2_of_not_clink1 hpc hpc'
    use p.take (i + 1)
    use p.drop (i + 1)
    rw[List.take_append_drop]
    apply And.intro rfl
    have hp:p ≠ []:=by{intro hp; simp[hp] at hpc'}
    have hfp1:p.take (i + 1) ≠ []:=by{simp[hp]}
    have hfp2:p.drop (i + 1) ≠ []:=by{
      simp only [ne_eq, List.drop_eq_nil_iff, not_le]
      exact Nat.succ_lt_of_lt_pred hi
    }
    simp only [List.head?_eq_some_head hfp2, List.head_drop, hfi', and_true]
    simp only [List.getLast?_eq_some_getLast hfp1, List.take_getLast hfp1]
    have h0:=Nat.succ_lt_of_lt_pred hi
    simp only [Nat.sub_eq, tsub_zero] at h0
    have h1:=min_eq_right_of_lt h0
    simp only [h1, ←Nat.pred_eq_sub_one, Nat.pred_succ, hfi, and_true]
    simp only [ne_eq, hfp1, not_false_eq_true,
      hfp2, and_self, and_true]
    rw[List.isChain_concat_append]
    constructor
    · {
      rw[List.isChain_concat_iff_of_ne_nil hfp1]
      constructor
      · {
        apply ischain_clink1_of_ischain_clink2_of_nodeinv_not_mem (List.isChain_take hpc)
        rw[←List.take_append_drop (i + 1) p] at hpd
        rw[List.nodup_append] at hpd
        have hpd:=hpd.right.right
        have hpd:=Function.swap (hpd (a:=H.nodeinv x) (b:=H.nodeinv x))
          (List.mem_of_getElem (i:=0) (by{
            rw[List.getElem_drop]
            · simp[hfi']
            simp only [List.length_drop, tsub_pos_iff_lt]
            exact Nat.succ_lt_of_lt_pred hi
          }))
        simp at hpd
        simp[hpd]
      }
      · {
        simp [List.getLast_take, add_tsub_cancel_right,
        List.getElem?_eq_getElem (Nat.lt_of_lt_pred hi), hfi, clink1, union_iff, fromFun,
        nodeinv_leftinv]
      }
    }
    · {
      rw[List.isChain_cons_iff_of_ne_nil hfp2]
      constructor
      · simp[hfi', clink1, union_iff, fromFun]
      · {
        rw[←List.take_append_drop (i + 1) p] at hpd
        rw[List.nodup_append] at hpd
        have hpd:=hpd.right.right (H.node x) (List.mem_of_getElem (i:=i) (by{
          rw[List.getElem_take]
          · simp[hfi]
          simp only [List.length_take, lt_inf_iff, lt_add_iff_pos_right, zero_lt_one, true_and]
          apply Nat.lt_of_lt_pred hi
        })) (H.node x)
        simp only [ne_eq, not_true_eq_false, imp_false] at hpd
        apply ischain_clink1_of_ischain_clink2_of_node_not_mem (List.isChain_drop hpc) hpd
      }
    }
  }


theorem walkupe_jordan {x : α} (h : H.jordan) : (H.WalkupE x).jordan := by{
  intro p hp
  unfold jordan at h
  have hpn : p ≠ []:=moebius_path_ne_nil hp
  have hp_backup:=hp
  unfold moebius_path at hp
  simp only [hpn, ↓reduceDIte] at hp
  rw[walkupe_ischain_clink_iff_ischain_clink2] at hp
  have ⟨hpd, hpc, hpm⟩:=hp
  rw[walkupe_nodeinv] at hpm
  rw[←List.mem_map_of_injective Subtype.val_injective] at hpm
  rw[List.map_drop, List.map_tail] at hpm
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective] at hpm
  rw[List.map_tail, skip_val, ←List.getLast_map (f:=Subtype.val) (by{
    rw[ne_eq, List.map_eq_nil_iff]; exact hpn})] at hpm
  rw[walkupe_node, skip_val, ←List.head_map (f:=Subtype.val) (by{
    rw[ne_eq, List.map_eq_nil_iff]; exact hpn})] at hpm
  generalize hp'_def : p.map Subtype.val = p'
  simp only [hp'_def] at hpc hpm
  have hp'n : p' ≠ [] :=by{
    rw[←hp'_def]
    rw[ne_eq, List.map_eq_nil_iff]
    exact hpn
  }
  have hp'x : x ∉ p' := by{
    rw[←hp'_def, List.mem_map]
    simp
  }
  have hp'd : p'.Nodup := by{
    rw[←hp'_def]
    apply (List.nodup_map_iff Subtype.val_injective).mpr hpd
  }
  cases em (p'.IsChain H.clink) with
  | inl hp'c => {
    have ⟨q, hq⟩:=exists_moebius_path_of_not_mem_of_nodup_of_clink_of_walkupe_cross_nlink
      hp'n hp'x hp'd hp'c hpm
    exact h q hq
  }
  | inr hp'c => {
    cases em (p'.IsChain (H.clink1 x)) with
    | inl hp'c1 => {
      have ⟨q, hq⟩:=exists_moebius_path_of_not_mem_of_nodup_of_clink1_of_walkupe_cross_nlink
        hp'n hp'x hp'd hp'c1 hpm
      exact h q hq
    }
    | inr hp'c1 =>{
      have ⟨p₁, p₂, hp_split_e, hp_split_c, hp₁, hp₂, hp₁l, hp₂h⟩:=
        split_nodup_ischain_clink2_of_not_clink1 hp'd hpc hp'c1
      rw[List.getLast?_eq_some_getLast hp₁, Option.some_inj] at hp₁l
      rw[List.head?_eq_some_head hp₂, Option.some_inj] at hp₂h
      have hp₁h : p₁.head hp₁ = p'.head hp'n := by{
        simp only [←hp_split_e]
        rw[List.head_append_left hp₁]
      }
      have hp₂l : p₂.getLast hp₂ = p'.getLast hp'n := by{
        simp only [←hp_split_e]
        rw[List.getLast_append_right hp₂]
      }
      have hnn : H.nodeinv x ≠ H.node x:=by{
        rw[←hp_split_e] at hp'd
        rw[List.nodup_append] at hp'd
        symm
        apply hp'd.right.right
        · rw[←hp₁l]; apply List.getLast_mem
        · rw[←hp₂h]; apply List.head_mem
      }
      have hnx : H.node x ≠ x:=by{
        intro h
        apply hnn
        rw[nodeinv_eq_iff_eq_node, h, h]
      }
      have hnx' : H.nodeinv x ≠ x:=by{
        intro h
        apply hnx
        nth_rw 1 [←h, nodeinv_rightinv]
      }
      have h0:p'.head hp'n ≠ H.nodeinv x:=by{
        rw[←hp_split_e] at hp'd
        rw[List.nodup_append] at hp'd
        rw[←hp₁h]
        apply hp'd.right.right
        · apply List.head_mem
        rw[←hp₂h]; apply List.head_mem
      }
      have h1:p'.getLast hp'n ≠ H.node x:=by{
        rw[←hp_split_e] at hp'd
        rw[List.nodup_append] at hp'd
        rw[←hp₂l]
        symm
        apply hp'd.right.right
        · rw[←hp₁l]; apply List.getLast_mem
        apply List.getLast_mem
      }
      have h0':skip' H.node x (p'.head hp'n) = H.node (p'.head hp'n):=by{
        rw[skip'_eq_of_apply_ne]
        rw[ne_eq, ←eq_nodeinv_iff_node_eq]
        exact h0
      }
      have h1':skip' H.nodeinv x (p'.getLast hp'n) = H.nodeinv (p'.getLast hp'n):=by{
        rw[skip'_eq_of_apply_ne]
        rw[ne_eq, nodeinv_eq_iff_eq_node]
        exact h1
      }
      rw[h0', h1'] at hpm
      have hp₁c1 : p₁.IsChain (H.clink1 x) := by{
        rw[List.append_assoc] at hp_split_c
        exact List.IsChain.left_of_append hp_split_c
      }
      have hp₂c1 : p₂.IsChain (H.clink1 x) := by{
        exact List.IsChain.right_of_append hp_split_c
      }
      have hp₁d : p₁.Nodup := by{
        rw[←hp_split_e] at hp'd
        exact hp'd.of_append_left
      }
      have hp₂d : p₂.Nodup := by{
        rw[←hp_split_e] at hp'd
        exact hp'd.of_append_right
      }
      have hp₁x : x ∉ p₁ := by{
        rw[←hp_split_e] at hp'x
        simp at hp'x
        simp[hp'x]
      }
      have hp₂x : x ∉ p₂ := by{
        rw[←hp_split_e] at hp'x
        simp at hp'x
        simp[hp'x]
      }
      have hq'd':(p₁ ++ [x] ++ p₂).Nodup := by{
        rw[List.nodup_append_comm, ←List.append_assoc, List.nodup_append_comm]
        rw[List.singleton_append, List.nodup_cons, List.nodup_append_comm]
        rw[List.mem_append, Or.comm, ←List.mem_append, hp_split_e]
        exact ⟨hp'x, hp'd⟩
      }
      cases em (p₁.IsChain H.clink) with
      | inl hp₁c => {
        cases em (p₂.IsChain H.clink) with
        | inl hp₂c => {
          apply h (p₁ ++ [x] ++ p₂)
          unfold moebius_path
          rw[dite_cond_eq_false (by{simp})]
          apply And.intro hq'd'
          constructor
          · {
            rw[List.isChain_concat_append]
            constructor
            · {
              rw[List.isChain_concat_iff_of_ne_nil hp₁]
              rw[hp₁l]
              apply And.intro hp₁c
              simp[clink, union_iff, fromFun, nodeinv_leftinv]
            }
            · {
              rw[List.isChain_cons_iff_of_ne_nil hp₂]
              constructor
              · simp[clink, hp₂h, union_iff, fromFun]
              exact hp₂c
            }
          }
          · {
            rw[List.getLast_append_right hp₂]
            simp only [List.append_assoc]
            rw[List.head_append_left hp₁]
            rw[List.tail_append_of_ne_nil hp₁]
            nth_rw 2 3 [←hp_split_e] at hpm
            rw[List.tail_append_of_ne_nil hp₁] at hpm
            rw[hp₂l, hp₁h]
            cases em (H.nodeinv (p'.getLast hp'n) ∈ p₁.tail) with
            | inl h0 => {
              rw[List.idxOf_append_of_mem h0, List.drop_append_of_le_length List.idxOf_le_length]
              rw[List.idxOf_append_of_mem h0, List.drop_append_of_le_length List.idxOf_le_length]
                at hpm
              rw[List.mem_append]
              rw[List.mem_append] at hpm
              apply hpm.imp_right
              rw[List.mem_append]
              apply Or.inr
            }
            | inr h0 => {
              rw[List.idxOf_append_of_notMem h0, List.drop_length_add_append]
              rw[List.idxOf_append_of_notMem h0, List.drop_length_add_append] at hpm
              rw[List.singleton_append, List.idxOf_cons_ne _ (by{
                symm
                rw[ne_eq, nodeinv_eq_iff_eq_node]
                exact h1
              }), List.drop_succ_cons]
              exact hpm
            }
          }
        }
        | inr hp₂c => {
          have ⟨q₁, q₂, hqp, hqc, hq₁, hq₂, hq₁l, hq₂h⟩:=split_nodup_ischain_clink1_of_not_clink
            hp₂d hp₂c1 hp₂c
          rw[List.getLast?_eq_some_getLast hq₁, Option.some_inj] at hq₁l
          rw[List.head?_eq_some_head hq₂, Option.some_inj] at hq₂h
          have hq₁h : q₁.head hq₁ = p₂.head hp₂ := by{
            simp only [←hqp]
            rw[List.head_append_left hq₁]
          }
          have hq₂l : q₂.getLast hq₂ = p₂.getLast hp₂ := by{
            simp only [←hqp]
            rw[List.getLast_append_right hq₂]
          }
          have hq'd : List.Nodup (q₁ ++ [x] ++ q₂) := by{
            rw[List.nodup_append_comm, ←List.append_assoc, List.nodup_append_comm]
            rw[List.singleton_append, List.nodup_cons, List.nodup_append_comm, hqp]
            apply (And.intro · hp₂d)
            rw[List.mem_append, Or.comm, ←List.mem_append, hqp]
            exact hp₂x
          }
          have hq₁x : x ∉ q₁ := by{
            rw[←hqp] at hp₂x
            simp at hp₂x
            simp[hp₂x]
          }
          have hq₂x : x ∉ q₂ := by{
            rw[←hqp] at hp₂x
            simp at hp₂x
            simp[hp₂x]
          }
          have hq₁d : q₁.Nodup := by{rw[←hqp] at hp₂d; exact hp₂d.of_append_left}
          have hq₂d : q₂.Nodup := by{rw[←hqp] at hp₂d; exact hp₂d.of_append_right}
          cases em (H.nodeinv (p'.getLast hp'n) ∈ q₁.tail) with
          | inl h2 => {
            apply h (q₁ ++ [x] ++ q₂)
            unfold moebius_path
            rw[dite_cond_eq_false (by{simp})]
            apply And.intro hq'd
            apply And.intro hqc
            rw[List.getLast_append_right hq₂]
            simp only [List.append_assoc]
            rw[List.head_append_left hq₁, List.tail_append_of_ne_nil hq₁, hq₁h, hq₂l, hp₂l, hp₂h]
            rw[nodeinv_rightinv, List.idxOf_append_of_mem h2]
            rw[List.drop_append_of_le_length List.idxOf_le_length]
            simp
          }
          | inr h2 => {
            have h3:H.nodeinv (p'.getLast hp'n) ∉ q₁ := by{
              rw[←List.cons_head_tail hq₁]
              rw[List.mem_cons, hq₁h, hp₂h, nodeinv_injective.eq_iff, not_or]
              apply (And.intro · h2)
              intro h
              apply hp'x
              rw[←h]
              apply List.getLast_mem
            }
            have hd:(p₁ ++ [x] ++ q₂).Nodup:=by{
              rw[List.nodup_append_comm, ←List.append_assoc, List.nodup_append_comm]
              rw[List.singleton_append, List.nodup_cons]
              rw[List.mem_append, not_or]
              apply And.intro ⟨hq₂x, hp₁x⟩
              rw[←hp_split_e, ←hqp, List.nodup_append_comm, List.append_assoc] at hp'd
              exact hp'd.of_append_right
            }
            have hc:(p₁ ++ [x] ++ q₂).IsChain H.clink := by{
              rw[List.isChain_concat_append]
              constructor
              · {
                rw[List.isChain_concat_iff_of_ne_nil hp₁, hp₁l]
                apply And.intro hp₁c
                simp[clink, union_iff, fromFun, nodeinv_leftinv]
              }
              · {
                rw[List.isChain_concat_append] at hqc
                exact hqc.right
              }
            }
            nth_rw 2 3 [←hp_split_e] at hpm
            rw[←hqp] at hpm
            rw[List.tail_append_of_ne_nil hp₁] at hpm
            cases em (H.node (p'.head hp'n) ∈ q₁) with
            | inl h4 => {
              have h5 : H.nodeinv (p'.getLast hp'n) ∈ p₁ :=by{
                cases em (H.nodeinv (p'.getLast hp'n) ∈ p₁) with
                | inl h5 => exact h5
                | inr h5 => {
                  rw[List.idxOf_append_of_notMem (by{
                    revert h5; rw[not_imp_not]; apply List.mem_of_mem_tail
                  }), List.drop_length_add_append] at hpm
                  rw[List.idxOf_append_of_notMem h3, List.drop_length_add_append] at hpm
                  have hpm':=List.mem_of_mem_drop hpm
                  rw[←hqp, List.nodup_append'] at hp₂d
                  exfalso
                  exact hp₂d.right.right h4 hpm'
                }
              }
              apply h ((q₁.take (q₁.idxOf (H.node (p'.head hp'n)) + 1)) ++ p₁ ++ [x] ++ q₂)
              unfold moebius_path
              rw[dite_cond_eq_false (by{simp})]
              constructor
              · {
                rw[List.append_assoc, List.append_assoc, List.nodup_append']
                apply And.intro hq₁d.take
                rw[←List.append_assoc]
                apply And.intro hd
                apply List.disjoint_of_subset_left (List.take_subset _ _)
                symm
                apply List.disjoint_of_nodup_append
                rw[List.append_assoc, List.nodup_append', List.nodup_append_comm (l₁:=q₂)]
                rw[List.disjoint_append_right, and_comm (a:=List.Disjoint _ _)]
                rw[←List.disjoint_append_right, hqp, ←List.nodup_append']
                exact hq'd'
              }
              have h6:q₁.take (q₁.idxOf (H.node (p'.head hp'n)) + 1) ≠ []:=by{
                simp[hq₁]
              }
              constructor
              · {
                rw[List.append_assoc, List.append_assoc, List.isChain_append, ←List.append_assoc]
                constructor
                · {
                  rw[List.append_assoc] at hqc
                  apply hqc.left_of_append.take
                }
                apply And.intro hc
                rw[List.append_assoc, List.head?_eq_some_head (by{simp})]
                simp only [Option.mem_def, Option.some.injEq]
                rw[List.getLast?_eq_some_getLast h6]
                simp only [Option.some.injEq]
                simp only [List.cons_append, List.nil_append, forall_eq']
                rw[List.head_append_left hp₁, hp₁h]
                rw[List.getLast_take]
                simp only [add_tsub_cancel_right]
                have h:=List.getElem?_eq_some_getElem_iff (List.idxOf_lt_length_of_mem h4)
                simp only [List.getElem_idxOf, iff_true] at h
                rw[h]
                simp[clink, union_iff, fromFun, nodeinv_leftinv, true_or]
              }
              · {
                rw[List.getLast_append_right hq₂, hq₂l, hp₂l]
                simp only [List.append_assoc]
                rw[List.head_append_left h6, List.head_take, hq₁h, hp₂h, nodeinv_rightinv]
                rw[List.tail_append_of_ne_nil h6]
                rw[List.idxOf_append_of_notMem (by{
                  revert h3
                  rw[not_imp_not]
                  apply List.mem_of_mem_take ∘ List.mem_of_mem_tail
                }), List.drop_length_add_append]
                rw[List.idxOf_append_of_mem h5, List.drop_append_of_le_length List.idxOf_le_length]
                simp
              }
            }
            | inr h4 => {
              apply h (p₁ ++ [x] ++ q₂)
              unfold moebius_path
              rw[dite_cond_eq_false (by{simp})]
              apply And.intro hd
              apply And.intro hc
              rw[List.getLast_append_right hq₂]
              simp only [List.append_assoc]
              rw[List.head_append_left hp₁, List.tail_append_of_ne_nil hp₁, hq₂l, hp₂l, hp₁h]
              cases em (H.nodeinv (p'.getLast hp'n) ∈ p₁.tail) with
              | inl h5 => {
                rw[List.idxOf_append_of_mem h5, List.drop_append_of_le_length List.idxOf_le_length]
                rw[List.idxOf_append_of_mem h5, List.drop_append_of_le_length List.idxOf_le_length]
                  at hpm
                rw[List.mem_append]
                rw[List.mem_append] at hpm
                apply hpm.imp_right
                rw[List.mem_append]
                intro h
                have h:=h.resolve_left h4
                rw[List.mem_append]
                exact Or.inr h
              }
              | inr h5 => {
                rw[List.idxOf_append_of_notMem h5, List.drop_length_add_append]
                rw[List.idxOf_append_of_notMem h5, List.drop_length_add_append] at hpm
                rw[List.idxOf_append_of_notMem h3, List.drop_length_add_append] at hpm
                rw[List.idxOf_append_of_notMem (by{simp[nodeinv_eq_iff_eq_node, h1]})]
                rw[List.drop_length_add_append]
                exact hpm
              }
            }
          }
        }
      }
      | inr hp₁c => {
        have ⟨q₁, q₂, hqp₁, hqc, hq₁, hq₂, hq₁l, hq₂h⟩:=split_nodup_ischain_clink1_of_not_clink
          hp₁d hp₁c1 hp₁c
        rw[List.getLast?_eq_some_getLast hq₁, Option.some_inj] at hq₁l
        rw[List.head?_eq_some_head hq₂, Option.some_inj] at hq₂h
        have hq₁h : q₁.head hq₁ = p₁.head hp₁ := by{
          simp only [←hqp₁]
          rw[List.head_append_left hq₁]
        }
        have hq₂l : q₂.getLast hq₂ = p₁.getLast hp₁ := by{
          simp only [←hqp₁]
          rw[List.getLast_append_right hq₂]
        }
        have hp₂c : p₂.IsChain H.clink := by{
          apply ischain_clink_of_ischain_clink1_of_face_not_mem hp₂c1
          rw[←hp_split_e] at hp'd
          rw[List.nodup_append'] at hp'd
          apply hp'd.right.right
          rw[←hqp₁, ←hq₂h, List.mem_append]
          right
          apply List.head_mem
        }
        have hq'd : List.Nodup (q₁ ++ [x] ++ q₂) := by{
          rw[List.nodup_append_comm, ←List.append_assoc, List.nodup_append_comm]
          rw[List.singleton_append, List.nodup_cons, List.nodup_append_comm, hqp₁]
          apply (And.intro · hp₁d)
          rw[List.mem_append, Or.comm, ←List.mem_append, hqp₁]
          exact hp₁x
        }
        have hq₁x : x ∉ q₁ := by{
          rw[←hqp₁] at hp₁x
          simp at hp₁x
          simp[hp₁x]
        }
        have hq₂x : x ∉ q₂ := by{
          rw[←hqp₁] at hp₁x
          simp at hp₁x
          simp[hp₁x]
        }
        have hq₁d : q₁.Nodup := by{rw[←hqp₁] at hp₁d; exact hp₁d.of_append_left}
        have hq₂d : q₂.Nodup := by{rw[←hqp₁] at hp₁d; exact hp₁d.of_append_right}
        cases em (H.node (p'.head hp'n) ∈ q₂) with
        | inl h2 => {
          apply h (q₁ ++ [x] ++ q₂)
          unfold moebius_path
          rw[dite_cond_eq_false (by{simp})]
          apply And.intro hq'd
          apply And.intro hqc
          simp only [List.append_assoc]
          rw[List.head_append_left hq₁]
          rw[List.tail_append_of_ne_nil hq₁]
          simp only [←List.append_assoc]
          rw[List.getLast_append_right hq₂]
          simp only [List.append_assoc]
          rw[hq₂l, hp₁l, nodeinv_leftinv]
          rw[List.idxOf_append_of_notMem (by{intro h; apply hq₁x; exact List.mem_of_mem_tail h})]
          rw[List.drop_length_add_append]
          rw[List.singleton_append, List.idxOf_cons_eq _ rfl]
          rw[List.drop_zero]
          rw[hq₁h, hp₁h]
          exact List.mem_cons_of_mem _ h2
        }
        | inr h2 => {
          have hd:(q₁ ++ [x] ++ p₂).Nodup:=by{
            rw[List.nodup_append_comm, ←List.append_assoc, List.nodup_append_comm]
            rw[List.singleton_append, List.nodup_cons]
            rw[List.mem_append, not_or]
            apply And.intro ⟨hp₂x, hq₁x⟩
            rw[←hp_split_e, ←hqp₁, List.nodup_append_comm, ←List.append_assoc] at hp'd
            exact hp'd.of_append_left
          }
          cases em (H.nodeinv (p'.getLast hp'n) ∈ q₂) with
          | inl h3 => {
            have h3':H.nodeinv (p'.getLast hp'n) ∉ q₁:=by{
              rw[←hqp₁] at hp₁d
              rw[List.nodup_append'] at hp₁d
              exact (hp₁d.right.right · h3)
            }
            nth_rw 2 3 [←hp_split_e] at hpm
            rw[List.tail_append_of_ne_nil hp₁] at hpm
            rw[←hqp₁] at hpm
            rw[List.tail_append_of_ne_nil hq₁] at hpm
            rw[List.append_assoc] at hpm
            rw[List.idxOf_append_of_notMem (by{
              revert h3'; rw[not_imp_not]; exact List.mem_of_mem_tail})] at hpm
            rw[List.drop_length_add_append] at hpm
            have h4:H.node (p'.head hp'n) ∈ p₂:=by{
              have hpm':=List.mem_of_mem_drop hpm
              rw[List.mem_append] at hpm'
              exact hpm'.resolve_left h2
            }
            apply h (q₁ ++ [x] ++ p₂ ++ (q₂.drop (q₂.idxOf (H.nodeinv (p'.getLast hp'n)))))
            unfold moebius_path
            rw[dite_cond_eq_false (by{simp})]
            have h5:(q₂.drop (q₂.idxOf (H.nodeinv (p'.getLast hp'n)))) ≠ []:=by{
              simp[List.idxOf_lt_length_iff, h3]
            }
            constructor
            · {
              rw[List.nodup_append']
              apply And.intro hd
              apply And.intro hq'd.of_append_right.drop
              apply List.disjoint_of_subset_right (List.drop_subset _ _)
              intro a ha hb
              simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
                List.mem_cons] at ha
              rw[←hqp₁, List.nodup_append'] at hp₁d
              have ha:=ha.resolve_left ((List.disjoint_comm.mp hp₁d.right.right) hb)
              have ha:=ha.resolve_left (fun h => hq₂x (h ▸ hb))
              rw[←hp_split_e, ←hqp₁, List.append_assoc] at hp'd
              have h3:=hp'd.of_append_right
              rw[List.nodup_append'] at h3
              apply h3.right.right hb ha
            }
            constructor
            · {
              rw[List.append_assoc]
              rw[List.isChain_concat_append]
              apply And.intro hqc.left_of_append
              rw[←List.cons_append]
              rw[List.isChain_append]
              constructor
              · {
                rw[List.isChain_cons_iff_of_ne_nil hp₂]
                simp [hp₂c]
                simp[clink, union_iff, fromFun, hp₂h]
              }
              constructor
              · {
                apply List.isChain_drop
                exact hqc.right_of_append
              }
              rw[List.getLast?_eq_some_getLast (by{simp})]
              simp only [Option.mem_def, Option.some.injEq]
              rw[List.head?_eq_some_head h5]
              simp only [Option.some_inj]
              rw[List.getLast_cons hp₂]
              simp only [List.head_drop, List.getElem_idxOf, forall_eq', hp₂l]
              simp[clink, union_iff, fromFun]
            }
            · {
              rw[List.getLast_append_right h5]
              rw[List.getLast_drop]
              simp only [List.append_assoc q₁]
              rw[List.head_append_left hq₁, List.tail_append_of_ne_nil hq₁]
              rw[hq₁h, hp₁h, hq₂l, hp₁l, nodeinv_leftinv]
              rw[List.idxOf_append_of_notMem (by{
                revert hq₁x; rw[not_imp_not]; apply List.mem_of_mem_tail})]
              rw[List.drop_length_add_append]
              rw[List.append_assoc, List.singleton_append]
              rw[List.idxOf_cons_self, List.drop_zero]
              simp[h4]
            }
          }
          | inr h3 => {
            apply h (q₁ ++ [x] ++ p₂)
            unfold moebius_path
            rw[dite_cond_eq_false (by{simp})]
            apply And.intro hd
            constructor
            · {
              rw[List.isChain_concat_append]
              constructor
              · apply hqc.left_of_append
              rw[List.append_assoc, List.singleton_append] at hp_split_c
              rw[List.isChain_cons_iff_of_ne_nil hp₂, hp₂h]
              simp[hp₂c]
              simp[clink, union_iff, fromFun]
            }
            · {
              rw[List.getLast_append_right hp₂]
              simp only [List.append_assoc]
              rw[List.head_append_left hq₁, List.tail_append_of_ne_nil hq₁]
              rw[hp₂l, hq₁h, hp₁h]
              nth_rw 2 3 [←hp_split_e] at hpm
              rw[List.tail_append_of_ne_nil hp₁] at hpm
              rw[←hqp₁] at hpm
              rw[List.tail_append_of_ne_nil hq₁] at hpm
              rw[List.append_assoc] at hpm
              cases em (H.nodeinv (p'.getLast hp'n) ∈ q₁.tail) with
              | inl h4 => {
                rw[List.idxOf_append_of_mem h4]
                rw[List.drop_append_of_le_length List.idxOf_le_length]
                rw[List.idxOf_append_of_mem h4] at hpm
                rw[List.drop_append_of_le_length List.idxOf_le_length] at hpm
                rw[List.mem_append] at hpm
                rw[List.mem_append]
                apply hpm.imp_right
                intro h
                rw[List.mem_append] at h
                rw[List.mem_append]
                right
                apply h.resolve_left
                exact h2
              }
              | inr h4 => {
                rw[List.idxOf_append_of_notMem h4, List.drop_length_add_append] at hpm
                rw[List.idxOf_append_of_notMem h3, List.drop_length_add_append] at hpm
                rw[List.idxOf_append_of_notMem h4, List.drop_length_add_append]
                rw[List.singleton_append, List.idxOf_cons_ne _ (by{
                  symm; rw[ne_eq, nodeinv_eq_iff_eq_node]; exact h1})]
                rw[List.drop_succ_cons]
                exact hpm
              }
            }
          }
        }
      }
    }
  }
}
