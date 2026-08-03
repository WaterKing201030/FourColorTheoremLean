import FourColorTheorem.Hypermap.Properties.Planar.Jordan.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem nil_not_moebius_path:¬H.moebius_path []:=by{unfold moebius_path;simp}
theorem moebius_path_ne_nil {p : List α} (hp : H.moebius_path p) : p ≠ [] :=
  fun h => nil_not_moebius_path (h ▸ hp)
theorem head_node_mem_moebius_path_tail {p : List α} (hp : H.moebius_path p) :
  H.node (p.head (moebius_path_ne_nil hp)) ∈ p.tail := by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.tail_cons, List.head_cons]
      unfold moebius_path at hp
      simp only [reduceCtorEq, ↓reduceDIte, List.nodup_cons, List.head_cons] at hp
      exact List.mem_of_mem_drop hp.right.right
    }
  }
theorem head_node_mem_moebius_path_tail_cons {x : α} {p : List α} (hp : H.moebius_path (x :: p))
  : H.node x ∈ p :=  by{
    have h:=head_node_mem_moebius_path_tail hp
    simp at h
    simp[h]
  }
theorem last_nodeinv_mem_moebius_path_tail {p : List α} (hp : H.moebius_path p) :
  H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.tail := by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.tail_cons]
      rw[List.getLast_cons_eq_getLastD]
      unfold moebius_path at hp
      rw[←List.idxOf_lt_length_iff]
      have hp'':=List.length_pos_of_mem hp.right.right
      simp only [List.length_drop, tsub_pos_iff_lt, List.tail_cons
      , List.getLast_cons_eq_getLastD] at hp''
      exact hp''
    }
  }
theorem last_nodeinv_mem_moebius_path_tail_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  H.nodeinv (p.getLastD x) ∈ p := by{
    have h:=last_nodeinv_mem_moebius_path_tail hp
    simp only [List.tail_cons] at h
    rw[List.getLast_cons_eq_getLastD] at h
    exact h
  }
theorem moebius_path_not_eq {p : List α} (hp : H.moebius_path p) :
  p.head (moebius_path_ne_nil hp) ≠ H.nodeinv (p.getLast (moebius_path_ne_nil hp)) :=by{
    have hp':=moebius_path_ne_nil hp
    match p with
    | x::p' => {
      simp only [List.head_cons, ne_eq]
      rw[List.getLast_cons_eq_getLastD]
      have hy := last_nodeinv_mem_moebius_path_tail_cons hp
      unfold moebius_path at hp
      rw[List.nodup_cons] at hp
      intro hn
      apply hp.left.left
      rw[hn]
      exact hy
    }
  }
theorem moebius_path_not_eq_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  x ≠ H.nodeinv (p.getLastD x) := by{
    rw[←List.getLast_cons_eq_getLastD]
    have hp:=moebius_path_not_eq hp
    simp at hp
    simp[hp]
  }
theorem moebius_path_not_eq' {p : List α} (hp : H.moebius_path p) :
  H.node (p.head (moebius_path_ne_nil hp)) ≠ p.getLast (moebius_path_ne_nil hp) := by{
    intro hn
    apply moebius_path_not_eq hp
    apply H.node_injective
    rw[nodeinv_eq]
    simp[nfe_cancel, hn]
  }
theorem moebius_path_not_eq'_cons {x : α} {p : List α} (hp : H.moebius_path (x::p)) :
  H.node x ≠ p.getLastD x := by{
    rw[←List.getLast_cons_eq_getLastD]
    have hp:=moebius_path_not_eq' hp
    simp at hp
    simp[hp]
  }
theorem moebius_path_tail_ne_nil {p : List α} (hp : H.moebius_path p) :
  p.tail ≠ []:=by{
    match p with
    | x::p' => {
      simp only [List.tail_cons, ne_eq]
      simp only [moebius_path, reduceCtorEq, ↓reduceDIte, List.nodup_cons, List.tail_cons,
        List.head_cons] at hp
      have hp':=List.mem_of_mem_drop hp.right.right
      apply List.ne_nil_of_mem hp'
    }
  }
theorem moebius_path_head_ne_last {p : List α} (hp : H.moebius_path p) :
  p.head (moebius_path_ne_nil hp) ≠ p.getLast (moebius_path_ne_nil hp) := by{
    have hpn:=moebius_path_ne_nil hp
    have hp'n:=moebius_path_tail_ne_nil hp
    unfold moebius_path at hp
    rw[dite_cond_eq_false (by{simp[hpn]})] at hp
    have hpd:=hp.left
    rw[←List.cons_head_tail hpn] at hpd
    rw[List.nodup_cons] at hpd
    intro h
    apply hpd.left
    rw[h]
    rw[←List.getLast_tail hp'n]
    apply List.getLast_mem
  }
theorem moebius_path_node_head_mem_tail {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p.tail :=by{
    have hpn:=moebius_path_ne_nil hp
    unfold moebius_path at hp
    simp only [hpn, ↓reduceDIte] at hp
    exact List.mem_of_mem_drop hp.right.right
  }
theorem moebius_path_node_head_mem_dropLast_tail {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p.dropLast.tail :=by{
    have ih:=moebius_path_node_head_mem_tail hp
    have hpn:=moebius_path_ne_nil hp
    nth_rw 1 [←List.concat_dropLast_getLast hpn] at ih
    have h:p.dropLast ≠ []:=by{
      intro h
      simp[h] at ih
    }
    rw[List.tail_append_of_ne_nil h, List.mem_append] at ih
    apply ih.resolve_right
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    apply moebius_path_not_eq'
    exact hp
  }
theorem moebius_path_node_head_mem {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈ p :=by{
    apply List.mem_of_mem_tail
    apply moebius_path_node_head_mem_tail
    exact hp
  }
theorem moebius_path_head_ne_node {p : List α} (hp : H.moebius_path p)
: p.head (moebius_path_ne_nil hp) ≠ H.node (p.head (moebius_path_ne_nil hp)) := by{
  have hpn:=moebius_path_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn, ↓reduceDIte] at hp
  have hpd:=hp.left
  rw[←List.cons_head_tail hpn, List.nodup_cons] at hpd
  intro h
  apply hpd.left
  rw[h]
  apply moebius_path_node_head_mem_tail
  exact hp_backup
}
theorem moebius_path_nodeinv_getLast_mem_tail {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.tail := by{
  have hpn:=moebius_path_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn, ↓reduceDIte] at hp
  have hpm:=hp.right.right
  have hpm':=List.ne_nil_of_mem hpm
  simp only [ne_eq, List.drop_eq_nil_iff, not_le] at hpm'
  rw[List.idxOf_lt_length_iff] at hpm'
  exact hpm'
}
theorem moebius_path_nodeinv_ne_getLast {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ≠ p.getLast (moebius_path_ne_nil hp) := by{
  have hpn:=moebius_path_ne_nil hp
  have hp'n:=moebius_path_tail_ne_nil hp
  have hp_backup := hp
  unfold moebius_path at hp
  simp only [hpn] at hp
  have hpm:=hp.right.right
  intro h
  rw[h] at hpm
  rw[←List.getLast_tail hp'n] at hpm
  rw[List.idxOf_getLast hp'n (by{
    have hpd:=hp.left
    rw[←List.cons_head_tail hpn, ←List.concat_dropLast_getLast hp'n] at hpd
    rw[←List.concat_eq_append, List.nodup_cons, List.nodup_concat] at hpd
    exact hpd.right.left
  })] at hpm
  rw[List.drop_length_sub_one hp'n] at hpm
  simp only [List.getLast_tail, List.mem_cons, List.not_mem_nil, or_false] at hpm
  apply moebius_path_not_eq' hp_backup
  exact hpm
}
theorem moebius_path_nodeinv_getLast_mem_dropLast_tail {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.dropLast.tail := by{
  have ih:=moebius_path_nodeinv_getLast_mem_tail hp
  have hpn:=moebius_path_ne_nil hp
  nth_rw 1 [←List.concat_dropLast_getLast hpn] at ih
  have h:p.dropLast ≠ []:=by{
    intro h
    simp[h] at ih
  }
  rw[List.tail_append_of_ne_nil h, List.mem_append] at ih
  apply ih.resolve_right
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  apply moebius_path_nodeinv_ne_getLast
  exact hp
}
theorem moebius_path_nodeinv_getLast_mem_dropLast {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p.dropLast := by{
  apply List.mem_of_mem_tail
  apply moebius_path_nodeinv_getLast_mem_dropLast_tail
  exact hp
}
theorem moebius_path_nodeinv_getLast_mem {p : List α} (hp : H.moebius_path p)
: H.nodeinv (p.getLast (moebius_path_ne_nil hp)) ∈ p := by{
  apply List.mem_of_mem_tail
  apply moebius_path_nodeinv_getLast_mem_tail
  exact hp
}
theorem card_ge_three_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : Fintype.card α ≥ 3:=by{
    apply Nat.le_of_not_gt
    simp only [Nat.lt_succ_iff]
    rw[Fintype.card_le_two_iff]
    rw[not_or, not_exists]
    simp only [not_exists, not_forall, not_or]
    have hpn:=moebius_path_ne_nil hp
    rw[not_isEmpty_iff]
    apply And.intro (Nonempty.intro (p.head hpn))
    intro a b
    have h0:=moebius_path_not_eq hp
    have h1:=moebius_path_head_ne_last hp
    have h2:=moebius_path_nodeinv_ne_getLast hp
    cases em (H.nodeinv (p.getLast hpn) = a) with
    | inl ha => {
      rw[←ha]
      cases em (p.getLast hpn = b) with
      | inl hb => {
        use p.head hpn
        rw[←hb]
        exact ⟨h0, h1⟩
      }
      | inr hb => {
        use p.getLast hpn
        exact ⟨h2.symm, hb⟩
      }
    }
    | inr ha => {
      cases em (p.getLast hpn = b) with
      | inl hb => {
        use H.nodeinv (p.getLast hpn)
        rw[←hb]
        exact ⟨ha, h2⟩
      }
      | inr hb => {
        cases em (H.nodeinv (p.getLast hpn) = b) with
        | inl hb' => {
          cases em (p.getLast hpn = a) with
          | inl ha' => {
            rw[←ha', ←hb']
            use p.head hpn
          }
          | inr ha' => {
            use p.getLast hpn
          }
        }
        | inr hb' => {
          use H.nodeinv (p.getLast hpn)
        }
      }
    }
  }
theorem length_ge_three_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : p.length ≥ 3 := by{
    have h0:=moebius_path_node_head_mem_dropLast_tail hp
    have hn:=moebius_path_ne_nil hp
    have hn':=moebius_path_tail_ne_nil hp
    rw[←List.cons_head_tail hn, ←List.concat_dropLast_getLast hn']
    simp only [List.getLast_tail, List.length_cons]
    apply Nat.succ_le_succ
    rw[List.length_append, List.length_singleton]
    apply Nat.succ_le_succ
    rw[←List.tail_dropLast]
    apply List.length_pos_of_mem h0
  }
theorem moebius_path_tail_tail_ne_nil {p : List α} (hp : H.moebius_path p)
  : p.tail.tail ≠ [] := by{
    have h:=length_ge_three_of_moebius_path hp
    match p with
    | [] | [_] | [_, _] => simp at h
    | _::_::_::_ => simp
  }
theorem card_pos_of_moebius_path {p : List α} (hp : H.moebius_path p)
  : Fintype.card α > 0:=by{
    apply (Nat.lt_of_lt_of_le · (card_ge_three_of_moebius_path hp))
    simp
  }
theorem moebius_path_nodup {p : List α} (hp : H.moebius_path p)
  : p.Nodup := by{
    simp[moebius_path] at hp
    simp[hp]
  }
theorem moebius_path_isChain_clink {p : List α} (hp : H.moebius_path p)
  : p.IsChain H.clink := by{
    simp[moebius_path] at hp
    simp[hp]
  }
theorem moebius_path_cross_nlink {p : List α} (hp : H.moebius_path p)
  : H.node (p.head (moebius_path_ne_nil hp)) ∈
  p.tail.drop (p.tail.idxOf (H.nodeinv (p.getLast (moebius_path_ne_nil hp)))) := by{
    simp[moebius_path, moebius_path_ne_nil hp] at hp
    simp[hp]
  }

end Hypermap
