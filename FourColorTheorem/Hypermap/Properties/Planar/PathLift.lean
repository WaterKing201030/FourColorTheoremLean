import Init.Data.Nat.Lemmas
import FourColorTheorem.Hypermap.Actions.Walkup.Basic
import FourColorTheorem.Hypermap.Properties.Planar.Euler.WalkupE
import FourColorTheorem.Hypermap.Properties.Planar.Jordan.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem isChain_clink_liftE {x : α} {p : List α} (hpx : x ∉ p) (hp : p.IsChain H.clink)
  : ∃q : List {a // a ≠ x}, q.IsChain (H.WalkupE x).clink ∧ q.map Subtype.val = p :=by{
    match p with
    | [] => use []; simp
    | [y] => {
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpx
      use [⟨y, Ne.symm hpx⟩]
      simp
    }
    | y::z::p' => {
      have hxy : x ≠ y :=by{simp at hpx; simp[hpx]}
      have hxz : x ≠ z :=by{simp at hpx; simp[hpx]}
      have hyzc : H.clink y z := by{rw[List.isChain_cons_cons] at hp; simp[hp]}
      rw[List.mem_cons, not_or] at hpx
      rw[List.isChain_cons_cons] at hp
      have ⟨q, hq⟩:=isChain_clink_liftE hpx.right hp.right
      use ⟨y, hxy.symm⟩::q
      rw[List.map_cons, hq.right]
      have hq':q ≠ []:=by{intro h; simp[h] at hq}
      apply (And.intro · rfl)
      rw[List.isChain_cons_iff_of_ne_nil hq']
      apply (And.intro · hq.left)
      rw[clink, union_iff, walkupe_nodeinv, walkupe_face, fromFun, fromFun]
      rw[Subtype.ext_iff, Subtype.ext_iff, skip_val, skip_val]
      rw[←List.cons_head_tail hq', List.map_cons, List.cons_eq_cons] at hq
      rw[hq.right.left]
      rw[clink, union_iff, fromFun, fromFun] at hp
      apply hp.left.imp
      all_goals
      intro h
      rw[skip'_eq_of_apply_ne, h]
      intro h'
      rw[h] at h'
      apply hpx.right
      simp[h']
    }
  }

theorem isChain_clink_liftN {x : α} {p : List α} (hpx : x ∉ p)
  (hpfx : H.face x ∉ p.tail) (hp : p.IsChain H.clink)
  : ∃q : List {a // a ≠ x}, q.IsChain (H.WalkupN x).clink ∧ q.map Subtype.val = p := by{
    match p with
    | [] => use []; simp
    | [y] => {
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpx
      use [⟨y, Ne.symm hpx⟩]
      simp
    }
    | y::z::p' => {
      have hxy : x ≠ y :=by{simp at hpx; simp[hpx]}
      have hxz : x ≠ z :=by{simp at hpx; simp[hpx]}
      have hyzc : H.clink y z := by{rw[List.isChain_cons_cons] at hp; simp[hp]}
      rw[List.mem_cons, not_or] at hpx
      rw[List.tail_cons, List.mem_cons, not_or] at hpfx
      rw[List.isChain_cons_cons] at hp
      have ⟨q, hq⟩:=isChain_clink_liftN hpx.right hpfx.right hp.right
      use ⟨y, hxy.symm⟩::q
      rw[List.map_cons, hq.right]
      have hq':q ≠ []:=by{intro h; simp[h] at hq}
      apply (And.intro · rfl)
      rw[List.isChain_cons_iff_of_ne_nil hq']
      apply (And.intro · hq.left)
      rw[clink, union_iff, WalkupN, permF_nodeinv, permF_face, fromFun, fromFun]
      rw[walkupe_node]
      rw[←List.cons_head_tail hq', List.map_cons, List.cons_eq_cons] at hq
      rw[edgeinv_eq_iff_eq_edge, walkupe_edge]
      rw[Subtype.ext_iff, Subtype.ext_iff, skip_val, skip_edge'_val]
      rw[hq.right.left]
      rw[clink, union_iff, fromFun, fromFun] at hyzc
      simp only
      rw[skip_edge'', skip']
      simp only [permN_edge, permN_node, permN_face]
      cases em (H.face y = z) with
      | inl hfyz => {
        right
        rw[ite_cond_eq_false, hfyz]
        simp only [eq_iff_iff, iff_false]
        rw[hfyz]
        apply Ne.symm
        exact hxz
      }
      | inr hfyz => {
        have hyzc:=hyzc.resolve_right hfyz
        rw[nodeinv_eq_iff_eq_node] at hyzc
        simp only [←hyzc, Eq.comm (a:=y), hxy, ↓reduceIte]
        cases em (H.edge y = x) with
        | inl heyx => {
          have hfxz:=heyx
          rw[hyzc, ←enf_cancel x, edge_inj, node_inj] at hfxz
          simp[hfxz] at hpfx
        }
        | inr heyx => {
          simp only [heyx, ↓reduceIte, ite_self, true_or]
        }
      }
    }
  }

theorem isChain_clink_liftF {x : α} {p : List α} (hpx : x ∉ p)
  (hpfx : H.nodeinv x ∉ p.tail) (hp : p.IsChain H.clink)
  : ∃q : List {a // a ≠ x}, q.IsChain (H.WalkupF x).clink ∧ q.map Subtype.val = p := by{
    match p with
    | [] => use []; simp
    | [y] => {
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpx
      use [⟨y, Ne.symm hpx⟩]
      simp
    }
    | y::z::p' => {
      have hxy : x ≠ y :=by{simp at hpx; simp[hpx]}
      have hxz : x ≠ z :=by{simp at hpx; simp[hpx]}
      have hyzc : H.clink y z := by{rw[List.isChain_cons_cons] at hp; simp[hp]}
      rw[List.mem_cons, not_or] at hpx
      rw[List.tail_cons, List.mem_cons, not_or] at hpfx
      rw[List.isChain_cons_cons] at hp
      have ⟨q, hq⟩:=isChain_clink_liftF hpx.right hpfx.right hp.right
      use ⟨y, hxy.symm⟩::q
      rw[List.map_cons, hq.right]
      have hq':q ≠ []:=by{intro h; simp[h] at hq}
      apply (And.intro · rfl)
      rw[List.isChain_cons_iff_of_ne_nil hq']
      apply (And.intro · hq.left)
      rw[clink, union_iff, WalkupF, permN_nodeinv, permN_face, fromFun, fromFun]
      rw[walkupe_edge]
      rw[←List.cons_head_tail hq', List.map_cons, List.cons_eq_cons] at hq
      rw[walkupe_faceinv]
      rw[Subtype.ext_iff, Subtype.ext_iff, skip_val, skip_edge'_val]
      rw[hq.right.left]
      rw[clink, union_iff, fromFun, fromFun] at hyzc
      simp only
      rw[skip_edge'', skip']
      simp only [permF_edge, permF_node, permF_face, permF_faceinv]
      cases em (H.nodeinv y = z) with
      | inl hnyz => {
        left
        rw[ite_cond_eq_false, hnyz]
        simp only [eq_iff_iff, iff_false]
        rw[hnyz]
        apply Ne.symm
        exact hxz
      }
      | inr hnyz => {
        have hyzc:=hyzc.resolve_left hnyz
        right
        simp only [hyzc, Eq.comm (a:=z), hxz, ↓reduceIte]
        rw[nodeinv_eq_iff_eq_node, Eq.comm] at hpfx
        simp[hpfx]
      }
    }
  }

theorem moebius_path_liftE_of_not_mem {x : α} {p : List α} (hpx : x ∉ p) (hp : H.moebius_path p)
  : ∃q, (H.WalkupE x).moebius_path q ∧ q.map Subtype.val = p :=by{
    have hpn:=moebius_path_ne_nil hp
    have hpd:=moebius_path_nodup hp
    have hpc:=moebius_path_isChain_clink hp
    have h0:=moebius_path_nodeinv_getLast_mem hp
    have h1:=moebius_path_node_head_mem hp
    have ⟨q, hq, hqp⟩:=isChain_clink_liftE hpx hpc
    use q
    refine ⟨?_, hqp⟩
    have hqn : q ≠ []:=by{intro h; simp[h] at hqp; contradiction}
    unfold moebius_path
    rw[dite_cond_eq_false (by{simp[hqn]})]
    rw[moebius_path, dite_cond_eq_false (by{simp[hpn]})] at hp
    simp only[hpd, hpc, true_and] at hp
    have hqd: q.Nodup := by{rw[←List.nodup_map_iff Subtype.val_injective, hqp]; exact hpd}
    refine ⟨hqd, hq, ?_⟩
    rw[walkupe_nodeinv, walkupe_node]
    rw[skip_eq_of_apply_ne]
    · {
      rw[skip_eq_of_apply_ne]
      · {
        rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, List.map_tail, hqp]
        simp only
        rw[←List.getLast_map (f:=Subtype.val) (hqp ▸ hpn)]
        rw[←List.mem_map_of_injective Subtype.val_injective]
        simp only
        rw[←List.head_map (f:=Subtype.val) (hqp ▸ hpn)]
        rw[List.map_drop, List.map_tail]
        simp only [hqp]
        exact hp
      }
      intro h
      apply hpx
      rw[←h]
      rw[←List.head_map (f:=Subtype.val) (hqp ▸ hpn)]
      simp only[hqp]
      exact h1
    }
    intro h
    apply hpx
    rw[←h]
    rw[←List.getLast_map (f:=Subtype.val) (hqp ▸ hpn)]
    simp only[hqp]
    exact h0
  }

theorem moebius_path_liftE_of_cons_nodeinv {x : α} {p : List α}
  (hp : H.moebius_path (x :: H.nodeinv x :: p))
: ∃q, (H.WalkupE x).moebius_path q ∧ q.map Subtype.val = H.nodeinv x::p := by{
  have hpn:=moebius_path_ne_nil hp
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  have hp''n:=moebius_path_tail_tail_ne_nil hp
  rw[List.tail_cons, List.tail_cons] at hp''n
  have h0:=moebius_path_nodeinv_getLast_mem hp
  have h1:=moebius_path_node_head_mem hp
  rw[List.nodup_cons] at hpd
  rw[List.isChain_cons_cons] at hpc
  have ⟨q, hq⟩:=isChain_clink_liftE hpd.left hpc.right
  use q
  refine ⟨?_, hq.right⟩
  have hqn:q ≠ []:=by{intro h; simp[h] at hq}
  have hqd:q.Nodup:=by{
    rw[←List.nodup_map_iff Subtype.val_injective, hq.right]
    exact hpd.right
  }
  nth_rw 2 [←List.cons_head_tail hqn] at hq
  rw[List.map_cons, List.cons_eq_cons] at hq
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp[hqn]})]
  refine ⟨hqd, hq.left, ?_⟩
  rw[walkupe_nodeinv, walkupe_node]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, hq.right.right]
  rw[skip_val, ←List.mem_map_of_injective Subtype.val_injective, skip_val]
  rw[List.map_drop, hq.right.right, hq.right.left]
  rw[skip'_eq_of_apply_eq (nodeinv_rightinv _), nodeinv_rightinv]
  have hq'n:q.tail ≠ []:=by{intro h; simp[h] at hq; simp[hq] at hp''n}
  rw[List.head_cons, List.getLast_cons_cons] at hpcross
  rw[←List.getLast_map (f:=Subtype.val)
  (by{simp only [List.map_eq_nil_iff, ne_eq, hqn, not_false_eq_true]})]
  rw[←List.cons_eq_cons, ←List.map_cons, List.cons_head_tail] at hq
  simp only [hq.right, List.getLast_cons hp''n]
  simp only [List.getLast_cons hp''n, List.tail_cons] at hpcross
  rw[List.idxOf_cons_ne _ (by{
    rw[nodeinv_injective.ne_iff]
    intro h
    apply hpd.left
    rw[List.mem_cons, h]
    right
    apply List.getLast_mem
  }), List.drop_succ_cons] at hpcross
  rw[skip'_eq_of_apply_ne]
  · exact hpcross
  have h:=moebius_path_not_eq hp
  simp only [List.head_cons, List.getLast_cons_cons, List.getLast_cons hp''n] at h
  exact h.symm
}

theorem moebius_path_liftF_of_cons_face_cons_nodeinv {x : α} {p : List α}
  (hp : H.moebius_path (x :: H.face x :: H.nodeinv (H.face x) :: p))
: ∃q, (H.WalkupF (H.face x)).moebius_path q ∧ q.map Subtype.val = (x::H.nodeinv (H.face x)::p)
:= by{
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  rw[List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hpd
  rw[List.isChain_cons_cons, List.isChain_cons_cons] at hpc
  have ⟨q, hq, hqp⟩:=isChain_clink_liftF hpd.right.left hpd.right.right.notMem hpc.right.right
  use ⟨x, hpd.left.left⟩::q
  rw[and_comm]
  constructor
  · rw[List.map_cons, hqp]
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp})]
  constructor
  · {
    rw[←List.nodup_map_iff Subtype.val_injective, List.map_cons, hqp, List.nodup_cons]
    exact ⟨hpd.left.right, hpd.right.right⟩
  }
  have hqn:q ≠ []:=by{intro h; simp[h] at hqp}
  have hqh:(q.head hqn).val = H.nodeinv (H.face x):=by{
    rw[←List.cons_head_tail hqn, List.map_cons, List.cons_eq_cons] at hqp
    exact hqp.left
  }
  constructor
  · {
    rw[List.isChain_cons_iff_of_ne_nil hqn]
    refine ⟨?_, hq⟩
    rw[WalkupF, clink, permN_nodeinv, permN_face, union_iff,
    fromFun, fromFun, faceinv_eq_iff_eq_face]
    rw[walkupe_face, walkupe_edge]
    right
    ext
    rw[hqh, skip_edge'_val, skip_edge'']
    rw[List.mem_cons (a:=H.face x), not_or, eq_nodeinv_iff_node_eq] at hpd
    simp [permF_edge, permF_node, permF_face, nodeinv_eq, face_inj,
    Ne.symm hpd.left.left, hpd.right.left.left]
  }
  rw[List.head_cons, List.getLast_cons hqn, List.tail_cons]
  rw[List.head_cons, List.getLast_cons (by{simp}), List.tail_cons] at hpcross
  rw[WalkupF, permN_nodeinv, walkupe_faceinv, permN_node, walkupe_face]
  simp only [permF_face, permF_faceinv]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, hqp, skip_val]
  rw[←List.getLast_map (f:=Subtype.val)
  (by{simp only [List.map_eq_nil_iff, ne_eq, hqn, not_false_eq_true]})]
  simp only [hqp]
  rw[←List.mem_map_of_injective Subtype.val_injective, skip_val]
  have h0:H.node x ≠ H.face x:=by{
    rw[List.mem_cons, not_or, eq_nodeinv_iff_node_eq] at hpd
    simp[hpd]
  }
  rw[skip'_eq_of_apply_ne h0]
  rw[List.getLast_cons_cons] at hpcross
  rw[List.map_drop]
  simp only [hqp]
  cases em ((H.nodeinv ((H.nodeinv (H.face x)::p).getLast (by{simp}))) = H.face x) with
  | inl h1 => {
    rw[List.idxOf_cons_eq _ h1.symm, List.drop_zero, List.mem_cons] at hpcross
    rw[skip'_eq_of_apply_eq h1, h1, List.idxOf_cons_self, List.drop_zero]
    apply hpcross.resolve_left h0
  }
  | inr h1 => {
    rw[List.idxOf_cons_ne _ (Ne.symm h1), List.drop_succ_cons] at hpcross
    rw[skip'_eq_of_apply_ne h1]
    exact hpcross
  }
}

theorem moebius_path_liftE_of_cons_face_cons_face_of_face_ne_nodeinv_last {x : α} {p : List α}
  (hp : H.moebius_path (x :: H.face x :: H.face (H.face x) :: p))
  (hpf : H.face x ≠ H.nodeinv ((x :: H.face x :: H.face (H.face x) :: p).getLast (by { simp })))
: ∃q, (H.WalkupE (H.face x)).moebius_path q ∧ q.map Subtype.val = (x::H.face (H.face x)::p)
:= by{
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  rw[List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hpd
  rw[List.isChain_cons_cons, List.isChain_cons_cons] at hpc
  have ⟨q, hq, hqp⟩:=isChain_clink_liftE hpd.right.left hpc.right.right
  use ⟨x, hpd.left.left⟩::q
  rw[and_comm]
  constructor
  · rw[List.map_cons, hqp]
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp})]
  constructor
  · {
    rw[←List.nodup_map_iff Subtype.val_injective, List.map_cons, hqp, List.nodup_cons]
    exact ⟨hpd.left.right, hpd.right.right⟩
  }
  have hqn:q ≠ []:=by{intro h; simp[h] at hqp}
  have hqh:(q.head hqn).val = H.face (H.face x):=by{
    rw[←List.cons_head_tail hqn, List.map_cons, List.cons_eq_cons] at hqp
    exact hqp.left
  }
  constructor
  · {
    rw[List.isChain_cons_iff_of_ne_nil hqn]
    refine ⟨?_, hq⟩
    rw[clink, union_iff, fromFun, fromFun]
    rw[walkupe_nodeinv, walkupe_face, Subtype.ext_iff, Subtype.ext_iff]
    rw[skip_val, skip_val, hqh]
    right
    rw[skip'_eq_of_apply_eq rfl]
  }
  rw[List.head_cons, List.getLast_cons hqn, List.tail_cons]
  rw[List.head_cons, List.getLast_cons (by{simp}), List.tail_cons] at hpcross
  rw[List.getLast_cons_cons] at hpcross hpf hpf
  rw[List.idxOf_cons_ne _ hpf, List.drop_succ_cons] at hpcross
  rw[walkupe_nodeinv]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, skip_val, hqp]
  rw[←List.getLast_map (f:=Subtype.val)
  (by{simp only [ne_eq, List.map_eq_nil_iff, hqn, not_false_eq_true]})]
  simp only [hqp]
  rw[←List.mem_map_of_injective Subtype.val_injective, walkupe_node, skip_val, List.map_drop]
  simp only [hqp]
  rw[skip'_eq_of_apply_ne hpf.symm]
  rw[skip'_eq_of_apply_ne]
  · exact hpcross
  intro h
  rw[h] at hpcross
  have h0:=List.mem_of_mem_drop hpcross
  exact hpd.right.left h0
}

theorem moebius_path_liftN_of_cons_face_cons_face_of_face_eq_nodeinv_last_of_face_ne_node_head
  {x : α} {p : List α} (hp : H.moebius_path (x :: H.face x :: H.face (H.face x) :: p))
  (hpf : H.face x = H.nodeinv ((x :: H.face x :: H.face (H.face x) :: p).getLast (by { simp })))
  (hpf' : H.face x ≠ H.node x)
: ∃q, (H.WalkupN (H.face x)).moebius_path q ∧ q.map Subtype.val = (x::H.face (H.face x)::p)
:= by{
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  rw[List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hpd
  rw[List.isChain_cons_cons, List.isChain_cons_cons] at hpc
  have ⟨q, hq, hqp⟩:=isChain_clink_liftN hpd.right.left hpd.right.right.notMem hpc.right.right
  use ⟨x, hpd.left.left⟩::q
  rw[and_comm]
  constructor
  · rw[List.map_cons, hqp]
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp})]
  constructor
  · {
    rw[←List.nodup_map_iff Subtype.val_injective, List.map_cons, hqp, List.nodup_cons]
    exact ⟨hpd.left.right, hpd.right.right⟩
  }
  have hqn:q ≠ []:=by{intro h; simp[h] at hqp}
  have hqh:(q.head hqn).val = H.face (H.face x):=by{
    rw[←List.cons_head_tail hqn, List.map_cons, List.cons_eq_cons] at hqp
    exact hqp.left
  }
  constructor
  · {
    rw[List.isChain_cons_iff_of_ne_nil hqn]
    refine ⟨?_, hq⟩
    rw[clink, union_iff, fromFun, fromFun]
    rw[WalkupN, permF_nodeinv, edgeinv_eq_iff_eq_edge, walkupe_edge]
    rw[permF_face, walkupe_node]
    simp only [permN_node]
    right
    ext
    rw[skip_val, skip'_eq_of_apply_eq rfl, hqh]
  }
  rw[List.head_cons, List.getLast_cons hqn, List.tail_cons]
  rw[List.head_cons, List.getLast_cons (by{simp}), List.tail_cons] at hpcross
  rw[List.getLast_cons_cons] at hpcross hpf hpf
  rw[List.idxOf_cons_eq _ hpf, List.drop_zero, List.mem_cons] at hpcross
  have hpcross':=hpcross.resolve_left hpf'.symm
  have h0' : H.node (H.face x) ≠ H.face x:=by{
    have h0':=moebius_path_nodeinv_ne_getLast hp
    rw[eq_nodeinv_iff_node_eq] at hpf
    simp only [List.getLast_cons_cons, ←hpf, nodeinv_leftinv] at h0'
    exact h0'.symm
  }
  have h0 :(H.permN.WalkupE (face x)).edgeinv (q.getLast hqn) = H.face (H.face x):=by{
    rw[List.mem_cons (a:=H.face x), not_or] at hpd
    change ((H.permN.WalkupE (face x)).edgeinv (q.getLast hqn)).val
      = Subtype.val (⟨H.face (H.face x), Ne.symm hpd.right.left.left⟩ : {a // a ≠ H.face x})
    apply congrArg Subtype.val
    rw[edgeinv_eq_iff_eq_edge, walkupe_edge]
    rw[skip_edge', Subtype.ext_iff]
    simp only [skip_edge'', permN_edge, permN_face, permN_node]
    apply H.nodeinv_injective
    simp only [apply_ite H.nodeinv, nodeinv_leftinv, enf_cancel, ↓reduceIte]
    rw[←List.getLast_map (f:=Subtype.val)
    (by{simp only [List.map_eq_nil_iff, ne_eq, hqn, not_false_iff]})]
    simp only [hqp, ←hpf]
    rw[ite_cond_eq_false]
    simp only [eq_iff_iff, iff_false]
    exact h0'
  }
  rw[WalkupN, permF_nodeinv, permF_node, walkupe_edge]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, h0, hqp, List.idxOf_cons_self, List.drop_zero]
  rw[←List.mem_map_of_injective Subtype.val_injective, hqp, skip_edge'_val]
  simp only [skip_edge'', permN_node, permN_edge, permN_face]
  simp only [hpf'.symm, h0', ↓reduceIte]
  rw[ite_cond_eq_false]
  · exact hpcross'
  simp only [eq_iff_iff, iff_false]
  rw[←enf_cancel (H.face x), edge_inj, node_inj]
  rw[List.mem_cons, not_or] at hpd
  exact hpd.left.right.left
}

theorem moebius_path_liftF_of_cons_face_cons_face_cons_nodeinv_of_face_eq_nodeinv_of_face_eq_node
  {x : α} {p : List α} (hp : H.moebius_path (x :: H.face x :: H.face (H.face x)
  :: H.nodeinv (H.face (H.face x)) :: p))
  (hpf : H.face x = H.nodeinv ((x :: H.face x :: H.face (H.face x) ::
  H.nodeinv (H.face (H.face x)) :: p).getLast (by { simp })))
  (hpf' : H.face x = H.node x)
: ∃q, (H.WalkupF (H.face (H.face x))).moebius_path q ∧ q.map Subtype.val =
(x::H.face x::H.nodeinv (H.face (H.face x))::p)
:= by{
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  rw[List.nodup_cons, List.nodup_cons, List.nodup_cons, List.mem_cons,
  not_or, List.mem_cons, not_or] at hpd
  rw[List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons] at hpc
  have ⟨q, hq, hqp⟩:=isChain_clink_liftF hpd.right.right.left
    hpd.right.right.right.notMem hpc.right.right.right
  use ⟨x, hpd.left.right.left⟩::⟨H.face x, List.ne_of_not_mem_cons hpd.right.left⟩::q
  rw[and_comm]
  constructor
  · rw[List.map_cons, List.map_cons, hqp]
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp})]
  constructor
  · {
    rw[←List.nodup_map_iff Subtype.val_injective, List.map_cons, List.map_cons,
    hqp, List.nodup_cons]
    constructor
    · rw[List.mem_cons, not_or]; exact ⟨hpd.left.left, hpd.left.right.right⟩
    rw[List.nodup_cons]
    exact ⟨List.not_mem_of_not_mem_cons hpd.right.left, hpd.right.right.right⟩
  }
  have hqn:q ≠ []:=by{intro h; simp[h] at hqp}
  have hqh:(q.head hqn).val = H.nodeinv (H.face (H.face x)):=by{
    rw[←List.cons_head_tail hqn, List.map_cons, List.cons_eq_cons] at hqp
    exact hqp.left
  }
  have h0:H.node (H.face x) ≠ H.face (H.face x):=by{
    rw[ne_eq, ←eq_nodeinv_iff_node_eq]
    simp at hpd
    simp[hpd]
  }
  constructor
  · {
    rw[List.isChain_cons_cons, List.isChain_cons_iff_of_ne_nil hqn]
    refine ⟨?_, ?_, hq⟩
    · {
      simp only [clink, ne_eq, WalkupF, permN_nodeinv, walkupe_faceinv, permN_face, union_iff,
        fromFun]
      simp only [permF_faceinv, Subtype.ext_iff, ne_eq, walkupe_edge, skip_edge'_val]
      right
      simp at hpd
      simp[skip_edge'', permF_edge, permF_node, permF_face, h0]
      simp[hpd]
    }
    · {
      simp only [clink, ne_eq, WalkupF, permN_nodeinv, walkupe_faceinv, permN_face, union_iff,
        fromFun]
      simp only [permF_faceinv, Subtype.ext_iff, ne_eq, hqh, walkupe_edge, skip_edge'_val]
      right
      simp[eq_nodeinv_iff_node_eq] at hpd
      simp[skip_edge'', permF_edge, permF_node, permF_face]
      simp[hpd, eq_nodeinv_iff_node_eq, nfe_cancel, face_inj, Ne.symm hpd.left.left]
    }
  }
  rw[List.head_cons, List.getLast_cons_cons, List.getLast_cons hqn, List.tail_cons]
  rw[WalkupF, permN_nodeinv, walkupe_faceinv, permN_node, walkupe_face]
  simp only [permF_face, permF_faceinv]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, List.map_cons, hqp]
  rw[skip_val, ←List.getLast_map (f:=Subtype.val)
  (by{simp only [List.map_eq_nil_iff, ne_eq, hqn, not_false_iff]})]
  simp only [hqp]
  simp only [List.getLast_cons_cons] at hpf
  rw[skip'_eq_of_apply_ne (by{rw[←hpf]; simp at hpd; simp[hpd]}), ←hpf]
  rw[List.idxOf_cons_self, List.drop_zero]
  rw[←List.mem_map_of_injective Subtype.val_injective, List.map_cons, hqp]
  rw[skip_val, skip'_eq_of_apply_ne (by{rw[←hpf']; simp at hpd; simp[hpd]}), ←hpf']
  simp
}

theorem moebius_path_liftE_of_cons_face_cons_face_cons_face_of_face_eq_nodeinv_of_face_eq_node
  {x : α} {p : List α} (hp : H.moebius_path (x :: H.face x :: H.face (H.face x)
  :: H.face (H.face (H.face x)) :: p))
  (hpf : H.face x = H.nodeinv ((x :: H.face x :: H.face (H.face x) ::
  H.face (H.face (H.face x)) :: p).getLast (by { simp })))
  (hpf' : H.face x = H.node x)
: ∃q, (H.WalkupE (H.face (H.face x))).moebius_path q ∧ q.map Subtype.val =
(x::H.face x::H.face (H.face (H.face x))::p)
:= by{
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  have hpcross:=moebius_path_cross_nlink hp
  rw[List.nodup_cons, List.nodup_cons, List.nodup_cons, List.mem_cons,
  not_or, List.mem_cons, not_or] at hpd
  rw[List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons] at hpc
  have ⟨q, hq, hqp⟩:=isChain_clink_liftE hpd.right.right.left hpc.right.right.right
  use ⟨x, hpd.left.right.left⟩::⟨H.face x, List.ne_of_not_mem_cons hpd.right.left⟩::q
  rw[and_comm]
  constructor
  · rw[List.map_cons, List.map_cons, hqp]
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp})]
  constructor
  · {
    rw[←List.nodup_map_iff Subtype.val_injective, List.map_cons, List.map_cons,
    hqp, List.nodup_cons]
    constructor
    · rw[List.mem_cons, not_or]; exact ⟨hpd.left.left, hpd.left.right.right⟩
    rw[List.nodup_cons]
    exact ⟨List.not_mem_of_not_mem_cons hpd.right.left, hpd.right.right.right⟩
  }
  have hqn:q ≠ []:=by{intro h; simp[h] at hqp}
  have hqh:(q.head hqn).val = H.face (H.face (H.face x)):=by{
    rw[←List.cons_head_tail hqn, List.map_cons, List.cons_eq_cons] at hqp
    exact hqp.left
  }
  constructor
  · {
    rw[List.isChain_cons_cons, List.isChain_cons_iff_of_ne_nil hqn]
    refine ⟨?_, ?_, hq⟩
    · {
      simp only [clink, ne_eq, walkupe_nodeinv, walkupe_face, union_iff, fromFun]
      simp only [Subtype.ext_iff, ne_eq, skip_val]
      right
      simp at hpd
      rw[skip'_eq_of_apply_ne]
      simp[hpd]
    }
    · {
      simp only [clink, ne_eq, walkupe_nodeinv, walkupe_face, union_iff, fromFun]
      simp only [Subtype.ext_iff, ne_eq, hqh, skip_val]
      right
      simp[skip'_eq_of_apply_eq]
    }
  }
  rw[List.head_cons, List.getLast_cons_cons, List.getLast_cons hqn, List.tail_cons]
  rw[walkupe_nodeinv, walkupe_node]
  rw[←List.idxOf_map_eq_of_inj Subtype.val_injective, List.map_cons, hqp]
  rw[skip_val, ←List.getLast_map (f:=Subtype.val)
  (by{simp only [List.map_eq_nil_iff, ne_eq, hqn, not_false_iff]})]
  simp only [hqp]
  simp only [List.getLast_cons_cons] at hpf
  rw[skip'_eq_of_apply_ne (by{rw[←hpf]; simp at hpd; simp[hpd]}), ←hpf]
  rw[List.idxOf_cons_self, List.drop_zero]
  rw[←List.mem_map_of_injective Subtype.val_injective, List.map_cons, hqp]
  rw[skip_val, skip'_eq_of_apply_ne (by{rw[←hpf']; simp at hpd; simp[hpd]}), ←hpf']
  simp
}

end Hypermap
