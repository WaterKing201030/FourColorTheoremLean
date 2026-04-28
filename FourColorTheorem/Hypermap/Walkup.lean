import FourColorTheorem.Hypermap.Walkup.Skip
import FourColorTheorem.Hypermap.Walkup.Gcomp
import FourColorTheorem.Hypermap.Walkup.Ecomp
import FourColorTheorem.Hypermap.Walkup.Jordan

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem euler_lhs_ge3_intro (x : α) : H.euler_lhs ≥ 3:=by{
  unfold euler_lhs
  have hgp:=H.gcomp_pos_intro x
  rw[mul_two, ←two_add_one_eq_three, ←one_add_one_eq_two]
  apply add_le_add
  · {
    apply add_le_add
    all_goals
    exact hgp
  }
  apply Nat.succ_le_of_lt
  rw[Fintype.card_pos_iff]
  apply Nonempty.intro x
}
theorem euler_rhs_ge3_intro (x : α) : H.euler_rhs ≥ 3:=by{
  unfold euler_rhs
  have hep:=H.ecomp_pos_intro x
  have hnp:=H.ncomp_pos_intro x
  have hfp:=H.fcomp_pos_intro x
  rw[←two_add_one_eq_three, ←one_add_one_eq_two, ←Nat.add_assoc]
  apply add_le_add
  · apply add_le_add hep hnp
  exact hfp
}
def nneg_genus (H : Hypermap α) := H.euler_rhs ≤ H.euler_lhs
theorem always_nneg_genus {α : Type _} [Fintype α] [DecidableEq α]
{H : Hypermap α} : H.nneg_genus := by{
  unfold nneg_genus
  cases isEmpty_or_nonempty α with
  | inl ha => {
    unfold euler_lhs euler_rhs
    unfold gcomp ecomp ncomp fcomp
    unfold Fintype.nComp
    simp
  }
  | inr ha => {
    have x:=ha.some
    have : Fintype.card {a // a ≠ x} < Fintype.card α:=by{
      simp[Fintype.card_pos_iff, ha]
    }
    have ih:=@always_nneg_genus _ _ _ (H.WalkupE x)
    unfold nneg_genus at ih
    rw[walkupe_euler_lhs, walkupe_euler_rhs] at ih
    cases em (H.isbarb x) with
    | inl hbx => {
      have hgx:=glink_self_of_isbarb hbx
      simp[hbx, hgx] at ih
      simp[Nat.sub_add_cancel (euler_lhs_ge3_intro x)] at ih
      simp[ih]
    }
    | inr hbx => {
      cases em (H.glink x x) with
      | inl hgx => {
        simp only [hbx, ↓reduceIte, hgx, Nat.reduceSubDiff, tsub_le_iff_right] at ih
        rw[Nat.sub_add_cancel (Nat.le_trans (by{simp}) (euler_lhs_ge3_intro x))] at ih
        simp[ih]
      }
      | inr hgx => {
        cases em (H.cross_edge x) with
        | inl hcex => {
          cases em (H.skip_edge'_issplit x) with
          | inl hsx => {
            simp[hbx, hgx, hcex, hsx] at ih
            simp[ih]
          }
          | inr hsx => {
            simp only [hbx, ↓reduceIte, hgx, hcex, tsub_zero, hsx, Nat.reduceSubDiff,
              Order.add_one_le_iff] at ih
            apply Nat.le_trans (Nat.le_of_lt ih)
            apply Nat.pred_le
          }
        }
        | inr hcex => {
          have hsx := not_skip_edge'_issplit_of_not_cross_edge hcex
          simp only [hbx, ↓reduceIte, hgx, hcex, Nat.reduceSubDiff, hsx, tsub_le_iff_right] at ih
          rw[Nat.sub_add_cancel (Nat.le_trans (by{simp}) (euler_lhs_ge3_intro x))] at ih
          simp[ih]
        }
      }
    }
  }
}
termination_by Fintype.card α
theorem euler_diff_ge_two_of_not_glink_of_cross_edge_of_not_split {α : Type _}
[Fintype α] [DecidableEq α] {H : Hypermap α} {x : α} (hgx : ¬H.glink x x)
(hcex : H.cross_edge x) (hsx : ¬H.skip_edge'_issplit x) : H.euler_lhs - H.euler_rhs ≥ 2:=by{
  have h:=always_nneg_genus (H:=H.WalkupE x)
  unfold nneg_genus at h
  rw[walkupe_euler_lhs, walkupe_euler_rhs] at h
  have hbx:¬H.isbarb x:=by{
    intro hbx
    apply hgx
    exact glink_self_of_isbarb hbx
  }
  simp only [hbx, ↓reduceIte, hgx, hcex, tsub_zero, hsx, Nat.reduceSubDiff,
    Order.add_one_le_iff] at h
  have h':=Nat.lt_pred_iff.mp h
  apply Nat.le_sub_of_add_le
  rw[Nat.add_comm]
  apply Nat.succ_le_of_lt
  simp at h'
  simp[h']
}
def even_genus (H : Hypermap α) := 2 ∣ H.euler_lhs - H.euler_rhs
theorem always_even_genus {α : Type _} [Fintype α] [DecidableEq α]
{H : Hypermap α} : H.even_genus := by{
  unfold even_genus
  cases isEmpty_or_nonempty α with
  | inl ha => {
    unfold euler_lhs euler_rhs
    unfold gcomp ecomp ncomp fcomp
    unfold Fintype.nComp
    simp
  }
  | inr ha => {
    have x:=ha.some
    have : Fintype.card {a // a ≠ x} < Fintype.card α:=by{
      simp[Fintype.card_pos_iff, ha]
    }
    have ih:=@always_even_genus _ _ _ (H.WalkupE x)
    unfold even_genus at ih
    rw[walkupe_euler_lhs, walkupe_euler_rhs] at ih
    cases em (H.isbarb x) with
    | inl hbx => {
      have hgx:=glink_self_of_isbarb hbx
      simp only [hgx, ↓reduceIte, hbx, Nat.reduceSubDiff] at ih
      rw[Nat.sub_sub, Nat.add_sub_cancel' (euler_rhs_ge3_intro x)] at ih
      simp[ih]
    }
    | inr hbx => {
      cases em (H.glink x x) with
      | inl hgx => {
        simp only [hbx, ↓reduceIte, hgx, Nat.reduceSubDiff] at ih
        rw[Nat.sub_sub, Nat.add_sub_cancel' (Nat.le_trans (by{simp}) (euler_rhs_ge3_intro x))] at ih
        simp[ih]
      }
      | inr hgx => {
        cases em (H.cross_edge x) with
        | inl hcex => {
          cases em (H.skip_edge'_issplit x) with
          | inl hsx => {
            simp[hbx, hgx, hcex, hsx] at ih
            simp[ih]
          }
          | inr hsx => {
            simp only [hbx, ↓reduceIte, hgx, hcex, tsub_zero, hsx, Nat.reduceSubDiff] at ih
            rw[Nat.sub_sub, Nat.add_comm, Nat.add_assoc, ←Nat.sub_sub] at ih
            rw[Nat.dvd_sub_self_right] at ih
            apply ih.elim id
            intro ih'
            have ih'':=euler_diff_ge_two_of_not_glink_of_cross_edge_of_not_split
              hgx hcex hsx
            have ih0:=Nat.le_antisymm ih' ih''
            simp[ih0]
          }
        }
        | inr hcex => {
          have hsx := not_skip_edge'_issplit_of_not_cross_edge hcex
          simp only [hbx, ↓reduceIte, hgx, hcex, Nat.reduceSubDiff, hsx] at ih
          rw[Nat.sub_sub,
          Nat.add_sub_cancel' (Nat.le_trans (by{simp}) (euler_rhs_ge3_intro x))] at ih
          simp[ih]
        }
      }
    }
  }
}
termination_by Fintype.card α
theorem walkupe_genus_le {x : α} : (H.WalkupE x).genus ≤ H.genus := by{
  unfold genus
  rw[walkupe_euler_lhs, walkupe_euler_rhs]
  apply Nat.div_le_div_right
  cases em (H.isbarb x) with
  | inl hbx => {
    have hgx:=glink_self_of_isbarb hbx
    simp[hbx, hgx, Nat.sub_sub, Nat.add_sub_cancel' (euler_rhs_ge3_intro x)]
  }
  | inr hbx => {
    cases em (H.glink x x) with
    | inl hgx => {
      simp[hbx, hgx, Nat.sub_sub]
      simp[Nat.add_sub_cancel' (Nat.le_trans (by{simp}:1 ≤ 3) (euler_rhs_ge3_intro x))]
      simp[Nat.sub_add_cancel H.always_nneg_genus]
    }
    | inr hgx => {
      cases em (H.cross_edge x) with
      | inl hcex => {
        cases em (H.skip_edge'_issplit x) with
        | inl hsx => {
          simp[hbx, hgx, hcex, hsx]
        }
        | inr hsx => {
          simp only [hgx, ↓reduceIte, hsx, Nat.reduceSubDiff, hbx, hcex, tsub_zero,
            tsub_le_iff_right]
          rw[Nat.add_assoc, Nat.add_assoc, ←Nat.add_assoc]
          simp[Nat.sub_add_cancel H.always_nneg_genus]
        }
      }
      | inr hcex => {
        have hsx := not_skip_edge'_issplit_of_not_cross_edge hcex
        simp[hbx, hgx, hcex, hsx, Nat.sub_sub]
        simp[Nat.add_sub_cancel' (Nat.le_trans (by{simp}:1 ≤ 3) (euler_rhs_ge3_intro x))]
        simp[Nat.sub_add_cancel H.always_nneg_genus]
      }
    }
  }
}
theorem walkupe_genus_eq_of_isbarb {x : α} (hbx : H.isbarb x)
: (H.WalkupE x).genus = H.genus := by{
  unfold genus
  rw[walkupe_euler_lhs, walkupe_euler_rhs]
  have hgx:H.glink x x:=glink_self_of_isbarb hbx
  simp[hbx, hgx, Nat.sub_sub, Nat.add_sub_cancel' (euler_rhs_ge3_intro x)]
}
theorem walkupe_genus_eq_of_glink {x : α} (hgx : H.glink x x)
: (H.WalkupE x).genus = H.genus := by{
  cases em (H.isbarb x) with
  | inl hbx => exact walkupe_genus_eq_of_isbarb hbx
  | inr hbx => {
    unfold genus
    rw[walkupe_euler_lhs, walkupe_euler_rhs]
    simp[hbx, hgx, Nat.sub_sub]
    simp[Nat.add_sub_cancel' (Nat.le_trans (by{simp}:1 ≤ 3) (euler_rhs_ge3_intro x))]
  }
}
theorem walkupe_genus_eq_of_not_cross_edge {x : α} (hcex : ¬H.cross_edge x)
: (H.WalkupE x).genus = H.genus := by{
  cases em (H.isbarb x) with
  | inl hbx => exact walkupe_genus_eq_of_isbarb hbx
  | inr hbx => {
    cases em (H.glink x x) with
    | inl hgx => exact walkupe_genus_eq_of_glink hgx
    | inr hgx => {
      have hsx := not_skip_edge'_issplit_of_not_cross_edge hcex
      unfold genus
      rw[walkupe_euler_lhs, walkupe_euler_rhs]
      simp[hbx, hgx, hcex, hsx, Nat.sub_sub]
      simp[Nat.add_sub_cancel' (Nat.le_trans (by{simp}:1 ≤ 3) (euler_rhs_ge3_intro x))]
    }
  }
}
theorem walkupe_genus_eq_of_issplit {x : α} (hsx : H.skip_edge'_issplit x)
: (H.WalkupE x).genus = H.genus := by{
  cases em (H.isbarb x) with
  | inl hbx => exact walkupe_genus_eq_of_isbarb hbx
  | inr hbx => cases em (H.glink x x) with
    | inl hgx => exact walkupe_genus_eq_of_glink hgx
    | inr hgx => cases em (H.cross_edge x) with
      | inl hcex => {
        unfold genus
        rw[walkupe_euler_lhs, walkupe_euler_rhs]
        simp[hbx, hgx, hcex, hsx]
      }
      | inr hcex => exact walkupe_genus_eq_of_not_cross_edge hcex
}
theorem planar_walkupe_planar {x : α} (h : H.planar) : (H.WalkupE x).planar := by{
  unfold planar at *
  have h':=walkupe_genus_le (H:=H) (x:=x)
  rw[h] at h'
  exact Nat.eq_zero_of_le_zero h'
}
theorem planar_walkupn_planar {x : α} (h : H.planar) : (H.WalkupN x).planar := by{
  rw[WalkupN, permF_planar]
  apply planar_walkupe_planar
  rw[permN_planar]
  exact h
}
theorem planar_walkupf_planar {x : α} (h : H.planar) : (H.WalkupF x).planar := by{
  rw[WalkupF, permN_planar]
  apply planar_walkupe_planar
  rw[permF_planar]
  exact h
}
theorem not_planar_of_not_glink_of_cross_edge_of_not_split {α : Type _}
[Fintype α] [DecidableEq α] {H : Hypermap α} {x : α} (hgx : ¬H.glink x x)
(hcex : H.cross_edge x) (hsx : ¬H.skip_edge'_issplit x) : ¬H.planar:=by{
  have h:=euler_diff_ge_two_of_not_glink_of_cross_edge_of_not_split hgx hcex hsx
  unfold planar
  apply Nat.ne_zero_of_lt (b:=0)
  unfold genus
  apply Nat.lt_of_succ_le
  rw[Nat.le_div_iff_mul_le (by{simp})]
  exact h
}

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

theorem not_planar_of_moebius_path_triple {x y z : α} (huniv : ∀ a, a ∈ [x, y, z])
  (hp : H.moebius_path [x, y, z]) : ¬H.planar := by{
  have h0:=moebius_path_node_head_mem_dropLast_tail hp
  have h1:=moebius_path_nodeinv_getLast_mem_dropLast_tail hp
  have hpd:=moebius_path_nodup hp
  have hpc:=moebius_path_isChain_clink hp
  simp only [List.dropLast_cons₂, List.dropLast_singleton, List.tail_cons, List.head_cons,
    List.mem_cons, List.not_mem_nil, or_false, ne_eq, reduceCtorEq, not_false_eq_true,
    List.getLast_cons, List.cons_ne_self, List.getLast_singleton] at h0 h1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_self, and_true] at hpd
  simp only [clink, List.isChain_cons_cons, union_iff, fromFun, nodeinv_eq_iff_eq_node,
    List.IsChain.singleton, and_true] at hpc
  rw[nodeinv_eq_iff_eq_node] at h1
  simp only [← h1, hpd, false_or] at hpc
  nth_rw 2 [←h0] at hpc
  simp only [node_inj, hpd, false_or] at hpc
  have h2:=hpc.left
  rw[←eq_faceinv_iff_face_eq, faceinv_eq, comp_apply, ←h1] at h2
  have h3:H.node z = x:=by{
    have h3:=huniv (H.node z)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    apply h3.resolve_right
    rw[←h0, node_inj]
    nth_rw 3 [h1]
    rw[node_inj]
    simp [Eq.comm (a:=z), hpd]
  }
  have h4:H.edge x = y:=by{
    rw[←enf_cancel y, edge_inj, hpc.right, h3]
  }
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huniv
  have he:H.ecomp = 1:=by{
    simp only [ecomp, Fintype.nComp_eq_one_iff_exists_all]
    unfold esetoid
    simp only
    use z
    intro a
    simp only [cedge, funReflTransGen_iff_iterate]
    cases huniv a with
    | inl ha => use 1; simp[ha, ←h2]
    | inr ha => cases ha with
      | inl ha => use 2; simp[ha, ←h2, h4]
      | inr ha => use 0; simp[ha]
  }
  have hn:H.ncomp = 1:=by{
    simp only [ncomp, Fintype.nComp_eq_one_iff_exists_all]
    unfold nsetoid
    simp only
    use x
    intro a
    simp only [cnode, funReflTransGen_iff_iterate]
    cases huniv a with
    | inl ha => use 0; simp[ha]
    | inr ha => cases ha with
      | inl ha => use 1; simp[ha, h0]
      | inr ha => use 2; simp[ha, h0, ←h1]
  }
  have hf:H.fcomp = 1:=by{
    simp only [fcomp, Fintype.nComp_eq_one_iff_exists_all]
    unfold fsetoid
    simp only
    use x
    intro a
    simp only [cface, funReflTransGen_iff_iterate]
    cases huniv a with
    | inl ha => use 0; simp[ha]
    | inr ha => cases ha with
      | inl ha => use 1; simp[ha, hpc]
      | inr ha => use 2; simp[ha, hpc]
  }
  have hg:H.gcomp = 1:=by{
    simp only [gcomp, Fintype.nComp_eq_one_iff_exists_all]
    unfold gsetoid
    simp only
    use x
    intro a
    cases huniv a with
    | inl ha => simp only [ha]; apply ReflTransGen.refl
    | inr ha => cases ha with
      | inl ha => simp only [ha]; apply ReflTransGen.single; simp[glink_iff, h0]
      | inr ha => {
        apply cglink_equivalence.symm
        simp only[ha]
        apply ReflTransGen.single
        simp[glink_iff, h3]
      }
  }
  have hc:Fintype.card α = 3:=by{
    have h1:=List.toFinset_card_of_nodup (moebius_path_nodup hp)
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd] at h1
    have h2:({x, y, z}:Finset α) = Finset.univ:=by{
      rw[Finset.eq_univ_iff_forall]
      intro a
      simp[huniv a]
    }
    rw [h2] at h1
    rw[←h1]
    simp
  }
  unfold planar genus euler_lhs euler_rhs
  simp[he, hn, hf, hg, hc]
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

theorem jordan_of_planar {α : Type _} [Fintype α] [DecidableEq α] {H : Hypermap α}
  (hp : H.planar) : H.jordan := by{
  obtain ⟨n, hn⟩:∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with
  | _ n ih => {
    intro p hj
    have hn_3 : n ≥ 3 :=by{
      rw[←hn]
      apply card_ge_three_of_moebius_path hj
    }
    have hn_p : n > 0 := by{
      rw[←hn]
      apply card_pos_of_moebius_path hj
    }
    have hpn:=moebius_path_ne_nil hj
    cases em (∀x, x ∈ p) with
    | inl hpx => {
      have hp'n := moebius_path_tail_ne_nil hj
      have hp''n := moebius_path_tail_tail_ne_nil hj
      have hlc:Fintype.card α = p.length:=by{
        apply Nat.le_antisymm
        · {
          have h:=List.toFinset_card_le p
          have h':p.toFinset.card = Fintype.card α:=by{
            rw[Finset.card_eq_iff_eq_univ]
            rw[Finset.eq_univ_iff_forall]
            simp only [List.mem_toFinset]
            exact hpx
          }
          rw[←h']
          exact h
        }
        · apply (moebius_path_nodup hj).length_le_card
      }
      match hp_def:p with
      | x::p1 => {
        rw[List.tail_cons] at hp'n hp''n
        rw[←hn, hlc] at ih
        match hp1_def:p1 with
        | y::p2 => {
          cases em (H.nodeinv x = y) with
          | inl h0 => {
            have ih':=ih (p2.length + 1) (by{simp}) (H:=H.WalkupE x) (planar_walkupe_planar hp)
              (by{simp[hlc]})
            rw[←h0] at hj
            have ⟨q, hq, _⟩:=moebius_path_liftE_of_cons_nodeinv hj
            exact ih' _ hq
          }
          | inr h0 => {
            have h0':H.face x = y:=by{
              have hj':=moebius_path_isChain_clink hj
              rw[List.isChain_cons_cons] at hj'
              have hj':=hj'.left
              simp only [clink,union_iff,fromFun] at hj'
              exact hj'.resolve_left h0
            }
            match hp2_def : p2 with
            | z::p3 => {
              cases em (H.nodeinv y = z) with
              | inl h1 => {
                have ⟨q, hq⟩:=H.moebius_path_liftF_of_cons_face_cons_nodeinv (x:=x) (p:=p3) (by{
                  simp only [← h0', ← h1] at hj
                  exact hj
                })
                have ih':=ih (x::z::p3).length (by{simp})
                  (H:=H.WalkupF (H.face x)) (planar_walkupf_planar hp)
                  (by{simp[hlc]})
                apply ih' _ hq.left
              }
              | inr h1 => {
                have h1':H.face y = z:=by{
                  have hj':=moebius_path_isChain_clink hj
                  rw[List.isChain_cons_cons, List.isChain_cons_cons] at hj'
                  have hj':=hj'.right.left
                  simp only [clink,union_iff,fromFun] at hj'
                  exact hj'.resolve_left h1
                }
                cases em (y = H.nodeinv ((x::y::z::p3).getLast (by{simp}))) with
                | inl hynl => cases em (y = H.node x) with
                  | inl hynh => {
                    match hp3_def:p3 with
                    | [] => apply not_planar_of_moebius_path_triple hpx hj hp
                    | w::p4 => {
                      have hzwc : H.clink z w := by{
                        have hc:=moebius_path_isChain_clink hj
                        simp[List.isChain_cons_cons] at hc
                        simp[hc]
                      }
                      simp only [clink, union_iff, fromFun] at hzwc
                      cases hzwc with
                      | inl hzwc => {
have ⟨q, hq⟩:=
  H.moebius_path_liftF_of_cons_face_cons_face_cons_nodeinv_of_face_eq_nodeinv_of_face_eq_node
  (x:=x) (p:=p4) (by{simp only [hzwc, h1', h0']; exact hj})
  (by{simp only [hzwc, h1', h0']; exact hynl}) (by{simp[h0', hynh]})
have ih':=ih (x::y::w::p4).length (by{simp}) (H:=(H.WalkupF (H.face (H.face x))))
  (planar_walkupf_planar hp) (by{simp[hlc]})
apply ih' _ hq.left
                      }
                      | inr hzwc => {
have ⟨q, hq⟩:=
  H.moebius_path_liftE_of_cons_face_cons_face_cons_face_of_face_eq_nodeinv_of_face_eq_node
  (x:=x) (p:=p4) (by{simp only [hzwc, h1', h0']; exact hj})
  (by{simp only [hzwc, h1', h0']; exact hynl}) (by{simp[h0', hynh]})
have ih':=ih (x::y::w::p4).length (by{simp}) (H:=(H.WalkupE (H.face (H.face x))))
  (planar_walkupe_planar hp) (by{simp[hlc]})
apply ih' _ hq.left
                      }
                    }
                  }
                  | inr hynh => {
have ⟨q, hq⟩:=
  H.moebius_path_liftN_of_cons_face_cons_face_of_face_eq_nodeinv_last_of_face_ne_node_head
  (x:=x) (p:=p3) (by{simp[h0', h1', hj]}) (by{simp only [h0', h1']; exact hynl})
  (by{simp[h0', hynh]})
have ih':=ih (x::z::p3).length (by{simp}) (H:=H.WalkupN (H.face x))
  (planar_walkupn_planar hp) (by{simp[hlc]})
apply ih' _ hq.left
                  }
                | inr hynl => {
have ⟨q, hq⟩:=H.moebius_path_liftE_of_cons_face_cons_face_of_face_ne_nodeinv_last (x:=x) (p:=p3)
  (by{simp[h0', h1', hj]}) (by{simp only [h0', h1', ne_eq, hynl, not_false_iff]})
have ih':=ih (x::z::p3).length (by{simp}) (H:=H.WalkupE (H.face x))
  (planar_walkupe_planar hp) (by{simp[hlc]})
apply ih' _ hq.left
                }
              }
            }
          }
        }
      }
    }
    | inr hpx => {
      rw[not_forall] at hpx
      have ⟨x, hpx⟩:=hpx
      have ih':=ih (n - 1) (Nat.pred_lt_self hn_p)
        (H:=H.WalkupE x) (planar_walkupe_planar hp)
      simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique] at ih'
      rw[hn] at ih'
      have ih'':=ih' rfl
      have ⟨q, hq⟩:=moebius_path_liftE_of_not_mem hpx hj
      apply ih'' q hq.left
    }
  }
}

end Hypermap
