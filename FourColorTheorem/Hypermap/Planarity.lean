import Init.Data.Nat.Lemmas
import FourColorTheorem.Hypermap.Actions.Walkup

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

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

theorem planar_of_jordan {α : Type _} [Fintype α] [DecidableEq α] {H : Hypermap α}
  (hj : H.jordan) : H.planar := by{
  cases isEmpty_or_nonempty α with
  | inl ha => {
    simp[planar, genus, euler_lhs, euler_rhs, gcomp, Fintype.nComp_eq_zero_iff.mpr ha]
  }
  | inr ha => {
    have ih:=euler_tree hj ha.some
    simp only [not_forall, not_and, ←or_iff_not_imp_left] at ih
    have ⟨b, hb, hb2⟩:=ih
    have hb':=walkupe_jordan (x:=b) hj
    have : Fintype.card {a // a ≠ b} < Fintype.card α:=by{
      simp[Fintype.card_pos_iff, ha]
    }
    have ih:=planar_of_jordan hb'
    rw[planar] at ih
    rw[planar]
    cases hb2 with
    | inl h => {
      have h:=glink_self_of_clink_self h
      rw[walkupe_genus_eq_of_glink h] at ih
      exact ih
    }
    | inr h => {
      rw[walkupe_genus_eq_of_not_cross_edge h] at ih
      exact ih
    }
  }
}
termination_by Fintype.card α

theorem planar_iff_jordan : H.planar ↔ H.jordan :=
  ⟨jordan_of_planar, planar_of_jordan⟩

end Hypermap
