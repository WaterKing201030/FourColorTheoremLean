import FourColorTheorem.Hypermap.Walkup.Skip
import FourColorTheorem.Hypermap.Walkup.Gcomp
import FourColorTheorem.Hypermap.Walkup.Ecomp

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

-- theorem walkupe_euler_lhs {x : α} : (H.WalkupE x).euler_lhs =
--   H.euler_lhs + 1 - if H.glink x x then (if H.isbarb x then 4 else 2)
--   else (if H.skip_edge'_issplit x then 0 else 2)
-- theorem walkupe_euler_rhs {x : α} :
--   (H.WalkupE x).euler_rhs = H.euler_rhs + 1 - if H.isbarb x then 4
--   else if H.cross_edge x then if H.glink x x then 2 else 0 else 2
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

end Hypermap
