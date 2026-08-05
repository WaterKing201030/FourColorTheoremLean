import Init.Data.Nat.Lemmas
import FourColorTheorem.Hypermap.Properties.Planar.Euler.Basic
import FourColorTheorem.Hypermap.Actions.Walkup
import FourColorTheorem.Hypermap.Properties.Planar.Euler.Perm

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem walkupe_euler_lhs {x : α} : (H.WalkupE x).euler_lhs =
  H.euler_lhs + 1 - if H.glink x x then (if H.isbarb x then 4 else 2)
  else (if H.skip_edge'_issplit x then 0 else 2) := by{
    unfold euler_lhs
    simp only [ne_eq, walkupe_gcomp, Fintype.card_subtype_compl, Fintype.card_unique]
    simp only [Nat.sub_mul, Nat.add_mul, one_mul, ite_mul, Nat.reduceMul, zero_mul]
    rw[←Nat.sub_add_comm (by{
      rw[apply_ite (· ≤ _)]
      rw[apply_ite (· ≤ _)]
      rw[apply_ite (· ≤ _)]
      simp only [Nat.reduceLeDiff, zero_lt_two, le_mul_iff_one_le_left, le_add_iff_nonneg_left,
        zero_le, if_true_right, ite_self]
      intro _ _
      unfold gcomp Fintype.nComp
      apply Nat.succ_le_of_lt
      apply Fintype.card_pos_iff.mpr
      apply Nonempty.intro ⟦x⟧
    })]
    apply congrArg (· - _)
    rw[←Nat.add_sub_assoc (by{
      apply Nat.succ_le_of_lt
      apply Fintype.card_pos_iff.mpr
      apply Nonempty.intro x
    })]
    rw[Nat.add_right_comm]
    simp
  }

theorem walkupe_euler_rhs {x : α} :
  (H.WalkupE x).euler_rhs = H.euler_rhs + 1 - if H.isbarb x then 4
  else if H.glink x x then 2 else if H.cross_edge x then 0 else 2 := by{
    unfold euler_rhs
    rw[walkupe_ecomp, walkupe_ncomp, walkupe_fcomp]
    have hep:=H.ecomp_pos_intro x
    have hnp:=H.ncomp_pos_intro x
    have hfp:=H.fcomp_pos_intro x
    cases em (H.isbarb x) with
    | inl hbx => {
      simp only [hbx, ↓reduceIte, Nat.reduceSubDiff]
      simp[isbarb_iff_all_perm_self] at hbx
      simp only [hbx, ↓reduceIte]
      rw[←Nat.sub_add_comm hep]
      rw[←Nat.sub_add_comm hnp]
      rw[←Nat.add_sub_assoc hfp]
      rw[Nat.sub_sub]
      rw[←Nat.add_sub_assoc
        (Nat.add_le_add hnp hfp)]
      rw[Nat.sub_sub]
    }
    | inr hbx => {
      cases em (H.cross_edge x) with
      | inl hcex => {
        cases em (H.glink x x) with
        | inl hgx => {
          have hex:=(cross_edge_iff_not_edge_self_of_not_isbarb_of_glink
          hbx hgx).mp hcex
          simp only [hgx, hcex, hbx, ↓reduceIte]
          simp only [add_tsub_cancel_right, Nat.reduceSubDiff]
          have hn:H.face x = x ↔ H.node x ≠ x:=by{
            constructor
            · {
              intro hfx hnx
              apply hex
              nth_rw 1 [←hnx, ←hfx, enf_cancel]
            }
            · {
              intro hnx
              exact (hgx.resolve_left hex).resolve_left hnx
            }
          }
          simp only [hn, ne_eq, ite_not]
          cases em (H.node x = x) with
          | inl hnx => {
            simp only [hnx, ↓reduceIte, tsub_zero]
            rw[←Nat.sub_add_comm hnp]
            rw[←Nat.add_sub_assoc]
            apply Nat.le_add_left_of_le
            exact hfp
          }
          | inr hnx => {
            simp only [hnx, ↓reduceIte, tsub_zero]
            rw[←Nat.add_sub_assoc hfp]
            rw[←Nat.add_sub_assoc]
            apply Nat.le_add_left_of_le
            exact hfp
          }
        }
        | inr hgx => {
          simp [hgx]
          simp [glink_iff] at hgx
          simp [hgx, hbx, hcex, Nat.succ_add]
        }
      }
      | inr hcex => {
        have hnx:=not_node_self_of_not_cross_edge hcex
        have hfx:=not_face_self_of_not_cross_edge hcex
        simp[hfx, hnx, hcex, hbx]
        simp[←Nat.sub_add_comm hep]
      }
    }
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

theorem not_planar_of_not_glink_of_cross_edge_of_not_split {α : Type _}
[Fintype α] [DecidableEq α] {H : Hypermap α} {x : α} (hgx : ¬H.glink x x)
(hcex : H.cross_edge x) (hsx : ¬H.skip_edge'_issplit x) : ¬H.Planar:=by{
  have h:=euler_diff_ge_two_of_not_glink_of_cross_edge_of_not_split hgx hcex hsx
  simp only [planar_def]
  apply Nat.ne_zero_of_lt (b:=0)
  unfold genus
  apply Nat.lt_of_succ_le
  rw[Nat.le_div_iff_mul_le (by{simp})]
  exact h
}

theorem Planar.walkupe {x : α} (h : H.Planar) : (H.WalkupE x).Planar := by{
  simp only [planar_def] at *
  have h':=walkupe_genus_le (H:=H) (x:=x)
  rw[h] at h'
  exact Nat.eq_zero_of_le_zero h'
}
theorem Planar.walkupn {x : α} (h : H.Planar) : (H.WalkupN x).Planar := by{
  rw[WalkupN, permF_planar_iff]
  apply Planar.walkupe
  rw[permN_planar_iff]
  exact h
}
theorem Planar.walkupf {x : α} (h : H.Planar) : (H.WalkupF x).Planar := by{
  rw[WalkupF, permN_planar_iff]
  apply Planar.walkupe
  rw[permF_planar_iff]
  exact h
}

end Hypermap
