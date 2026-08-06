import FourColorTheorem.Discretize.GridHypermap.GMInner

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

section facecard

theorem GMDartHypermap_fsetoid_n3_iterate {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart} {m : ℕ}
  (hn3u : (node ∘ node ∘ node)^[m] u ∈ hgp.GMGrid) :
  funReflTransGen hgp.GMface u ⟨_, hn3u⟩ := by{
    match u with | ⟨d, hd⟩ => {
      induction m using Nat.strongRec generalizing d with
      | ind m ih => {
        have node_lemma : node (node (node d)) ∈ hgp.GMGrid ∨ (node (node d)) ∈ hgp.GMGrid
          ∨ node d ∈ hgp.GMGrid := by{
            apply of_not_not
            intro node_lemma
            simp only [not_or] at node_lemma
            have hn := hd
            rw[mem_GMGrid_iff] at hn
            simp only [mem_GMGrid_iff, not_or, node_3, face_half] at node_lemma
            have h0 := node_lemma.left.left
            have h1 := node_lemma.right.right.right
            rw[← face_half, fen_cancel] at h1
            exact hn.elim h1 h0
          }
        simp only at hn3u
        rcases em (∃m' < m, m' > 0 ∧ (node ∘ node ∘ node)^[m'] d ∈ hgp.GMGrid)
            with ⟨m', hm'm, hm'0, hm'⟩ | hall
        · {
          have ih' := ih (m - m') (Nat.sub_lt (Nat.zero_lt_of_lt hm'm) hm'0) _ hm'
            (by{rw[← iterate_add_apply, Nat.sub_add_cancel (le_of_lt hm'm)]; exact hn3u})
          simp only[← iterate_add_apply, Nat.sub_add_cancel (le_of_lt hm'm)] at ih'
          have ih'' := ih m' hm'm d hd hm'
          exact ReflTransGen.trans ih'' ih'
        }
        simp only [gt_iff_lt, not_exists, not_and] at hall
        have hm4 : m < 4 := by{
          apply lt_of_not_ge
          intro h
          have hall1 := hall 1 (by{omega}) (by{simp})
          have hall2 := hall 2 (by{omega}) (by{simp})
          have hall3 := hall 3 (by{omega}) (by{simp})
          simp only [iterate_zero, comp_apply, iterate_succ, node_4, id] at hall1 hall2 hall3
          simp[hall1, hall2, hall3] at node_lemma
        }
        match m with
        | 0 => simp[funReflTransGen.refl]
        | 1 => {
          simp only [iterate_one, comp_apply] at hn3u
          apply ReflTransGen.single
          simp only [fromFun, iterate_one, comp_apply, Subtype.ext_iff, GMface]
          rw[List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
        }
        | 2 => {
          have hall1 := hall 1 (by{simp}) (by{simp})
          simp only [iterate_succ, iterate_zero_apply, comp_apply, node_4] at hn3u hall1
          apply ReflTransGen.single
          simp only [fromFun, iterate_succ, iterate_zero_apply, comp_apply,
            Subtype.ext_iff, GMface, node_4]
          rw[List.find?_cons_of_neg, List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
          · simp[hall1]
        }
        | 3 => {
          have hall1 := hall 1 (by{simp}) (by{simp})
          have hall2 := hall 2 (by{simp}) (by{simp})
          simp only [iterate_succ, iterate_zero_apply, comp_apply, node_4] at hn3u hall1 hall2
          apply ReflTransGen.single
          simp only [fromFun, iterate_succ, iterate_zero_apply, comp_apply,
            Subtype.ext_iff, GMface, node_4]
          rw[List.find?_cons_of_neg, List.find?_cons_of_neg,
            List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
          · simp[hall2]
          · simp[hall1]
        }
      }
    }
  }

theorem GMDartHypermap_fsetoid_iff_end0 {hgp : GridMapProper ab0 cm0} {u0 u1 : hgp.GMDart} :
  funReflTransGen GMface u0 u1 ↔ end0 u0 = end0 u1 := by{
    constructor
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hh ht ih => {
        rw[fromFun] at ht
        rw[ih, ← ht, GMface_end0]
      }
    }
    · {
      intro h
      rw[end0_eq_exists_iterate_3] at h
      have ⟨m, hm⟩:=h
      clear h
      match u0, u1 with | ⟨d0, hd0⟩, ⟨d1, hd1⟩ => {
        simp only at hm
        induction m using Nat.strongRec generalizing d0 with
        | ind m ih => {
          simp only [← hm]
          apply GMDartHypermap_fsetoid_n3_iterate
        }
      }
    }
  }

theorem GMDartHypermap_fcomp {hgp : GridMapProper ab0 cm0}
  : hgp.GMDartHypermap.fcomp = (hgp.extendBBox.width + 1) * (hgp.extendBBox.height + 1) := by{
    let CMGridBox : GRectangle := ⟨
      ⟨hgp.extendBBox.hspan.lb, hgp.extendBBox.hspan.ub + 1⟩,
      ⟨hgp.extendBBox.vspan.lb, hgp.extendBBox.vspan.ub + 1⟩
    ⟩
    have CMGridBox_area : CMGridBox.area = (hgp.extendBBox.width + 1) * (hgp.extendBBox.height + 1)
    := by{
      simp only [GRectangle.area, GRectangle.width, GRectangle.height, GInterval.width,
      CMGridBox, add_sub_right_comm]
      congr
      · {
        rw[Int.toNat_add]
        · rfl
        · apply le_of_lt (Int.sub_pos_of_lt (GRectangle.hspan_lt_of_proper hgp.extendBBox_proper))
        · simp
      }
      · {
        rw[Int.toNat_add]
        · rfl
        · apply le_of_lt (Int.sub_pos_of_lt (GRectangle.vspan_lt_of_proper hgp.extendBBox_proper))
        · simp
      }
    }
    rw[← CMGridBox_area, ← GRectangle.enum_length,
      ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
    rw[Hypermap.fcomp]
    apply Fintype.card_congr
    have mem_lemma {u : hgp.GMDart} : end0 u ∈ CMGridBox.enum := by{
      rw[GRectangle.mem_enum_iff]
      match u with | ⟨d, hd⟩ => {
        simp only
        simp only [mem_GMGrid_iff] at hd
        simp only [edge_half, GRectangle.mem_iff, GInterval.mem_iff] at hd
        simp only [end0, GRectangle.mem_iff, CMGridBox, GInterval.mem_iff]
        simp only [Int.lt_add_one_iff]
        simp only [GPoint.add_def]
        simp only [GPoint.add_def, GPoint.sub_def] at hd
        rcases GPoint.mod2_cases (p:=d) with h | h | h | h
        all_goals
        simp only [GPoint.ccw, h, sub_zero, add_zero, add_sub_cancel_right, Int.le_sub_one_iff,
          Int.sub_one_lt_iff, sub_self, add_zero] at hd
        simp[h]
        omega
      }
    }
    have exists_GMGrid {p : GPixel} (hp : p ∈ CMGridBox) : ∃d, end0 d = p ∧ d ∈ hgp.GMGrid := by{
      match p with | ⟨px, py⟩ => {
        simp only [GRectangle.mem_iff, GInterval.mem_iff, CMGridBox, Int.lt_add_one_iff] at hp
        have hh := GRectangle.hspan_lt_of_proper hgp.extendBBox_proper
        have hv := GRectangle.vspan_lt_of_proper hgp.extendBBox_proper
        rcases lt_or_eq_of_le hp.left.right with hplr | hplr
        · {
          rcases lt_or_eq_of_le hp.right.right with hprr | hprr
          · {
            use 2 • ⟨px, py⟩
            rw[end0, GPoint.half_double, GPoint.mod2_double, mem_GMGrid_iff, add_zero]
            apply And.intro rfl
            left
            rw[GPoint.half_double]
            simp only [GRectangle.mem_iff, GInterval.mem_iff]
            omega
          }
          · {
            use 2 • ⟨px, py⟩ + ⟨0, -1⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
        }
        · {
          rcases lt_or_eq_of_le hp.right.right with hprr | hprr
          · {
            use 2 • ⟨px, py⟩ + ⟨-1, 0⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
          · {
            use 2 • ⟨px, py⟩ + ⟨-1, -1⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
        }
      }
    }
    let f : Quotient hgp.GMDartHypermap.fsetoid → { x // x ∈ CMGridBox.enum } :=
      fun q => ⟨end0 q.out, mem_lemma⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro q1 q2 hq12
      unfold f at hq12
      rw[Subtype.ext_iff] at hq12
      simp only at hq12
      rw[← GMDartHypermap_fsetoid_iff_end0] at hq12
      rw[← Quotient.out_equiv_out]
      exact hq12
    }
    · {
      intro ⟨p, hp⟩
      rw[GRectangle.mem_enum_iff] at hp
      have ⟨d, hd0, hd⟩:=exists_GMGrid hp
      use ⟦⟨d, hd⟩⟧
      unfold f
      have hout := Quotient.mk_out (s:=hgp.GMDartHypermap.fsetoid) ⟨d, hd⟩
      change funReflTransGen GMface _ _ at hout
      rw[GMDartHypermap_fsetoid_iff_end0] at hout
      simp only [hout, hd0]
    }
  }
end facecard

end GridMapProper
end GridPlane
