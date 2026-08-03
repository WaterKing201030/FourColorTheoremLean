import FourColorTheorem.Hypermap.Actions.Walkup
import FourColorTheorem.Hypermap.Coloring

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

class IsMinimalCounterExample {α : Type u} [Fintype α]
  [DecidableEq α] (H : Hypermap α) : Prop
  extends H.PlanarBridgelessPlainPrecubic where
  non_colorable : ¬H.fourColorable
  minimal {α' : Type u} [Fintype α'] [DecidableEq α']
    {H' : Hypermap α'} : H'.PlanarBridgelessPlainPrecubic →
    Fintype.card α' < Fintype.card α → H'.fourColorable

theorem MinimalCounterExample.cubic (Hm : H.IsMinimalCounterExample) :
  H.cubic := by{
  have Hc := Hm.precubic
  have Hb := Hm.bridgeless
  have Hp := Hm.plain
  have Hb' := Hb.node_period_ge_two
  simp only [cubic_def]
  simp only [precubic_def] at Hc
  have Hbc : ∀x, minimalPeriod H.node x = 2 ∨ minimalPeriod H.node x = 3 := by{
    intro x
    specialize Hb' x
    specialize Hc x
    omega
  }
  intro x
  specialize Hbc x
  apply Hbc.resolve_left
  clear Hbc
  intro Hbc
  rw[minimalPeriod_eq_two_iff] at Hbc
  rcases Hbc with ⟨hn2, hn1⟩
  let H1 := H.WalkupE x
  let H2 := H1.WalkupE ⟨node x, hn1⟩
  have H2p : H2.planar := by{
    apply planar_walkupe_planar
    apply planar_walkupe_planar
    exact Hm.planar
  }
  have H2c : H2.precubic := by{
    apply walkupe_precubic_of_precubic
    apply walkupe_precubic_of_precubic
    exact Hm.precubic
  }
  have H2p' : H2.plain := by{
    apply walkupe2_plain_of_plain_of_node_period_two <;> assumption
  }
  have H2b : H2.bridgeless := by{
    apply walkupe2_bridgeless_of_bridgeless_of_plain_of_node_period_two <;> assumption
  }
  have H2c' := Hm.minimal (H' := H2) ⟨⟨⟨H2p, H2b⟩, H2p'⟩, H2c⟩ (by{
    simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique]
    rw[Nat.sub_sub]
    apply Nat.sub_lt ?_ (by{simp})
    rw[Fintype.card_pos_iff]
    apply Nonempty.intro x
  })
  have ⟨k2, hk2f, hk2e⟩:=H2c'
  have hcf'' := isColoring.cface_invariant ⟨hk2f, hk2e⟩
  apply Hm.non_colorable
  let k : α → FourColor := fun y =>
    if hz : ∃z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface y z then
      k2 (Classical.choose hz)
    else
      FourColor.ofBits false (y == x)
  use k
  unfold isColoring
  have hf_iff : face x = x ↔ face (node x) = node x := by{
    rw[plain_iff_edge_edge] at Hp
    constructor
    · {
      intro hfx
      have h0 := H.nfe_cancel (H.edge x)
      rw[(Hp x).left, hfx] at h0
      nth_rw 1 [h0]
      apply H.node_injective
      rw[hn2, nfe_cancel]
    }
    · {
      intro hfnx
      have h0 := H.nfe_cancel (H.edge (H.node x))
      rw[(Hp (node x)).left, hfnx, hn2] at h0
      nth_rw 1 [h0, fen_cancel]
    }
  }
  have hfe_iff : edge x = node x ↔ face x = x := by{
    rw[Hp.edge_eq_eq_eq_edge, ← faceinv_apply, eq_faceinv_iff_face_eq]
  }
  have hfen : H.cface (edge x) (node x) := by{
    apply ReflTransGen.single
    change _ = _
    apply H.node_injective
    rw[nfe_cancel, hn2]
  }
  have hfen' : H.cface x (edge (node x)) := by{
    apply H.cface_equivalence.symm
    apply ReflTransGen.single
    exact fen_cancel _
  }
  have h'fn : ¬H.cface x (node x) := by{
    rw[H.cface_equivalence.comm]
    specialize Hb (node x)
    contrapose Hb
    apply Hb.trans
    exact hfen'
  }
  have h'fn' : face x ≠ node x := by{
    contrapose h'fn
    rw[← h'fn]
    apply funReflTransGen.single
  }
  have h'fn'' : face (node x) ≠ x := by{
    contrapose h'fn
    apply cface_equivalence.symm
    rw[← cface_face, h'fn]
    apply ReflTransGen.refl
  }
  have hcf : ∀ (x : α), k (face x) = k x := by{
    intro a
    unfold k
    simp only [H.cface_face]
    congr 1
    ext hb
    push_neg at hb
    have ha : a = x ∨ a = node x := by{
      by_contra ha
      push_neg at ha
      specialize hb ⟨⟨a, ha.left⟩, by{simp[ha.right]}⟩
      apply hb
      simp only
      apply ReflTransGen.refl
    }
    have hfa : face a = x ∨ face a = node x := by{
      by_contra hfa
      push_neg at hfa
      specialize hb ⟨⟨face a, hfa.left⟩, by{simp[hfa.right]}⟩
      apply hb
      simp only
      apply funReflTransGen.single
    }
    have ha' : face a = a := by{
      have ha' := ha
      rcases ha' with ha' | ha'
      · {
        apply (Or.resolve_right · (by{rwa[ha']})) at hfa
        rw[hfa, ha']
      }
      · {
        apply (Or.resolve_left · (by{rwa[ha']})) at hfa
        rw[hfa, ha']
      }
    }
    rw[ha']
  }
  have hcf' := isColoring.cface_invariant' hcf
  constructor
  · {
    intro a
    rcases em (a = x ∨ a = node x) with ha | ha
    · {
      have hna : node (node a) = a := by{
        rcases ha with ha | ha <;> simp[ha, hn2]
      }
      have hfna : face (node a) ≠ a := by{
        rcases ha with ha | ha <;> simpa[ha, hn2]
      }
      unfold k
      rcases eq_or_ne (face a) a with hfa | hfa
      · {
        have hfa' : edge a = node a := by{
          rwa[Hp.edge_eq_eq_eq_edge, ← faceinv_apply, eq_faceinv_iff_face_eq]
        }
        have hfa'' : face (node a) = node a := by{
          nth_rw 1 [← hfa']
          rw[← H.node_inj, nfe_cancel, hna]
        }
        have hz0 : ¬∃ z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface a z := by{
          intro ⟨z, hz⟩
          rw[cface, funReflTransGen_iff_iterate] at hz
          rcases hz with ⟨n, hn⟩
          rw[IsFixedPt.iterate hfa] at hn
          rcases ha with ha | ha
          · have hz := z.val.prop; simp[← hn, ha] at hz
          · have hz := z.prop; simp[Subtype.ext_iff,  ← hn, ha] at hz
        }
        have hz1 : ¬∃ z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface (edge a) z := by{
          intro ⟨z, hz⟩
          rw[cface, funReflTransGen_iff_iterate] at hz
          rcases hz with ⟨n, hn⟩
          rw[hfa', IsFixedPt.iterate hfa''] at hn
          rcases ha with ha | ha
          · have hz := z.prop; simp[Subtype.ext_iff,  ← hn, ha] at hz
          · have hz := z.val.prop; simp[← hn, ha, hn2] at hz
        }
        have hfx : face x = x :=by{
          rcases ha with ha | ha
          · exact ha ▸ hfa
          · rw[ha, hn2] at hfa''; exact hfa''
        }
        rw[dif_neg hz0, dif_neg hz1, FourColor.ofBits_injective.ne_iff]
        simp only [ne_eq, beq_eq_beq]
        rcases ha with ha | ha
        · simp[ha, Hp.edge_ne]
        · simp only [ha, hn1, iff_false, not_not]; rw[← H.face_inj, fen_cancel, hfx]
      }
      have hfx' : face x ≠ x ∧ face (node x) ≠ node x := by{
        rcases ha with ha | ha <;> simp only [ha] at hfa
        · apply And.intro hfa
          rw[← H.node_injective.ne_iff, hn2, ← edgeinv_apply]
          rw[ne_eq, edgeinv_eq_iff_eq_edge, ← H.edge_inj, Hp.edge_edge, ← H.face_inj, fen_cancel]
          exact hfa.symm
        · refine And.intro ?_ hfa
          rwa[ne_eq, hf_iff]
      }
      have hfx'' : edge x ≠ node x := by{
        rw[ne_eq, hfe_iff]
        exact hfx'.left
      }
      have hfa' : face a ≠ x ∧ face a ≠ node x := by{
        rcases ha with ha | ha <;> simpa[ha, hfx']
      }
      have hfa'' : edge a ≠ x ∧ edge a ≠ node x := by{
        rcases ha with ha | ha
        · simpa[ha, Hp.edge_ne]
        rw[ha, ← H.face_injective.ne_iff, fen_cancel]
        apply And.intro hfx'.1.symm
        rw[← H.face_injective.ne_iff, fen_cancel]
        exact h'fn''.symm
      }
      have hfa''' : H.faceinv a ≠ x ∧ H.faceinv a ≠ node x := by{
        simp only [ne_eq, faceinv_eq_iff_eq_face]
        rcases ha with ha | ha
        · simp[ha, hfx'.1.symm, h'fn''.symm]
        · simp[ha, h'fn'.symm, hfx'.2.symm]
      }
      let a' : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩} :=
        ⟨⟨H.faceinv a, hfa'''.1⟩, by{simp[hfa'''.2]}⟩
      let ea' : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩} := ⟨⟨edge a, hfa''.1⟩, by{simp[hfa''.2]}⟩
      have hz0 : ∃z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface a z := by{
        use a'
        apply H.cface_equivalence.symm
        apply ReflTransGen.single
        simp only[fromFun, a', faceinv_rightinv]
      }
      have hz1 : ∃z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface (edge a) z := by{
        use ea'
        apply ReflTransGen.refl
      }
      rw[dif_pos hz0, dif_pos hz1]
      have hz0_spec := Classical.choose_spec hz0
      have hz1_spec := Classical.choose_spec hz1
      have hz0_spec' : H.cface (H.faceinv a) _ := by{
        apply funReflTransGen.head (b:=face (H.faceinv a)) rfl
        · rw[faceinv_rightinv]
          exact hz0_spec
      }
      change H.cface a' _ at hz0_spec'
      change H.cface ea' _ at hz1_spec
      rw[← walkupe_cface, ← walkupe_cface] at hz0_spec' hz1_spec
      have hcf''0 := hcf'' _ _ hz0_spec'
      have hcf''1 := hcf'' _ _ hz1_spec
      rw[← hcf''0, ← hcf''1]
      have ih : ea' = ((H.WalkupE x).WalkupE ⟨_, hn1⟩).edge a' := by{
        unfold ea' a'
        simp only [faceinv_apply]
        rcases ha with ha | ha
        · simp only [ha]
          rw[walkupe2_edge_val_edge_node_of_plain_of_node_period_two' Hp hn1 hn2 rfl]
        · simp only [ha, hn2]
          rw[walkupe2_edge_val_edge_of_plain_of_node_period_two' Hp hn1 hn2 rfl]
      }
      rw[ih]
      apply hk2f
    }
    push_neg at ha
    let a' : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩} := ⟨⟨a, ha.1⟩, by{simp[ha.2]}⟩
    have hz0 : ∃ z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface a ↑↑z :=
      ⟨a', by{simp[cface, funReflTransGen]; rfl}⟩
    rcases em (a = edge x ∨ a = edge (node x)) with hea | hea
    · {
      have hfx' : face x ≠ x ∧ face (node x) ≠ node x := by{
        rw[ne_eq, ne_eq, ← hf_iff, and_self]
        intro hfx'
        have hfx'' := hf_iff.mp hfx'
        rw[← faceinv_apply, eq_faceinv_iff_face_eq] at hea
        nth_rw 2 [← hfx'] at hea
        rw[H.face_inj] at hea
        apply (Or.resolve_right · ha.1) at hea
        rw[← H.node_inj, ← H.edge_inj, enf_cancel, hn2, ← hea] at hfx''
        exact ha.2 hfx''.symm
      }
      have hfea : H.faceinv (edge a) ≠ x ∧ H.faceinv (edge a) ≠ node x := by{
        rcases hea with hea | hea
        · simp[hea, Hp.edge_edge, faceinv_eq_iff_eq_face, hfx'.1.symm, h'fn''.symm]
        · simp[faceinv_eq_iff_eq_face, hea, Hp.edge_edge, hfx'.2.symm, h'fn'.symm]
      }
      let ea' : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩} :=
        ⟨⟨H.faceinv (edge a), hfea.1⟩, by{simp[hfea.2]}⟩
      unfold k
      have hz1 : ∃ z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface (edge a) ↑↑z := by{
        use ea'
        apply H.cface_equivalence.symm
        apply ReflTransGen.single
        simp[ea', fromFun, faceinv_rightinv]
      }
      rw[dif_pos hz0, dif_pos hz1]
      have hz0_spec := Classical.choose_spec hz0
      have hz1_spec := Classical.choose_spec hz1
      have hz1_spec' : H.cface (H.faceinv (edge a)) _ := by{
        apply funReflTransGen.head rfl
        · rw[faceinv_rightinv]
          exact hz1_spec
      }
      change H.cface a' _ at hz0_spec
      change H.cface ea' _ at hz1_spec'
      simp only [← walkupe_cface] at hz0_spec hz1_spec'
      have hcf''0 := hcf'' _ _ hz0_spec
      have hcf''1 := hcf'' _ _ hz1_spec'
      rw[← hcf''0, ← hcf''1]
      have ih : ea' = ((H.WalkupE x).WalkupE ⟨_, hn1⟩).edge a' := by{
        unfold ea' a'
        simp only [faceinv_apply]
        rcases hea with hea | hea
        · simp only [hea, Hp.edge_edge]
          rw[walkupe2_edge_val_edge_of_plain_of_node_period_two' Hp hn1 hn2 rfl]
        · simp only [hea, Hp.edge_edge, hn2]
          rw[walkupe2_edge_val_edge_node_of_plain_of_node_period_two' Hp hn1 hn2 rfl]
      }
      rw[ih]
      apply hk2f
    }
    push_neg at hea
    unfold k
    have h0 :=
      H.walkupe2_edge_val_of_plain_of_node_period_two Hp hn1 hn2 (a:=⟨⟨a, ha.1⟩, by{simp[ha.2]}⟩)
      hea.1 hea.2
    simp only at h0
    have hz1 : ∃ z : {a : {a // a ≠ x} // a ≠ ⟨node x, hn1⟩}, H.cface (edge a) ↑↑z :=
      ⟨((H.WalkupE x).WalkupE ⟨_, hn1⟩).edge ⟨⟨a, ha.1⟩, by{simp[ha.2]}⟩,
        by{simp[h0, cface, funReflTransGen]; rfl}⟩
    rw[dif_pos hz0, dif_pos hz1]
    have hz0_spec := Classical.choose_spec hz0
    have hz1_spec := Classical.choose_spec hz1
    have hcf''0 := hcf'' ⟨⟨a, ha.1⟩, by{simp[ha.2]}⟩ (Classical.choose hz0)
      (by{simpa[H1, H2, walkupe_cface]})
    have hcf''1 := hcf'' (((H.WalkupE x).WalkupE ⟨_, hn1⟩).edge ⟨⟨a, ha.1⟩, by{simp[ha.2]}⟩)
      (Classical.choose hz1) (by{simpa[H1, H2, walkupe_cface, h0]})
    rw[← hcf''0, ← hcf''1]
    apply hk2f
  }
  · exact hcf
}

end Hypermap
