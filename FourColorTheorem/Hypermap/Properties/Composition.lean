import FourColorTheorem.Hypermap.Properties.Planar
import FourColorTheorem.Hypermap.Properties.BridgeLoop
import FourColorTheorem.Hypermap.Properties.Plain
import FourColorTheorem.Hypermap.Properties.Cubic
import FourColorTheorem.Hypermap.Properties.Pentagonal

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

structure PlanarBridgeless (H : Hypermap α) : Prop
  extends H.Planar, H.Bridgeless where
structure PlanarBridgelessPlain (H : Hypermap α) : Prop
  extends H.PlanarBridgeless, H.Plain where
structure PlanarBridgelessPlainPrecubic (H : Hypermap α) : Prop
  extends H.PlanarBridgelessPlain, H.Precubic where

theorem concatedge_bridgeless_of_bridgeless_of_plain_of_subdiv
  (Hb : H.Bridgeless) (Hp : H.Plain) {x : α} (hxv : H.isSubdivVertice x)
  : ((H.WalkupE x).WalkupE ⟨_, hxv.node_ne⟩).Bridgeless := by{
  rw[bridgeless_def] at Hb
  rw[bridgeless_def]
  intro ⟨⟨y, hyx⟩, hynx⟩
  simp only [ne_eq, Subtype.mk.injEq] at hynx
  simp only [walkupe_cface]
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge ⟨y, hyx⟩) ≠ ⟨node x, hxv.node_ne⟩ := by{
    rw[← comp_apply (f:=(H.WalkupE x).face) (g:=(H.WalkupE x).edge), ← nodeinv_eq, ne_eq,
    nodeinv_eq_iff_eq_node, walkupe_node, Subtype.ext_iff, skip_val, skip']
    simp[hxv.node_2, hynx]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hxv.node_ne⟩ = ⟨node x, hxv.node_ne⟩ := by{
    simp[walkupe_node, Subtype.ext_iff, skip_val, skip', hxv.node_2]
  }
  simp only
  rw[if_neg h0, h1]
  have hynx' : face (edge y) ≠ x := by{
    contrapose hynx
    rw[← hynx, nfe_cancel]
  }
  rw[plain_iff_edge_edge] at Hp
  simp only [walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge'', apply_ite Subtype.val,
  fen_cancel, ↓reduceIte, hynx', Hp]
  rcases eq_or_ne (edge x) (node x) with hexnx | hexnx
  · {
    rw[if_pos hexnx]
    rcases ne_or_eq (edge y) x with heyx | heyx
    · rw[if_neg heyx]; apply Hb
    simp only [heyx, ↓reduceIte]
    specialize Hb y
    contrapose Hb
    rw[heyx]
    apply Hb.trans
    apply ReflTransGen.single
    rw[fromFun, fen_cancel]
  }
  · {
    rw[if_neg hexnx]
    rcases eq_or_ne (edge y) x with heyx | heyx
    · {
      simp only [heyx, ↓reduceIte, Hp]
      specialize Hb y
      contrapose Hb
      rw[heyx]
      apply Hb.trans
      apply ReflTransGen.single
      rw[fromFun, fen_cancel]
    }
    rw[if_neg heyx]
    rcases ne_or_eq (edge y) (node x) with heynx | heynx
    · rw[if_neg heynx]; apply Hb
    rw[if_pos heynx]
    specialize Hb x
    contrapose Hb
    apply cface_equivalence.trans ?_ Hb
    apply cface_equivalence.symm
    apply congrArg edge at heynx
    simp only [Hp] at heynx
    rw[heynx]
    apply ReflTransGen.single
    rw[fromFun, fen_cancel]
  }
}

theorem PlanarBridgelessPlainPrecubic.concatEdge
  (Hh : H.PlanarBridgelessPlainPrecubic) {x : α} (hxv : H.isSubdivVertice x)
  : ((H.WalkupE x).WalkupE ⟨_, hxv.node_ne⟩).PlanarBridgelessPlainPrecubic := by{
    have Hc := Hh.toPrecubic
    have Hb := Hh.toBridgeless
    have Hp := Hh.toPlain
    have Hb' := Hb.node_period_ge_two
    simp only [precubic_def] at Hc
    let H1 := H.WalkupE x
    let H2 := H1.WalkupE ⟨node x, hxv.node_ne⟩
    have H2p : H2.Planar := by{
      apply Planar.walkupe
      apply Planar.walkupe
      exact Hh.toPlanar
    }
    have H2c : H2.Precubic := by{
      apply Precubic.walkupe
      apply Precubic.walkupe
      exact Hh.toPrecubic
    }
    have H2p' : H2.Plain := by{
      apply Plain.concat_edge <;> assumption
    }
    have H2b : H2.Bridgeless := by{
      apply concatedge_bridgeless_of_bridgeless_of_plain_of_subdiv <;> assumption
    }
    refine ⟨⟨⟨H2p, H2b⟩, H2p'⟩, H2c⟩
  }

end Hypermap
