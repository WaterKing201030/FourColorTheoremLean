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

structure PlanarBridgeless : Prop where
  planar : H.planar
  bridgeless : H.bridgeless
structure PlainCubic : Prop where
  plain : H.plain
  cubic : H.cubic
structure PlainCubicConnected : Prop extends H.PlainCubic where
  connected : H.connected
structure PlanarPlainCubicConnected : Prop extends H.PlainCubicConnected where
  planar : H.planar
structure PlainCubicPentagonal : Prop extends H.PlainCubic where
  pentagonal : H.pentagonal
structure PlanarBridgelessPlain : Prop extends H.PlanarBridgeless where
  plain : H.plain
structure PlanarBridgelessPlainConnected : Prop extends H.PlanarBridgelessPlain where
  connected : H.connected
structure PlanarBridgelessPlainPrecubic : Prop extends H.PlanarBridgelessPlain where
  precubic : H.precubic

theorem walkupe2_bridgeless_of_bridgeless_of_plain_of_node_period_two
  (Hb : H.bridgeless) (Hp : H.plain) {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).bridgeless := by{
  rw[bridgeless] at Hb
  rw[bridgeless]
  intro ⟨⟨y, hyx⟩, hynx⟩
  simp only [ne_eq, Subtype.mk.injEq] at hynx
  simp only [walkupe_cface]
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge ⟨y, hyx⟩) ≠ ⟨node x, hnx⟩ := by{
    rw[← comp_apply (f:=(H.WalkupE x).face) (g:=(H.WalkupE x).edge), ← nodeinv_eq, ne_eq,
    nodeinv_eq_iff_eq_node, walkupe_node, Subtype.ext_iff, skip_val, skip']
    simp[hn2x, hynx]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ := by{
    simp[walkupe_node, Subtype.ext_iff, skip_val, skip', hn2x]
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

theorem walkupe2_planarBridgelessPlainPrecubic_of_planarBridgelessPlainPrecubic
  (Hh : H.PlanarBridgelessPlainPrecubic) {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).PlanarBridgelessPlainPrecubic := by{
    have Hc := Hh.precubic
    have Hb := Hh.bridgeless
    have Hp := Hh.plain
    have Hb' := Hb.node_period_ge_two
    simp only [precubic_def] at Hc
    let H1 := H.WalkupE x
    let H2 := H1.WalkupE ⟨node x, hnx⟩
    have H2p : H2.planar := by{
      apply planar_walkupe_planar
      apply planar_walkupe_planar
      exact Hh.planar
    }
    have H2c : H2.precubic := by{
      apply walkupe_precubic_of_precubic
      apply walkupe_precubic_of_precubic
      exact Hh.precubic
    }
    have H2p' : H2.plain := by{
      apply walkupe2_plain_of_plain_of_node_period_two <;> assumption
    }
    have H2b : H2.bridgeless := by{
      apply walkupe2_bridgeless_of_bridgeless_of_plain_of_node_period_two <;> assumption
    }
    exact ⟨⟨⟨H2p, H2b⟩, H2p'⟩, H2c⟩
  }

end Hypermap
