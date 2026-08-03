import FourColorTheorem.Hypermap.Actions.Walkup.Skip

namespace Hypermap
variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

section cubic
theorem walkupe_precubic_of_precubic (Hc : H.precubic) (x : α) : (H.WalkupE x).precubic := by{
  rw[precubic_def] at *
  intro x'
  have Hc' := Hc x'.val
  apply le_trans ?_ Hc'
  apply Finite.skip_minimalPeriod_le
}
end cubic

section plain
theorem walkupe2_plain_of_plain_of_node_period_two (Hp : H.plain) {x : α}
  (hnx : node x ≠ x) (hn2x : node (node x) = x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).plain := by{
  rw[plain_iff_edge_edge]
  intro a
  have Hp' := Hp
  rw[plain_iff_edge_edge] at Hp
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  simp only [Subtype.ext_iff, ne_eq]
  rcases eq_or_ne a.val.val (edge x) with haex | haex
  · {
    rw[walkupe2_edge_val_edge_of_plain_of_node_period_two Hp' hnx hn2x haex]
    constructor
    · {
      rw[walkupe2_edge_val_edge_of_plain_of_node_period_two' Hp' hnx hn2x haex]
      rw[walkupe2_edge_val_edge_node_of_plain_of_node_period_two Hp' hnx hn2x, haex]
      rfl
    }
    · rwa[haex, H.edge_inj]
  }
  rcases eq_or_ne a.val.val (edge (node x)) with haenx | haenx
  · {
    rw[walkupe2_edge_val_edge_node_of_plain_of_node_period_two' Hp' hnx hn2x haenx]
    constructor
    · {
      rw[walkupe2_edge_val_edge_of_plain_of_node_period_two Hp' hnx hn2x, haenx]
      rfl
    }
    · {
      simp only
      exact haex.symm
    }
  }
  simp only [walkupe2_edge_val_of_plain_of_node_period_two Hp' hnx hn2x haex haenx, ne_eq, Hp,
    not_false_eq_true, and_true]
  rw[walkupe2_edge_val_of_plain_of_node_period_two' Hp' hnx hn2x haex,
  walkupe2_edge_val_of_plain_of_node_period_two' Hp' hnx hn2x]
  · simp[Hp]
  · simp[edge_inj, hax]
  · simp[edge_inj, hanx]
  · simp[haenx]
}
theorem walkupe2_cedge_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a b : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x)
  (haen : a ≠ edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).cedge a b ↔ H.cedge a b := by{
  have H2p := walkupe2_plain_of_plain_of_node_period_two Hp hnx hn2x
  rw[H2p.cedge_cases_iff, Hp.cedge_cases_iff]
  apply or_congr
  · simp[Subtype.ext_iff]
  simp only [Subtype.ext_iff]
  rw[walkupe2_edge_val_of_plain_of_node_period_two Hp hnx hn2x hae haen]
}
lemma walkupe2_edge_val_ne_edge_node_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x) :
  ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a ≠ edge (node x) := by{
  have H2p := walkupe2_plain_of_plain_of_node_period_two Hp hnx hn2x
  contrapose hae
  rw[← H2p.edge_edge (p:=a)]
  rw[walkupe2_edge_val_edge_node_of_plain_of_node_period_two Hp hnx hn2x hae]
}
lemma walkupe2_edge_val_ne_edge_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (haen : a ≠ edge (node x)) :
  ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a ≠ edge x := by{
  have H2p := walkupe2_plain_of_plain_of_node_period_two Hp hnx hn2x
  contrapose haen
  rw[← H2p.edge_edge (p:=a)]
  rw[walkupe2_edge_val_edge_of_plain_of_node_period_two Hp hnx hn2x haen]
}
end plain

section bridgeless
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
end bridgeless

end Hypermap
