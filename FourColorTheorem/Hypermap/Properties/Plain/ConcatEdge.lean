import FourColorTheorem.Hypermap.Properties.Plain.Basic
import FourColorTheorem.Hypermap.Actions.Walkup.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

lemma walkupe_node_self_of_node_period_two {x : α} (hnx : node x ≠ x)
  (hn2x : node (node x) = x)
  : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ := by{
  simp[walkupe_node, Subtype.ext_iff, skip_val, skip', hn2x]
}
lemma walkupe_face_edge_self_of_node_period_two {x : α} (hnx : node x ≠ x)
  (hn2x : node (node x) = x)
  : (H.WalkupE x).face ((H.WalkupE x).edge ⟨node x, hnx⟩) = ⟨node x, hnx⟩ := by{
  rw[← comp_apply (f:=(H.WalkupE x).face), ← nodeinv_eq, nodeinv_eq_iff_eq_node]
  rw[walkupe_node_self_of_node_period_two hnx hn2x]
}
lemma walkupe2_edge_val_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x)
  (hane : a ≠ edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = H.edge a := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true] at h1nx
    rcases eq_or_ne (edge x) x with hex | hex
    · rw[if_pos hex]
    rw[if_neg hex]
    rw[if_neg hex] at h1nx
    rw[← comp_apply (f:=face), ← nodeinv_eq]
    simp only [H.nodeinv_eq_iff_eq_node, if_neg hanx]
    rw[apply_ite (· = _), edge_inj, edge_inj]
    simp only [ne_eq, if_true_right, Ne.symm hanx]
    rw[← H.edge_injective.eq_iff]
    simp[Hp, h1nx, hanx]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  have haex' : edge a.val.val ≠ x := by{
    contrapose hae
    apply H.edge_injective
    simp[hae, Hp]
  }
  have hanex' : edge a.val.val ≠ node x := by{
    contrapose hane
    apply H.edge_injective
    simp[hane, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val ≠ ⟨node x, hnx⟩ := by{
    simp[Subtype.ext_iff, walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx', haex', hanex']
  }
  rw[if_neg h2]
  simp only [walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx', if_false, haex']
}
lemma walkupe2_edge_val_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x)
  (hane : a ≠ edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = ⟨⟨H.edge a, by{
    apply H.edge_injective.ne_iff.mp
    rw[plain_iff_edge_edge] at Hp
    simp[Hp, hae]
  }⟩, by{
    simp only [ne_eq, Subtype.ext_iff]
    rw[← H.edge_injective.eq_iff]
    rw[plain_iff_edge_edge] at Hp
    simpa[Hp]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_of_plain_of_node_period_two Hp hnx hn2x hae hane]
}
lemma walkupe2_edge_val_edge_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a = edge x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = edge (node x) := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true, Hp, if_false] at h1nx
    simp only[Hp, if_false, hanx']
    simp only[hae, Hp, if_true]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have haex' : edge a.val.val = x := by{
    apply H.edge_injective
    simp[hae, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val ≠ ⟨node x, hnx⟩ := by{
    simp[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge'', Hp, hanx']
    simp[haex', Hp]
  }
  rw[if_neg h2]
  simp[walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx']
  simp[haex']
}
lemma walkupe2_edge_val_edge_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a = edge x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a =
  ⟨⟨edge (node x), by{
    rw[plain_iff_edge_edge] at Hp
    apply H.edge_injective.ne_iff.mp
    have ha := a.prop
    simp[Subtype.ext_iff, hae] at ha
    simp[Hp, Ne.symm ha]
  }⟩, by{
    rw[plain_iff_edge_edge] at Hp
    simp[Subtype.ext_iff, Hp]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_edge_of_plain_of_node_period_two Hp hnx hn2x hae]
}
lemma walkupe2_edge_val_edge_node_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (haen : a = edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = edge x := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true, Hp, if_false] at h1nx
    simp only[Hp, if_false, hanx']
    simp only[haen, Hp, hnx, if_false, h1nx]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have haenx' : edge a.val.val = node x := by{
    apply H.edge_injective
    simp[haen, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val = ⟨node x, hnx⟩ := by{
    simp[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge'', Hp, hanx']
    simp[haenx', hnx]
  }
  rw[if_pos h2]
  simp[walkupe_edge, skip_edge'_val, skip_edge'', Hp, fen_cancel]
}
lemma walkupe2_edge_val_edge_node_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (haen : a = edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a =
  ⟨⟨edge x, by{
    rw[plain_iff_edge_edge] at Hp
    simp[Hp]
  }⟩, by{
    rw[plain_iff_edge_edge] at Hp
    simp only [ne_eq, Subtype.ext_iff]
    apply H.edge_injective.ne_iff.mp
    have ha := a.val.prop
    simp[haen] at ha
    simp[Hp, Ne.symm ha]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_edge_node_of_plain_of_node_period_two Hp hnx hn2x haen]
}
lemma walkupe2_cedge_closure (Hp : H.plain)
  {x : α}
  {a b : α} (ha : a ≠ x) (han : a ≠ node x) (hae : a ≠ edge x) (haen : a ≠ edge (node x))
  (hab : H.cedge a b) :
  b ≠ x ∧ b ≠ node x ∧ b ≠ edge x ∧ b ≠ edge (node x) := by{
  rw[Hp.cedge_cases_iff] at hab
  rcases hab with hab | hab
  · simp[← hab, ha, han, hae, haen]
  simp[← hab, Hp.edge_eq_eq_eq_edge, Hp.edge_edge, ha, han, hae, haen]
}

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

end Hypermap
