import FourColorTheorem.Hypermap.Actions.Walkup.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def isSubdivVertice (H : Hypermap α) (x : α) :=
  H.node (H.node x) = x ∧ H.node x ≠ x
theorem isSubdivVertice.node_2 {x : α} (hx : H.isSubdivVertice x)
  : node (node x) = x := hx.1
theorem isSubdivVertice.node_ne {x : α} (hx : H.isSubdivVertice x)
  : node x ≠ x := hx.2
theorem isSubdivVertice.node_subdiv {x : α} (hx : H.isSubdivVertice x)
  : H.isSubdivVertice (node x) := by{
  rw[isSubdivVertice, hx.node_2]
  simp[hx.node_ne.symm]
}
theorem isSubdivVertice.node_eq_eq_eq_node {x y : α} (hx : H.isSubdivVertice x)
  : node x = y ↔ x = node y := by{
  nth_rw 1 [← H.node_inj, hx.node_2]
}

lemma isSubdivVertice.walkupe_node_self {x : α} (hx : H.isSubdivVertice x)
  : (H.WalkupE x).node ⟨node x, hx.node_ne⟩ = ⟨node x, hx.node_ne⟩ := by{
  simp[walkupe_node, Subtype.ext_iff, skip_val, skip', hx.node_2]
}
lemma isSubdivVertice.walkupe_face_edge_self {x : α} (hx : H.isSubdivVertice x)
  : (H.WalkupE x).face ((H.WalkupE x).edge ⟨node x, hx.node_ne⟩) = ⟨node x, hx.node_ne⟩ := by{
  rw[← comp_apply (f:=(H.WalkupE x).face), ← nodeinv_eq, nodeinv_eq_iff_eq_node]
  rw[isSubdivVertice.walkupe_node_self hx]
}

@[reducible] def concatEdge {x : α} (hx : H.isSubdivVertice x)
  : Hypermap {a : {a // a ≠ x} // a ≠ ⟨_, hx.node_ne⟩} :=
  (H.WalkupE x).WalkupE ⟨_, hx.node_ne⟩

end Hypermap
