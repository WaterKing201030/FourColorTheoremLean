import FourColorTheorem.Discretize.GridHypermap.GMDart
import FourColorTheorem.Hypermap.Properties.Plain.Basic

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

def GMInner (hgp : GridMapProper ab0 cm0) : Set hgp.GMDart :=
  {u | u.val.half ∈ hgp.extendBBox}
theorem mem_GMInner_iff {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
: u ∈ hgp.GMInner ↔ u.val.half ∈ hgp.extendBBox := by{
  unfold GMInner
  rw[Set.mem_setOf]
}
theorem mem_GMInner_iff' {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
: u ∈ hgp.GMInner ↔ u.val ∈ (hgp.extendBBox).zoom := by{
  rw[GRectangle.mem_zoom, mem_GMInner_iff]
}
theorem GMnode_val_of_mem_GMInner {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
(hu : u ∈ hgp.GMInner)
  : (GMnode u).val = edge (node u) := by{
    rw[GMnode]
    simp only
    rw[List.find?_cons_of_pos, Option.getD_some]
    simp only [decide_eq_true_eq]
    rw[← face_3]
    rw[mem_GMGrid_iff]
    simp only [face_half]
    exact Or.inl hu
  }
theorem GMnode_inner_closed {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
(hu : u ∈ hgp.GMInner) : GMnode u ∈ hgp.GMInner := by{
  rw[mem_GMInner_iff, GMnode_val_of_mem_GMInner hu, ←face_3]
  simp only [face_half]
  exact hu
}
theorem funReflTransGen_GMnode_inner_closed {hgp : GridMapProper ab0 cm0} {u0 u1 : hgp.GMDart}
  (hu01 : funReflTransGen GMnode u0 u1) (hu0 : u0 ∈ hgp.GMInner) : u1 ∈ hgp.GMInner := by{
    induction hu01 with
    | refl => exact hu0
    | tail hh ht ih => rw[fromFun] at ht; rw[← ht]; exact GMnode_inner_closed ih
  }
theorem funReflTransGen_GMnode_inner_closed_iff {hgp : GridMapProper ab0 cm0}
{u0 u1 : hgp.GMDart}
  (hu01 : funReflTransGen GMnode u0 u1) : u0 ∈ hgp.GMInner ↔ u1 ∈ hgp.GMInner := by{
    constructor
    · apply funReflTransGen_GMnode_inner_closed; exact hu01
    · apply funReflTransGen_GMnode_inner_closed
      apply hgp.GMDartHypermap.cnode_Symm.symm
      exact hu01
  }
theorem GMface_end0 {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
: end0 (GMface u) = end0 u := by{
  match u with | ⟨d, hd⟩ => {
    rcases em (node (node (node d)) ∈ hgp.GMGrid) with h2f | h2f
    · {
      have h2f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = node (node (node d))
        := List.find?_cons_of_pos (decide_eq_true h2f)
      simp only [GMface, h2f', Option.getD_some, node_end0]
    }
    rcases em (node (node d) ∈ hgp.GMGrid) with h1f | h1f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = node (node d)
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_pos]; simp[h1f]
        · simp[h2f]
      }
      simp only [GMface, h1f', Option.getD_some, node_end0]
    }
    rcases em (node d ∈ hgp.GMGrid) with h0f | h0f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = node d
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_pos]; simp[h0f]
          · simp[h1f]
        · simp[h2f]
      }
      simp only [GMface, h1f', Option.getD_some, node_end0]
    }
    have h0n : edge (node d) ∉ hgp.GMGrid := by{
      rw[edge_mem_GMGrid_iff]
      exact h0f
    }
    simp only [←face_3, mem_GMGrid_iff, face_half, not_or] at h0n
    rw[node_3, mem_GMGrid_iff, face_half, not_or] at h2f
    rw[mem_GMGrid_iff] at hd
    exfalso
    apply hd.elim h0n.left h2f.left
  }
}
theorem GMedge_inner_cases {hgp : GridMapProper ab0 cm0} {u : hgp.GMDart}
: u ∈ hgp.GMInner ∨ GMedge u ∈ hgp.GMInner := by{
  simp only [hgp.mem_GMInner_iff, GMedge]
  have hu := u.prop
  rw[hgp.mem_GMGrid_iff] at hu
  exact hu
}

abbrev GMInnerDart (hgp : GridMapProper ab0 cm0) := {u // u ∈ hgp.GMInner}
abbrev GMOuterDart (hgp : GridMapProper ab0 cm0) := {u // u ∉ hgp.GMInner}
@[inline] noncomputable instance instFintypeGMInnerDart {hgp : GridMapProper ab0 cm0}
: Fintype hgp.GMInnerDart := by{
  classical
  apply Subtype.fintype
}
@[inline] noncomputable instance instFintypeGMOuterDart {hgp : GridMapProper ab0 cm0}
: Fintype hgp.GMOuterDart := by{
  classical
  apply Subtype.fintype
}

noncomputable instance GMDart_equiv_GMInnerDart_sum_GMOuterDart {hgp : GridMapProper ab0 cm0} :
  hgp.GMDart ≃ hgp.GMInnerDart ⊕ hgp.GMOuterDart :=
  Equiv.subtype_em (α := hgp.GMDart) (P := (· ∈ hgp.GMInner))

theorem GMInnerDart_card {hgp : GridMapProper ab0 cm0}
  : Fintype.card hgp.GMInnerDart = hgp.extendBBox.area * 4 := by{
  rw[← GRectangle.area_zoom, ← GRectangle.enum_length,
  ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
  apply Fintype.card_congr
  let f : hgp.GMInnerDart → { x // x ∈ hgp.extendBBox.zoom.enum } :=
    fun ⟨⟨d, hd⟩, hu⟩ => ⟨d, by{
      simp only [mem_GMInner_iff] at hu
      simp only [GRectangle.mem_enum_iff, GRectangle.mem_zoom]
      exact hu
    }⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro u1 u2 hu
    match u1, u2 with
    | ⟨⟨d1, hd1⟩, hu1⟩, ⟨⟨d2, hd2⟩, hu2⟩ => {
      unfold f at hu
      simp at hu
      simp[hu]
    }
  }
  · {
    intro ⟨d, hd⟩
    rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom] at hd
    use ⟨⟨d, by{simp[mem_GMGrid_iff, hd]}⟩, by{simp[mem_GMInner_iff, hd]}⟩
  }
}

theorem GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner {hgp : GridMapProper ab0 cm0}
  {u : hgp.GMDart} (hu : u ∈ hgp.GMInner)
  : ((hgp.GMDartHypermap).nodeinv u).val = face u.val := by{
    nth_rw 2 [← Hypermap.nodeinv_rightinv (H:=hgp.GMDartHypermap) u]
    change _ = face (hgp.GMnode _)
    have hu' : (hgp.GMDartHypermap).nodeinv u ∈ hgp.GMInner := by{
      apply funReflTransGen_GMnode_inner_closed ?_ hu
      apply (hgp.GMDartHypermap).cnode_equivalence.symm
      apply ReflTransGen.single
      rw[fromFun, (hgp.GMDartHypermap).nodeinv_rightinv]
    }
    rw[hgp.GMnode_val_of_mem_GMInner hu', fen_cancel]
  }
theorem GMDartHypermap_node_val_eq_en_of_mem_GMInner {hgp : GridMapProper ab0 cm0}
  {u : hgp.GMDart} (hu : u ∈ hgp.GMInner)
  : (hgp.GMDartHypermap.node u).val = edge (node u.val) := by{
    change (GMnode _).val = _
    rw[GMnode_val_of_mem_GMInner hu]
  }
theorem GMDartHypermap_faceinv_val_eq_node_of_mem_GMInner {hgp : GridMapProper ab0 cm0}
  {u : hgp.GMDart} (hu : u ∈ hgp.GMInner)
  : (hgp.GMDartHypermap.faceinv u).val = node u.val := by{
    rw[Hypermap.faceinv_eq, comp_apply, GMDartHypermap_edge_val_eq,
    GMDartHypermap_node_val_eq_en_of_mem_GMInner hu, edge_2]
  }

end GridMapProper
end GridPlane
