import FourColorTheorem.Discretize.GridHypermap.CMatte
import FourColorTheorem.Hypermap.Properties.Plain.Basic

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

noncomputable def GMGrid (hgp : GridMapProper ab0 cm0) : List GDart :=
  let inner : GRectangle := hgp.extendBBox.zoom
  inner.enum ++ inner.enum.map edge
theorem mem_GMGrid_iff {hgp : GridMapProper ab0 cm0} {d : GDart} : d ∈ hgp.GMGrid
  ↔ d.half ∈ hgp.extendBBox ∨ (edge d).half ∈ hgp.extendBBox
:= by{
  unfold GMGrid
  rw[List.mem_append]
  apply or_congr
  · rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom]
  · {
    nth_rw 1 [← edge_2 (d:=d)]
    rw[List.mem_map_of_injective edge_injective]
    rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom]
  }
}
theorem edge_mem_GMGrid_iff {hgp : GridMapProper ab0 cm0} {d : GDart}
  : edge d ∈ hgp.GMGrid ↔ d ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff, mem_GMGrid_iff, or_comm, edge_2]
}
theorem CM_subset_GMGrid {hgp : GridMapProper ab0 cm0} {i : Fin n}
: ∀{x}, x.half ∈ hgp.extendCMatte i → x ∈ hgp.GMGrid := by{
  intro x hx
  have IH := hgp.CM_subset_CMBBox (i := i)
  have IH' := @IH x.half (by{rw[Matte.mem_toRegion_iff_mem]; simp[hx]})
  rw[← GRectangle.mem_iff_toRegion] at IH'
  rw[mem_GMGrid_iff]
  simp[IH']
}

abbrev GMDart (hgp : GridMapProper ab0 cm0) := {d : GDart // d ∈ hgp.GMGrid}

def GMedge {hgp : GridMapProper ab0 cm0} : hgp.GMDart → hgp.GMDart :=
  fun ⟨d, hd⟩ => ⟨edge d, hgp.edge_mem_GMGrid_iff.mpr hd⟩
theorem GMedge_2 {hgp : GridMapProper ab0 cm0} {d : hgp.GMDart}
: hgp.GMedge (hgp.GMedge d) = d := by{
  match d with | ⟨d, hd⟩ => simp[GMedge, edge_2]
}

theorem GMDart_nonempty {hgp : GridMapProper ab0 cm0} : Nonempty hgp.GMDart := by{
  refine Nonempty.intro ⟨2 • ⟨(hgp.extendBBox).hspan.lb, (hgp.extendBBox).vspan.lb⟩, ?_⟩
  rw[mem_GMGrid_iff]
  left
  rw[GPoint.half_double]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GRectangle.hspan_lt_of_proper hgp.extendBBox_proper,
  GRectangle.vspan_lt_of_proper hgp.extendBBox_proper]
}

noncomputable def GMface {hgp : GridMapProper ab0 cm0} (u : hgp.GMDart) : hgp.GMDart :=
  let t := [node (node (node u)), node (node u), node u].find?
    (· ∈ hgp.GMGrid)
  ⟨t.getD u.val, by{
    match ht : t with
    | none => exact u.prop
    | some d => {
      have ht':=(List.find?_eq_some_iff_getElem.mp ht).left
      rw[Option.getD_some]
      rw[decide_eq_true_eq] at ht'
      exact ht'
    }
  }⟩

noncomputable def GMnode {hgp : GridMapProper ab0 cm0} (u : hgp.GMDart) : hgp.GMDart :=
  let t := [edge (node u), edge (node (node u)), edge (node (node (node u)))].find?
    (· ∈ hgp.GMGrid)
  ⟨t.getD u.val, by{
    match ht : t with
    | none => exact u.prop
    | some d => {
      have ht':=(List.find?_eq_some_iff_getElem.mp ht).left
      rw[Option.getD_some]
      rw[decide_eq_true_eq] at ht'
      exact ht'
    }
  }⟩

theorem GM_enf_cancel {hgp : GridMapProper ab0 cm0}
: ∀u : hgp.GMDart, GMedge (GMnode (GMface u)) = u := by{
  intro u
  match hu : u with | ⟨d, hd⟩ => {
    rcases em (node (node (node d)) ∈ hgp.GMGrid) with h2f | h2f
    · {
      have h2f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = node (node (node d))
        := List.find?_cons_of_pos (decide_eq_true h2f)
      simp only [GMface, h2f', Option.getD_some]
      have h2n : [edge d, edge (node d), edge (node (node d))].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = edge d := by{
          apply List.find?_cons_of_pos
          simp[edge_mem_GMGrid_iff, hd]
        }
      simp only[GMnode, node_4, h2n, Option.getD_some, GMedge, edge_2]
    }
    have h2n : edge (node (node (node d))) ∉ hgp.GMGrid := by{
      rw[edge_mem_GMGrid_iff]; exact h2f
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
      simp only [GMface, h1f', Option.getD_some]
      have h1n : [edge (node (node (node d))), edge d, edge (node d)].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = edge d := by{
          rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_pos]; simp[edge_mem_GMGrid_iff, hd]
          · simp[h2n]
        }
      simp only[GMnode, node_4, h1n, Option.getD_some, GMedge, edge_2]
    }
    have h1n : edge (node (node d)) ∉ hgp.GMGrid := by{
      rw[edge_mem_GMGrid_iff]; exact h1f
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
      simp only [GMface, h1f', Option.getD_some]
      have h1n : [edge (node (node d)), edge (node (node (node d))), edge d].find?
        (fun x ↦ decide (x ∈ hgp.GMGrid)) = edge d := by{
          rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_neg]
            · rw[List.find?_cons_of_pos]; simp[edge_mem_GMGrid_iff, hd]
            · simp[h2n]
          · simp[h1n]
        }
      simp only[GMnode, node_4, h1n, Option.getD_some, GMedge, edge_2]
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

@[reducible] noncomputable def GMDartHypermap (hgp : GridMapProper ab0 cm0)
  : Hypermap hgp.GMDart :=
  ⟨GMedge, GMnode, GMface, GM_enf_cancel⟩

theorem GMDartHypermap_plain {hgp : GridMapProper ab0 cm0}
 : hgp.GMDartHypermap.Plain := by{
  rw[Hypermap.plain_def']
  intro p _
  rw[Set.mem_setOf, minimalPeriod_eq_two_iff]
  change GMedge (GMedge p) = p ∧ GMedge p ≠ p
  rw [GMedge_2]
  simp only [true_and]
  simp[GMedge, Subtype.ext_iff, edge_ne]
}

theorem GMDartHypermap_edge_val_eq {hgp : GridMapProper ab0 cm0}
{u : hgp.GMDart}
  : (hgp.GMDartHypermap.edge u).val = edge u.val := by{
    change (GMedge _).val = _
    rw[GMedge]
  }


end GridMapProper
end GridPlane
