import FourColorTheorem.Discretize.GridHypermap.GMCutout
import FourColorTheorem.Hypermap.Properties.Composition
import FourColorTheorem.Hypermap.Coloring

namespace GridPlane
namespace GridMapProper
open Relation
open Function
open Hypermap
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

@[reducible] noncomputable def gridHypermap (hgp : GridMapProper ab0 cm0) :=
  (Classical.choice hgp.exists_cutout).G.dual

theorem gridHypermap_planarBridgeless {hgp : GridMapProper ab0 cm0}
  : hgp.gridHypermap.PlanarBridgeless := by{
  constructor
  · {
    have h := (Classical.choice hgp.exists_cutout).map_planar
    exact h.dual
  }
  · {
    unfold gridHypermap
    rw[Hypermap.dual_bridgeless_iff]
    rcases (Classical.choice hgp.exists_cutout) with ⟨α, G, h, r, planG, Ih, hE, hF, hN, Dr, cycNr⟩
    simp only
    rw[Hypermap.loopless_def]
    intro x xNex
    wlog bb_hx : h x ∈ hgp.GMInner with H
    · {
      have bb_hx' : hgp.GMDartHypermap.edge (h x) ∈ _ := hgp.GMedge_inner_cases.resolve_left bb_hx
      rw[← hE] at bb_hx'
      specialize H (n := n) (ab0 := ab0) (cm0 := cm0) (hgp := hgp)
        α G h r planG Ih hE hF hN Dr cycNr (G.edge x)
      apply H ?_ bb_hx'
      apply G.cnode_equivalence.symm
      apply (Eq.mp · xNex)
      congr
      apply Ih
      rw[hE, hE]
      change h x = hgp.GMedge (hgp.GMedge _)
      rw[GMedge_2]
    }
    rcases em (∃i, x ∈ r i) with ⟨i, ri_x⟩ | r'x
    · {
      specialize cycNr i (by{simp})
      rcases cycNr with ⟨cycNri, Uri⟩
      have cycNri' := List.forall_mem_of_isCycleChain cycNri ri_x
      have ri_ex : G.edge x ∈ r i := by{
        rw[cnode, funReflTransGen_iff_iterate] at xNex
        rcases xNex with ⟨n, hn⟩
        specialize cycNri' n
        rwa [← hn]
      }
      rw[← List.mem_map_of_injective Ih, ← List.mem_reverse, Dr] at ri_x ri_ex
      rw[hE, hgp.mem_GMring_iff_val_mem_ring] at ri_ex
      change edge _ ∈ _ at ri_ex
      have ri_ex' := Matte.not_mem_ring_of_edge_mem_ring ri_ex
      rw[hgp.mem_GMring_iff_val_mem_ring] at ri_x
      contradiction
    }
    suffices H : (h x).val.half = (h (G.edge x)).val.half by{
      rw[hE] at H
      change GPoint.half _ = GPoint.half (edge (h x).val) at H
      have H' := edge_half_ne (d := (h x).val)
      exact H' H.symm
    }
    have IH : ∀ i n, Hypermap.node^[n] x ∉ r i := by{
      intro i n hn
      have IH := (cycNr i (by{simp})).1
      have IH' := funReflTransGen_iff_mem_of_isCycleChain IH hn (y:=x)
      apply r'x
      use i
      rw[IH']
      apply cnode_equivalence.symm
      apply funReflTransGen.iterate
    }
    have IH' : ∀n, h (G.node^[n] x) ∈ hgp.GMInner := by{
      intro n
      induction n with
      | zero => exact bb_hx
      | succ n' ih => {
        rw[iterate_succ_apply', hN _ (by{simp[IH]})]
        apply hgp.GMnode_inner_closed
        exact ih
      }
    }
    rw[cnode, funReflTransGen_iff_iterate] at xNex
    rcases xNex with ⟨k, hk⟩
    rw[← hk]
    clear hk
    push_neg at r'x
    induction k with
    | zero => rfl
    | succ k' ih => {
      rw[iterate_succ_apply']
      rw[hN]
      · {
        change _ = GPoint.half (hgp.GMnode _).val
        rw[hgp.GMnode_val_of_mem_GMInner, ← face_3, face_half, face_half, face_half, ih]
        simp[IH']
      }
      · simp[IH]
    }
  }
}

open FourColor
theorem gridHypermap_coloring {hgp : GridMapProper ab0 cm0}
(Hc : hgp.gridHypermap.fourColorable) :
∃ k : Fin n → Fin 4, ∀e, (ab0 e).proper → k e.1.1 ≠ k e.1.2 := by{
  unfold gridHypermap at *
  rw[fourColorable_dual_iff] at Hc
  rcases Hc with ⟨k, kE, kN⟩
  let C :=  (Classical.choice hgp.exists_cutout)
  have k_r : ∀i, ∀x ∈ C.r i, ∀y ∈ C.r i, k x = k y := by{
    intro i
    have ⟨cycNri, Uri⟩ := C.ring_proper i (by{simp})
    have cycNri' := fun x y => funReflTransGen_iff_mem_of_isCycleChain cycNri (x:=x) (y := y)
    have kN' := isGraphColoring.cnode_invariant' kN
    intro x hx y hy
    exact kN' x y ((cycNri' x y hx).mp hy)
  }
  clear kN
  let kn : C.α → Fin 4:= fun x => match k x with
    | color0 => 0
    | color1 => 1
    | color2 => 2
    | color3 => 3
  have kn_inj {x y : C.α} : kn x = kn y ↔ k x = k y := by{
    unfold kn
    match k x with | color0 | color1 | color2 | color3 => {
      match k y with | color0 | color1 | color2 | color3 => simp
    }
  }
  use fun i => kn ((C.r i).head (C.r_ne_nil i))
  intro e habep
  have hgp' := hgp.extendCMatte_proper_adj habep
  rcases hgp' with ⟨d, hd2, hed1⟩
  have hd : d ∈ hgp.GMGrid := by{
    rw[Matte.mem_ring_iff_mem_disk_border] at hd2
    change _ ∧ _ at hd2
    rw[← Matte.mem_iff] at hd2
    exact hgp.CM_subset_GMGrid hd2.left
  }
  have hed : edge d ∈ hgp.GMGrid := by{
    rw[Matte.mem_ring_iff_mem_disk_border] at hed1
    change _ ∧ _ at hed1
    rw[← Matte.mem_iff] at hed1
    exact hgp.CM_subset_GMGrid hed1.left
  }
  change (⟨d, hd⟩ : hgp.GMDart).val ∈ _ at hd2
  change (⟨edge d, hed⟩ : hgp.GMDart).val ∈ _ at hed1
  rw[← hgp.mem_GMring_iff_val_mem_ring] at hd2 hed1
  have heu : (⟨edge d, hed⟩ : hgp.GMDart) = GMedge ⟨d, hd⟩ := by{rfl}
  rw[← C.ring_def] at hd2 hed1
  rw[List.mem_reverse] at hd2 hed1
  rw[List.mem_map] at hd2
  have ⟨x, hx2, hxu⟩ := hd2
  have hex : C.G.edge x ∈ C.r e.val.1 := by{
    have ke' := C.enc_morph_edge x
    rw[hxu] at ke'
    apply (Eq.trans · heu.symm) at ke'
    rw[← ke', List.mem_map_of_injective C.enc_injective] at hed1
    exact hed1
  }
  have kE' := kE x
  simp only
  rw[ne_eq, kn_inj]
  apply (Eq.mp · kE')
  congr 1
  · {
    apply k_r e.val.1
    · assumption
    · apply List.head_mem
  }
  · {
    apply k_r e.val.2
    · assumption
    · apply List.head_mem
  }
}

end GridMapProper
end GridPlane
