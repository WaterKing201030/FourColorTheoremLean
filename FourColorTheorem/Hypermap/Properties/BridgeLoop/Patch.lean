import FourColorTheorem.Hypermap.Actions.Patch
import FourColorTheorem.Hypermap.Properties.BridgeLoop.Basic

open Function
open Relation

namespace Hypermap

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]

namespace Patch

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]
variable {G : Hypermap α} {Gd : Hypermap αd} {Gr : Hypermap αr}
variable {hd : αd → α} {hr : αr → α} {bGd : List αd} {bGr : List αr}
variable (patchG : Patch G Gd Gr hd hr bGd bGr)
include patchG

theorem of_bridgeless (br'G : G.bridgeless) : Gd.bridgeless ∧ Gr.bridgeless := by{
  constructor
  · {
    rw[bridgeless]
    intro x hx
    have hx':=patchG.cface_of_disk_cface hx
    apply br'G (hd x)
    apply Eq.mp ?_ hx'
    congr
    rw[patchG.disk_edge_morph]
    intro hxb
    have hexb : edge x ∈ bGd := (patchG.disk_border_cedge_close hxb).mp (funReflTransGen.single _ _)
    have ih := (patchG.disk_border_cface_unique hxb hx).mp hexb
    have br'G' := br'G (hd x)
    have ⟨xr, hxre, hxrn⟩:=patchG.exists_galois_en_of_mem_bGd hxb
    rw[ih] at hxre
    rw[hxre, ← patchG.rem_edge_morph, ← patchG.rem_cface_iff] at br'G'
    rw[hxre, patchG.rem_hom_injective.eq_iff] at hxrn
    apply br'G'
    nth_rw 2 [hxrn]
    nth_rw 1 [← Gr.fen_cancel xr]
    apply Gr.cface_equivalence.symm
    apply funReflTransGen.single
  }
  · {
    intro x hx
    apply br'G (hr x)
    have hx' := patchG.cface_of_rem_cface hx
    apply Eq.mp ?_ hx'
    congr
    rw[patchG.rem_edge_morph]
  }
}

theorem bridgeless_of (bridge'Gd : Gd.bridgeless) (bridge'Gr : Gr.bridgeless)
  (chord'Gd : Gd.chordless bGd) : G.bridgeless := by{
  intro x xFex
  have x'R : x ∉ patchG.rem := by{
    intro xR
    have ⟨xr, hxr⟩:=xR
    rw[← hxr, ← patchG.rem_edge_morph, ← patchG.rem_cface_iff] at xFex
    exact bridge'Gr _ xFex
  }
  have ⟨xD, x'B⟩ := not_or.mp (x'R ∘ patchG.mem_rem_iff.mpr)
  rw[not_not] at xD
  rcases xD with ⟨xd, hxd⟩
  rw[← hxd] at x'B xFex
  rw[disk_mem_border_iff] at x'B
  rw[← patchG.disk_edge_morph _ x'B] at xFex
  have xO : hd xd ∈ patchG.outer := by{
    by_contra x'O
    rw[← patchG.disk_cface_iff_of_mem_outerC x'O] at xFex
    exact bridge'Gd _ xFex
  }
  have hemxd : hd (edge xd) = edge (hd xd) :=
    patchG.disk_edge_morph _ x'B
  have exO : hd (edge xd) ∈ patchG.outer :=
    patchG.outer_cface_close _ xO _ xFex
  rw[← patchG.mem_borderFband_iff, mem_fband_iff] at xO exO
  rcases xO with ⟨yd, ydB, Fxdyd⟩
  rcases exO with ⟨zd, zdB, Fexdzd⟩
  have Aydzd : Gd.adj yd zd :=
    ⟨xd, Gd.cface_equivalence.symm Fxdyd, Fexdzd⟩
  rw[chordless_def] at chord'Gd
  have hyc := chord'Gd yd ydB _ Aydzd
  have hc := patchG.disk_border_cycle.cycle
  have ⟨yr, hyre, hyrn⟩ := patchG.exists_galois_en_of_mem_bGd ydB
  have ⟨zr, hzre, hzrn⟩ := patchG.exists_galois_en_of_mem_bGd zdB
  have Fxdyd' := patchG.cface_of_disk_cface Fxdyd
  have Fexdzd' := patchG.cface_of_disk_cface Fexdzd
  have Fydzd' : G.cface _ _ := (G.cface_equivalence.symm Fxdyd').trans (xFex.trans Fexdzd')
  have hzdn : zd ≠ bGd.next yd ydB := by{
    intro hzdn
    have hcn : _ = _ :=
      (List.isCycleChain_iff_next_of_nodup patchG.disk_border_cycle.nodup).mp hc
      yd ydB
    rw[← hzdn] at hcn
    rw[hcn] at hyre
    rw[hyrn, hyre, ← patchG.rem_cface_iff] at Fydzd'
    nth_rw 2 [← Gr.fen_cancel yr] at Fydzd'
    apply bridge'Gr (node yr)
    apply Fydzd'.trans
    apply Gr.cface_equivalence.symm
    apply funReflTransGen.single
  }
  have hzdp : zd ≠ bGd.prev yd ydB := by{
    intro hzdn
    rw[List.eq_prev_iff_next_eq patchG.disk_border_cycle.nodup zdB] at hzdn
    symm at hzdn
    have hcn : _ = _ :=
      (List.isCycleChain_iff_next_of_nodup patchG.disk_border_cycle.nodup).mp hc
      zd zdB
    rw[← hzdn] at hcn
    rw[hcn] at hzre
    rw[hzrn, hzre, ← patchG.rem_cface_iff] at Fydzd'
    nth_rw 1 [← Gr.fen_cancel zr] at Fydzd'
    apply Gr.cface_equivalence.symm at Fydzd'
    apply bridge'Gr (node zr)
    apply Fydzd'.trans
    apply Gr.cface_equivalence.symm
    apply funReflTransGen.single
  }
  exact hzdn (hyc hzdp)
}

end Patch
end Hypermap
