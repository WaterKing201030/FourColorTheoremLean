import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Hypermap.Actions.Walkup

open Function
open Relation

namespace Hypermap

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]

structure Patch (G : Hypermap α) (Gd : Hypermap αd) (Gr : Hypermap αr)
  (hd : αd → α) (hr : αr → α) (bGd : List αd) (bGr : List αr) : Prop where
  disk_hom_injective : Injective hd
  rem_hom_injective : Injective hr
  disk_border_cycle : Gd.simpleCycle (fromFun Gd.edge) bGd
  rem_border_cycle : bGr.IsCycleChain (fromFun Gr.node) ∧ bGr.Nodup
  rem_border_order : bGr.map hr = (bGd.map hd).reverse
  rem_hom_codom : ∀x, (∃y, hr y = x) ↔ (∀y, hd y ≠ x) ∨ x ∈ bGd.map hd
  disk_edge_morph : ∀x ∉ bGd, hd (Gd.edge x) = G.edge (hd x)
  disk_node_morph : ∀x, hd (Gd.node x) = G.node (hd x)
  rem_edge_morph : ∀x, hr (Gr.edge x) = G.edge (hr x)
  rem_node_morph : ∀x ∉ bGr, hr (Gr.node x) = G.node (hr x)

namespace Patch

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {αd : Type _} [Fintype αd] [DecidableEq αd]
variable {αr : Type _} [Fintype αr] [DecidableEq αr]
variable {G : Hypermap α} {Gd : Hypermap αd} {Gr : Hypermap αr}
variable {hd : αd → α} {hr : αr → α} {bGd : List αd} {bGr : List αr}
abbrev diskBorder (_ : Patch G Gd Gr hd hr bGd bGr):= bGd.map hd
abbrev remBorder (_ : Patch G Gd Gr hd hr bGd bGr):= bGr.map hr
abbrev border (p : Patch G Gd Gr hd hr bGd bGr) := {x | x ∈ p.diskBorder}
abbrev disk (_ : Patch G Gd Gr hd hr bGd bGr) := {x | ∃xd, hd xd = x}
abbrev rem (_ : Patch G Gd Gr hd hr bGd bGr) := {x | ∃xr, hr xr = x}

variable (patchG : Patch G Gd Gr hd hr bGd bGr)
include patchG
theorem mem_disk_def {x : α} : x ∈ patchG.disk ↔ ∃xd, hd xd = x := by rfl
theorem mem_rem_def {x : α} : x ∈ patchG.rem ↔ ∃xr, hr xr = x := by rfl
theorem mem_border_iff_disk {x : α} : x ∈ patchG.border ↔ x ∈ patchG.diskBorder := by{
  rfl
}
theorem mem_border_disk_iff_rem {x : α} : x ∈ patchG.diskBorder ↔ x ∈ patchG.remBorder := by{
  rw[diskBorder, remBorder, patchG.rem_border_order, List.mem_reverse]
}
theorem mem_border_iff_rem {x : α} : x ∈ patchG.border ↔ x ∈ patchG.remBorder := by{
  rw[← patchG.mem_border_disk_iff_rem, patchG.mem_border_iff_disk]
}
theorem disk_mem_border_iff {xd : αd} : hd xd ∈ patchG.border ↔ xd ∈ bGd := by{
  rw[mem_border_iff_disk, List.mem_map_of_injective patchG.disk_hom_injective]
}
theorem rem_mem_border_iff {xr : αr} : hr xr ∈ patchG.border ↔ xr ∈ bGr := by{
  rw[mem_border_iff_rem, List.mem_map_of_injective patchG.rem_hom_injective]
}
theorem disk_border_length : patchG.diskBorder.length = bGd.length := by{simp}
theorem rem_border_length : patchG.remBorder.length = bGr.length := by{simp}
theorem disk_rem_border_length_eq : patchG.diskBorder.length = patchG.remBorder.length := by{
  unfold diskBorder remBorder
  rw[patchG.rem_border_order, List.length_reverse]
}
theorem disk_rem_border_length_eq' : bGd.length = bGr.length := by{
  rw[← patchG.disk_border_length, ← patchG.rem_border_length]
  rw[patchG.disk_rem_border_length_eq]
}
theorem disk_hom_codom : ∀x, (∃y, hd y = x) ↔ (∀y, hr y ≠ x) ∨ x ∈ bGr.map hr := by{
  intro x
  have ih := patchG.rem_hom_codom x
  rw[patchG.mem_border_disk_iff_rem] at ih
  constructor
  · {
    intro ⟨y, hyx⟩
    simp only [ne_eq,
      (by { simp only [ne_eq, not_forall, Decidable.not_not]; exact ⟨y, hyx⟩
        } : ¬∀ y, hd y ≠ x), false_or] at ih
    rw[← ih]
    apply (em' (∃y, hr y = x)).imp_left
    simp
  }
  · {
    intro h
    rcases h with h | h
    · {
      simp only [h, exists_false, ne_eq, List.mem_map, and_false, or_false, false_iff, not_forall,
        Decidable.not_not] at ih
      exact ih
    }
    · {
      rw[← patchG.mem_border_disk_iff_rem] at h
      simp only [List.mem_map] at h
      have ⟨y, _, hy⟩:=h
      exact ⟨y, hy⟩
    }
  }
}
theorem mem_disk_iff_rem {x : α} : x ∈ patchG.disk ↔ x ∉ patchG.rem ∨ x ∈ patchG.remBorder := by{
  simp[patchG.disk_hom_codom]
}
theorem mem_rem_iff_disk {x : α} : x ∈ patchG.rem ↔ x ∉ patchG.disk ∨ x ∈ patchG.diskBorder := by{
  simp[patchG.rem_hom_codom]
}

theorem mem_disk_iff {x : α} : x ∈ patchG.disk ↔ x ∉ patchG.rem ∨ x ∈ patchG.border := by{
  simp only [patchG.mem_border_iff_rem, mem_disk_iff_rem]
}
theorem mem_rem_iff {x : α} : x ∈ patchG.rem ↔ x ∉ patchG.disk ∨ x ∈ patchG.border := by{
  simp only [patchG.mem_border_iff_disk, mem_rem_iff_disk]
}

theorem disk_border_order : bGd.map hd = (bGr.map hr).reverse := by{
  apply List.reverse_injective
  rw[List.reverse_reverse, patchG.rem_border_order]
}

theorem border_antisymm_disk {xd : αd} : (∃xr, hr xr = hd xd) ↔ xd ∈ bGd := by{
  rw[patchG.rem_hom_codom, List.mem_map_of_injective patchG.disk_hom_injective]
  simp
}
theorem border_antisymm_rem {xr : αr} : (∃xd, hd xd = hr xr) ↔ xr ∈ bGr := by{
  rw[patchG.disk_hom_codom, List.mem_map_of_injective patchG.rem_hom_injective]
  simp
}
theorem disk_border_cedge_close {xd : αd} (hxd : xd ∈ bGd) {yd : αd}
  : Gd.cedge xd yd ↔ yd ∈ bGd := by{
    symm
    apply Relation.funReflTransGen_iff_mem_of_isCycleChain
    · exact patchG.disk_border_cycle.cycle
    · exact hxd
  }
theorem disk_cedge_of_mem_border {xd yd : αd} (hxd : xd ∈ bGd) (hyd : yd ∈ bGd)
  : Gd.cedge xd yd := by{
    rw[patchG.disk_border_cedge_close hxd]
    exact hyd
  }
theorem rem_border_cnode_close {xr : αr} (hxr : xr ∈ bGr) {yr : αr}
  : Gr.cnode xr yr ↔ yr ∈ bGr := by{
    symm
    apply Relation.funReflTransGen_iff_mem_of_isCycleChain
    · exact patchG.rem_border_cycle.left
    · exact hxr
  }
theorem rem_cnode_of_mem_border {xr yr : αr} (hxr : xr ∈ bGr) (hyr : yr ∈ bGr)
  : Gr.cnode xr yr := by{
    rw[patchG.rem_border_cnode_close hxr]
    exact hyr
  }
theorem disk_edge_mem {xd : αd} : edge xd ∈ bGd ↔ xd ∈ bGd := by{
  constructor
  · {
    intro h
    rw[← patchG.disk_border_cedge_close h]
    apply cedge_equivalence.symm
    apply funReflTransGen.single
  }
  · {
    intro h
    rw[← patchG.disk_border_cedge_close h]
    apply funReflTransGen.single
  }
}
theorem rem_node_mem {xr : αr} : node xr ∈ bGr ↔ xr ∈ bGr := by{
  constructor
  · {
    intro h
    rw[← patchG.rem_border_cnode_close h]
    apply cnode_equivalence.symm
    apply funReflTransGen.single
  }
  · {
    intro h
    rw[← patchG.rem_border_cnode_close h]
    apply funReflTransGen.single
  }
}
theorem disk_union_rem' {x : α} : (∃ xd, hd xd = x) ∨ (∃xr, hr xr = x) := by{
  rw[patchG.disk_hom_codom]
  rw[or_comm, ← or_assoc]
  left
  apply (em _).imp_right
  simp
}
theorem disk_union_rem : patchG.disk ∪ patchG.rem = Set.univ := by{
  rw[Set.eq_univ_iff_forall]
  intro x
  simp[disk, rem, patchG.disk_union_rem']
}

theorem disk_inter_rem' {x : α} (hxd : ∃ xd, hd xd = x) (hxr : ∃ xr, hr xr = x) :
  x ∈ patchG.border := by{
  have ⟨xd, hxd'⟩:=hxd
  rw[mem_border_iff_disk]
  unfold diskBorder
  rw[← hxd', List.mem_map_of_injective patchG.disk_hom_injective]
  rw[← patchG.border_antisymm_disk]
  have ⟨xr, hxr'⟩:=hxr
  exact ⟨xr, hxr'.trans hxd'.symm⟩
}
theorem disk_inter_rem_iff' {x : α} : (∃ xd, hd xd = x) ∧ (∃ xr, hr xr = x) ↔
  x ∈ patchG.border := by{
  constructor
  · intro ⟨h0, h1⟩; exact patchG.disk_inter_rem' h0 h1
  · {
    intro hxd
    rw[mem_border_iff_disk] at hxd
    unfold diskBorder at hxd
    have hxr:=patchG.mem_border_disk_iff_rem.mp hxd
    rw[List.mem_map] at hxd hxr
    have ⟨xd, _, hxd'⟩ := hxd
    have ⟨xr, _, hxr'⟩ := hxr
    exact ⟨⟨xd, hxd'⟩, ⟨xr, hxr'⟩⟩
  }
}
theorem disk_inter_rem : patchG.disk ∩ patchG.rem = patchG.border := by{
  ext x
  simp[patchG.disk_inter_rem_iff']
}
theorem border_subset_disk : patchG.border ⊆ patchG.disk := by{
  rw[← disk_inter_rem]
  apply Set.inter_subset_left
}
theorem border_subset_rem : patchG.border ⊆ patchG.rem := by{
  rw[← disk_inter_rem]
  apply Set.inter_subset_right
}
theorem rem_compl_subset_disk : patchG.remᶜ ⊆ patchG.disk := by{
  intro x hx
  rw[Set.mem_compl_iff] at hx
  rw[mem_disk_iff_rem]
  left
  exact hx
}
theorem disk_compl_subset_rem : patchG.diskᶜ ⊆ patchG.rem := by{
  intro x hx
  rw[Set.mem_compl_iff] at hx
  rw[mem_rem_iff_disk]
  left
  exact hx
}
theorem disk_eq_rem_compl_union_border : patchG.disk = patchG.remᶜ ∪ patchG.border := by{
  rw[← disk_inter_rem, Set.union_inter_distrib_left, Set.compl_union_self, Set.inter_univ]
  rw[Eq.comm, Set.union_eq_right]
  apply patchG.rem_compl_subset_disk
}
theorem rem_eq_disk_compl_union_border : patchG.rem = patchG.diskᶜ ∪ patchG.border := by{
  rw[← disk_inter_rem, Set.union_inter_distrib_left, Set.compl_union_self, Set.univ_inter]
  rw[Eq.comm, Set.union_eq_right]
  apply patchG.disk_compl_subset_rem
}


theorem diskBorder_nodup : patchG.diskBorder.Nodup := by{
  unfold diskBorder
  apply List.Nodup.map
  · exact patchG.disk_hom_injective
  · exact patchG.disk_border_cycle.nodup
}
theorem remBorder_nodup : patchG.remBorder.Nodup := by{
  unfold remBorder
  apply List.Nodup.map
  · exact patchG.rem_hom_injective
  · exact patchG.rem_border_cycle.right
}

theorem disk_rem_hom_surj : ∀x, (∃y, hd y = x) ∨ (∃y, hr y = x) := by{
  intro x
  rcases em (x ∈ patchG.rem) with hxr | hxr
  · {
    have ⟨x, hx⟩:=hxr
    right
    exact ⟨_, hx⟩
  }
  · {
    rw[mem_rem_iff, not_or, not_not, mem_border_iff_disk] at hxr
    have ⟨x, hx⟩:=hxr.left
    rw[← hx, List.mem_map_of_injective patchG.disk_hom_injective] at hxr
    left
    exact ⟨_, hx⟩
  }
}
theorem disk_not_border_rem_hom_surj : ∀x, (∃y ∉ bGd, hd y = x) ∨ (∃y, hr y = x) := by{
  intro x
  rcases em (x ∈ patchG.rem) with hxr | hxr
  · {
    have ⟨x, hx⟩:=hxr
    right
    exact ⟨_, hx⟩
  }
  · {
    rw[mem_rem_iff, not_or, not_not, mem_border_iff_disk] at hxr
    have ⟨x, hx⟩:=hxr.left
    rw[← hx, List.mem_map_of_injective patchG.disk_hom_injective] at hxr
    left
    exact ⟨_, hxr.right, hx⟩
  }
}
theorem disk_rem_not_border_hom_surj : ∀x, (∃y, hd y = x) ∨ (∃y ∉ bGr, hr y = x) := by{
  intro x
  rcases em (x ∈ patchG.disk) with hxd | hxd
  · {
    have ⟨x, hx⟩:=hxd
    left
    exact ⟨_, hx⟩
  }
  · {
    rw[mem_disk_iff, not_or, not_not, mem_border_iff_rem] at hxd
    have ⟨x, hx⟩:=hxd.left
    rw[← hx, List.mem_map_of_injective patchG.rem_hom_injective] at hxd
    right
    exact ⟨_, hxd.right, hx⟩
  }
}

theorem galois_connect_edge_node {xd : αd} {xr : αr}
  : hd (Gd.edge xd) = hr xr ↔ hd xd = hr (Gr.node xr) := by{
    rcases em (xd ∈ bGd) with b_xd | b_xd
    · {
      rcases em (xr ∈ bGr) with b_xr | b_xr
      · {
        have ⟨cycEb, EbS⟩:=patchG.disk_border_cycle
        have ⟨cycNb, NbNd⟩:=patchG.rem_border_cycle
        rw[List.isCycleChain_iff_next_of_nodup (simpleList.nodup EbS)] at cycEb
        specialize cycEb xd b_xd; unfold fromFun at cycEb
        rw[cycEb, ← List.map_next_apply patchG.disk_hom_injective]
        simp only [patchG.disk_border_order]
        rw[List.next_reverse_eq_prev _
          (List.Nodup.map patchG.rem_hom_injective NbNd) _
          (by{
            rw[patchG.rem_border_order, List.mem_reverse]
            exact List.mem_map_of_mem b_xd
          })]
        rw[List.isCycleChain_iff_prev_of_nodup NbNd] at cycNb
        specialize cycNb (bGr.next xr b_xr) (List.next_mem _ _ _); unfold fromFun at cycNb
        rw[List.prev_next _ NbNd] at cycNb
        rw[cycNb, ← List.map_next_apply patchG.rem_hom_injective]
        rw[List.prev_eq_iff_eq_next (List.Nodup.map patchG.rem_hom_injective NbNd)
        ?_ (List.mem_map_of_mem b_xr)]
        rw[patchG.rem_border_order, List.mem_reverse]
        exact List.mem_map_of_mem b_xd
      }
      · {
        constructor
        · {
          intro h
          exfalso
          apply b_xr
          have b_xr' := patchG.border_antisymm_rem.mp ⟨_, h⟩
          exact b_xr'
        }
        · {
          intro h
          exfalso
          apply b_xr
          have b_xr' := patchG.border_antisymm_rem.mp ⟨_, h⟩
          have h' := patchG.rem_border_cnode_close b_xr' (yr:=xr)
          rw[← h', Hypermap.cnode_equivalence.comm]
          apply funReflTransGen.single
        }
      }
    }
    · {
      constructor
      · {
        intro h
        exfalso
        apply b_xd
        have b_xd' := patchG.border_antisymm_disk.mp ⟨_, h.symm⟩
        have h' := patchG.disk_border_cedge_close b_xd' (yd:=xd)
        rw[← h', Hypermap.cedge_equivalence.comm]
        apply funReflTransGen.single
      }
      · {
        intro h
        exfalso
        apply b_xd
        have b_xd' := patchG.border_antisymm_disk.mp ⟨_, h.symm⟩
        exact b_xd'
      }
    }
  }
theorem exists_galois_en_of_mem_bGd {xd : αd} (b_xd : xd ∈ bGd) :
  ∃xr, hd (edge xd) = hr xr ∧ hd xd = hr (node xr) := by{
    simp only [patchG.galois_connect_edge_node, and_self]
    have xdP : hd xd ∈ patchG.rem
      := by{rw[mem_rem_iff_disk]; right; exact List.mem_map_of_mem b_xd}
    rw[rem, Set.mem_setOf] at xdP
    have ⟨xr, hxrd⟩:=xdP
    use Gr.face (Gr.edge xr)
    rw[nfe_cancel, hxrd]
  }
theorem exists_galois_en_of_mem_bGr {xr : αr} (b_xr : xr ∈ bGr) :
  ∃xd, hd (edge xd) = hr xr ∧ hd xd = hr (node xr) := by{
    simp only [patchG.galois_connect_edge_node, and_self]
    have xrP : hr xr ∈ patchG.disk
      := by{rw[mem_disk_iff_rem]; right; exact List.mem_map_of_mem b_xr}
    rw[disk, Set.mem_setOf] at xrP
    have ⟨xd, hxdr⟩:=xrP
    use Gd.node (Gd.face xd)
    rw[← patchG.galois_connect_edge_node, enf_cancel, hxdr]
  }
theorem disk_nodeinv_morph : ∀x, hd (Gd.nodeinv x) = G.nodeinv (hd x) := by{
  intro _
  rw[G.eq_nodeinv_iff_node_eq, ← patchG.disk_node_morph, nodeinv_rightinv]
}
theorem rem_edgeinv_morph : ∀x, hr (Gr.edgeinv x) = G.edgeinv (hr x) := by{
  intro _
  rw[G.eq_edgeinv_iff_edge_eq, ← patchG.rem_edge_morph, edgeinv_rightinv]
}
theorem disk_face_morph : ∀x ∉ bGd, hd (face x) = face (hd x) := by{
  intro xd b'xd
  rw[← fen_cancel (hd _), ← patchG.disk_node_morph, face_inj]
  nth_rw 2 [← enf_cancel xd]
  rw[patchG.disk_edge_morph]
  rw[← patchG.disk_edge_mem, enf_cancel]
  exact b'xd
}
theorem rem_face_morph : ∀x ∉ bGr.map Gr.faceinv, hr (face x) = face (hr x) := by{
  intro xr b'fxr
  rw[← fen_cancel (hr _), face_inj]
  nth_rw 2 [← enf_cancel xr]
  rw[patchG.rem_edge_morph, edge_inj]
  rw[patchG.rem_node_morph]
  simp only [List.mem_map, not_exists, not_and, faceinv_eq_iff_eq_face] at b'fxr
  intro h
  exact b'fxr _ h rfl
}
theorem rem_face_morph' : ∀x, face x ∉ bGr → hr (face x) = face (hr x) := by{
  intro x hx
  apply patchG.rem_face_morph x
  rw[← Gr.faceinv_leftinv x, List.mem_map_of_injective Gr.faceinv_injective]
  exact hx
}
theorem rem_faceinv_morph : ∀x ∉ bGr, hr (Gr.faceinv x) = G.faceinv (hr x) := by{
  intro x hx
  rw[← G.face_inj, faceinv_rightinv]
  rw[← patchG.rem_face_morph, faceinv_rightinv]
  rw[List.mem_map_of_injective Gr.faceinv_injective]
  exact hx
}

abbrev outer := {x : α | ∃y ∈ patchG.rem, G.cface y x}

abbrev borderFband (_ : Patch G Gd Gr hd hr bGd bGr) := Gd.fband bGd
abbrev borderFbandComplType := {x // x ∉ patchG.borderFband}
@[inline] instance borderFbandComplType.instFintype : Fintype patchG.borderFbandComplType :=
  Subtype.fintype (· ∉ patchG.borderFband)

abbrev remGClosure (_ : Patch G Gd Gr hd hr bGd bGr) := {x | ∃yr, G.cglink (hr yr) x}

end Patch

end Hypermap
