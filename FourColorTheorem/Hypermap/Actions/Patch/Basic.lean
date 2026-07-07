import FourColorTheorem.Hypermap.Basic

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
theorem rem_border_cnode_close {xr : αr} (hxr : xr ∈ bGr) {yr : αr}
  : Gr.cnode xr yr ↔ yr ∈ bGr := by{
    symm
    apply Relation.funReflTransGen_iff_mem_of_isCycleChain
    · exact patchG.rem_border_cycle.left
    · exact hxr
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

theorem card_inex : Fintype.card αd + Fintype.card αr = Fintype.card α + patchG.diskBorder.length
:= by{
  rw[← Fintype.card_sum, ← List.Subtype.fintype_card_eq_length_of_nodup patchG.diskBorder_nodup,
  ← Fintype.card_sum]
  apply Fintype.card_congr
  let f : αd ⊕ αr → α ⊕ { x // x ∈ patchG.diskBorder } := fun x =>
    match x with
    | Sum.inl x => if hxd : x ∈ bGd then Sum.inr ⟨hd x, by{
      rw[List.mem_map_of_injective patchG.disk_hom_injective]
      exact hxd
    }⟩ else Sum.inl (hd x)
    | Sum.inr x => Sum.inl (hr x)
  apply Equiv.ofBijective f
  constructor
  · {
    intro x1 x2 hx12
    match x1 with
    | Sum.inl x1 => match x2 with
      | Sum.inl x2 => {
        simp only [f] at hx12
        rw[apply_dite (· = _), apply_dite (_ = ·)] at hx12
        simp only [reduceCtorEq, Sum.inl.injEq, dite_eq_ite, if_false_left,
        patchG.disk_hom_injective.eq_iff] at hx12
        rcases em (x1 ∈ bGd) with hx1d | hx1d
        · {
          simp only [hx1d, ↓reduceDIte] at hx12
          rcases em (x2 ∈ bGd) with hx2d | hx2d
          · {
            simp[hx2d, patchG.disk_hom_injective.eq_iff] at hx12
            simp[hx12]
          }
          · simp[hx2d] at hx12
        }
        · simp[hx1d] at hx12; simp[hx12]
      }
      | Sum.inr x2 => {
        rcases em (x1 ∈ bGd) with hx1d | hx1d
        all_goals
        simp only [hx1d, ↓reduceDIte, Sum.inl.injEq, f, reduceCtorEq] at hx12
        try exfalso; apply hx1d; rw[← patchG.border_antisymm_disk]; exact ⟨x2, hx12.symm⟩
      }
    | Sum.inr x1 => match x2 with
      | Sum.inl x2 => {
        simp only [f] at hx12
        rw[apply_dite (_ = ·)] at hx12
        simp only [reduceCtorEq, Sum.inl.injEq, dite_eq_ite, if_false_left] at hx12
        exfalso
        apply hx12.left
        rw[← patchG.border_antisymm_disk]
        exact ⟨x1, hx12.right⟩
      }
      | Sum.inr x2 => {
        simp[f] at hx12
        simp[patchG.rem_hom_injective hx12]
      }
  }
  · {
    intro x
    match x with
    | Sum.inl x => {
      rcases em (x ∈ patchG.rem) with hxr | hxr
      · {
        have ⟨x, hx⟩:=hxr
        use Sum.inr x
        simp[f, hx]
      }
      · {
        rw[mem_rem_iff, not_or, not_not, mem_border_iff_disk] at hxr
        have ⟨x, hx⟩:=hxr.left
        rw[← hx, List.mem_map_of_injective patchG.disk_hom_injective] at hxr
        use Sum.inl x
        simp[f, hxr, hx]
      }
    }
    | Sum.inr ⟨x, hx⟩ => {
      rw[List.mem_map] at hx
      have ⟨x, hx', hx⟩:=hx
      use Sum.inl x
      simp[f, hx', hx]
    }
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
        rw[List.isCycleChain_iff_next_of_nodup (nodup_of_simpleList EbS)] at cycEb
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

theorem disk_face_eq_face_rem_iff {xd : αd} {xr : αr} :
  (hd (face xd) = face (hr xr)) ↔ hd xd = hr (face xr) := by{
    nth_rw 2 [← enf_cancel xd]
    rw[patchG.galois_connect_edge_node, patchG.disk_node_morph]
    nth_rw 2 [← edge_inj]
    rw[← patchG.rem_edge_morph, enf_cancel]
    nth_rw 2 [← face_inj]
    rw[fen_cancel]
  }

theorem disk_border_cface_unique {xd yd : αd} (hxd : xd ∈ bGd) (hxdyd : Gd.cface xd yd)
  : yd ∈ bGd ↔ yd = xd := by{
    have ih := patchG.disk_border_cycle.simple
    unfold simpleList at ih
    rw[List.nodup_map_iff_inj_on patchG.disk_border_cycle.nodup] at ih
    constructor
    · {
      intro hyd
      specialize ih _ hxd _ hyd
      symm; apply ih
      rw[Quotient.eq_iff_equiv]
      exact hxdyd
    }
    · intro h; exact h ▸ hxd
  }
theorem cface_of_disk_cface {xd yd : αd} (hxdyd : Gd.cface xd yd) : G.cface (hd xd) (hd yd) := by{
  have hwlog {xd yd : αd} :
  (∃n, Gd.face^[n] xd = yd ∧ ∀m < n, Gd.face^[m] xd ∉ bGd) → G.cface (hd xd) (hd yd) := by{
    intro ⟨n, hn0, hn1⟩
    rw[cface, funReflTransGen_iff_iterate]
    use n
    induction n generalizing yd with
    | zero => simp at hn0; simp[hn0]
    | succ n' ih => {
      specialize ih rfl (fun m hmn' => hn1 m (Nat.lt_succ_of_lt hmn'))
      rw[iterate_succ_apply'] at hn0
      rw[iterate_succ_apply', ih, ← patchG.disk_face_morph, hn0]
      apply hn1; simp
    }
  }
  have hydxd := Gd.cface_equivalence.symm hxdyd
  rw[cface, funReflTransGen_iff_iterate_minimal] at hxdyd hydxd
  have ⟨nx, hnxy, hnxm⟩ := hxdyd
  have ⟨ny, hnyx, hnym⟩ := hydxd
  rcases em (∀m < nx, Gd.face^[m] xd ∉ bGd) with himpx | himpx
  · {
    apply hwlog
    use nx
  }
  rcases em (∀m < ny, Gd.face^[m] yd ∉ bGd) with himpy | himpy
  · {
    apply G.cface_equivalence.symm
    apply hwlog
    use ny
  }
  have hxy : xd = yd := by{
    simp only [not_forall, Decidable.not_not] at himpx himpy
    simp only [exists_prop] at himpx himpy
    have ⟨mx, hmxn, hmxb⟩:=himpx
    have ⟨my, hmyn, hmyb⟩:=himpy
    have hcxm : Gd.cface xd (face^[mx] xd) := by apply funReflTransGen.iterate
    have hcym : Gd.cface yd (face^[my] yd) := by apply funReflTransGen.iterate
    have hcxy : Gd.cface xd yd := by rw[← hnxy]; apply funReflTransGen.iterate
    have ih0 : Gd.cface (face^[mx] xd) (face^[my] yd) :=
      (Gd.cface_equivalence.symm hcxm).trans (hcxy.trans hcym)
    have ih := (patchG.disk_border_cface_unique hmxb ih0).mp hmyb
    rcases lt_trichotomy (nx - mx) (ny - my) with hnmxy | hnmxy | hnmxy
    · {
      exfalso
      apply hnym ((ny - my) - (nx - mx)) (by omega)
      rw[← hnxy, ← iterate_add_apply, ← Nat.sub_add_comm (Nat.le_of_lt hnmxy)]
      rw[Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self (Nat.le_of_lt hmxn)]
      rw[iterate_add_apply, ← ih, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmyn), hnyx]
    }
    · rw[← hnyx, ← Nat.sub_add_cancel (Nat.le_of_lt hmyn), iterate_add_apply, ← hnmxy, ih,
      ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmxn), hnxy]
    · {
      exfalso
      apply hnxm ((nx - mx) - (ny - my)) (by omega)
      rw[← hnyx, ← iterate_add_apply, ← Nat.sub_add_comm (Nat.le_of_lt hnmxy)]
      rw[Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self (Nat.le_of_lt hmyn)]
      rw[iterate_add_apply, ih, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmxn), hnxy]
    }
  }
  rw[hxy]
  apply ReflTransGen.refl
}

theorem cface_of_rem_cface {xr yr : αr} (hxryr : Gr.cface xr yr) : G.cface (hr xr) (hr yr) := by{
  rw[cface, funReflTransGen_iff_iterate] at hxryr
  have ⟨n, hnxy⟩:=hxryr; clear hxryr
  induction n generalizing xr with
  | zero => simp at hnxy; simp[hnxy, cface, funReflTransGen]; rfl
  | succ n' ih => {
    specialize ih (xr := face xr) (by{rw[← iterate_succ_apply, hnxy]})
    apply funReflTransGen.trans ?_ ih
    rcases em' (face xr ∈ bGr) with b_xr | b_xr
    · {
      have ih' := patchG.rem_face_morph xr (by{
        simp only [List.mem_map]
        intro ⟨xr', hxr'b, hxr'r⟩
        rw[faceinv_eq_iff_eq_face] at hxr'r
        rw[hxr'r] at hxr'b
        contradiction
      })
      rw[ih']
      apply funReflTransGen.single
    }
    have ⟨xd, hxde, hxrn⟩ := patchG.exists_galois_en_of_mem_bGr b_xr
    rw[← G.edge_inj, ← patchG.rem_edge_morph, enf_cancel] at hxrn
    rw[← hxrn, ← hxde]
    apply funReflTransGen.trans (funReflTransGen.single _ _)
    rw[← comp_apply (f:=G.face) (g:=G.edge), ← G.nodeinv_eq, ← patchG.disk_nodeinv_morph,
    Gd.nodeinv_eq, comp_apply]
    apply G.cface_equivalence.symm
    apply patchG.cface_of_disk_cface
    apply funReflTransGen.single
  }
}
theorem rem_cface_of_cface {xr yr : αr} (hxryr : G.cface (hr xr) (hr yr)) : Gr.cface xr yr := by{
  -- 我们泛化hr xr为x
  -- 若x在rem中，则只需证x对应的xr得到Gr.cface xr yr
  -- 考虑x的下一步，若
  -- 否则，不存在这样的xr，但是有xd。引入新谓词cFdr，假设存在一个边界点，这个边界点在Gd.cface上和该点连接。
  let cFdr : α → αr → Prop := fun x xr =>
    ∃xd, hd xd = x ∧ ∃yd, hd yd = hr xr ∧ Gd.cface yd xd
  generalize hrxrx : hr xr = x
  have ind_tmp : if x ∈ patchG.rem then x = hr xr else cFdr x xr := by{simp[← hrxrx]}
  rw[hrxrx] at hxryr
  clear hrxrx
  rw[cface, funReflTransGen_iff_iterate] at hxryr
  have ⟨n, hn⟩:=hxryr
  clear hxryr
  induction n generalizing x xr with
  | zero => {
    simp at hn
    simp[hn, patchG.rem_hom_injective.eq_iff] at ind_tmp
    simp[ind_tmp, cface, funReflTransGen]
    rfl
  }
  | succ n' ih => {
    have ih' := fun xr h => ih (xr := xr) (face x) h (by{rw[← iterate_succ_apply, hn]})
    cases em (x ∈ patchG.rem) with
    | inl hxr => {
      simp only [hxr, ↓reduceIte] at ind_tmp
      suffices H : Gr.cface (face xr) yr by apply funReflTransGen.head rfl H
      apply ih'
      cases em (face xr ∈ bGr) with
      | inl hfxb => {
        have ⟨xd, hxde, hxdn⟩ := patchG.exists_galois_en_of_mem_bGr hfxb
        have hxde' := hxde
        rw[← patchG.disk_face_eq_face_rem_iff] at hxde'
        rw[← hxde]
        unfold cFdr
        rw[ind_tmp, ← hxde', ← hxde]
        simp only [patchG.disk_hom_injective.eq_iff, ↓existsAndEq, true_and]
        have lem : Gd.cface _ _ := funReflTransGen.single Gd.face (edge xd)
        simp only [lem, if_true_right]
        intro hdd
        rw[mem_rem_iff_disk] at hdd
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply, not_true_eq_false, List.mem_map,
          false_or, patchG.disk_hom_injective.eq_iff, ↓ existsAndEq, and_true] at hdd
        have hxde' := patchG.border_antisymm_disk.mp ⟨_, hxde.symm⟩
        refine (patchG.disk_border_cface_unique hxde' ?_).mp hdd
        exact funReflTransGen.single _ _
      }
      | inr hfxb => {
        have hfi := patchG.rem_face_morph' _ hfxb
        rw[hfi, ind_tmp, ← hfi]
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply, ↓reduceIte]
      }
    }
    | inr hxr => {
      have ⟨hxd, hxb⟩ := not_or.mp (hxr ∘ patchG.mem_rem_iff.mpr)
      rw[not_not] at hxd
      simp only [hxr, ↓reduceIte] at ind_tmp
      have ⟨xd, Dxd, yd, Dyd, ydFxd⟩:=ind_tmp
      have hxdb : xd ∉ bGd := (Dxd ▸ hxb) ∘ patchG.disk_mem_border_iff.mpr
      have hfi := patchG.disk_face_morph _ hxdb
      have hfxd : face x ∈ patchG.disk := by{
        rw[← Dxd, ← hfi]
        simp
      }
      cases em (face x ∈ patchG.rem) with
      | inl hfxr => {
        simp only [hfxr, ↓reduceIte] at ih'
        have ydFxd' : Gd.cface _ _ := ydFxd.tail rfl
        have hfxb : face x ∈ patchG.border := by{simp[← patchG.disk_inter_rem, hfxd, hfxr]}
        rw[← Dxd, ← hfi, disk_mem_border_iff] at hfxb
        apply ih'
        rw[← Dxd, ← hfi, ← Dyd]
        congr
        apply (patchG.disk_border_cface_unique ?_ ydFxd').mp hfxb
        exact patchG.border_antisymm_disk.mp ⟨_, Dyd.symm⟩
      }
      | inr hfxr => {
        simp only [hfxr, ↓reduceIte] at ih'
        apply ih'
        unfold cFdr
        rw[← Dxd, ← hfi, ← Dyd]
        simp only [patchG.disk_hom_injective.eq_iff, exists_eq_left]
        apply ydFxd.tail rfl
      }
    }
  }
}
theorem rem_cface_iff {xr yr : αr} : Gr.cface xr yr ↔ G.cface (hr xr) (hr yr) :=
  ⟨patchG.cface_of_rem_cface, patchG.rem_cface_of_cface⟩

theorem rem_cedge_close : ∀x ∈ patchG.rem, ∀y, G.cedge x y → y ∈ patchG.rem := by{
  intro x hx y hxy
  rw[cedge, funReflTransGen_iff_iterate] at hxy
  have ⟨n, hnxy⟩ := hxy; clear hxy
  rw[rem, Set.mem_setOf] at hx
  rw[rem, Set.mem_setOf]
  have ⟨xr, hxr⟩:=hx
  clear hx
  rw[← hnxy, ← hxr]
  use edge^[n] xr
  induction n generalizing y with
  | zero => simp
  | succ n' ih => {
    specialize ih (edge^[n'] x) rfl
    rw[iterate_succ_apply', patchG.rem_edge_morph, ih, iterate_succ_apply']
  }
}
theorem disk_cnode_close : ∀x ∈ patchG.disk, ∀y, G.cnode x y → y ∈ patchG.disk := by{
  intro x hx y hxy
  rw[cnode, funReflTransGen_iff_iterate] at hxy
  have ⟨n, hnxy⟩ := hxy; clear hxy
  rw[disk, Set.mem_setOf] at hx
  rw[disk, Set.mem_setOf]
  have ⟨xd, hxd⟩:=hx
  clear hx
  rw[← hnxy, ← hxd]
  use node^[n] xd
  induction n generalizing y with
  | zero => simp
  | succ n' ih => {
    specialize ih (node^[n'] x) rfl
    rw[iterate_succ_apply', patchG.disk_node_morph, ih, iterate_succ_apply']
  }
}

abbrev outer := {x : α | ∃y ∈ patchG.rem, G.cface y x}
theorem outer_cface_close : ∀x ∈ patchG.outer, ∀y, G.cface x y → y ∈ patchG.outer := by{
  intro x ⟨z, hz, hzx⟩ y hxy
  exact ⟨z, hz, hzx.trans hxy⟩
}
theorem outerC_cface_close : ∀x ∉ patchG.outer, ∀y, G.cface x y → y ∉ patchG.outer := by{
  intro x hx y hxy
  revert hx
  rw[not_imp_not]
  intro hy
  apply patchG.outer_cface_close _ hy
  apply G.cface_equivalence.symm
  exact hxy
}
theorem rem_subset_outer : patchG.rem ⊆ patchG.outer := by{
  intro x hx
  rw[rem, Set.mem_setOf] at hx
  have ⟨xr, hxr⟩:=hx
  use x
  constructor
  · use xr
  · apply funReflTransGen.refl
}
theorem outerC_subset_disk : patchG.outerᶜ ⊆ patchG.disk := by{
  intro x hx
  rw[Set.mem_compl_iff] at hx
  rw[mem_disk_iff_rem]
  left
  intro hx'
  have hx'' := patchG.rem_subset_outer hx'
  contradiction
}
theorem border_subset_outer : patchG.border ⊆ patchG.outer :=
  patchG.border_subset_rem.trans patchG.rem_subset_outer
theorem outerC_subset_disk_diff_border : patchG.outerᶜ ⊆ patchG.disk \ patchG.border := by{
  intro x hx
  rw[Set.mem_diff]
  apply And.intro (patchG.outerC_subset_disk hx)
  revert hx; rw[Set.mem_compl_iff, not_imp_not]
  apply border_subset_outer
}

abbrev borderFband (_ : Patch G Gd Gr hd hr bGd bGr) := Gd.fband bGd
abbrev borderFbandComplType := {x // x ∉ patchG.borderFband}
@[inline] instance borderFbandComplType.instFintype : Fintype patchG.borderFbandComplType :=
  Subtype.fintype (· ∉ patchG.borderFband)

theorem mem_borderFband_iff {xd : αd} : xd ∈ patchG.borderFband ↔ hd xd ∈ patchG.outer := by{
  constructor
  · -- 正向：xd ∈ borderFband ⇒ hd xd ∈ outer
    rw[mem_fband_iff]
    intro ⟨zd, hzd, hxdzd⟩
    have h := patchG.cface_of_disk_cface hxdzd
    have hzdb := patchG.disk_mem_border_iff.mpr hzd
    rw [mem_border_iff_rem] at hzdb
    rw [outer, Set.mem_setOf]
    use hd zd
    constructor
    · exact patchG.border_subset_rem (patchG.mem_border_iff_rem.mpr hzdb)
    · exact G.cface_equivalence.symm h
  · -- 反向：hd xd ∈ outer ⇒ xd ∈ borderFband
    intro hxd_outer
    rw [outer, Set.mem_setOf] at hxd_outer
    rcases hxd_outer with ⟨y, hyr, hyxd⟩
    rw [rem, Set.mem_setOf] at hyr
    rcases hyr with ⟨yr, hyr⟩
    rw [← hyr] at hyxd
    -- 现在有 G.cface (hd xd) (hr yr)，对称得 cface (hd xd) y
    have h := G.cface_equivalence.symm hyxd
    rw [cface, funReflTransGen_iff_iterate] at h
    rcases h with ⟨n, hn⟩
    rw[mem_fband_iff, cface]
    simp only [funReflTransGen_iff_iterate]
    simp only [↓existsAndEq, and_true]
    -- 反证法：假设对任意 k ≤ n，face^k xd ∉ bGd
    by_contra h_not
    -- 具体否定：存在某个 k≤n 使 face^k xd ∈ bGd
    push_neg at h_not
    have h_not' : ∀ k, k ≤ n → Gd.face^[k] xd ∉ bGd := fun k hk => h_not k
    -- 归纳证明：对任意 k ≤ n，G.face^k (hd xd) = hd (Gd.face^k xd)
    have H : ∀ k, k ≤ n → G.face^[k] (hd xd) = hd (Gd.face^[k] xd) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' := Nat.le_of_succ_le hk
        specialize ih hk'
        rw [iterate_succ_apply', ih, ← patchG.disk_face_morph]
        · rw[← iterate_succ_apply' Gd.face]
        · exact h_not' k hk'  -- 确保 face^k xd 不在边界，才能使用 disk_face_morph
    -- 取 k = n
    specialize H n (le_refl n)
    rw [hn] at H
    -- 现在有 hr yr = hd (Gd.face^n xd)，所以 hr yr 同时在 disk 和 rem 中
    have h_disk : hd (Gd.face^[n] xd) ∈ patchG.disk := by use Gd.face^[n] xd
    rw [← H] at h_disk
    have h_rem := hyr
    -- hr yr ∈ disk ∩ rem = border
    have h_border := patchG.disk_inter_rem' h_disk (by{simp})
    rw [H, mem_border_iff_disk, List.mem_map_of_injective patchG.disk_hom_injective] at h_border
    -- 于是 face^n xd ∈ bGd，与假设矛盾
    exact h_not' n (le_refl n) h_border
}

theorem outerC_face_morph : ∀xd, hd xd ∉ patchG.outer → hd (face xd) = face (hd xd) := by{
  intro xd hxd
  have ⟨hxd', hxb⟩ := patchG.outerC_subset_disk_diff_border hxd
  rw[disk_mem_border_iff] at hxb
  apply patchG.disk_face_morph _ hxb
}

theorem disk_cface_iff_of_mem_outerC {xd yd : αd} (hxdoc : hd xd ∉ patchG.outer)
  : Gd.cface xd yd ↔ G.cface (hd xd) (hd yd) := by{
    have ih : AdjunctionOn hd (fromFun face) (fromFun face) patchG.outerᶜ := by{
      apply adjunctionOn_of_strict
      · exact patchG.outerC_cface_close
      · exact ⟨fun _ _ => G.cface_equivalence.symm⟩
      · exact ⟨fun _ _ => Gd.cface_equivalence.symm⟩
      · exact patchG.disk_hom_injective
      · intro y; apply patchG.outerC_subset_disk
      · {
        intro x y hx
        simp only [fromFun, ← patchG.outerC_face_morph _ hx, patchG.disk_hom_injective.eq_iff]
      }
    }
    exact ih.functor xd yd hxdoc
  }

theorem borderFband_face_close
: ∀x ∈ patchG.borderFband, ∀y, Gd.cface x y → y ∈ patchG.borderFband
:= by{
  intro x hx y hxy
  simp only [borderFband, fband, List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq]
  simp only [borderFband, fband, List.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at hx
  have ⟨x', hx', hxx'⟩:=hx
  exact ⟨x', hx', (Gd.cface_equivalence.symm hxy).trans hxx'⟩
}
theorem borderFbandCompl_face_close
: ∀x ∉ patchG.borderFband, ∀y, Gd.cface x y → y ∉ patchG.borderFband
:= by{
  intro x hx y hxy
  revert hx; rw[not_imp_not]; intro hy
  apply patchG.borderFband_face_close _ hy
  apply Gd.cface_equivalence.symm
  exact hxy
}

theorem plain_iff : G.plain ↔ Gd.plainSubset {x | x ∉ bGd} ∧ Gr.plain := by{
  change _ ↔ _ ⊆ _ ∧ _
  rw[Set.setOf_subset_setOf, plain_iff_edge_edge, plain_iff_edge_edge]
  simp only [minimalPeriod_eq_two_iff]
  constructor
  · {
    intro h
    constructor
    · {
      intro x hx
      specialize h (hd x)
      rw[← patchG.disk_edge_morph _ hx, patchG.disk_hom_injective.ne_iff, ← patchG.disk_edge_morph,
      patchG.disk_hom_injective.eq_iff] at h
      · exact h
      revert hx; rw[not_imp_not]
      intro hx
      rw[← patchG.disk_border_cedge_close hx]
      apply Gd.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      intro x
      specialize h (hr x)
      rw[← patchG.rem_edge_morph, patchG.rem_hom_injective.ne_iff, ← patchG.rem_edge_morph,
      patchG.rem_hom_injective.eq_iff] at h
      exact h
    }
  }
  · {
    intro ⟨hd, hr⟩ x
    rcases patchG.disk_not_border_rem_hom_surj x with ⟨x', hx', hx'x⟩ | ⟨x', hx'⟩
    · {
      specialize hd _ hx'
      rw[← hx'x, ← patchG.disk_edge_morph _ hx', patchG.disk_hom_injective.ne_iff]
      refine ⟨?_, hd.right⟩
      rw[← patchG.disk_edge_morph, hd.left]
      revert hx'; rw[not_imp_not]
      intro hx
      rw[← patchG.disk_border_cedge_close hx]
      apply Gd.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    · {
      specialize hr x'
      rw[← hx', ← patchG.rem_edge_morph, patchG.rem_hom_injective.ne_iff, ← patchG.rem_edge_morph,
      patchG.rem_hom_injective.eq_iff]
      exact hr
    }
  }
}

theorem cubic_iff : G.cubic ↔ Gd.cubic ∧ Gr.cubicSubset {x | x ∉ bGr} := by{
  change _ ↔ _ ∧ _ ⊆ _
  simp only [Set.setOf_subset_setOf, cubic_iff_period_three, minimalPeriod_eq_three_iff]
  constructor
  · {
    intro h
    constructor
    · {
      intro x
      specialize h (hd x)
      rw[← patchG.disk_node_morph, patchG.disk_hom_injective.ne_iff, ← patchG.disk_node_morph,
      ← patchG.disk_node_morph, patchG.disk_hom_injective.eq_iff] at h
      exact h
    }
    · {
      intro x hx
      specialize h (hr x)
      rw[← patchG.rem_node_morph _ hx, patchG.rem_hom_injective.ne_iff, ← patchG.rem_node_morph,
      ← patchG.rem_node_morph, patchG.rem_hom_injective.eq_iff] at h
      · exact h
      · revert hx; rw[not_imp_not]
        intro hx
        rw[← patchG.rem_border_cnode_close hx]
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.tail (b:=node x)
        · apply funReflTransGen.single
        · rfl
      · revert hx; rw[not_imp_not]
        intro hx
        rw[← patchG.rem_border_cnode_close hx]
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.single
    }
  }
  · {
    intro ⟨hd, hr⟩ x
    rcases patchG.disk_rem_not_border_hom_surj x with ⟨x', hx'⟩ | ⟨x', hx', hx'x⟩
    · {
      specialize hd x'
      rw[← hx', ← patchG.disk_node_morph, patchG.disk_hom_injective.ne_iff,
      ← patchG.disk_node_morph, ← patchG.disk_node_morph, patchG.disk_hom_injective.eq_iff]
      exact hd
    }
    · {
      specialize hr _ hx'
      rw[← hx'x, ← patchG.rem_node_morph _ hx', patchG.rem_hom_injective.ne_iff]
      refine ⟨?_, hr.right⟩
      rw[← patchG.rem_node_morph]
      · {
        rw[← patchG.rem_node_morph, hr.left]
        revert hx'; rw[not_imp_not]
        intro hx'
        rw[← patchG.rem_border_cnode_close hx']
        apply Gr.cnode_equivalence.symm
        apply funReflTransGen.tail (b:=node x')
        · apply funReflTransGen.single
        · rfl
      }
      revert hx'; rw[not_imp_not]
      intro hx'
      rw[← patchG.rem_border_cnode_close hx']
      apply Gr.cnode_equivalence.symm
      apply funReflTransGen.single
    }
  }
}
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

end Patch

end Hypermap
