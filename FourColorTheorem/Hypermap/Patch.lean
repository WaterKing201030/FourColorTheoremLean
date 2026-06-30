import FourColorTheorem.Hypermap.Walkup

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
theorem mem_border_iff_disk {x : α} : x ∈ patchG.border ↔ x ∈ patchG.diskBorder := by{
  rfl
}
theorem mem_border_disk_iff_rem {x : α} : x ∈ patchG.diskBorder ↔ x ∈ patchG.remBorder := by{
  rw[diskBorder, remBorder, patchG.rem_border_order, List.mem_reverse]
}
theorem mem_border_iff_rem {x : α} : x ∈ patchG.border ↔ x ∈ patchG.remBorder := by{
  rw[← patchG.mem_border_disk_iff_rem, patchG.mem_border_iff_disk]
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
  x ∈ patchG.diskBorder := by{
  have ⟨xd, hxd'⟩:=hxd
  unfold diskBorder
  rw[← hxd', List.mem_map_of_injective patchG.disk_hom_injective]
  rw[← patchG.border_antisymm_disk]
  have ⟨xr, hxr'⟩:=hxr
  exact ⟨xr, hxr'.trans hxd'.symm⟩
}
theorem disk_inter_rem_iff' {x : α} : (∃ xd, hd xd = x) ∧ (∃ xr, hr xr = x) ↔
  x ∈ patchG.diskBorder := by{
  constructor
  · intro ⟨h0, h1⟩; exact patchG.disk_inter_rem' h0 h1
  · {
    intro hxd
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

theorem galois_connect {xd : αd} {xr : αr}
  : hd (Gd.edge xd) = hr xr ↔ hd xd = hr (Gr.node xr) := by{
    rcases em (xd ∈ bGd) with b_xd | b_xd
    · {
      rcases em (xr ∈ bGr) with b_xr | b_xr
      · {
        
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
theorem exists_galois_of_mem_bGd {xd : αd} (hxd : xd ∈ bGd) :
  ∃xr, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by{
    simp only [patchG.galois_connect, and_self]
  }
theorem exists_galois_of_mem_bGr {xr : αr} (hxr : xr ∈ bGr) :
  ∃xd, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by{
    simp only [patchG.galois_connect, and_self]

  }

end Patch

end Hypermap
