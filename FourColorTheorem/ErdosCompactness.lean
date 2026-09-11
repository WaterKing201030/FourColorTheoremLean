import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Compactness.Compact

namespace SimpleGraph

theorem Colorable.induce {V : Type*} {G : SimpleGraph V} {k : ℕ}
  (hG : G.Colorable k) (S : Set V) :
  (G.induce S).Colorable k := by{
  rcases hG with ⟨f, hf⟩
  let f' : ↑S → Fin k := fun a => f a.val
  use f'
  intro a b hab
  simp only [comap_adj, Function.Embedding.subtype_apply] at hab
  specialize hf hab
  simp at hf
  simpa
}

theorem Colorable.induce_iff {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : k > 0)
  (S : Set V) :
  (G.induce S).Colorable k ↔ ((G.induce S).map (Function.Embedding.subtype _)).Colorable k := by{
  let : NeZero k := by{simp[neZero_iff]; omega}
  constructor
  · apply Colorable.map
  intro h
  have ⟨f, hf⟩ := h
  let f' : ↑S → Fin k := fun x => f x.val
  use f'
  intro a b hab
  simp only [comap_adj, Function.Embedding.subtype_apply] at hab
  simp only [completeGraph_eq_top, top_adj, ne_eq] at hf
  simp only [completeGraph_eq_top, top_adj, ne_eq]
  apply hf
  rw[map_adj]
  simpa
}

theorem Colorable.subgraph {V : Type*} {G : SimpleGraph V} {k : ℕ}
  (hG : G.Colorable k) (G' : G.Subgraph) :
  SimpleGraph.Colorable (Subgraph.coe G') k := by{
  have ⟨f, hf⟩ := hG
  let f' : ↑G'.verts → Fin k := fun a => f a.val
  use f'
  intro a b
  simp only [Subgraph.coe_adj, completeGraph_eq_top, top_adj, ne_eq]
  intro hab
  specialize hf (G'.adj_sub hab)
  simp only [completeGraph_eq_top, top_adj, ne_eq] at hf
  exact hf
}

theorem Colorable.isSubgraph {V : Type*} {G G' : SimpleGraph V} {k : ℕ} (hG : G.Colorable k)
  (hGG' : G' ≤ G) : G'.Colorable k := by{
  have ⟨f, hf⟩ := hG
  use f
  intro a b hab
  specialize hGG' hab
  exact hf hGG'
}

def LocallyColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (S : Finset V), (G.induce (S : Set V)).Colorable k

theorem locallyColorable_zero_iff_empty {V : Type*} (G : SimpleGraph V) :
    LocallyColorable G 0 ↔ IsEmpty V := by{
  classical
  constructor
  · {
    intro h
    rw[← not_nonempty_iff]
    intro h'
    let a := h'.some
    specialize h {a}
    simp at h
  }
  · {
    intro hv v
    simp
    simp[Finset.eq_empty_of_isEmpty]
  }
}

def coloringConstraint {V : Type*} (G : SimpleGraph V) (k : ℕ)
  (S : Finset V) : Set (V → Fin k) :=
  { c | ∀ u v, u ∈ S → v ∈ S → G.Adj u v → c u ≠ c v }

theorem isClosed_coloringConstraint {V : Type*} {G : SimpleGraph V} {k : ℕ}
  {S : Finset V} :
    IsClosed (coloringConstraint G k S) := by{
  have h_eq : coloringConstraint G k S =
      ⋂ (u ∈ S) (v ∈ S) (_ : G.Adj u v), { c | c u ≠ c v } := by{
    ext c
    simp only [coloringConstraint, ne_eq, Set.mem_setOf_eq, Set.mem_iInter]
    aesop
  }
  rw [h_eq]
  refine isClosed_biInter fun u _ => isClosed_biInter fun v _ =>
    isClosed_sInter ?_
  simp only [ne_eq, Set.mem_range, exists_prop, and_imp, forall_apply_eq_imp_iff]
  intro _
  have h_map : Continuous (fun c : V → Fin k => (c u, c v)) :=
    (continuous_apply u).prodMk (continuous_apply v)
  have h_closed_diag : IsClosed { p : Fin k × Fin k | p.1 ≠ p.2 } :=
    isClosed_discrete _
  exact h_closed_diag.preimage h_map
}

theorem inter_coloringConstraint {V : Type*} [Nonempty V]
  {G : SimpleGraph V} {k : ℕ} (h : LocallyColorable G k)
    (s : Finset (Finset V)) :
    (⋂ x ∈ s, (coloringConstraint G k x)).Nonempty := by{
  classical
  let S_all : Finset V := s.sup id
  obtain ⟨c_ind, hc_ind⟩ := h S_all
  have hk : k > 0 := by{
    rw[gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq]
    intro hk
    rw[hk, locallyColorable_zero_iff_empty, ← not_nonempty_iff] at h
    contradiction
  }
  let c : V → Fin k := fun v =>
    if hv : v ∈ S_all then c_ind ⟨v, hv⟩ else ⟨0, hk⟩
  use c
  simp only [Set.mem_iInter]
  simp only [coloringConstraint, Set.mem_setOf]
  intro S hS u v hu hv hadj
  have hu_all : u ∈ S_all := by{
    unfold S_all
    apply Set.mem_of_subset_of_mem (s₁ := S) ?_ hu
    simp only [SetLike.coe_subset_coe, Finset.le_eq_subset]
    change id S ≤ _
    apply Finset.le_sup hS
  }
  have hv_all : v ∈ S_all := by{
    unfold S_all
    apply Set.mem_of_subset_of_mem (s₁ := S) ?_ hv
    simp only [SetLike.coe_subset_coe, Finset.le_eq_subset]
    change id S ≤ _
    apply Finset.le_sup hS
  }
  have hu_if : c u = c_ind ⟨u, hu_all⟩ := dif_pos hu_all
  have hv_if : c v = c_ind ⟨v, hv_all⟩ := dif_pos hv_all
  rw [hu_if, hv_if]
  apply hc_ind
  simpa
}

theorem deBruijn_erdos' {V : Type*} [Nonempty V]
  {G : SimpleGraph V} {k : ℕ}
  (h : LocallyColorable G k) : G.Colorable k := by{
  classical
  have h_compact : IsCompact (Set.univ : Set (V → Fin k)) := by{
    rw [← Set.pi_univ]
    apply isCompact_univ_pi
    intro i
    exact isCompact_univ
  }
  have h_nonempty : (⋂ (S : Finset V), coloringConstraint G k S).Nonempty := by{
    rw[← Set.univ_inter (⋂ S, G.coloringConstraint k S)]
    apply h_compact.inter_iInter_nonempty (coloringConstraint G k)
    · {
      intro S
      exact isClosed_coloringConstraint
    }
    · {
      intro s
      rw[Set.univ_inter]
      exact inter_coloringConstraint h _
    }
  }
  rcases h_nonempty with ⟨c, hc⟩
  simp only [Set.mem_iInter] at hc
  use c
  intro u v hadj
  have h_c := hc {u, v}
  exact h_c u v (Finset.mem_insert_self u {v})
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) hadj
}

theorem deBruijn_erdos {V : Type*} {G : SimpleGraph V} {k : ℕ}
  (h : LocallyColorable G k) : G.Colorable k := by{
  rcases isEmpty_or_nonempty V with instV | instV
  · simp[Colorable.of_isEmpty]
  · apply deBruijn_erdos' h
}

theorem deBruijn_erdos_iff {V : Type*} {G : SimpleGraph V} {k : ℕ}
  : G.LocallyColorable k ↔ G.Colorable k := by{
  apply Iff.intro deBruijn_erdos
  intro h s
  apply h.induce
}

end SimpleGraph
