import FourColorTheorem.RealPlane.Coloring
import FourColorTheorem.ErdosCompactness

namespace RealPlane
namespace Map
abbrev CoveredPoint (m : Map) := {p : Point // m.cover p}
abbrev CoveredPointMap (m : Map) : CoveredPoint m → CoveredPoint m → Prop
  := InvImage m Subtype.val
theorem CoveredPointMap.instEquivalence {m : Map} [IsPlainMap m]
  : Equivalence (CoveredPointMap m) where
  symm := Map.symm
  trans := Map.trans
  refl := by{
    intro ⟨x, hx⟩
    simp only [CoveredPointMap, InvImage]
    apply hx
  }
abbrev CoveredPointSetoid (m : Map) [IsPlainMap m] : Setoid (CoveredPoint m)
  := Setoid.mk (CoveredPointMap m) CoveredPointMap.instEquivalence
abbrev CoveredPointQuotient (m : Map) [IsPlainMap m] := Quotient (CoveredPointSetoid m)

namespace CoveredPointQuotient

def adjacent (m : Map) [IsPlainMap m]
  : CoveredPointQuotient m → CoveredPointQuotient m → Prop :=
  Quotient.lift₂ (fun a b => m.adjacent a b)
    (by
      intro ⟨a, ha⟩ ⟨a', ha'⟩ ⟨b, hb⟩ ⟨b', hb'⟩ haa' hbb'
      change CoveredPointMap m _ _ at haa' hbb'
      simp only [CoveredPointMap, InvImage] at haa' hbb'
      simp only [eq_iff_iff]
      have eq_ab : m a = m b := Map.eq_of_rel haa'
      have eq_ab' : m a' = m b' := Map.eq_of_rel hbb'
      unfold Map.adjacent
      rw[eq_ab]
      change ¬m _ _ ∧ _ ↔ _
      rw[Map.comm (m:=m), eq_ab', Map.comm (m:=m)]
      apply and_congr_right'
      rw[Map.boundary, eq_ab, eq_ab']
      rfl
    )
theorem adjacent_symm {m : Map} [IsPlainMap m] : Symmetric (adjacent m) := by{
  intro a b
  rw[←Quotient.out_eq a, ←Quotient.out_eq b]
  unfold adjacent
  generalize ha : a.out = a'
  generalize hb : b.out = b'
  simp only [Map.adjacent, Quotient.lift_mk, and_imp]
  intro (h0 : ¬m _ _) h1
  rw[Map.comm (m:=m)]
  apply And.intro h0
  rw[Map.boundary] at *
  rw[Set.inter_comm]
  exact h1
}
theorem adjacent_irrefl {m : Map} [IsPlainMap m] : Std.Irrefl (adjacent m) := ⟨by{
  intro a
  rw[←Quotient.out_eq a]
  generalize a.out = a'
  let ⟨a'', (ha' : m a'' a'')⟩:=a'
  simp only [adjacent, Quotient.lift_mk, Map.adjacent, not_and]
  change ¬m a'' a'' → _
  simp[ha']
}⟩
end CoveredPointQuotient

def simpleGraph (m : Map) [IsPlainMap m] : SimpleGraph (CoveredPointQuotient m) where
  Adj := CoveredPointQuotient.adjacent m
  symm := CoveredPointQuotient.adjacent_symm
  loopless := CoveredPointQuotient.adjacent_irrefl

theorem simpleGraph_colorable_iff {m : Map} [IsPlainMap m] {n : ℕ}
: m.simpleGraph.Colorable n ↔ m.colorable_with n := by{
  classical
  unfold colorable_with
  constructor
  · {
    intro ⟨f, hk1⟩
    simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj, ne_eq] at hk1
    let k : Map := fun z1 z2 =>
      if h1 : m.cover z1 then
        if h2 : m.cover z2 then
          f ⟦⟨z1, h1⟩⟧ = f ⟦⟨z2, h2⟩⟧
        else
          False
      else
        False
    use k
    have hkp : IsPlainMap k := by{
      apply IsPlainMap.mk
      · {
        intro p1 p2 hk
        simp only [dite_else_false, k] at *
        aesop
      }
      · {
        intro p1 p2 p3 hk1 hk2
        simp only [dite_else_false, k] at *
        aesop
      }
    }
    have hkc : k.cover = m.cover := by{
      ext z
      change k z z ↔ m z z
      simp[k]; rfl
    }
    constructor
    · {
      apply IsColoringMap.mk
      · assumption
      · {
        intro z (hz : k z z)
        unfold k at hz
        simp only [dite_eq_ite, if_false_right, and_true, ite_then_self, imp_false,
          Decidable.not_not] at hz
        exact hz
      }
      · {
        intro z1 z2 (hz12 : m z1 z2)
        change k _ _
        unfold k
        simp only [cover_of_rel_left hz12, cover_of_rel_right hz12, ↓reduceDIte]
        congr 1
        rw[Quotient.eq]
        change m _ _
        simpa
      }
      · {
        intro p1 p2 hp12
        unfold k
        simp only [cover_of_adjacent_left hp12, ↓reduceDIte, cover_of_adjacent_right hp12]
        apply hk1
        unfold simpleGraph
        simp only
        simpa [CoveredPointQuotient.adjacent]
      }
    }
    · {
      simp only [at_most_regions_iff]
      simp only [hkc]
      let f' : Fin n → Point :=
        fun i => if h : ∃p : m.CoveredPoint, f ⟦p⟧ = i
          then (Classical.choose h).val
          else ⟨0, 0⟩
      use f'
      intro p hp
      use f ⟦⟨p, hp⟩⟧
      simp only [f']
      rw[dif_pos ⟨⟨p, hp⟩, rfl⟩]
      have hp' := Classical.choose_spec (⟨⟨p, hp⟩, rfl⟩ : ∃ p_1, f ⟦p_1⟧ = f ⟦⟨p, hp⟩⟧)
      unfold k
      simpa[hp, (Classical.choose (⟨⟨p, hp⟩, rfl⟩ : ∃ p_1, f ⟦p_1⟧ = f ⟦⟨p, hp⟩⟧)).prop]
    }
  }
  · {
    simp only [at_most_regions_iff]
    intro h
    rcases h with ⟨k, hk, ⟨f, hf⟩⟩
    have h_exist : ∀ (p : CoveredPointQuotient m), ∃ i, k (f i) p.out.val :=
      fun p => hf p.out.val (hk.coloring_consistent p.out.val p.out.prop)
    let f' : CoveredPointQuotient m → Fin n := fun p =>
      @Classical.choose (Fin n) (fun i => k (f i) p.out.val) (h_exist p)
    exact ⟨{
      toFun := f'
      map_rel' := by
        intro a b hab
        simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj, ne_eq]
        have ha : k (f (f' a)) a.out.val :=
          @Classical.choose_spec (Fin n) (fun i => k (f i) a.out.val) (h_exist a)
        have hb : k (f (f' b)) b.out.val :=
          @Classical.choose_spec (Fin n) (fun i => k (f i) b.out.val) (h_exist b)
        intro h_eq
        have ha' : k (f (f' b)) a.out.val := h_eq ▸ ha
        rw[@comm _ hk.coloring_plain] at ha'
        have h_trans := @trans _ hk.coloring_plain _ _ _ ha' hb
        rw [← Quotient.out_eq a, ← Quotient.out_eq b] at hab
        simp only [simpleGraph, CoveredPointQuotient.adjacent, Quotient.lift₂_mk] at hab
        exact hk.coloring_adjacent hab h_trans
    }⟩
  }
}

noncomputable def finiteSubmap (m : Map) [IsPlainMap m] (s : Finset m.CoveredPointQuotient) : Map :=
  fun p => by{
    classical
    exact if hp : m.cover p then if ⟦⟨p, hp⟩⟧ ∈ s then m p else fun _ => False else fun _ => False
  }

theorem finiteSubmap_submap {m : Map} [IsPlainMap m] {s : Finset m.CoveredPointQuotient}
  : finiteSubmap m s ≤ m := by{
  intro z y
  change m.finiteSubmap _ _ _ → m z _
  simp only [finiteSubmap]
  split_ifs <;> simp
}

instance finiteSubmap_plain {m : Map} [IsPlainMap m] {s : Finset m.CoveredPointQuotient}
: IsPlainMap (finiteSubmap m s) := by{
  constructor
  · {
    intro p1 p2 hp12
    simp only [finiteSubmap] at *
    split_ifs at hp12 <;> try contradiction
    simp only [cover_of_rel_right hp12, dite_true]
    rw[if_pos]
    · rwa[@comm m]
    apply (Eq.mp · (by assumption : ⟦⟨p1, _⟩⟧ ∈ s))
    congr 1
    rw[Quotient.eq]
    change m _ _
    simpa
  }
  · {
    intro p1 p2 p3 hp12 hp23
    simp only [finiteSubmap] at *
    split_ifs at hp12 <;> try contradiction
    split_ifs at hp23 <;> try contradiction
    simp only [cover_of_rel_left hp12, dite_true]
    simp only [if_pos (by assumption : ⟦⟨p1, _⟩⟧ ∈ s)]
    exact trans hp12 hp23
  }
}
theorem finiteSubmap_iff {m : Map} [IsPlainMap m] {s : Finset m.CoveredPointQuotient}
{z1 z2 : Point} : m.finiteSubmap s z1 z2 ↔
  (∃h1 : m.cover z1, ⟦⟨z1, h1⟩⟧ ∈ s) ∧ (∃h2 : m.cover z2, ⟦⟨z2, h2⟩⟧ ∈ s) ∧ m z1 z2 := by{
  unfold finiteSubmap
  rcases em (m.cover z1) with h1 | h1
  · {
    simp only [h1, ↓reduceDIte, exists_true_left]
    rcases em (⟦⟨z1, h1⟩⟧ ∈ s) with h1s | h1s
    · {
      simp only [h1s, ↓reduceIte, true_and, iff_and_self]
      intro h12
      simp only [cover_of_rel_right h12, exists_true_left]
      apply Eq.mp ?_ h1s
      congr 1
      rw[Quotient.eq]
      change m _ _
      simpa
    }
    · simp[h1s]
  }
  · simp[h1]
}
theorem finiteSubmap_cover_iff {m : Map} [IsPlainMap m] {s : Finset m.CoveredPointQuotient}
  {p : Point} : (m.finiteSubmap s).cover p ↔ ∃h : m.cover p, ⟦⟨p, h⟩⟧ ∈ s := by{
  change m.finiteSubmap _ _ _ ↔ _
  rw[finiteSubmap_iff, ← and_assoc, and_self]
  apply Iff.intro And.left
  intro ⟨h0, h1⟩
  simp only [h1, h0, exists_const, true_and]
  exact h0
}

theorem finiteSubmap_eq_of_mem {m : Map} [IsPlainMap m] {s : Finset m.CoveredPointQuotient}
{p : Point} (hp : m.cover p) (hp' : ⟦⟨p, hp⟩⟧ ∈ s) :
  m.finiteSubmap s p = m p := by{
  symm
  ext q
  change m p q ↔ m.finiteSubmap s p q
  rw[finiteSubmap_iff]
  rw[← and_assoc]
  simp only [iff_and_self]
  intro mpq
  simp only [hp', cover_of_rel_left mpq, exists_const, cover_of_rel_right mpq, exists_true_left,
    true_and]
  apply Eq.mp ?_ hp'
  congr 1
  rw[Quotient.eq]
  change m _ _
  simpa
}

lemma finiteSubmap_open {m : Map} [IsSimpleMap m] {s : Finset m.CoveredPointQuotient}
: ∀p, IsOpen (finiteSubmap m s p) := by{
  intro p
  simp only [Region.isOpen_iff_isOpen']
  intro q hq
  have h := IsSimpleMap.map_open (m:=m) p
  simp only [Region.isOpen_iff_isOpen'] at h
  change m.finiteSubmap s p q at hq
  rw[finiteSubmap_iff] at hq
  specialize h q hq.2.2
  have ⟨u, hu⟩ := h
  use u
  apply And.intro hu.1
  apply Eq.mp ?_ hu.2
  congr 1
  symm
  apply finiteSubmap_eq_of_mem (cover_of_rel_left hq.2.2)
  have ⟨_, hp'⟩ := hq.1
  exact hp'
}

instance finiteSubmap_simple {m : Map} [IsSimpleMap m] {s : Finset m.CoveredPointQuotient}
: IsSimpleMap (finiteSubmap m s) := by{
  apply IsSimpleMap.mk
  · exact finiteSubmap_open
  · {
    intro p
    rw[Region.isPreconnected_iff_connected'_of_isOpen]
    · {
      intro R1 R2 hR1 hR2 hR12 hmR1 hmR2
      have h : ∃h : m.cover p, ⟦⟨p, h⟩⟧ ∈ s := by{
        have ⟨q, hq⟩ := hmR1
        rw[Set.mem_inter_iff] at hq
        have hq' : m.finiteSubmap s p q := hq.1
        rw[finiteSubmap_iff] at hq'
        exact hq'.1
      }
      have h : m.finiteSubmap s p = m p := by{
        have ⟨h0, h1⟩ := h
        apply finiteSubmap_eq_of_mem h0 h1
      }
      rw[h] at hR12 hmR1 hmR2
      have h := IsSimpleMap.map_connected (m := m) p
      rw[Region.isPreconnected_iff_connected'_of_isOpen] at h
      · apply h _ _ hR1 hR2 hR12 hmR1 hmR2
      · apply IsSimpleMap.map_open
    }
    · apply finiteSubmap_open
  }
}
instance finiteSubmap_finiteSimple {m : Map} [IsSimpleMap m] {s : Finset m.CoveredPointQuotient}
: IsFiniteSimpleMap (finiteSubmap m s) := by{
  apply IsFiniteSimpleMap.mk
  use s.card
  simp only [at_most_regions_iff]
  let f : Fin s.card → Point := fun i => (s.toList[i]'(by{simp})).out.val
  use f
  intro p hp
  change m.finiteSubmap s p p at hp
  rw[finiteSubmap_iff] at hp
  have ⟨h0, h1⟩ := hp.1
  simp only [finiteSubmap_iff]
  simp only [h1, h0, exists_const, true_and]
  unfold f
  simp only [Fin.getElem_fin, Subtype.coe_eta, Quotient.out_eq, exists_prop]
  simp only [← Finset.mem_toList, List.getElem_mem, and_true]
  simp only [Subtype.prop, true_and]
  rw[← Finset.mem_toList, List.mem_iff_getElem] at h1
  have ⟨i, hi, hig⟩ := h1
  use ⟨i, by{simp at hi; simp[hi]}⟩
  simp only [hig]
  have h := Quotient.mk_out (s := m.CoveredPointSetoid) ⟨p, h0⟩
  exact h
}

noncomputable def finiteSubmap_embedding {m : Map} [IsPlainMap m]
  {s : Finset m.CoveredPointQuotient}
  : (m.finiteSubmap s).CoveredPointQuotient ↪ m.CoveredPointQuotient
  := by{
  classical
  let f : (m.finiteSubmap s).CoveredPointQuotient → m.CoveredPointQuotient :=
    fun q => ⟦⟨q.out.val, by{
      have hq := q.out.prop
      change m.finiteSubmap s _ _ at hq
      rw[finiteSubmap_iff] at hq
      exact hq.2.2
    }⟩⟧
  use f
  intro a b hab
  unfold f at hab
  rw[Quotient.eq] at hab
  change m _ _ at hab
  simp only at hab
  rw[← Quotient.out_eq a, ← Quotient.out_eq b]
  rw[Quotient.eq]
  change m.finiteSubmap s _ _
  rw[finiteSubmap_iff]
  have ha := a.out.prop
  have hb := b.out.prop
  change m.finiteSubmap _ _ _ at ha hb
  rw[finiteSubmap_iff] at ha hb
  simp[ha, hb, hab]
}

theorem finiteSubmap_adj_of_adj {m : Map} [IsPlainMap m]
  {s : Finset m.CoveredPointQuotient} {z1 z2 : Point}
  (h12 : m.adjacent z1 z2) (h1 : ⟦⟨z1, cover_of_adjacent_left h12⟩⟧ ∈ s)
  (h2 : ⟦⟨z2, cover_of_adjacent_right h12⟩⟧ ∈ s)
  : (m.finiteSubmap s).adjacent z1 z2 := by{
  let inst0 : IsPlainMap m := by{assumption}
  let inst1 : IsPlainMap (m.finiteSubmap s) := finiteSubmap_plain
  let inst2 z : IsPlainMap ((m.finiteSubmap s).corner_map z) :=
    cornermap_plain
  unfold adjacent
  constructor
  · {
    rw[finiteSubmap_iff]
    push_neg
    simp[h12.1]
  }
  rcases h12.2 with ⟨z, hzc, hzb⟩
  use z
  change _ ∧ _
  constructor
  · {
    rw[mem_not_corner_iff]
    rcases hzc with ⟨f, hf⟩
    use f
    intro p hp
    unfold corner_map at hp
    simp only [cover] at hp
    change z ∈ closure (m.finiteSubmap s p) ∧ (m.finiteSubmap s).cover p at hp
    rw[finiteSubmap_cover_iff] at hp
    rcases hp.2 with ⟨hp0, hp1⟩
    rw[finiteSubmap_eq_of_mem _ hp1] at hp
    specialize hf p (by{
      split_ands
      · exact hp.1
      · exact hp0
    })
    rcases hf with ⟨i, hi, hig⟩
    use i, hi
    apply @symm _ (inst2 z)
    change _ ∧ _
    rw[finiteSubmap_eq_of_mem _ hp1]
    apply And.intro hp.1
    apply @symm
    exact hig.2
  }
  · {
    rw[mem_boundary_iff]
    rw[finiteSubmap_eq_of_mem _ h1, finiteSubmap_eq_of_mem _ h2]
    exact hzb
  }
}

theorem induce_subgraph_finiteSubmap {m : Map} [IsPlainMap m]
  {s : Finset m.CoveredPointQuotient} :
  (m.simpleGraph.induce s).map (Function.Embedding.subtype _)
  ≤ (m.finiteSubmap s).simpleGraph.map (m.finiteSubmap_embedding (s := s)) := by{
  intro u v huv
  rw[SimpleGraph.map_adj] at huv
  have ⟨u', v', hu'v', hu', hv'⟩ := huv
  simp only [SetLike.coe_sort_coe, Function.Embedding.subtype_apply] at hu' hv'
  rw[SimpleGraph.induce_adj] at hu'v'
  simp only [simpleGraph] at hu'v'
  unfold CoveredPointQuotient.adjacent at hu'v'
  rw[hu', hv'] at hu'v'
  rw [← Quotient.out_eq u, ← Quotient.out_eq v, Quotient.lift₂_mk] at hu'v'
  rw[SimpleGraph.map_adj]
  let u'' : (m.finiteSubmap s).CoveredPointQuotient := ⟦⟨u.out.val, by{
    rw[finiteSubmap_cover_iff]
    simp only [Subtype.coe_eta, Quotient.out_eq, cover_of_adjacent_left hu'v', exists_const]
    rw[← hu']
    exact u'.prop
  }⟩⟧
  let v'' : (m.finiteSubmap s).CoveredPointQuotient := ⟦⟨v.out.val, by{
    rw[finiteSubmap_cover_iff]
    simp only [Subtype.coe_eta, Quotient.out_eq, cover_of_adjacent_right hu'v', exists_const]
    rw[← hv']
    exact v'.prop
  }⟩⟧
  have hu'' := Quotient.mk_out (s := (m.finiteSubmap s).CoveredPointSetoid) ⟨u.out.val, by{
    rw[finiteSubmap_cover_iff]
    simp only [Subtype.coe_eta, Quotient.out_eq, cover_of_adjacent_left hu'v', exists_const]
    rw[← hu']
    exact u'.prop
  }⟩
  have hv'' := Quotient.mk_out (s := (m.finiteSubmap s).CoveredPointSetoid) ⟨v.out.val, by{
    rw[finiteSubmap_cover_iff]
    simp only [Subtype.coe_eta, Quotient.out_eq, cover_of_adjacent_right hu'v', exists_const]
    rw[← hv']
    exact v'.prop
  }⟩
  change m.finiteSubmap s u''.out _ at hu''
  change m.finiteSubmap s v''.out _ at hv''
  simp only at hu'' hv''
  use u'', v''
  rw[finiteSubmap_iff] at hu'' hv''
  constructor
  · {
    simp only [simpleGraph, CoveredPointQuotient.adjacent]
    rw[← Quotient.out_eq u'', ← Quotient.out_eq v'', Quotient.lift₂_mk]
    apply finiteSubmap_adj_of_adj
    · {
      rcases hu''.1 with ⟨_, h1⟩
      exact h1
    }
    · {
      rcases hv''.1 with ⟨_, h1⟩
      exact h1
    }
    · {
      rw[congr_adjacent_left_of_rel (symm hu''.2.2)] at hu'v'
      rw[congr_adjacent_right_of_rel (symm hv''.2.2)] at hu'v'
      exact hu'v'
    }
  }
  constructor
  · {
    unfold finiteSubmap_embedding
    simp only [Function.Embedding.coeFn_mk]
    rw[Quotient.mk_eq_iff_out]
    change m _ _
    simp only
    exact hu''.2.2
  }
  · {
    unfold finiteSubmap_embedding
    simp only [Function.Embedding.coeFn_mk]
    rw[Quotient.mk_eq_iff_out]
    change m _ _
    simp only
    exact hv''.2.2
  }
}

theorem compactness {nc : ℕ}
(fin_colorable : finColorable nc) : ∀m : Map, [IsSimpleMap m] → m.colorable_with nc := by{
  intro m hm
  rw[← simpleGraph_colorable_iff, ← SimpleGraph.deBruijn_erdos_iff]
  intro s
  have hnc : nc > 0 := finColorable_pos fin_colorable
  let neznc : NeZero nc := by{simp[neZero_iff]; omega}
  suffices ((SimpleGraph.induce (↑s) m.simpleGraph).map
    (Function.Embedding.subtype _)).Colorable nc by{
    rwa[SimpleGraph.Colorable.induce_iff hnc]
  }
  apply SimpleGraph.Colorable.isSubgraph ?_ induce_subgraph_finiteSubmap
  apply SimpleGraph.Colorable.map
  rw[simpleGraph_colorable_iff]
  apply fin_colorable
}

theorem compactness_iff {nc : ℕ} :
  (∀m : Map, [IsSimpleMap m] → m.colorable_with nc) ↔ finColorable nc := by{
  apply Iff.intro ?_ compactness
  intro ih m inst
  exact ih m
}

end Map
end RealPlane
