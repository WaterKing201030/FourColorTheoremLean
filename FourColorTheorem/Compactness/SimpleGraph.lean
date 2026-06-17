import FourColorTheorem.Reals.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace GraphColorModel

open RealPlane

abbrev CoveredPoint (m : Map) := {p : Point // m.cover p}
abbrev CoveredPointMap (m : Map) : CoveredPoint m → CoveredPoint m → Prop
  := InvImage m Subtype.val
theorem CoveredPointMap.instEquivalence {m : Map} [IsPlainMap m]
  : Equivalence (CoveredPointMap m) where
  symm := map_symm
  trans := map_trans'
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
      have eq_ab : m a = m b := eq_of_rel haa'
      have eq_ab' : m a' = m b' := eq_of_rel hbb'
      unfold Map.adjacent
      rw[eq_ab]
      change ¬m _ _ ∧ _ ↔ _
      rw[map_comm (m:=m), eq_ab', map_comm (m:=m)]
      apply and_congr_right'
      rw[Map.border, eq_ab, eq_ab']
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
  change ¬m _ _ ∧ _
  rw[map_comm (m:=m)]
  apply And.intro h0
  rw[Map.border] at *
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

theorem finite_of_at_most_regions {m : Map} [IsPlainMap m] {n : ℕ} (hm : m.at_most_regions n)
  : Finite (CoveredPointQuotient m) := by{
    obtain ⟨f, hf⟩ := hm  -- f : Fin n → Point, ∀ p, m.cover p → ∃ i, m (f i) p

    -- 定义从商集到 Fin n 的映射 ψ
    let ψ : CoveredPointQuotient m → Fin n := fun x =>
      let p := Quotient.out x  -- p : CoveredPoint m，其覆盖性由类型保证
      Classical.choose (hf p.val p.property)  -- 由 hf 得到 i 满足 m (f i) p.val

    -- 证明 ψ 是单射
    have ψ_inj : Function.Injective ψ := by{
      intro x y hxy
      have hx := Classical.choose_spec (hf (Quotient.out x).val (Quotient.out x).property)
      have hy := Classical.choose_spec (hf (Quotient.out y).val (Quotient.out y).property)
      -- 此时有 m (f i) (Quotient.out x).val 和 m (f i) (Quotient.out y).val
      generalize hix : Classical.choose (hf (Quotient.out x).val (Quotient.out x).property) = ix
      generalize hiy : Classical.choose (hf (Quotient.out y).val (Quotient.out y).property) = iy
      rw[hix] at hx
      rw[hiy] at hy
      unfold ψ at hxy
      simp only [hix, hiy] at hxy
      have hxy := map_trans' (map_symm hx) (hxy ▸ hy)
      rw[← Quotient.out_eq x, ← Quotient.out_eq y]
      rw[Quotient.eq_iff_equiv]
      exact hxy
    }
    -- 单射给出有限性（Fin n 是有限集）
    exact Finite.of_injective ψ ψ_inj
  }
@[reducible] noncomputable def fintype_of_at_most_regions {m : Map} [IsPlainMap m] {n : ℕ}
  (hm : m.at_most_regions n) : Fintype (CoveredPointQuotient m) :=
  @Fintype.ofFinite (CoveredPointQuotient m) (finite_of_at_most_regions hm)
theorem card_le_of_at_most_regions {m : Map} [IsPlainMap m] {n : ℕ} (hm : m.at_most_regions n)
  : @Fintype.card (CoveredPointQuotient m) (fintype_of_at_most_regions hm) ≤ n := by{
    let := fintype_of_at_most_regions hm
    obtain ⟨f, hf⟩ := hm  -- f : Fin n → Point, ∀ p, m.cover p → ∃ i, m (f i) p
    -- 定义从商集到 Fin n 的映射 ψ
    let ψ : CoveredPointQuotient m → Fin n := fun x =>
      let p := Quotient.out x  -- p : CoveredPoint m，其覆盖性由类型保证
      Classical.choose (hf p.val p.property)  -- 由 hf 得到 i 满足 m (f i) p.val
    -- 证明 ψ 是单射
    have ψ_inj : Function.Injective ψ := by{
      intro x y hxy
      have hx := Classical.choose_spec (hf (Quotient.out x).val (Quotient.out x).property)
      have hy := Classical.choose_spec (hf (Quotient.out y).val (Quotient.out y).property)
      -- 此时有 m (f i) (Quotient.out x).val 和 m (f i) (Quotient.out y).val
      generalize hix : Classical.choose (hf (Quotient.out x).val (Quotient.out x).property) = ix
      generalize hiy : Classical.choose (hf (Quotient.out y).val (Quotient.out y).property) = iy
      rw[hix] at hx
      rw[hiy] at hy
      unfold ψ at hxy
      simp only [hix, hiy] at hxy
      have hxy := map_trans' (map_symm hx) (hxy ▸ hy)
      rw[← Quotient.out_eq x, ← Quotient.out_eq y]
      rw[Quotient.eq_iff_equiv]
      exact hxy
    }
    -- 基数上界
    have card_le : Fintype.card (CoveredPointQuotient m) ≤ n := by
      have h := Fintype.card_le_of_injective ψ ψ_inj
      simp at h; simp[h]
    exact card_le
  }
theorem at_most_region_of_finite {m : Map} [IsPlainMap m] [Finite (CoveredPointQuotient m)] :
    m.at_most_regions (Nat.card (CoveredPointQuotient m)) := by{
    let : Fintype (CoveredPointQuotient m) := Fintype.ofFinite _
    let f := Finite.equivFin (CoveredPointQuotient m)
    let f' := fun i => (f.symm i).out.val
    use f'
    intro p hp
    let i' := f ⟦⟨p, hp⟩⟧
    use i'
    unfold f' i'
    simp only [Equiv.symm_apply_apply]
    have h := (⟦⟨p, hp⟩⟧ : CoveredPointQuotient m).out_eq
    rw[Quotient.eq_iff_equiv] at h
    exact h
  }

def colorable_with (m : Map) [IsPlainMap m] (n : ℕ) :=
  ∃f : CoveredPointQuotient m → ℕ, (∀p, f p < n) ∧ (∀p p', adjacent m p p' → f p ≠ f p')

theorem colorable_with_iff {m : Map} [IsPlainMap m] {n : ℕ} :
  colorable_with m n ↔ m.colorable_with n := by{
  constructor
  · {
    intro ⟨f, f_ub, f_adj⟩
    classical
    let k : Map := fun p1 p2 =>
      if hmp1 : m.cover p1 then
        if hmp2 : m.cover p2 then
          let p1' : CoveredPointQuotient m := ⟦⟨p1, hmp1⟩⟧
          let p2' : CoveredPointQuotient m := ⟦⟨p2, hmp2⟩⟧
          f p1' = f p2'
        else False
      else False
    use k
    split_ands
    · {
      apply IsColoringMap.mk
      · {
        apply IsPlainMap.mk
        · {
          intro p1 p2 hp1p2
          change k _ _ at *
          simp only [ne_eq, dite_else_false, k] at *
          have ⟨h0, h1, h2⟩:=hp1p2
          simp[h0, h1, h2]
        }
        · {
          intro p1 p2 hp1p2 p3 hp2p3
          change k _ _ at *
          simp only [ne_eq, dite_else_false, k] at *
          have ⟨h0, h1, h2⟩:=hp1p2
          have ⟨_, h3, h4⟩:=hp2p3
          simp[h0, h2, h3, h4]
        }
      }
      · {
        intro p hp
        change k p p at hp
        simp only [dite_else_false, exists_idem, exists_prop, and_true, k] at hp
        exact hp
      }
      · {
        intro p1 p2 hp1p2
        change k p1 p2
        have ⟨hmp1, hmp2⟩:=refl_of_rel hp1p2
        simp only [dite_else_false, hmp2, exists_true_left, hmp1, k]
        congr 1
        rw[Quotient.eq_iff_equiv]
        change CoveredPointMap m _ _
        simp only [CoveredPointMap, InvImage]
        exact hp1p2
      }
      · {
        intro p1 p2 hp1p2
        rcases em' (m.cover p1) with hmp1 | hmp1
        · unfold k; simp[hmp1]
        rcases em' (m.cover p2) with hmp2 | hmp2
        · unfold k; simp[hmp2]
        let p1' : CoveredPointQuotient m := ⟦⟨p1, hmp1⟩⟧
        let p2' : CoveredPointQuotient m := ⟦⟨p2, hmp2⟩⟧
        have hp1p2' : adjacent m p1' p2' := by{
          unfold adjacent p1' p2'
          simp[hp1p2]
        }
        have f_adj' := f_adj _ _ hp1p2'
        simp only [dite_else_false, hmp2, exists_true_left, hmp1, ne_eq, k]
        exact f_adj'
      }
    }
    · {
      rw[Map.at_most_regions_eq_at_most_regions']
      unfold Map.at_most_regions'
      unfold k
      simp only [Map.cover, dite_eq_ite, if_false_right, and_true, ite_then_self, imp_false,
        Decidable.not_not, dite_else_false]
      let f' : ℕ → Point := fun i =>
        if h_choose : ∃p, f p = i then
          (Classical.choose h_choose).out.val
        else
          ⟨0, 0⟩
      use f'
      intro p hmp
      use f ⟦⟨p, hmp⟩⟧
      apply And.intro (by{apply f_ub})
      unfold f'
      simp only [exists_apply_eq_apply, ↓reduceDIte, Subtype.coe_eta, Quotient.out_eq, hmp,
        exists_true_left, exists_prop]
      have h_choose_spec := Classical.choose_spec (⟨_, rfl⟩ : ∃p_1, f p_1 = f ⟦⟨p, hmp⟩⟧)
      simp only [h_choose_spec]
      refine ⟨?_, rfl⟩
      have h:=(Classical.choose (⟨_, rfl⟩ : ∃p_1, f p_1 = f ⟦⟨p, hmp⟩⟧)).out.property
      exact h
    }
  }
  · {
    unfold Map.colorable_with
    rw[Map.at_most_regions_eq_at_most_regions']
    intro ⟨k, ⟨hkP, hkm, hmk, hkadj⟩, ⟨f, hkf⟩⟩
    classical
    let f' : CoveredPointQuotient m → ℕ :=
      fun q => let ⟨p, hp⟩:=q.out
        Classical.choose (hkf p (hmk _ hp))
    use f'
    constructor
    · {
      intro q
      unfold f'
      match q.out with | ⟨p, hp⟩ => {
        simp only [gt_iff_lt]
        have h:=Classical.choose_spec (hkf p (hmk _ hp))
        exact h.left
      }
    }
    · {
      intro q q' hqq'
      rw[← q.out_eq, ← q'.out_eq] at hqq'
      unfold adjacent at hqq'
      rw[Quotient.lift₂_mk] at hqq'
      unfold f'
      match hq:q.out, hq':q'.out with | ⟨p, hp⟩, ⟨p', hp'⟩ => {
        simp only [ne_eq]
        simp only [hq, hq'] at hqq'
        have hkadj':=hkadj hqq'
        intro h
        have h0:=(Classical.choose_spec (hkf p (hmk _ hp))).right
        have h1:=(Classical.choose_spec (hkf p' (hmk _ hp'))).right
        rw[h] at h0
        have h2 := map_trans' (map_symm h0) h1
        contradiction
      }
    }
  }
}

def finColorable (nc : ℕ) :=
  ∀m, [IsSimpleMap m] → Finite (CoveredPointQuotient m) → colorable_with m nc

theorem finColorable_iff {nc : ℕ} :
  finColorable nc ↔ RealPlane.finColorable nc := by{
    constructor
    · {
      intro h m hm
      rw[← colorable_with_iff]
      apply h
      have ⟨_, h'⟩:=hm.map_finite
      apply finite_of_at_most_regions h'
    }
    · {
      intro h m ms md
      rw[RealPlane.finColorable] at h
      rw[colorable_with_iff]
      apply h
      apply IsFiniteSimpleMap.mk
      have h' := at_most_region_of_finite (m:=m)
      exact ⟨_, h'⟩
    }
  }

def simpleGraph (m : Map) [IsPlainMap m] : SimpleGraph (CoveredPointQuotient m) where
  Adj := adjacent m
  symm := adjacent_symm
  loopless := adjacent_irrefl

end CoveredPointQuotient

end GraphColorModel
