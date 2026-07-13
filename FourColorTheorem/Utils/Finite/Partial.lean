import FourColorTheorem.Utils.Finite.Chain

namespace Fintype
open Relation
open Function

variable {α : Type _} [Fintype α]

@[inline] instance Relation.ClosureBorder.instDecidableMembership [DecidableEq α] {r : α → α → Prop}
  [DecidableRel r] {D : Set α} [DecidablePred (· ∈ D)] : DecidablePred (· ∈ ClosureBorder r D)
  := by{
    intro x
    simp only[ClosureBorder, Set.mem_setOf]
    apply instDecidableAnd (dp := by{
      apply @Fintype.decidableExistsFintype _ _ (by{
        intro x
        apply instDecidableAnd (dp := inferInstance) (dq := by{
          apply ReflTransGen.finDec
        })
      })
    }) (dq := by{
      apply @Fintype.decidableExistsFintype _ _ (by{
        intro x
        apply instDecidableAnd (dp := inferInstance) (dq := by{
          apply ReflTransGen.finDec
        })
      })
    })
  }

def nCompSet (r : Setoid α) [DecidableRel r] (D : Set α) [DecidablePred (· ∈ D)] : ℕ :=
  let : Fintype {x // x ∈ D} := Subtype.fintype (· ∈ D)
  let : DecidableRel (LiftOn r.r D) := instDecidableLiftOn
  Fintype.nComp ⟨_, LiftOn_equivalence_of_equivalence D r.iseqv⟩
theorem nCompSet_univ {r : Setoid α} [DecidableRel r] :
  nCompSet r Set.univ = nComp r := by{
    unfold nCompSet nComp
    simp only
    let e : Quotient ⟨_, LiftOn_equivalence_of_equivalence Set.univ r.iseqv⟩ ≃ Quotient r := by{
      let f :Quotient ⟨_, LiftOn_equivalence_of_equivalence Set.univ r.iseqv⟩ → Quotient r:=
        fun q => ⟦q.out.val⟧
      apply Equiv.ofBijective f
      constructor
      · {
        intro qx qy hqxy
        unfold f at hqxy
        rw[← Quotient.out_eq qx, ← Quotient.out_eq qy]
        rw[Quotient.eq]
        rw[Quotient.eq] at hqxy
        simp only [LiftOn, hqxy]
      }
      · {
        intro qy
        use ⟦⟨qy.out, Set.mem_univ _⟩⟧
        unfold f
        symm
        nth_rw 1 [← Quotient.out_eq qy]
        rw[Quotient.eq]
        have h := Quotient.mk_out (s := ⟨_, LiftOn_equivalence_of_equivalence Set.univ r.iseqv⟩)
          ⟨qy.out, Set.mem_univ _⟩
        simp only[LiftOn] at h
        exact r.iseqv.symm h
      }
    }
    let : DecidableRel (LiftOn r.r Set.univ) := inferInstance
    let : Fintype (Quotient ⟨_, LiftOn_equivalence_of_equivalence Set.univ r.iseqv⟩) := by
      apply Quotient.fintype
    have he := ofEquiv_card e
    apply Eq.mp ?_ he.symm
    congr
    · apply Subsingleton.elim
    · apply Subsingleton.elim
  }

theorem nCompSet_eq_nComp {r : Setoid α} [DecidableRel r] {D : Set α} [DecidablePred (· ∈ D)] :
  nCompSet r D = nComp ⟨_, LiftOn_equivalence_of_equivalence D r.iseqv⟩ := by{
    unfold nCompSet nComp
    congr
  }
@[simp] theorem nCompSet_empty {r : Setoid α} [DecidableRel r] :
  nCompSet r ∅ = 0 := by{
    unfold nCompSet
    simp only
    let inst : IsEmpty { x // x ∈ (∅ : Set α)} := by{
      simp only [Set.mem_empty_iff_false]
      exact Subtype.isEmpty_false
    }
    have h := nComp_eq_zero_iff.mpr inst
    rw[← h]
    congr
    apply Subsingleton.elim
  }

theorem nCompSet_inex_of_closure {r : Setoid α} [DecidableRel r] {D : Set α} [DecidablePred (· ∈ D)]
  (rClo : Closure r D) : nComp r = nCompSet r D + nCompSet r Dᶜ := by{
    unfold nCompSet nComp
    simp only
    rw[← Fintype.card_sum]
    let e : Quotient r ≃ Quotient ⟨_, LiftOn_equivalence_of_equivalence D r.iseqv⟩
    ⊕ Quotient ⟨_, LiftOn_equivalence_of_equivalence Dᶜ r.iseqv⟩ := by{
      let f : Quotient r → Quotient ⟨_, LiftOn_equivalence_of_equivalence D r.iseqv⟩
      ⊕ Quotient ⟨_, LiftOn_equivalence_of_equivalence Dᶜ r.iseqv⟩ :=
        fun q => if hq : q.out ∈ D then Sum.inl ⟦⟨q.out, hq⟩⟧ else Sum.inr ⟦⟨q.out, hq⟩⟧
      apply Equiv.ofBijective f; constructor
      · {
        intro qx qy hqxy
        unfold f at hqxy
        rcases em (qx.out ∈ D) with hqx | hqx
        · {
          simp only [hqx, ↓reduceDIte] at hqxy
          rcases em' (qy.out ∈ D) with hqy | hqy
          · simp[hqy] at hqxy
          simp only [hqy, ↓reduceDIte, Sum.inl.injEq] at hqxy
          rw[Quotient.eq] at hqxy
          simp only [LiftOn] at hqxy
          rw[← Quotient.out_equiv_out]
          exact hqxy
        }
        simp only [hqx, ↓reduceDIte] at hqxy
        rcases em (qy.out ∈ D) with hqy | hqy
        · simp[hqy] at hqxy
        simp only [hqy, ↓reduceDIte, Sum.inr.injEq] at hqxy
        rw[Quotient.eq] at hqxy
        simp only [LiftOn] at hqxy
        rw[← Quotient.out_equiv_out]
        exact hqxy
      }
      · {
        intro sq
        match sq with
        | Sum.inl qy => {
          use ⟦qy.out.val⟧
          unfold f
          have hqy := qy.out.prop
          have hqy' := Quotient.mk_out qy.out (s:=r)
          rw[closure_iff_single] at rClo
          apply r.iseqv.symm at hqy'
          have rClo' := rClo _ hqy _ hqy'
          simp only [rClo', ↓reduceDIte, Sum.inl.injEq]
          rw[Quotient.mk_eq_iff_out]
          change LiftOn _ _ _ _
          simp only [LiftOn]
          exact r.iseqv.symm hqy'
        }
        | Sum.inr qy => {
          use ⟦qy.out.val⟧
          unfold f
          have hqy := qy.out.prop
          have hqy' := Quotient.mk_out qy.out (s:=r)
          have rCloc := (compl_closure_of_equivalence r.iseqv).mpr rClo
          rw[closure_iff_single] at rCloc
          apply r.iseqv.symm at hqy'
          have rCloc' : _ ∉ _:= rCloc _ hqy _ hqy'
          simp only [rCloc', ↓reduceDIte, Sum.inr.injEq]
          rw[Quotient.mk_eq_iff_out]
          change LiftOn _ _ _ _
          simp only [LiftOn]
          exact r.iseqv.symm hqy'
        }
      }
    }
    have he := ofEquiv_card e
    apply Eq.mp ?_ he.symm
    congr
    · apply Subsingleton.elim
  }

theorem nCompSet_sum_of_closure {r : Setoid α} [DecidableRel r] {D1 D2 : Set α}
  [DecidablePred (· ∈ D1)] [DecidablePred (· ∈ D2)]
  (rClo1 : Closure r D1) (hD12 : Disjoint D1 D2)
  : nCompSet r (D1 ∪ D2) = nCompSet r D1 + nCompSet r D2 := by{
    unfold nCompSet nComp
    simp only
    let e : Quotient ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩
      ≃ Quotient ⟨_, LiftOn_equivalence_of_equivalence D1 r.iseqv⟩ ⊕
      Quotient ⟨_, LiftOn_equivalence_of_equivalence D2 r.iseqv⟩ := by{
        let f : Quotient ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩
      → Quotient ⟨_, LiftOn_equivalence_of_equivalence D1 r.iseqv⟩ ⊕
      Quotient ⟨_, LiftOn_equivalence_of_equivalence D2 r.iseqv⟩ := fun q =>
          if hq : q.out.val ∈ D1
          then Sum.inl ⟦⟨q.out.val, hq⟩⟧
          else Sum.inr ⟦⟨q.out.val, q.out.prop.resolve_left hq⟩⟧
        apply Equiv.ofBijective f; constructor
        · {
          intro qx qy hqxy
          unfold f at hqxy
          rcases em (qx.out.val ∈ D1) with hD1x | hD1x
          · {
            simp only [hD1x, ↓reduceDIte] at hqxy
            rcases em' (qy.out.val ∈ D1) with hD1y | hD1y
            · simp[hD1y] at hqxy
            simp only [hD1y, ↓reduceDIte, Sum.inl.injEq] at hqxy
            simp only[Quotient.eq, LiftOn] at hqxy
            rw[← Quotient.out_equiv_out]
            exact hqxy
          }
          simp only [hD1x, ↓reduceDIte] at hqxy
          rcases em (qy.out.val ∈ D1) with hD1y | hD1y
          · simp[hD1y] at hqxy
          simp only [hD1y, ↓reduceDIte, Sum.inr.injEq] at hqxy
          simp only[Quotient.eq, LiftOn] at hqxy
          rw[← Quotient.out_equiv_out]
          exact hqxy
        }
        · {
          intro sq
          match sq with
          | Sum.inl qy => {
            use ⟦⟨qy.out.val, Or.inl qy.out.prop⟩⟧
            unfold f
            rw[dite_cond_eq_true, Sum.inl.injEq, Quotient.mk_eq_iff_out]
            · {
              change LiftOn _ _ _ _
              unfold LiftOn
              simp only
              have hy := Quotient.mk_out
                (s := ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩)
                ⟨qy.out.val, Or.inl qy.out.prop⟩
              simp only[LiftOn] at hy
              exact hy
            }
            · {
              apply eq_true
              refine rClo1 _ qy.out.prop _ ?_
              have hy := Quotient.mk_out
                (s := ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩)
                ⟨qy.out.val, Or.inl qy.out.prop⟩
              simp only[LiftOn] at hy
              apply r.iseqv.symm at hy
              apply ReflTransGen.single hy
            }
          }
          | Sum.inr qy => {
            use ⟦⟨qy.out.val, Or.inr qy.out.prop⟩⟧
            unfold f
            rw[dite_cond_eq_false, Sum.inr.injEq, Quotient.mk_eq_iff_out]
            · {
              change LiftOn _ _ _ _
              unfold LiftOn
              simp only
              have hy := Quotient.mk_out
                (s := ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩)
                ⟨qy.out.val, Or.inr qy.out.prop⟩
              simp only[LiftOn] at hy
              exact hy
            }
            · {
              apply eq_false
              have rClo1' : Closure r D1ᶜ := by
                rw[compl_closure_of_equivalence r.iseqv]
                exact rClo1
              unfold Closure at rClo1'
              simp only [Set.mem_compl_iff] at rClo1'
              symm at hD12
              rw[Set.disjoint_iff, Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem] at hD12
              simp only [Set.mem_inter_iff, not_and] at hD12
              have hqy := hD12 _ qy.out.prop
              refine rClo1' _ hqy _ ?_
              have hy := Quotient.mk_out
                (s := ⟨_, LiftOn_equivalence_of_equivalence (D1 ∪ D2) r.iseqv⟩)
                ⟨qy.out.val, Or.inr qy.out.prop⟩
              simp only[LiftOn] at hy
              apply r.iseqv.symm at hy
              apply ReflTransGen.single hy
            }
          }
        }
      }
    have he := ofEquiv_card e.symm
    rw[card_sum] at he
    apply Eq.mp ?_ he
    congr
    apply Subsingleton.elim
  }

theorem nComp_adjunctionOn_partial {β : Type _} [Fintype β]
  [DecidableEq α] [DecidableEq β] {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop} [DecidableRel e] [DecidableRel e']
  {D : Set α} [DecidablePred (· ∈ D)] (A : AdjunctionOn h e e' D) :
  @nCompSet _ _ ⟨_, A.equivalence_reflTransGen_e'⟩ ReflTransGen.finDec {x | h x ∈ D} inferInstance =
  @nCompSet _ _ ⟨_, A.equivalence_reflTransGen_e⟩ ReflTransGen.finDec D inferInstance := by{
    have hA := nComp_adjunctionOn A
    simp only [nCompSet_eq_nComp]
    apply Eq.mp ?_ hA.symm
    congr 1
    · {
      congr 1
      · apply Subsingleton.elim
      apply Subsingleton.elim
    }
    · {
      congr 1
      · apply Subsingleton.elim
      apply Subsingleton.elim
    }
  }

theorem nComp_adjunctionOn_partial_of_full {β : Type _} [Fintype β]
  [DecidableEq α] [DecidableEq β] {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop} [DecidableRel e] [DecidableRel e']
  {D : Set α} [DecidablePred (· ∈ D)] (A : AdjunctionOn h e e' D) (hb : ∀ x, h x ∈ D) :
  @nComp _ _ ⟨_, A.equivalence_reflTransGen_e'⟩ ReflTransGen.finDec =
  @nCompSet _ _ ⟨_, A.equivalence_reflTransGen_e⟩ ReflTransGen.finDec D inferInstance := by{
    have hA := nComp_adjunctionOn_partial A
    rw[← hA]
    unfold nCompSet
    simp only
    unfold nComp
    simp only
    let e : Quotient ⟨_, A.equivalence_reflTransGen_e'⟩ ≃ Quotient
      ⟨_, LiftOn_equivalence_of_equivalence {x | h x ∈ D} A.equivalence_reflTransGen_e'⟩ := by{
      let f : Quotient ⟨_, A.equivalence_reflTransGen_e'⟩ → Quotient
        ⟨_, LiftOn_equivalence_of_equivalence {x | h x ∈ D} A.equivalence_reflTransGen_e'⟩ :=
        fun q => ⟦⟨q.out, by{simp[hb]}⟩⟧
      apply Equiv.ofBijective f; constructor
      · {
        intro qx qy h
        unfold f at h
        rw[Quotient.eq] at h
        simp only [LiftOn] at h
        rw[← Quotient.out_equiv_out]
        exact h
      }
      · {
        intro qy
        use ⟦qy.out.val⟧
        unfold f
        rw[Quotient.mk_eq_iff_out]
        change LiftOn _ _ _ _
        simp only [LiftOn]
        have hqy := Quotient.mk_out qy.out.val (s:=⟨_, A.equivalence_reflTransGen_e'⟩)
        simp only at hqy
        exact hqy
      }
    }
    let inst : Fintype (Quotient ⟨_, A.equivalence_reflTransGen_e'⟩) := by{
      classical
      apply Quotient.fintype
    }
    have he := Fintype.ofEquiv_card e
    apply Eq.mp ?_ he.symm
    congr
    · apply Subsingleton.elim
    · apply Subsingleton.elim
  }

end Fintype
