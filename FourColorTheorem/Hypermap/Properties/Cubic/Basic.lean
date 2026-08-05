import FourColorTheorem.Hypermap.Properties.Cubic.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem cubic_iff_period_three : H.Cubic ↔ ∀x, H.node (H.node (H.node x)) = x ∧ H.node x ≠ x := by{
  rw[cubic_def']
  unfold cubicSubset
  simp[Set.eq_univ_iff_forall]
  simp[minimalPeriod_eq_three_iff]
}

namespace Cubic
theorem node_ne (hc : H.Cubic) (x : α) : H.node x ≠ x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).right
}
theorem node_3 (hc : H.Cubic) (x : α) : H.node (H.node (H.node x)) = x := by{
  rw[cubic_iff_period_three] at hc
  exact (hc x).left
}
theorem node_2_ne (hc : H.Cubic) (x : α) : H.node (H.node x) ≠ x := by{
  rw[cubic_iff_period_three] at hc
  intro h
  have h' := (hc x).left
  rw[h] at h'
  exact (hc x).right h'
}

theorem cnode_cases (hC : H.Cubic) {x y : α} (hxy : H.cnode x y) :
  x = y ∨ node x = y ∨ node (node x) = y := by{
  rw[cnode, funReflTransGen_iff_iterate] at hxy
  rcases hxy with ⟨n, hn⟩
  have hC' : IsPeriodicPt H.node 3 x := hC.node_3 x
  rw[← hC'.iterate_mod_apply] at hn
  have hlt : n % 3 < 3 := by omega
  match hm : n % 3 with
  | 0 | 1 | 2 => simp[hm] at hn; simp[hn]
  | _ + 3 => simp[hm, Nat.add_assoc] at hlt
}
theorem quotient_cases (hC : H.Cubic) (x : α) : ∃q : Quotient H.nsetoid,
  q.out = x ∨ node (q.out) = x ∨ node (node (q.out)) = x := by{
  let q : Quotient H.nsetoid := ⟦x⟧
  use q
  rcases eq_or_ne q.out x with hqx | hqx
  · simp[hqx]
  rcases eq_or_ne (node q.out) x with hnqx | hnqx
  · simp[hnqx]
  right; right
  have ih : H.cnode q.out x :=
    Quotient.mk_out (s := H.nsetoid) x
  apply hC.cnode_cases at ih
  simp[hqx, hnqx] at ih
  assumption
}
theorem ncomp_triple (hC : H.Cubic) : Fintype.card α = H.ncomp * 3 := by{
  have hC' := hC
  rw[cubic_iff_period_three] at hC
  let q1 := {x // ∃q : Quotient H.nsetoid, q.out = x}
  let q2 := {x // ∃q : Quotient H.nsetoid, node (q.out) = x}
  let q3 := {x // ∃q : Quotient H.nsetoid, node (node (q.out)) = x}
  let q1fin : Fintype q1 := inferInstance
  let q2fin : Fintype q2 := inferInstance
  let q3fin : Fintype q3 := inferInstance
  let q12e : q1 ≃ q2 := by{
    let f : q1 → q2 := fun ⟨x, hx⟩ => ⟨node x, by{
      have ⟨q, hq⟩:=hx; use q; rw[hq]
    }⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro ⟨x0, hx0⟩ ⟨x1, hx1⟩ hx01
      rw[Subtype.ext_iff] at hx01
      rw[Subtype.ext_iff]
      simp only [f, node_inj] at hx01
      simp[hx01]
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use ⟨node (node x), ⟨q, by{rw[←hq, (hC q.out).left]}⟩⟩
      simp[f, hC x]
    }
  }
  let q23e : q2 ≃ q3 := by{
    let f : q2 → q3 := fun ⟨x, hx⟩ => ⟨node x, by{
      have ⟨q, hq⟩:=hx; use q; rw[hq]
    }⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro ⟨x0, hx0⟩ ⟨x1, hx1⟩ hx01
      rw[Subtype.ext_iff] at hx01
      rw[Subtype.ext_iff]
      simp only [f, node_inj] at hx01
      simp[hx01]
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use ⟨node (node x), ⟨q, by{rw[←hq, (hC q.out).left]}⟩⟩
      simp[f, hC x]
    }
  }
  have hq1e : H.ncomp = Fintype.card q1 := by{
    apply Fintype.card_congr
    let f : Quotient H.nsetoid → q1 := fun q => ⟨q.out, ⟨q, rfl⟩⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro Q0 Q1 hQ
      simp only [f] at hQ
      rw[Subtype.ext_iff] at hQ
      simp only [Quotient.out_inj] at hQ
      exact hQ
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use q
      simp only [f, hq]
    }
  }
  have hq12e := Fintype.card_congr q12e
  have hq23e := Fintype.card_congr q23e
  change _ = _ * (Nat.succ 2)
  rw[hq1e, Nat.mul_succ, mul_two]
  nth_rw 2 3 [hq12e]
  nth_rw 2 [hq23e]
  rw[Nat.add_assoc, ← Fintype.card_sum, ← Fintype.card_sum]
  apply Fintype.card_congr
  let f : α → q1 ⊕ q2 ⊕ q3 := fun x => by{
    let inst : Decidable (∃q : Quotient H.nsetoid, q.out = x) := inferInstance
    match inst with
    | isTrue hq => exact Sum.inl ⟨x, hq⟩
    | isFalse hq => {
      let inst' : Decidable (∃q : Quotient H.nsetoid, node (q.out) = x) := inferInstance
      match inst' with
      | isTrue hq' => exact Sum.inr (Sum.inl ⟨x, hq'⟩)
      | isFalse hq' => {
        have hq' : ∃q : Quotient H.nsetoid, node (node (q.out)) = x := by{
          push_neg at hq hq'
          have ⟨q, hq''⟩ := hC'.quotient_cases x
          use q
          simp[hq, hq'] at hq''
          assumption
        }
        exact Sum.inr (Sum.inr ⟨x, hq'⟩)
      }
    }
  }
  apply Equiv.ofBijective f
  constructor
  · {
    intro x0 x1 hx01
    unfold f at hx01
    set inst0 : Decidable (∃q : Quotient H.nsetoid, q.out = x0) := inferInstance
    set inst0' : Decidable (∃q : Quotient H.nsetoid, node (q.out) = x0) := inferInstance
    set inst1 : Decidable (∃q : Quotient H.nsetoid, q.out = x1) := inferInstance
    set inst1' : Decidable (∃q : Quotient H.nsetoid, node (q.out) = x1) := inferInstance
    match inst0, inst1, inst0', inst1' with
    | isTrue _, isTrue _, _, _ | isFalse _, isFalse _, isTrue _, isTrue _
    | isFalse _, isFalse _, isFalse _, isFalse _ => {
      simp only [Sum.inl.injEq, Sum.inr.injEq] at hx01
      rw[Subtype.ext_iff] at hx01
      exact hx01
    }
  }
  · {
    intro x'
    match x' with
    | Sum.inl ⟨x, hx⟩ => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.nsetoid, q.out = x) := inferInstance
      simp only
      match inst with
      | isTrue hp => simp
      | isFalse hp => contradiction
    }
    | Sum.inr (Sum.inl ⟨x, hx⟩) => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.nsetoid, q.out = x) := inferInstance
      set inst' : Decidable (∃q : Quotient H.nsetoid, node (q.out) = x) := inferInstance
      have hinstp : ¬∃q : Quotient H.nsetoid, q.out = x := by{
        push_neg
        intro q hq
        have ⟨q', hq'⟩ := hx
        have hqq' : H.nsetoid q.out q'.out := by{
          change H.cnode q.out q'.out
          apply H.cnode_equivalence.symm
          apply ReflTransGen.single
          change _ = _
          rw[hq', hq]
        }
        have hq_mk := Quotient.out_equiv_out.mp hqq'
        rw[← hq_mk, ← hq] at hq'
        exact (hC _).2 hq'
      }
      have hinst : inst = isFalse hinstp := by{
        match inst with
        | isTrue _ => contradiction
        | isFalse _ => rfl
      }
      have hinst' : inst' = isTrue hx := by{
        match inst' with
        | isTrue _ => rfl
        | isFalse _ => contradiction
      }
      simp only [hinst, hinst']
    }
    | Sum.inr (Sum.inr ⟨x, hx⟩) => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.nsetoid, q.out = x) := inferInstance
      set inst' : Decidable (∃q : Quotient H.nsetoid, node (q.out) = x) := inferInstance
      have hinstp : ¬∃q : Quotient H.nsetoid, q.out = x := by{
        push_neg
        intro q hq
        have ⟨q', hq'⟩ := hx
        have hqq' : H.nsetoid q.out q'.out := by{
          change H.cnode q.out q'.out
          apply H.cnode_equivalence.symm
          apply funReflTransGen.head rfl
          apply ReflTransGen.single
          change _ = _
          rw[hq', hq]
        }
        have hq_mk := Quotient.out_equiv_out.mp hqq'
        rw[← hq_mk, ← hq] at hq'
        exact hC'.node_2_ne _ hq'
      }
      have hinstp' : ¬∃q : Quotient H.nsetoid, node (q.out) = x := by{
        push_neg
        intro q hq
        have ⟨q', hq'⟩ := hx
        have hqq' : H.nsetoid q.out q'.out := by{
          change H.cnode q.out q'.out
          apply H.cnode_equivalence.symm
          apply ReflTransGen.single
          change _ = _
          rw[← H.node_inj, hq', hq]
        }
        have hq_mk := Quotient.out_equiv_out.mp hqq'
        rw[← hq_mk, ← hq] at hq'
        exact (hC _).2 hq'
      }
      have hinst : inst = isFalse hinstp := by{
        match inst with
        | isTrue _ => contradiction
        | isFalse _ => rfl
      }
      have hinst' : inst' = isFalse hinstp' := by{
        match inst' with
        | isTrue _ => contradiction
        | isFalse _ => rfl
      }
      simp only[hinst, hinst']
    }
  }
}
end Cubic

end Hypermap
