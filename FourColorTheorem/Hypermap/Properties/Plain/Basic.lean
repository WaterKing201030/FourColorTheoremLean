import FourColorTheorem.Hypermap.Properties.Plain.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

namespace plain

theorem cedge_cases (hp : H.plain) {x y : α} (hxy : H.cedge x y)
  : x = y ∨ edge x = y := by{
    rw[cedge, funReflTransGen_iff_iterate] at hxy
    have ⟨n, hn⟩:=hxy
    clear hxy
    rw[plain_iff_edge_edge] at hp
    induction n generalizing x with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      specialize ih hn
      rw[(hp x).left] at ih
      exact Or.symm ih
    }
  }
theorem cedge_cases_iff (hp : H.plain) {x y : α}
  : H.cedge x y ↔ x = y ∨ edge x = y := by{
    apply Iff.intro hp.cedge_cases
    intro h
    rcases h with h | h
    · rw[h]; apply ReflTransGen.refl
    · rw[← h]; apply funReflTransGen.single
  }
theorem cedge_cases'_iff (hp : H.plain) {x y : α}
  : H.cedge x y ↔ x = y ∨ x = edge y := by{
    rw[hp.cedge_cases_iff]
    apply or_congr_right
    nth_rw 1 [← edge_inj]
    rw[plain_iff_edge_edge] at hp
    rw[(hp x).left]
  }
theorem cedge_cases' (hp : H.plain) {x y : α} (hxy : H.cedge x y)
  : x = y ∨ x = edge y := hp.cedge_cases'_iff.mp hxy

theorem equotient_lemma (hP : H.plain) (x : α) : (∃q : Quotient H.esetoid, q.out = x)
↔ ¬∃q : Quotient H.esetoid, edge (q.out) = x := by{
  have hP' := hP
  rw[plain_iff_edge_edge] at hP
  constructor
  · {
    intro ⟨q0, hq0⟩ ⟨q1, hq1⟩
    have hQ : q0 = q1 := by{
      rw[← Quotient.out_equiv_out]
      change H.cedge q0.out q1.out
      rw[← edge_inj, (hP q1.out).left] at hq1
      rw[hq0, hq1]
      apply funReflTransGen.single
    }
    rw[← hQ, ← hq0] at hq1
    exact (hP q0.out).right hq1
  }
  · {
    intro h
    rw[not_exists] at h
    specialize h ⟦edge x⟧
    use ⟦edge x⟧
    have h0 : H.cedge ⟦edge x⟧.out x := by{
      have h0 : H.cedge ⟦edge x⟧.out (edge x) := by{
        have h0 := Quotient.mk_out (s := H.esetoid) (edge x)
        exact h0
      }
      apply H.cedge_equivalence.trans h0
      apply H.cedge_equivalence.symm
      apply funReflTransGen.single
    }
    rw[hP'.cedge_cases_iff] at h0
    exact h0.resolve_right h
  }
}
theorem ecomp_double (hP : H.plain) : Fintype.card α = H.ecomp * 2 := by{
  have hP' := hP
  rw[plain_iff_edge_edge] at hP
  let q1 := {x // ∃q : Quotient H.esetoid, q.out = x}
  let q2 := {x // ∃q : Quotient H.esetoid, edge (q.out) = x}
  let q1fin : Fintype q1 := inferInstance
  let q2fin : Fintype q2 := inferInstance
  let q12e : q1 ≃ q2 := by{
    let f : q1 → q2 := fun ⟨x, hx⟩ => ⟨edge x, by{
      have ⟨q, hq⟩:=hx; use q; rw[hq]
    }⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro ⟨x0, hx0⟩ ⟨x1, hx1⟩ hx01
      rw[Subtype.ext_iff] at hx01
      rw[Subtype.ext_iff]
      simp only [f, edge_inj] at hx01
      simp[hx01]
    }
    · {
      intro ⟨x, ⟨q, hq⟩⟩
      use ⟨edge x, ⟨q, by{rw[←hq, (hP q.out).left]}⟩⟩
      simp[f, hP x]
    }
  }
  have hq1e : H.ecomp = Fintype.card q1 := by{
    apply Fintype.card_congr
    let f : Quotient H.esetoid → q1 := fun q => ⟨q.out, ⟨q, rfl⟩⟩
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
  rw[hq1e, mul_two]
  nth_rw 2 [hq12e]
  rw[← Fintype.card_sum]
  apply Fintype.card_congr
  let f : α → q1 ⊕ q2 := fun x => by{
    let inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
    match inst with
    | isTrue hq => exact Sum.inl ⟨x, hq⟩
    | isFalse hq => {
      have hq' : ∃q : Quotient H.esetoid, edge (q.out) = x := by{
        rw[hP'.equotient_lemma, not_not] at hq
        exact hq
      }
      exact Sum.inr ⟨x, hq'⟩
    }
  }
  apply Equiv.ofBijective f
  constructor
  · {
    intro x0 x1 hx01
    unfold f at hx01
    set inst0 : Decidable (∃q : Quotient H.esetoid, q.out = x0) := inferInstance
    set inst1 : Decidable (∃q : Quotient H.esetoid, q.out = x1) := inferInstance
    match inst0, inst1 with
    | isFalse _, isTrue _ | isTrue _, isFalse _ => simp at hx01
    | isTrue _, isTrue _ | isFalse _, isFalse _ => {
      simp only [Sum.inl.injEq, Sum.inr.injEq] at hx01; rw[Subtype.ext_iff] at hx01; exact hx01
    }
  }
  · {
    intro x'
    match x' with
    | Sum.inl ⟨x, hx⟩ => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
      simp only
      match inst with
      | isTrue hp => simp
      | isFalse hp => contradiction
    }
    | Sum.inr ⟨x, hx⟩ => {
      use x
      unfold f
      set inst : Decidable (∃q : Quotient H.esetoid, q.out = x) := inferInstance
      simp only
      match inst with
      | isTrue hp => {
        rw[hP'.equotient_lemma] at hp
        contradiction
      }
      | isFalse hp => simp only
    }
  }
}
theorem edge_edge (hp : H.plain) {p : α} : H.edge (H.edge p) = p := by{
  rw[plain_iff_edge_edge] at hp
  rw[(hp p).left]
}
theorem edgeinv_eq_edge (hp : H.plain) : H.edgeinv = H.edge := by{
  ext x
  rw[← edge_inj, edgeinv_rightinv, hp.edge_edge]
}
theorem edge_eq_eq_eq_edge (hp : H.plain) {a b : α} : H.edge a = b ↔ a = H.edge b := by{
  nth_rw 1 [← hp.edgeinv_eq_edge, edgeinv_eq_iff_eq_edge]
}
theorem edge_ne (hp : H.plain) (p : α) : H.edge p ≠ p := by{
  rw[plain_iff_edge_edge] at hp
  exact (hp p).right
}
end plain

end Hypermap
