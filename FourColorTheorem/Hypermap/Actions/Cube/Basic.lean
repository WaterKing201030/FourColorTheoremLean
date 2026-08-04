import FourColorTheorem.Hypermap.Actions.Cube.Defs

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation
open CubeTag

theorem cube_cface_cte_iff_cedge {x y : α} :
  H.cube.cface (CTe, x) (CTe, y) ↔ H.cedge x y := by{
    rw[cface, cedge, funReflTransGen_iff_iterate, funReflTransGen_iff_iterate]
    constructor
    · {
      intro ⟨n, hn⟩
      use n
      induction n generalizing x with
      | zero => simp at hn; simp[hn]
      | succ n' ih => {
        rw[iterate_succ_apply] at hn
        specialize ih hn
        rwa[iterate_succ_apply]
      }
    }
    · {
      intro ⟨n, hn⟩
      use n
      induction n generalizing x with
      | zero => simp at hn; simp[hn]
      | succ n' ih => {
        rw[iterate_succ_apply] at hn
        specialize ih hn
        rwa[iterate_succ_apply]
      }
    }
  }
theorem cube_cface_cte_iff_cedge' {x y : H.CubeDart}
  (htx : x.fst = CTe) (hty : y.fst = CTe) :
  H.cube.cface x y ↔ H.cedge x.snd y.snd := by{
    match x, y with
    | (tx, x), (ty, y) => simp at htx hty; simp[htx, hty, cube_cface_cte_iff_cedge]
  }
theorem cube_cte_of_cface_cte {x y : α} {t : CubeTag}
  (hxy : H.cube.cface (CTe, x) (t, y)) : t = CTe := by{
    rw[cface, funReflTransGen_iff_iterate] at hxy
    rcases hxy with ⟨n, hn⟩
    induction n generalizing x with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      exact ih hn
    }
  }
theorem cube_cte_of_cface_cte' {x y : H.CubeDart} (hx : x.fst = CTe)
  (hxy : H.cube.cface x y) : y.fst = CTe := by{
    match x, y with
    | (_, _), (_, _) =>
      simp only at hx; simp only [hx] at hxy
      apply cube_cte_of_cface_cte at hxy
      exact hxy
  }
theorem cube_cface_ctfe_iff_cnode {x y : α} :
  H.cube.cface (CTfe, x) (CTfe, y) ↔ H.cnode x y := by{
    rw[cface, cnode, funReflTransGen_iff_iterate, funReflTransGen_iff_iterate]
    constructor
    · {
      intro ⟨n, hn⟩
      use n
      induction n generalizing x with
      | zero => simp at hn; simp[hn]
      | succ n' ih => {
        rw[iterate_succ_apply] at hn
        specialize ih hn
        rwa[iterate_succ_apply]
      }
    }
    · {
      intro ⟨n, hn⟩
      use n
      induction n generalizing x with
      | zero => simp at hn; simp[hn]
      | succ n' ih => {
        rw[iterate_succ_apply] at hn
        specialize ih hn
        rwa[iterate_succ_apply]
      }
    }
  }
theorem cube_cface_ctfe_iff_cnode' {x y : H.CubeDart}
  (htx : x.fst = CTfe) (hty : y.fst = CTfe) :
  H.cube.cface x y ↔ H.cnode x.snd y.snd := by{
    match x, y with
    | (tx, x), (ty, y) => simp at htx hty; simp[htx, hty, cube_cface_ctfe_iff_cnode]
  }
theorem cube_ctfe_of_cface_ctfe {x y : α} {t : CubeTag}
  (hxy : H.cube.cface (CTfe, x) (t, y)) : t = CTfe := by{
    rw[cface, funReflTransGen_iff_iterate] at hxy
    rcases hxy with ⟨n, hn⟩
    induction n generalizing x with
    | zero => simp at hn; simp[hn]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      exact ih hn
    }
  }
theorem cube_ctfe_of_cface_ctfe' {x y : H.CubeDart} (hx : x.fst = CTfe)
  (hxy : H.cube.cface x y) : y.fst = CTfe := by{
    match x, y with
    | (_, _), (_, _) =>
      simp only at hx; simp only [hx] at hxy
      apply cube_ctfe_of_cface_ctfe at hxy
      exact hxy
  }
theorem cube_cface_ctnf {x : α} {t : CubeTag}
  (ht : t ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface (t, x) (CTnf, x) := by{
    rw[cface, funReflTransGen_iff_iterate]
    match t with
    | CTn => use 3; rfl
    | CTen => use 2; rfl
    | CTf => use 1; rfl
    | CTnf => use 0; rfl
  }
theorem cube_cface_ctnf_pred_eq {x : α} {t : CubeTag}
  (ht : t ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface (t, x) = H.cube.cface (CTnf, x) := by{
  apply H.cube.cface_pred_eq_of_cface
  apply cube_cface_ctnf ht
}
theorem cube_cface_ctnf_pred_eq' {x : α} {t : CubeTag} {y : H.CubeDart}
  (ht : t ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface y (t, x) ↔ H.cube.cface y (CTnf, x) := by{
  simp only [H.cube.cface_equivalence.comm (a:=y)]
  rw[cube_cface_ctnf_pred_eq ht]
}
theorem cube_cface_self {x : α} {t0 t1 : CubeTag}
  (ht0 : t0 ∈ [CTn, CTen, CTf, CTnf]) (ht1 : t1 ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface (t0, x) (t1, x) := by{
    rw[cube_cface_ctnf_pred_eq ht0]
    apply H.cube.cface_equivalence.symm
    rw[cube_cface_ctnf_pred_eq ht1]
    apply ReflTransGen.refl
  }
theorem cube_tag_of_cface {x y : α} {tx ty : CubeTag} (htx : tx ∈ [CTn, CTen, CTf, CTnf])
  (hxy : H.cube.cface (tx, x) (ty, y)) : ty ∈ [CTn, CTen, CTf, CTnf] := by{
    rw[cface, funReflTransGen_iff_iterate] at hxy
    rcases hxy with ⟨n, hn⟩
    induction n generalizing x tx with
    | zero => simp at hn htx; simpa[← hn.1]
    | succ n' ih => {
      rw[iterate_succ_apply] at hn
      match tx with
      | CTn | CTen | CTf | CTnf =>
        exact ih (by{trivial}) hn
    }
  }
theorem cube_tag_of_cface' {x y : H.CubeDart} (hx : x.fst ∈ [CTn, CTen, CTf, CTnf])
  (hxy : H.cube.cface x y) : y.fst ∈ [CTn, CTen, CTf, CTnf] := by{
    match x, y with
    | (_, _), (_, _) =>
      simp only at hx
      apply H.cube_tag_of_cface hx
      exact hxy
  }

lemma cube_face_4_CTnf {x : α}
  : H.cube.face^[4] (CTnf, x) = (CTnf, H.face x) := by{
    simp[CubeDart.face]
  }
lemma cube_face_4_mul_CTnf {x : α} {n : ℕ}
  : H.cube.face^[4 * n] (CTnf, x) = (CTnf, H.face^[n] x) := by{
    rw[iterate_mul]
    induction n with
    | zero => simp
    | succ n' ih => {
      rw[iterate_succ_apply', ih, cube_face_4_CTnf, iterate_succ_apply']
    }
  }
theorem cube_cface_iff_cface {x y : α} {tx ty : CubeTag}
  (htx : tx ∈ [CTn, CTen, CTf, CTnf]) (hty : ty ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface (tx, x) (ty, y) ↔ H.cface x y := by{
    rw[cube_cface_ctnf_pred_eq htx, cube_cface_ctnf_pred_eq' hty]
    rw[cface, cface, funReflTransGen_iff_iterate, funReflTransGen_iff_iterate]
    constructor
    · {
      intro ⟨n, hn⟩
      have ⟨k, hk⟩ : ∃k, n = 4 * k := by{
        use n / 4
        rw[← Nat.mod_add_div n 4, iterate_add_apply, cube_face_4_mul_CTnf] at hn
        have hm : n % 4 < 4 := Nat.mod_lt _ (by trivial)
        nth_rw 1 [← Nat.div_add_mod n 4]
        simp only [Nat.add_eq_left]
        generalize n % 4 = m at *
        match m with
        | 0 => simp
        | 1 | 2 | 3 => simp[CubeDart.face] at hn
      }
      rw[hk] at hn
      clear! n
      use k
      rw[cube_face_4_mul_CTnf] at hn
      simp only [Prod.mk.injEq, true_and] at hn
      exact hn
    }
    · {
      intro ⟨n, hn⟩
      use 4 * n
      rw[cube_face_4_mul_CTnf, hn]
    }
  }
theorem cube_cface_iff_cface' {x y : H.CubeDart}
  (htx : x.fst ∈ [CTn, CTen, CTf, CTnf]) (hty : y.fst ∈ [CTn, CTen, CTf, CTnf]) :
  H.cube.cface x y ↔ H.cface x.snd y.snd := by{
  match x, y with
  | (tx, x), (ty, y) => simp at htx hty; simp[htx, hty, cube_cface_iff_cface]
}
theorem cube_cglink_ctnf {x : α} {t : CubeTag} :
  H.cube.cglink (t, x) (CTnf, x) := by{
    match t with
    | CTn | CTen | CTf | CTnf => {
      apply cglink_of_cface
      apply cube_cface_ctnf
      trivial
    }
    | CTe => {
      apply ReflTransGen.head (b:=(CTf, x))
      · simp[glink_iff, CubeDart.node]
      apply cglink_of_cface
      apply cube_cface_ctnf
      trivial
    }
    | CTfe => {
      apply ReflTransGen.head (b:=(CTn, x))
      · simp[glink_iff, CubeDart.edge]
      apply cglink_of_cface
      apply cube_cface_ctnf
      trivial
    }
  }
theorem cube_cglink_ctnf_pred_eq {x : α} {t : CubeTag} :
  H.cube.cglink (t, x) = H.cube.cglink (CTnf, x) := by{
  apply H.cube.cglink_pred_eq_of_cglink
  apply cube_cglink_ctnf
}
theorem cube_cglink_ctnf_pred_eq' {x : α} {t : CubeTag} {y : H.CubeDart} :
  H.cube.cglink y (t, x) ↔ H.cube.cglink y (CTnf, x) := by{
  simp only [H.cube.cglink_equivalence.comm (a:=y)]
  rw[cube_cglink_ctnf_pred_eq]
}
theorem cube_cglink_iff {x y : α} {tx ty : CubeTag}
: H.cube.cglink (tx, x) (ty, y) ↔ H.cglink x y := by{
  constructor
  · {
    generalize htx : (tx, x) = cx
    generalize hty : (ty, y) = cy
    have hcx : cx.snd = x := by{simp[← htx]}
    have hcy : cy.snd = y := by{simp[← hty]}
    rw[← hcx, ← hcy]
    clear! x y tx ty
    intro h
    induction h with
    | refl => apply ReflTransGen.refl
    | @tail cz cy hh ht ih => {
      apply ih.trans
      clear ih hh
      match cz, cy with
      | (tz, z), (ty, y) => {
        rw[glink_iff] at ht
        simp only[cube_edge, cube_node, cube_face] at ht
        simp only
        rcases ht with ht | ht | ht
        all_goals
        match tz with
        | CTn | CTen | CTf | CTnf | CTe | CTfe => {
          simp only [CubeDart.edge, CubeDart.node, CubeDart.face, Prod.mk.injEq] at ht
          rw[← ht.2]
          try {
            apply ReflTransGen.single
            simp[glink_iff]
          }
          try {
            apply ReflTransGen.head (b:=face z)
            · simp[glink_iff]
            apply ReflTransGen.single
            simp[glink_iff]
          }
          try {
            apply ReflTransGen.head (b:=edge z)
            · simp[glink_iff]
            apply ReflTransGen.single
            simp[glink_iff]
          }
        }
      }
    }
  }
  · {
    rw[cube_cglink_ctnf_pred_eq, cube_cglink_ctnf_pred_eq']
    intro h
    rw[cglink, ReflTransGen_iff_isChain_option] at h
    rcases h with ⟨l, hl, hlh, hlt⟩
    induction l generalizing x with
    | nil => simp at hlh
    | cons x' l' ih => {
      simp only [List.head?_cons, Option.some.injEq] at hlh
      rcases eq_or_ne l' [] with hl'n | hl'n
      · {
        simp only [hl'n, List.getLast?_singleton, Option.some.injEq] at hlt
        rw[← hlh, hlt]
        apply ReflTransGen.refl
      }
      rw[List.isChain_cons_iff_of_ne_nil hl'n] at hl
      rw[List.getLast?_cons_of_ne_nil hl'n] at hlt
      specialize ih (x:=l'.head hl'n) hl.2 (l'.head?_eq_some_head hl'n) hlt
      apply ReflTransGen.trans ?_ ih
      apply And.left at hl
      rw[glink_iff] at hl
      change H.cube.cglink _ _
      rcases hl with hl | hl | hl <;> rw[← hl, hlh]
      · {
        rw[← cube_cglink_ctnf_pred_eq (t := CTen)]
        apply H.cube.cglink_of_cedge
        apply ReflTransGen.single
        rfl
      }
      · {
        rw[← cube_cglink_ctnf_pred_eq (t := CTn), ← cube_cglink_ctnf_pred_eq' (t := CTen)]
        apply H.cube.cglink_of_cnode
        apply ReflTransGen.single
        rfl
      }
      · {
        rw[← cube_cglink_ctnf_pred_eq' (t := CTn)]
        apply H.cube.cglink_of_cface
        apply ReflTransGen.single
        rfl
      }
    }
  }
}
theorem cube_cglink_iff' {x y : H.CubeDart}
: H.cube.cglink x y ↔ H.cglink x.snd y.snd := by{
  match x, y with
  | (_, _), (_, _) => rw[cube_cglink_iff]
}

theorem cube_card : Fintype.card H.CubeDart = Fintype.card α * 6 := by{
  unfold CubeDart
  rw[Fintype.card_prod, Nat.mul_comm]
  congr
}
theorem cube_gcomp : H.cube.gcomp = H.gcomp := by{
  unfold gcomp Fintype.nComp
  simp only
  let f : Quotient H.cube.gsetoid → Quotient H.gsetoid :=
    fun q => ⟦q.out.snd⟧
  let e : Quotient H.cube.gsetoid ≃ Quotient H.gsetoid := by{
    apply Equiv.ofBijective f
    constructor
    · {
      intro q1 q2 hq12
      unfold f at hq12
      rw[Quotient.eq] at hq12
      change H.cglink _ _ at hq12
      rw[← H.cube_cglink_iff (tx := q1.out.1) (ty := q2.out.1)] at hq12
      change H.cube.gsetoid q1.out q2.out at hq12
      rw[← Quotient.out_equiv_out]
      exact hq12
    }
    · {
      intro q2
      let q1 : Quotient H.cube.gsetoid := ⟦(CTnf, q2.out)⟧
      have hq1 : H.cube.cglink _ _ := Quotient.mk_out (s:=H.cube.gsetoid) (CTnf, q2.out)
      use q1
      unfold f
      rw[Quotient.mk_eq_iff_out]
      change H.cglink _ _
      rw[cube_cglink_iff'] at hq1
      exact hq1
    }
  }
  have he := Fintype.ofEquiv_card e
  rw[← he]
  congr
  apply Subsingleton.elim
}
theorem cube_fcomp : H.cube.fcomp = H.ecomp + H.ncomp + H.fcomp := by{
  unfold fcomp ecomp ncomp Fintype.nComp
  simp only
  rw[← Fintype.card_sum, ← Fintype.card_sum]
  let f : Quotient H.cube.fsetoid → ((Quotient H.esetoid ⊕ Quotient H.nsetoid) ⊕ Quotient H.fsetoid)
    := fun q =>
      if q.out.fst = CTe then
        Sum.inl (Sum.inl ⟦q.out.snd⟧)
      else if q.out.fst = CTfe then
        Sum.inl (Sum.inr ⟦q.out.snd⟧)
      else
        Sum.inr ⟦q.out.snd⟧
  let e : Quotient H.cube.fsetoid ≃ ((Quotient H.esetoid ⊕ Quotient H.nsetoid) ⊕ Quotient H.fsetoid)
    := by{
    apply Equiv.ofBijective f
    constructor
    · {
      intro q0 q1 hq01
      unfold f at hq01
      rcases eq_or_ne q0.out.1 CTe with hq0e | hq0e
      · {
        have hq1e : q1.out.1 = CTe := by{
          by_contra hq1e
          simp only [hq0e, ↓reduceIte, hq1e] at hq01
          rw[apply_ite (_ = ·)] at hq01
          simp at hq01
        }
        simp only [hq0e, ↓reduceIte, hq1e, Sum.inl.injEq] at hq01
        rw[Quotient.eq_iff_equiv] at hq01
        change H.cedge _ _ at hq01
        rw[← Quotient.out_equiv_out]
        change H.cube.cface _ _
        rwa[H.cube_cface_cte_iff_cedge' hq0e hq1e]
      }
      have hq1e : q1.out.1 ≠ CTe := by{
        by_contra hq1e
        simp only [hq0e, ↓reduceIte, hq1e] at hq01
        rw[apply_ite (· = _)] at hq01
        simp at hq01
      }
      simp only [hq0e, ↓reduceIte, hq1e] at hq01
      rcases eq_or_ne q0.out.1 CTfe with hq0fe | hq0fe
      · {
        have hq1fe : q1.out.1 = CTfe := by{
          by_contra hq1fe
          simp[hq0fe, hq1fe] at hq01
        }
        simp only [hq0fe, ↓reduceIte, hq1fe, Sum.inl.injEq, Sum.inr.injEq] at hq01
        rw[Quotient.eq_iff_equiv] at hq01
        change H.cnode _ _ at hq01
        rw[← Quotient.out_equiv_out]
        change H.cube.cface _ _
        rwa[H.cube_cface_ctfe_iff_cnode' hq0fe hq1fe]
      }
      have hq1fe : q1.out.1 ≠ CTfe := by{
        by_contra hq1fe
        simp[hq0fe, hq1fe] at hq01
      }
      simp only [hq0fe, ↓reduceIte, hq1fe, Sum.inr.injEq] at hq01
      have hq0 : q0.out.1 ∈ [CTn, CTen, CTf, CTnf] := by{
        match hq1 : q0.out.1 with
        | CTn | CTen | CTf | CTnf => trivial
        | CTe | CTfe => contradiction
      }
      have hq1 : q1.out.1 ∈ [CTn, CTen, CTf, CTnf] := by{
        match hq1 : q1.out.1 with
        | CTn | CTen | CTf | CTnf => trivial
        | CTe | CTfe => contradiction
      }
      rw[Quotient.eq_iff_equiv] at hq01
      change H.cface _ _ at hq01
      rw[← Quotient.out_equiv_out]
      change H.cube.cface _ _
      rwa[H.cube_cface_iff_cface' hq0 hq1]
    }
    · {
      intro q
      match q with
      | Sum.inl (Sum.inl qe) => {
        let q' : Quotient H.cube.fsetoid := ⟦(CTe, qe.out)⟧
        use q'
        unfold f
        have hq' : q'.out.1 = CTe := by{
          have hq' : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTe, qe.out)
          apply cface_equivalence.symm at hq'
          apply cube_cte_of_cface_cte' (by trivial) at hq'
          exact hq'
        }
        simp only [hq', ↓reduceIte, Sum.inl.injEq]
        rw[Quotient.mk_eq_iff_out]
        change H.cedge _ _
        unfold q'
        have hq'q : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTe, qe.out)
        rw[cube_cface_cte_iff_cedge' hq' (by trivial)] at hq'q
        exact hq'q
      }
      | Sum.inl (Sum.inr qn) => {
        let q' : Quotient H.cube.fsetoid := ⟦(CTfe, qn.out)⟧
        use q'
        unfold f
        have hq' : q'.out.1 = CTfe := by{
          have hq' : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTfe, qn.out)
          apply cface_equivalence.symm at hq'
          apply cube_ctfe_of_cface_ctfe' (by trivial) at hq'
          exact hq'
        }
        simp only [hq', reduceCtorEq, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq]
        rw[Quotient.mk_eq_iff_out]
        change H.cnode _ _
        unfold q'
        have hq'q : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTfe, qn.out)
        rw[cube_cface_ctfe_iff_cnode' hq' (by trivial)] at hq'q
        exact hq'q
      }
      | Sum.inr qf => {
        let q' : Quotient H.cube.fsetoid := ⟦(CTnf, qf.out)⟧
        use q'
        unfold f
        have hq' : q'.out.1 ∈ [CTn, CTen, CTf, CTnf] := by{
          have hq' : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTnf, qf.out)
          apply cface_equivalence.symm at hq'
          apply cube_tag_of_cface' (by{simp}) at hq'
          exact hq'
        }
        have hq'' : q'.out.1 ≠ CTe ∧ q'.out.1 ≠ CTfe := by{
          match hq'' : q'.out.1 with
          | CTn | CTen | CTf | CTnf => trivial
          | CTe | CTfe => simp[hq''] at hq'
        }
        simp only [hq'', ↓reduceIte, Sum.inr.injEq]
        rw[Quotient.mk_eq_iff_out]
        change H.cface _ _
        unfold q'
        have hq'q : H.cube.cface _ _ := Quotient.mk_out (s := H.cube.fsetoid) (CTnf, qf.out)
        rw[cube_cface_iff_cface' hq' (by{simp})] at hq'q
        exact hq'q
      }
    }
  }
  have ih := Fintype.ofEquiv_card e.symm
  apply Eq.mp ?_ ih
  congr
  · apply Subsingleton.elim
}

theorem cube_connected : H.cube.connected ↔ H.connected := by{
  unfold connected
  simp[cube_gcomp]
}

end Hypermap
