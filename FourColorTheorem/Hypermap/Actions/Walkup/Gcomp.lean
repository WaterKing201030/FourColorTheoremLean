import FourColorTheorem.Hypermap.Actions.Walkup.Basic

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def skip_edge'_remain_set (H : Hypermap α) (x : α) :=
  {y : {a // a ≠ x} | ∃z : {a // a ≠ x}, H.clink x z ∧ H.cclink z y}
@[inline] instance skip_edge'_remain_set.instDecidableMem
  {x : α} {y : {a // a ≠ x}} : Decidable (y ∈ H.skip_edge'_remain_set x) := by{
    unfold skip_edge'_remain_set
    rw[Set.mem_setOf_eq]
    infer_instance
  }

theorem mem_skip_edge'_remain_set_iff_cclink {x : α} {y : {a // a ≠ x}}
  : y ∈ skip_edge'_remain_set H x ↔ H.cclink x y :=by{
    unfold skip_edge'_remain_set
    rw[Set.mem_setOf_eq]
    unfold clink
    simp only [union_iff, fromFun, nodeinv_eq_iff_eq_node]
    constructor
    · {
      intro ⟨z, hz, hzy⟩
      apply (ReflTransGen.head · hzy)
      unfold clink
      simp[union_iff, fromFun, nodeinv_eq_iff_eq_node, hz]
    }
    · {
      intro h
      cases em (H.face x = x) with
      | inl hfx => {
        cases em (H.node x = x) with
        | inl hnx => {
          have hex:H.edge x = x:=by{
            nth_rw 1 [←hfx] at hnx
            rw[←H.edge_inj] at hnx
            rw[enf_cancel] at hnx
            exact hnx.symm
          }
          have hbx:=H.isbarb_iff_all_perm_self.mpr ⟨hex, hnx, hfx⟩
          have hbx':=(H.isbarb_cclink_iff hbx).mp h
          rw[Eq.comm] at hbx'
          have hy:=y.prop
          contradiction
        }
        | inr hnx => {
          have hnx': H.nodeinv x ≠ x:=by{
            intro hn
            apply hnx
            nth_rw 1 [←hn]
            rw[nodeinv_eq, comp_apply, nfe_cancel]
          }
          use ⟨H.nodeinv x, hnx'⟩
          simp only [nodeinv_eq, nfe_cancel, comp_apply, true_or, true_and]
          apply (cclink_equivalence.trans · h)
          apply cclink_equivalence.symm
          apply ReflTransGen.single
          simp[clink, fromFun, union_iff, nodeinv_eq]
        }
      }
      | inr hfx => {
        use ⟨H.face x, hfx⟩
        apply And.intro (Or.inr rfl)
        apply (cclink_equivalence.trans · h)
        apply cclink_equivalence.symm
        apply ReflTransGen.single
        simp[clink, fromFun, union_iff]
      }
    }
  }

def skip_edge'_remain_subtype (H : Hypermap α) (x : α) :=
  {a : {a // a ≠ x} // a ∈ H.skip_edge'_remain_set x}
@[inline] instance skip_edge'_remain_subtype.fintype {x : α}
 : Fintype (H.skip_edge'_remain_subtype x)
:= by{
  unfold skip_edge'_remain_subtype
  apply Subtype.fintype
}
def skip_edge'_csetoid (H : Hypermap α) (x : α) : Setoid (skip_edge'_remain_subtype H x)
  := (H.WalkupE x).csetoid.ofSubtype (· ∈ H.skip_edge'_remain_set x)
@[inline] instance skip_edge'_csetoid.dec {x : α} : DecidableRel (H.skip_edge'_csetoid x):=by{
  unfold skip_edge'_csetoid
  apply Setoid.ofSubtype.decidable
}
theorem skip_edge'_csetoid_iff_csetoid {x : α}
  {u v : H.skip_edge'_remain_subtype x}
 : H.skip_edge'_csetoid x u v ↔ (H.WalkupE x).csetoid u.val v.val
  := by{
    have h:=Setoid.ofSubtype_iff (s:=(H.WalkupE x).csetoid) (p:=(· ∈ H.skip_edge'_remain_set x))
      (u:=u) (v:=v)
    exact h
  }
def skip_edge'_remain_set_ncomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.skip_edge'_csetoid x)
def skip_edge'_issplit (H : Hypermap α) (x : α) :=
  H.skip_edge'_remain_set_ncomp x > 1
theorem isbarb_iff_skip_edge'_set_remain_ncomp {x : α}
  : H.isbarb x ↔ H.skip_edge'_remain_set_ncomp x = 0:=by{
    unfold skip_edge'_remain_set_ncomp
    rw[Fintype.nComp_eq_zero_iff]
    unfold skip_edge'_remain_subtype
    rw[isEmpty_subtype]
    unfold skip_edge'_remain_set
    simp only [Set.mem_setOf_eq]
    constructor
    · {
      intro h y ⟨z, hxz, hzy⟩
      apply z.prop
      apply Eq.symm
      apply (H.isbarb_cclink_iff h).mp
      apply ReflTransGen.single hxz
    }
    · {
      intro hy
      cases em (H.face x = x) with
      | inl hfx => {
        cases em (H.node x = x) with
        | inl hnx => {
          exact isbarb_iff_node_face_self.mpr ⟨hnx, hfx⟩
        }
        | inr hnx => {
          have hnx':H.nodeinv x ≠ x:=by{
            rw[ne_eq, ←H.node_inj, Eq.comm]
            simp[nodeinv_eq, nfe_cancel, hnx]
          }
          exfalso
          apply hy ⟨H.nodeinv x, hnx'⟩
          use ⟨H.nodeinv x, hnx'⟩
          simp[cclink_equivalence.refl, clink, union_iff, fromFun]
        }
      }
      | inr hfx => {
        exfalso
        apply hy ⟨H.face x, hfx⟩
        exact ⟨⟨H.face x, hfx⟩, by{simp[clink, union_iff, fromFun]}
          , H.cclink_equivalence.refl _⟩
      }
    }
  }

theorem not_glink_self_and_cross_edge_of_skip_edge'_issplit {x : α}
  (hx : H.skip_edge'_issplit x) : ¬H.glink x x ∧ H.cross_edge x:=by{
    unfold skip_edge'_issplit at hx
    unfold skip_edge'_remain_set_ncomp at hx
    rw[Fintype.nComp_gt_one_iff] at hx
    have ⟨a, b, hab⟩:=hx
    let ⟨a', ha'⟩:=a
    let ⟨b', hb'⟩:=b
    unfold skip_edge'_remain_subtype at a b
    simp only [mem_skip_edge'_remain_set_iff_cclink] at ha' hb'
    unfold skip_edge'_csetoid at hab
    unfold Setoid.ofSubtype at hab
    simp only [InvImage] at hab
    unfold csetoid at hab
    simp only at hab
    have hsub : ∀z:{a // a ≠ x}, z ≠ x:=fun z => z.prop
    have hsub' : ∀z:{a // a ≠ x}, x ≠ z:=fun z => z.prop.symm
    cases em (H.edge x = x) with
    | inl hex => {
      exfalso
      have hnx:H.node x ≠ x:=by{
        intro hnx
        have hfx:H.face x = x:=by{
          nth_rw 1 [←hex, ←hnx, fen_cancel]
        }
        have hbx:=H.isbarb_iff_all_perm_self.mpr ⟨hex, hnx, hfx⟩
        rw[isbarb_cclink_iff hbx, Eq.comm (a:=x)] at ha'
        simp[a'.prop] at ha'
      }
      have hfx:H.face x ≠ x:=by{
        intro hfx
        have hnx:H.node x = x:=by{
          nth_rw 1 [←hfx, ←hex, nfe_cancel]
        }
        have hbx:=H.isbarb_iff_all_perm_self.mpr ⟨hex, hnx, hfx⟩
        rw[isbarb_cclink_iff hbx, Eq.comm (a:=x)] at ha'
        simp[a'.prop] at ha'
      }
      apply hab
      have ha:=(H.cclink_face_iff_of_edge_self hex hfx).mp ha'
      have hb:=(H.cclink_face_iff_of_edge_self hex hfx).mp hb'
      exact (cclink_equivalence.symm ha).trans hb
    }
    | inr hex => {
      have ha'':=(cclink_edge_or_edgeinv_iff_of_not_edge_self hex).mp ha'
      have hb'':=(cclink_edge_or_edgeinv_iff_of_not_edge_self hex).mp hb'
      cases ha'' with
      | inl ha'' => {
        have hb'':=hb''.resolve_left (hab ∘ ((H.WalkupE x).cclink_equivalence.symm ha'').trans)
        have h:H.cross_edge x:=by{
          apply (em (H.cross_edge x)).resolve_right
          intro h
          have h':=not_cross_edge_walkupe_cedge h (u:=⟨H.edge x, hex⟩)
            (v:=⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩)
            rfl rfl
          have h'':=cclink_of_cedge h'
          apply hab
          apply ((H.WalkupE x).cclink_equivalence.symm ha'').trans
          apply h''.trans
          exact hb''
        }
        apply (And.intro · h)
        simp only [glink, union_iff, fromFun, hex, false_or, not_or]
        rw[←not_or]
        intro hnf
        apply hab
        have hnf':(H.WalkupE x).edge ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩
          = ⟨H.edge x, hex⟩:=by{
            rw[H.walkupe_edge]
            ext
            rw[skip_edge'_val]
            simp only
            unfold skip_edge''
            simp only [hex, ↓reduceIte, edgeinv_eq, comp_apply, enf_cancel, ite_eq_left_iff,
              edge_inj]
            rw[not_imp_comm]
            rw[←or_iff_not_imp_left]
            exact hnf
          }
        apply (ReflTransGen.trans · hb'')
        apply cclink_equivalence.symm
        apply (ReflTransGen.trans · ha'')
        apply cclink_of_cedge
        apply ReflTransGen.single
        exact hnf'
      }
      | inr ha'' => {
        have hb'':=hb''.resolve_right (hab ∘ ((H.WalkupE x).cclink_equivalence.symm ha'').trans)
        have h:H.cross_edge x:=by{
          apply (em (H.cross_edge x)).resolve_right
          intro h
          have h':=not_cross_edge_walkupe_cedge h (u:=⟨H.edge x, hex⟩)
            (v:=⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩)
            rfl rfl
          have h'':=cclink_of_cedge h'
          apply hab
          apply cclink_equivalence.symm
          apply ((H.WalkupE x).cclink_equivalence.symm hb'').trans
          apply h''.trans
          exact ha''
        }
        apply (And.intro · h)
        simp only [glink, union_iff, fromFun, hex, false_or, not_or]
        rw[←not_or]
        intro hnf
        apply hab
        have hnf':(H.WalkupE x).edge ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩
          = ⟨H.edge x, hex⟩:=by{
            rw[H.walkupe_edge]
            ext
            rw[skip_edge'_val]
            simp only
            unfold skip_edge''
            simp only [hex, ↓reduceIte, edgeinv_eq, comp_apply, enf_cancel, ite_eq_left_iff,
              edge_inj]
            rw[not_imp_comm]
            rw[←or_iff_not_imp_left]
            exact hnf
          }
        apply cclink_equivalence.symm
        apply (ReflTransGen.trans · ha'')
        apply cclink_equivalence.symm
        apply (ReflTransGen.trans · hb'')
        apply cclink_of_cedge
        apply ReflTransGen.single
        exact hnf'
      }
    }
  }

theorem skip_edge'_remain_set_ncomp_le_two {x : α} :
  H.skip_edge'_remain_set_ncomp x ≤ 2 := by{
    unfold skip_edge'_remain_set_ncomp
    unfold Fintype.nComp
    rw[Fintype.card_le_two_iff]
    rw[isEmpty_quotient_iff]
    cases em (H.isbarb x) with
    | inl hbx => {
      apply Or.inl
      unfold skip_edge'_remain_subtype
      simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink]
      apply Subtype.isEmpty_of_false
      intro u
      rw[H.isbarb_cclink_iff hbx, Eq.comm (a:=x)]
      exact u.prop
    }
    | inr hbx => {
      rw[isbarb_iff_all_perm_self, not_and, not_and] at hbx
      apply Or.inr
      cases em (H.edge x = x) with
      | inl hex => {
        have hnx:H.node x ≠ x:=by{
          intro hnx
          apply hbx hex hnx
          nth_rw 1 [←hex, ←hnx, fen_cancel]
        }
        have hfx:H.face x ≠ x:=by{
          intro hfx
          apply hnx
          nth_rw 1 [←hfx, ←hex, nfe_cancel]
        }
        use ⟦⟨⟨H.face x, hfx⟩, by{
          simp only [mem_skip_edge'_remain_set_iff_cclink]
          apply ReflTransGen.single
          simp[clink, union_iff, fromFun]
        }⟩⟧
        use ⟦⟨⟨H.face x, hfx⟩, by{
          simp only [mem_skip_edge'_remain_set_iff_cclink]
          apply ReflTransGen.single
          simp[clink, union_iff, fromFun]
        }⟩⟧
        intro z
        rw[or_self]
        rw[Quotient.eq_mk_iff_out]
        simp only [ne_eq, skip_edge'_csetoid_iff_csetoid]
        unfold csetoid
        simp only [ne_eq]
        apply cclink_equivalence.symm
        rw[←cclink_face_iff_of_edge_self hex hfx]
        have hz:=z.out.prop
        rw[mem_skip_edge'_remain_set_iff_cclink] at hz
        exact hz
      }
      | inr hex => {
        have hex':=hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr
        use ⟦⟨⟨H.edge x, hex⟩, by{
          simp only [mem_skip_edge'_remain_set_iff_cclink]
          rw[cclink_iff_cglink]
          apply ReflTransGen.single
          simp[glink, union_iff, fromFun]
        }⟩⟧
        use ⟦⟨⟨H.edgeinv x, hex'⟩, by{
          simp only [mem_skip_edge'_remain_set_iff_cclink]
          rw[cclink_iff_cglink]
          apply cglink_equivalence.symm
          apply ReflTransGen.single
          simp[glink, union_iff, fromFun, edgeinv_eq, enf_cancel]
        }⟩⟧
        intro z
        simp only [Quotient.eq_mk_iff_out, skip_edge'_csetoid_iff_csetoid]
        have h:=cclink_edge_or_edgeinv_iff_of_not_edge_self hex (u:=z.out.val)
        unfold csetoid
        simp only
        simp only [cclink_equivalence.symmetric.iff (x:=z.out.val)]
        rw[←h]
        have hz:=z.out.prop
        rw[mem_skip_edge'_remain_set_iff_cclink] at hz
        exact hz
      }
    }
  }

theorem skip_edge'_issplit_iff_card_eq_two {x : α} :
  H.skip_edge'_issplit x ↔ H.skip_edge'_remain_set_ncomp x = 2:=by{
    unfold skip_edge'_issplit
    constructor
    · {
      intro h
      apply Nat.le_antisymm
      · exact skip_edge'_remain_set_ncomp_le_two
      · exact Nat.succ_le_of_lt h
    }
    · intro h; simp[h]
  }
theorem not_skip_edge'_issplit_of_not_cross_edge {x : α}
  (hx : ¬H.cross_edge x) : ¬H.skip_edge'_issplit x := by{
    intro hn
    apply hx
    exact (not_glink_self_and_cross_edge_of_skip_edge'_issplit hn).right
  }

def skip_edge'_complement_subtype (H : Hypermap α) (x : α) :=
  {a : {a // a ≠ x} // a ∉ H.skip_edge'_remain_set x}
@[inline] instance skip_edge'_complement_subtype.fintype
  : Fintype (H.skip_edge'_complement_subtype x)
:= by{
  unfold skip_edge'_complement_subtype
  apply Subtype.fintype
}
def skip_edge'_complement_csetoid (H : Hypermap α) (x : α)
  : Setoid (skip_edge'_complement_subtype H x)
  := (H.WalkupE x).csetoid.ofSubtype (· ∉ H.skip_edge'_remain_set x)
@[inline] instance skip_edge'_complement_csetoid.dec {x : α} :
  DecidableRel (H.skip_edge'_complement_csetoid x):=by{
  unfold skip_edge'_complement_csetoid
  apply Setoid.ofSubtype.decidable
  }


theorem skip_edge'_complement_csetoid_iff_csetoid {x : α}
  {u v : H.skip_edge'_complement_subtype x} :
  H.skip_edge'_complement_csetoid x u v ↔ H.cclink u.val v.val:=by{
    unfold skip_edge'_complement_csetoid
    have h:=Setoid.ofSubtype_iff (s:=(H.WalkupE x).csetoid)
      (p:=(· ∉ H.skip_edge'_remain_set x)) (u:=u) (v:=v)
    nth_rw 2 [csetoid] at h
    simp only at h
    have hu:=u.prop
    simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink] at hu
    rw[walkupe_cclink_of_not_cclink hu] at h
    exact h
  }
def skip_edge'_complement_set_ncomp (H : Hypermap α) (x : α) :=
  Fintype.nComp (H.skip_edge'_complement_csetoid x)

theorem walkupe_gcomp_eq_skip_edge'_remain_add_complement {x : α}
  : (H.WalkupE x).gcomp = H.skip_edge'_remain_set_ncomp x
    + H.skip_edge'_complement_set_ncomp x:=by{
      unfold gcomp
      unfold skip_edge'_remain_set_ncomp
      unfold skip_edge'_complement_set_ncomp
      unfold Fintype.nComp
      simp only
      rw[←Fintype.card_sum]
      let e:Quotient (H.WalkupE x).gsetoid ≃
        Quotient (H.skip_edge'_csetoid x)
        ⊕ Quotient (H.skip_edge'_complement_csetoid x):=by{
          let toFun:Quotient (H.WalkupE x).gsetoid →
            Quotient (H.skip_edge'_csetoid x)
            ⊕ Quotient (H.skip_edge'_complement_csetoid x):=
            fun q => if hq:H.cclink x q.out
            then Sum.inl ⟦⟨q.out, by{
              simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink]
              exact hq
            }⟩⟧
            else Sum.inr ⟦⟨q.out, by{
              simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink]
              exact hq
            }⟩⟧
          let invFun:Quotient (H.skip_edge'_csetoid x)
            ⊕ Quotient (H.skip_edge'_complement_csetoid x) →
            Quotient (H.WalkupE x).gsetoid :=
            fun q => match q with
              | Sum.inl q' => ⟦q'.out.val⟧
              | Sum.inr q' => ⟦q'.out.val⟧
          have left_inv : LeftInverse invFun toFun := by{
            intro q
            unfold toFun
            simp only [ne_eq, apply_dite]
            simp only [invFun]
            cases em (H.cclink x q.out) with
            | inl hcc => {
              simp only [hcc, ↓reduceDIte, Quotient.mk_eq_iff_out]
              let qo:H.skip_edge'_remain_subtype x:=
                ⟨q.out, by{simp[mem_skip_edge'_remain_set_iff_cclink, hcc]}⟩
              change (H.WalkupE x).gsetoid _ _
              unfold gsetoid
              simp only
              have h:=Quotient.mk_out (s:=H.skip_edge'_csetoid x) qo
              unfold skip_edge'_csetoid at h
              have h':=(H.WalkupE x).csetoid.ofSubtype_iff
                (p:=(· ∈ H.skip_edge'_remain_set x))
                (u:=(Quotient.mk (H.skip_edge'_csetoid x) qo).out) (v:=qo)
              nth_rw 2 [csetoid] at h'
              simp only at h'
              rw[cclink_iff_cglink] at h'
              rw[←h']
              apply (Eq.mp · h)
              congr
            }
            | inr hcc => {
              simp only [hcc, ↓reduceDIte, Quotient.mk_eq_iff_out]
              let qo:H.skip_edge'_complement_subtype x:=
                ⟨q.out, by{simp[mem_skip_edge'_remain_set_iff_cclink, hcc]}⟩
              change (H.WalkupE x).gsetoid _ _
              unfold gsetoid
              simp only
              have h:=Quotient.mk_out (s:=H.skip_edge'_complement_csetoid x) qo
              unfold skip_edge'_complement_csetoid at h
              have h':=(H.WalkupE x).csetoid.ofSubtype_iff
                (p:=(· ∉ H.skip_edge'_remain_set x))
                (u:=(Quotient.mk (H.skip_edge'_complement_csetoid x) qo).out) (v:=qo)
              nth_rw 2 [csetoid] at h'
              simp only at h'
              rw[cclink_iff_cglink] at h'
              rw[←h']
              apply (Eq.mp · h)
              congr
            }
          }
          have right_inv : RightInverse invFun toFun := by{
            intro q
            match q with
            | Sum.inl q' => {
              unfold invFun
              simp only
              unfold toFun
              have hq':=q'.out.prop
              have h:=Quotient.mk_out (s:=(H.WalkupE x).csetoid) q'.out.val
              have h':=cclink_of_cclink_WalkupE h
              rw[mem_skip_edge'_remain_set_iff_cclink] at hq'
              have h'':=hq'.trans (cclink_equivalence.symm h')
              rw[dite_cond_eq_true]
              · {
                simp only [ne_eq, Sum.inl.injEq, Quotient.mk_eq_iff_out]
                simp only [skip_edge'_csetoid_iff_csetoid]
                apply (Eq.mp · h)
                congr
                · simp[csetoid_eq_gsetoid]
                simp[csetoid_eq_gsetoid]
              }
              · {
                simp only [ne_eq, eq_iff_iff, iff_true]
                apply (Eq.mp · h'')
                congr
                · simp[csetoid_eq_gsetoid]
                simp[csetoid_eq_gsetoid]
              }
            }
            | Sum.inr q' => {
              unfold invFun
              simp only
              unfold toFun
              have hq':=q'.out.prop
              have h:=Quotient.mk_out (s:=(H.WalkupE x).csetoid) q'.out.val
              have h':=cclink_of_cclink_WalkupE h
              rw[mem_skip_edge'_remain_set_iff_cclink] at hq'
              have h'':=fun h => hq' (ReflTransGen.trans h h')
              rw[dite_cond_eq_false]
              · {
                simp only [ne_eq, Sum.inr.injEq, Quotient.mk_eq_iff_out]
                simp only [skip_edge'_complement_csetoid_iff_csetoid]
                apply (Eq.mp · h')
                congr
                · simp[csetoid_eq_gsetoid]
                simp[csetoid_eq_gsetoid]
              }
              · {
                simp only [ne_eq, eq_iff_iff, iff_false]
                apply (Eq.mp · h'')
                congr
                · simp[csetoid_eq_gsetoid]
                simp[csetoid_eq_gsetoid]
              }
            }
          }
          exact ⟨toFun, invFun, left_inv, right_inv⟩
      }
      have h:=(Fintype.ofEquiv_card e).symm
      apply (Eq.mp · h)
      congr
      apply Subsingleton.elim
    }
theorem walkupe_skip_edge'_complement_ncomp_succ {x : α} :
  H.skip_edge'_complement_set_ncomp x + 1 = H.gcomp := by{
    rw[←Fintype.card_unit]
    unfold skip_edge'_complement_set_ncomp
    unfold gcomp
    unfold Fintype.nComp
    rw[←Fintype.card_sum]
    let e:Quotient H.gsetoid ≃
        Quotient (H.skip_edge'_complement_csetoid x) ⊕ Unit := by{
          let toFun:Quotient H.gsetoid →
            Quotient (H.skip_edge'_complement_csetoid x) ⊕ Unit
          := fun q => if h:H.cclink x q.out then Sum.inr ()
          else Sum.inl ⟦⟨⟨q.out, by{intro h'; simp[h', cclink_equivalence.refl x] at h}⟩,
          by{
            simp[mem_skip_edge'_remain_set_iff_cclink, h]
          }⟩⟧
          let invFun:Quotient (H.skip_edge'_complement_csetoid x) ⊕ Unit →
            Quotient H.gsetoid := fun q => match q with
          | Sum.inl q' => ⟦q'.out.val.val⟧
          | Sum.inr q' => ⟦x⟧
          have left_inv : LeftInverse invFun toFun := by{
            intro q
            unfold toFun
            simp only [apply_dite]
            unfold invFun
            simp only
            cases em (H.cclink x q.out) with
            | inl hqx => {
              simp only [hqx, ↓reduceDIte, Quotient.mk_eq_iff_out]
              change H.cglink x q.out
              simp[←cclink_iff_cglink, hqx]
            }
            | inr hqx => {
              simp only [hqx, ↓reduceDIte, ne_eq, Quotient.mk_eq_iff_out]
              change H.cglink _ _
              have h:=Quotient.mk_out (s:=H.gsetoid) q.out
              unfold gsetoid at h
              simp only at h
              apply (H.cglink_equivalence.trans · h)
              simp only [Quotient.out_eq, ← cclink_iff_cglink]
              have hq:q.out ≠ x:=by{
                intro h'; simp[h', cclink_equivalence.refl x] at hqx
              }
              have h'':=skip_edge'_complement_csetoid_iff_csetoid
                (H:=H) (x:=x) (u:=(Quotient.mk (H.skip_edge'_complement_csetoid x)
                ⟨⟨q.out, by{intro h'; simp[h', cclink_equivalence.refl x] at hqx}⟩,
                by{
                  simp[mem_skip_edge'_remain_set_iff_cclink, hqx]
                }⟩).out)
                (v:=⟨⟨q.out, hq⟩, by{simp[mem_skip_edge'_remain_set_iff_cclink, hqx]}⟩)
              rw[←h'']
              have hq:=Quotient.mk_out (s:=H.skip_edge'_complement_csetoid x)
                ⟨⟨q.out, hq⟩, by{simp[mem_skip_edge'_remain_set_iff_cclink, hqx]}⟩
              exact hq
            }
          }
          have right_inv : RightInverse invFun toFun := by{
            intro q
            unfold invFun
            match q with
            | Sum.inl q' => {
              simp only [ne_eq]
              unfold toFun
              rw[dite_cond_eq_false]
              · {
                simp only [ne_eq, Sum.inl.injEq, Quotient.mk_eq_iff_out]
                simp only [skip_edge'_complement_csetoid_iff_csetoid, ne_eq]
                have hq:=Quotient.mk_out (s:=H.gsetoid) (q'.out.val.val)
                rw[cclink_iff_cglink]
                exact hq
              }
              · {
                have hq:=q'.out.prop
                simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink] at hq
                simp only [eq_iff_iff, iff_false]
                intro hn
                apply hq
                apply cclink_equivalence.trans hn
                have hq:=Quotient.mk_out (s:=H.gsetoid) (q'.out.val.val)
                rw[cclink_iff_cglink]
                exact hq
              }
            }
            | Sum.inr q' => {
              simp only
              unfold toFun
              simp only [cclink_iff_cglink, ne_eq, dite_eq_left_iff, reduceCtorEq, imp_false,
                Decidable.not_not]
              apply H.cglink_equivalence.symm
              have hq:=Quotient.mk_out (s:=H.gsetoid) x
              exact hq
            }
          }
          exact ⟨toFun, invFun, left_inv, right_inv⟩
        }
    have h:=Fintype.ofEquiv_card e
    apply (Eq.mp · h)
    congr
    apply Subsingleton.elim
  }
theorem skip_edge'_remain_set_ncomp_eq_one_of_not_isbarb_and_glink
  {x : α} (hbx : ¬H.isbarb x) (hgx : H.glink x x) :
  H.skip_edge'_remain_set_ncomp x = 1 :=by{
    apply Nat.le_antisymm
    · {
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_le_of_ne
      · exact skip_edge'_remain_set_ncomp_le_two
      rw[←skip_edge'_issplit_iff_card_eq_two]
      intro hs
      have hs':=not_glink_self_and_cross_edge_of_skip_edge'_issplit hs
      simp[hgx] at hs'
    }
    · {
      apply Nat.succ_le_of_lt
      apply Nat.pos_of_ne_zero
      rw[ne_eq, ←isbarb_iff_skip_edge'_set_remain_ncomp]
      apply hbx
    }
}
theorem skip_edge'_remain_set_ncomp_eq_one_of_not_glink_and_not_cross_edge
  {x : α} (hgx : ¬H.glink x x) (hcex : ¬H.cross_edge x) :
  H.skip_edge'_remain_set_ncomp x = 1 :=by{
    apply Nat.le_antisymm
    · {
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_le_of_ne
      · exact skip_edge'_remain_set_ncomp_le_two
      rw[←skip_edge'_issplit_iff_card_eq_two]
      intro hs
      have hs':=not_glink_self_and_cross_edge_of_skip_edge'_issplit hs
      simp[hcex] at hs'
    }
    · {
      apply Nat.succ_le_of_lt
      apply Nat.pos_of_ne_zero
      rw[ne_eq, ←isbarb_iff_skip_edge'_set_remain_ncomp]
      intro hbx
      apply hgx
      simp[isbarb_iff_all_perm_self] at hbx
      simp[glink_iff]
      simp[hbx]
    }
}

@[inline] instance skip_edge'_issplit.decidable
  : DecidablePred H.skip_edge'_issplit := fun x => by{
    rw[skip_edge'_issplit_iff_card_eq_two]
    infer_instance
  }
theorem walkupe_gcomp' {x : α} : (H.WalkupE x).gcomp +
  (if H.glink x x then (if H.isbarb x then 2 else 1)
  else (if H.skip_edge'_issplit x then 0 else 1))
  = H.gcomp + 1
  := by{
    rw[walkupe_gcomp_eq_skip_edge'_remain_add_complement]
    rw[←walkupe_skip_edge'_complement_ncomp_succ (x:=x)]
    rw[Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm]
    apply congrArg
    simp only [Nat.reduceAdd]
    cases em (H.glink x x) with
    | inl hgx => {
      simp only[hgx, ↓reduceIte]
      cases em (H.isbarb x) with
      | inl hbx => {
        simp[hbx, ↓reduceIte]
        simp[isbarb_iff_skip_edge'_set_remain_ncomp.mp hbx]
      }
      | inr hbx => {
        simp[hbx,
        skip_edge'_remain_set_ncomp_eq_one_of_not_isbarb_and_glink hbx hgx]
      }
    }
    | inr hgx => {
      simp only[hgx, ↓reduceIte]
      cases em (H.skip_edge'_issplit x) with
      | inl hcex => {
        simp[hcex, ←skip_edge'_issplit_iff_card_eq_two]
      }
      | inr hcex => {
        simp only [hcex, ↓reduceIte, Nat.reduceEqDiff]
        apply Nat.le_antisymm
        · {
          unfold skip_edge'_issplit at hcex
          exact Nat.le_of_not_lt hcex
        }
        · {
          apply Nat.succ_le_of_lt
          unfold skip_edge'_remain_set_ncomp Fintype.nComp
          simp only [Fintype.card_pos_iff]
          simp[glink_iff] at hgx
          apply Nonempty.intro
          exact ⟦⟨⟨H.edge x, hgx.left⟩, by{
            simp only [ne_eq, mem_skip_edge'_remain_set_iff_cclink]
            simp only [cclink_iff_cglink]
            apply ReflTransGen.single
            simp[glink_iff]
          }⟩⟧
        }
      }
    }
  }
theorem walkupe_gcomp {x : α} : (H.WalkupE x).gcomp = H.gcomp + 1 -
  if H.glink x x then (if H.isbarb x then 2 else 1)
  else (if H.skip_edge'_issplit x then 0 else 1) := by{
    apply Nat.eq_sub_of_add_eq
    exact walkupe_gcomp'
  }


end Hypermap
