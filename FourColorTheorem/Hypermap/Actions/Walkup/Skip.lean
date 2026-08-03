import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Hypermap.Actions.Perm

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

def skip_edge'' (H : Hypermap α) (x : α) : α → α :=
  fun z =>
    if H.edge x = x then H.edge z else
    if H.face (H.edge z) = x then H.edge x else
    if H.edge z = x then H.edge (H.node x) else H.edge z
lemma skip_edge''_subproof {x : α} {u : {a // a ≠ x}}
  : H.skip_edge'' x u ≠ x:=by{
    unfold skip_edge''
    cases em (edge x = x) with
    | inl hx => {
      simp only [hx, ↓reduceIte, ne_eq]
      nth_rw 2 [←hx]
      rw[H.edge_injective.eq_iff]
      exact u.prop
    }
    | inr hx => {
      simp only [hx, ↓reduceIte, ne_eq]
      cases em (H.face (H.edge u.val) = x) with
      | inl hfeu => simp[hfeu, hx]
      | inr hfeu => {
        simp only [hfeu, ↓reduceIte]
        cases em (H.edge u = x) with
        | inl heu => {
          simp only [heu, ↓reduceIte]
          intro hen
          apply hfeu
          rw[heu]
          have hen':=congrArg H.face hen
          rw[fen_cancel] at hen'
          exact hen'.symm
        }
        | inr heu => simp[heu]
      }
    }
  }
def skip_edge' (H : Hypermap α) (x : α) : {a // a ≠ x} → {a // a ≠ x} :=
  fun u => ⟨H.skip_edge'' x u, H.skip_edge''_subproof⟩
lemma skip_edge'_cancel {x : α} : ∀z:{a // a ≠ x}, H.skip_edge' x
  (skip H.node_injective x (skip H.face_injective x z)) = z:=by{
    intro ⟨z, hz⟩
    cases em (H.face z = x) with
    | inl hfz => {
      rw[skip_eq_of_apply_eq H.face_injective hfz]
      simp only
      cases em (H.node (H.face (H.face z)) = x) with
      | inl hnffz => {
        rw[skip_eq_of_apply_eq H.node_injective hnffz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hnffz':H.face z = H.edge x:=by{
          have hnffz':=congrArg H.edge hnffz
          rw[enf_cancel] at hnffz'
          exact hnffz'
        }
        have hex:=hnffz'.symm.trans hfz
        unfold skip_edge''
        simp[hex]
        simp[hnffz', nfe_cancel]
        simp[←hfz, enf_cancel]
      }
      | inr hnffz => {
        rw[skip_eq_of_apply_ne H.node_injective hnffz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hnffz':H.face z ≠ H.edge x:=by{
          intro hnffz'
          apply hnffz
          apply H.edge_injective
          rw[enf_cancel]
          exact hnffz'
        }
        have hex:=Ne.symm (hfz ▸ hnffz')
        unfold skip_edge''
        have hfx:H.face x ≠ x:=by{
          intro h
          apply hz
          have h':=hfz.trans h.symm
          exact H.face_injective h'
        }
        simp only [hex, ↓reduceIte, hfz, enf_cancel, hfx]
        rw[←hfz, enf_cancel]
      }
    }
    | inr hfz => {
      rw[skip_eq_of_apply_ne H.face_injective hfz]
      simp only
      cases em (H.node (H.face z) = x) with
      | inl hnfz => {
        rw[skip_eq_of_apply_eq H.node_injective hnfz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        have hex:H.edge x ≠ x:=by{
          have hnfz':=congrArg H.edge hnfz
          rw[enf_cancel] at hnfz'
          rw[←hnfz']
          exact hz
        }
        unfold skip_edge''
        simp only [hex, ↓reduceIte, hnfz, fen_cancel]
        rw[←hnfz, enf_cancel]
      }
      | inr hnfz => {
        rw[skip_eq_of_apply_ne H.node_injective hnfz]
        simp only
        unfold skip_edge'
        simp only [Subtype.ext_iff]
        unfold skip_edge''
        rw[enf_cancel]
        simp[hfz, hz]
      }
    }
}
theorem skip_edge'_eq_of_glink {x : α} (hx : H.glink x x) : H.skip_edge' x =
  skip H.edge_injective x:=by{
  unfold glink at hx
  repeat rw[union_iff] at hx
  unfold fromFun at hx
  ext ⟨z, hz⟩
  unfold skip_edge' skip_edge''
  simp only [ne_eq]
  cases em (H.edge z = x) with
  | inl hzx => {
    rw[skip_eq_of_apply_eq H.edge_injective hzx]
    simp only [hzx, ↓reduceIte]
    cases hx with
    | inl hx => simp[hx]
    | inr hx => cases hx with
      | inl hx => simp only [hx, ite_self, ite_eq_right_iff]; exact Eq.symm
      | inr hx => simp only [hx, ite_eq_right_iff, ite_true]; exact Eq.symm
  }
  | inr hzx => {
    rw[skip_eq_of_apply_ne H.edge_injective hzx]
    simp only [hzx, ↓reduceIte, ite_eq_left_iff, ite_eq_right_iff]
    intro hex
    simp only [hex, false_or] at hx
    simp only [H.edge_injective.eq_iff, hz.symm, imp_false]
    intro hfez
    cases hx with
    | inl hx => {
      have hfez':=congrArg H.node hfez
      rw[nfe_cancel] at hfez'
      exact hz (hfez'.trans hx)
    }
    | inr hx => {
      have hfez':=hfez.trans hx.symm
      rw[H.face_inj] at hfez'
      contradiction
    }
  }
}
theorem skip_edge'_val {x : α} {u : {a // a ≠ x}}
  : (H.skip_edge' x u).val = H.skip_edge'' x u:=by{
    unfold skip_edge'
    simp
}
@[reducible] def WalkupE (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  ⟨H.skip_edge' x, skip H.node_injective x, skip H.face_injective x, skip_edge'_cancel⟩

theorem walkupe_edge {x : α} : (H.WalkupE x).edge = H.skip_edge' x:=rfl
theorem walkupe_node {x : α} : (H.WalkupE x).node = skip H.node_injective x:=rfl
theorem walkupe_face {x : α} : (H.WalkupE x).face = skip H.face_injective x:=rfl
theorem walkupe_ncomp' {x : α} : (H.WalkupE x).ncomp + (if H.node x = x then 1 else 0)
  = H.ncomp := by{
  have h:=Fintype.nComp_skip_setoid (hf:=H.node_injective) (x:=x)
  exact h
}
theorem walkupe_ncomp {x : α} : (H.WalkupE x).ncomp = H.ncomp - (if H.node x = x then 1 else 0)
  := by{
  apply Nat.eq_sub_of_add_eq
  exact walkupe_ncomp'
}
theorem walkupe_fcomp' {x : α} : (H.WalkupE x).fcomp + (if H.face x = x then 1 else 0)
  = H.fcomp := by{
  have h:=Fintype.nComp_skip_setoid (hf:=H.face_injective) (x:=x)
  exact h
}
theorem walkupe_fcomp {x : α} : (H.WalkupE x).fcomp = H.fcomp - (if H.face x = x then 1 else 0)
  := by{
  apply Nat.eq_sub_of_add_eq
  exact walkupe_fcomp'
}

def cross_edge (H : Hypermap α) (x : α) := H.cedge x (H.node x)
@[inline] instance cross_edge.decidable : DecidablePred H.cross_edge := fun x =>
  (inferInstance : DecidableRel H.cedge) x (H.node x)
theorem not_node_self_of_not_cross_edge {x : α} (hx : ¬H.cross_edge x)
  : H.node x ≠ x:=by{
    intro hn
    unfold cross_edge at hx
    rw[hn] at hx
    exact hx (cedge_equivalence.refl _)
  }
theorem not_face_self_of_not_cross_edge {x : α} (hx : ¬H.cross_edge x)
  : H.face x ≠ x:=by{
    intro hfx
    apply hx
    unfold cross_edge
    nth_rw 2 [←hfx]
    apply cedge_equivalence.symm
    nth_rw 2 [←enf_cancel x]
    apply ReflTransGen.single
    rfl
  }
def isbarb (H : Hypermap α) (x : α) := {y | H.clink x y} ⊆ {x}
theorem isbarb_iff_all_perm_self {x : α}
  : H.isbarb x ↔ H.edge x = x ∧ H.node x = x ∧ H.face x = x:=by{
    unfold isbarb
    rw[Set.subset_singleton_iff]
    simp only [Set.mem_setOf_eq]
    unfold clink
    simp only [union_iff]
    unfold fromFun
    rw[nodeinv_eq, comp_apply]
    constructor
    · {
      intro hy
      have hy':=hy _ (Or.inl rfl)
      have hy'':=hy _ (Or.inr rfl)
      simp only [hy'', and_true]
      nth_rw 3 [←hy']
      rw[nfe_cancel]
      simp only [and_true]
      have hy''':=hy'.trans hy''.symm
      rw[H.face_inj] at hy'''
      exact hy'''
    }
    · {
      intro ⟨he, hn, hf⟩ y
      simp only [hf, Eq.comm (a:=y)]
      nth_rw 1 [←hn]
      rw[fen_cancel, or_self]
      exact id
    }
  }
@[inline] instance isbarb.instDecidable : DecidablePred H.isbarb := by{
  intro x
  simp only [isbarb_iff_all_perm_self]
  infer_instance
}
theorem isbarb_iff_node_face_self {x : α}
  : H.isbarb x ↔ H.node x = x ∧ H.face x = x:=by{
    rw[isbarb_iff_all_perm_self]
    constructor
    · exact fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩
    intro ⟨h1, h2⟩
    apply (And.intro · ⟨h1, h2⟩)
    nth_rw 1 [←h1, ←h2]
    rw[enf_cancel]
  }
theorem glink_self_of_isbarb {x : α} (hx : H.isbarb x)
  : H.glink x x := by{
    unfold glink
    simp[isbarb_iff_all_perm_self] at hx
    simp[fromFun, union_iff, hx]
  }
theorem clink_self_of_isbarb {x : α} (hx : H.isbarb x)
  : H.clink x x := by{
    unfold clink
    simp[isbarb_iff_all_perm_self] at hx
    simp[fromFun, union_iff, hx]
  }
theorem isbarb_cglink_iff {x y : α} (hx : H.isbarb x)
  :H.cglink x y ↔ y = x:=by{
    constructor
    · {
      intro h
      unfold cglink at h
      induction h with
      | refl => rfl
      | tail hxa hay ih => {
        apply (Eq.trans · ih)
        simp[isbarb_iff_all_perm_self] at hx
        simp[fromFun, union_iff, ih, hx, glink] at hay
        simp[ih, hay]
      }
    }
    · exact (· ▸ ReflTransGen.refl)
  }
theorem isbarb_cclink_iff {x y : α} (hx : H.isbarb x)
  : H.cclink x y ↔ x = y:=by{
    simp[cclink_iff_cglink, isbarb_cglink_iff hx, Eq.comm]
  }
theorem isbarb_cedge_iff {x y : α} (hx : H.isbarb x)
  : H.cedge x y ↔ x = y:=by{
    simp only [isbarb_iff_all_perm_self] at hx
    unfold cedge
    simp[funReflTransGen_iff_iterate, iterate_fixed hx.left]
  }
theorem walkupE_clink_of_clink {x : α} {u v : {a // a ≠ x}}
  :H.clink u v → (H.WalkupE x).clink u v:=by{
    unfold WalkupE
    unfold clink
    rw[union_iff, union_iff]
    unfold fromFun
    rw[nodeinv_eq_iff_eq_node, nodeinv_eq_iff_eq_node]
    simp only [Subtype.ext_iff]
    apply Or.imp
    · {
      intro huv
      rw[Function.skip_eq_of_eq H.node_injective huv.symm]
    }
    · {
      intro huv
      rw[Function.skip_eq_of_eq H.face_injective huv]
    }
  }
theorem cclink_of_cclink_WalkupE {x : α} {u v : {a // a ≠ x}}
  : (H.WalkupE x).cclink u v → H.cclink u v:=by{
    unfold cclink
    intro h
    induction h with
    | refl => rfl
    | @tail w b huw hwb ih => {
      apply ih.trans
      unfold clink at hwb
      rw[union_iff] at hwb
      unfold fromFun at hwb
      rw[walkupe_face] at hwb
      rw[nodeinv_eq_iff_eq_node, walkupe_node] at hwb
      cases em (H.face w = x) with
      | inl hwx => {
        have hwx':=skip_eq_of_apply_eq H.face_injective hwx
        rw[hwx'] at hwb
        cases em (H.node b = x) with
        | inl hbx => {
          have hbx':=skip_eq_of_apply_eq H.node_injective hbx
          rw[hbx'] at hwb
          simp only [Subtype.ext_iff] at hwb
          cases hwb with
          | inl hwb => {
            apply ReflTransGen.tail (b:=H.node b)
            · {
              apply ReflTransGen.single
              unfold clink
              rw[union_iff]
              unfold fromFun
              rw[nodeinv_eq_iff_eq_node]
              exact Or.inl hwb
            }
            · {
              unfold clink
              rw[union_iff]
              unfold fromFun
              rw[nodeinv_eq_iff_eq_node]
              simp
            }
          }
          | inr hwb => {
            apply ReflTransGen.tail (b:=H.face w)
            · {
              apply ReflTransGen.single
              unfold clink
              rw[union_iff]
              unfold fromFun
              simp
            }
            · {
              unfold clink
              rw[union_iff]
              unfold fromFun
              exact Or.inr hwb
            }
          }
        }
        | inr hbx => {
          have hbx':=skip_eq_of_apply_ne H.node_injective hbx
          rw[hbx'] at hwb
          simp only [Subtype.ext_iff] at hwb
          cases hwb with
          | inl hwb => {
            apply ReflTransGen.single
            unfold clink
            rw[union_iff]
            unfold fromFun
            rw[nodeinv_eq_iff_eq_node]
            exact Or.inl hwb
          }
          | inr hwb => {
            apply ReflTransGen.tail (b:=H.face w)
            · {
              apply ReflTransGen.single
              unfold clink
              rw[union_iff]
              unfold fromFun
              simp
            }
            · {
              unfold clink
              rw[union_iff]
              unfold fromFun
              exact Or.inr hwb
            }
          }
        }
      }
      | inr hwx => {
        have hwx':=skip_eq_of_apply_ne H.face_injective hwx
        rw[hwx'] at hwb
        cases em (H.node b = x) with
        | inl hbx => {
          have hbx':=skip_eq_of_apply_eq H.node_injective hbx
          rw[hbx'] at hwb
          simp only [Subtype.ext_iff] at hwb
          cases hwb with
          | inl hwb => {
            apply ReflTransGen.tail (b:=H.node b)
            · {
              apply ReflTransGen.single
              unfold clink
              rw[union_iff]
              unfold fromFun
              rw[nodeinv_eq_iff_eq_node]
              exact Or.inl hwb
            }
            · {
              unfold clink
              rw[union_iff]
              unfold fromFun
              rw[nodeinv_eq_iff_eq_node]
              simp
            }
          }
          | inr hwb => {
            apply ReflTransGen.single
            unfold clink
            rw[union_iff]
            unfold fromFun
            exact Or.inr hwb
          }
        }
        | inr hbx => {
          have hbx':=skip_eq_of_apply_ne H.node_injective hbx
          rw[hbx'] at hwb
          simp only [Subtype.ext_iff] at hwb
          apply ReflTransGen.single
          unfold clink
          rw[union_iff]
          unfold fromFun
          rw[nodeinv_eq_iff_eq_node]
          apply hwb
        }
      }
    }
  }

theorem not_cross_edge_walkupe_cedge {x : α} {u v : {a // a ≠ x}}
  (hex : ¬H.cross_edge x) (hux : u = H.edge x) (hvx : v = H.edgeinv x)
  : (H.WalkupE x).cedge u v :=by{
    have h1:H.edge x ≠ x:=hux ▸ u.prop
    have h2:H.cedge u v:=by{
      apply H.cedge_equivalence.symm
      apply ReflTransGen.tail (b:=x)
      · {
        apply ReflTransGen.single
        simp[fromFun, hvx, edgeinv_eq, enf_cancel]
      }
      · simp[fromFun, hux]
    }
    have h3:H.cedge u x:=by{
      apply H.cedge_equivalence.symm
      apply ReflTransGen.single
      simp[fromFun, hux]
    }
    have ⟨n, hnx, hnm⟩:=funReflTransGen_iff_iterate_minimal.mp h3
    have ⟨m, hmv, hmm⟩:=funReflTransGen_iff_iterate_minimal.mp h2
    have hvx':x = H.edge v:=by{
      rw[hvx, edgeinv_eq, comp_apply, enf_cancel]
    }
    have hmn:m + 1 = n:=by{
      have hmv':=congrArg H.edge hmv
      rw[←iterate_succ_apply' H.edge, ←hvx'] at hmv'
      apply Nat.le_antisymm
      · {
        have h1:n > 0:=by{
          apply Nat.pos_of_ne_zero
          intro hn
          rw[hn] at hnx
          simp[u.prop] at hnx
        }
        match n with
        | n' + 1 => {
          apply Nat.succ_le_succ
          rw[iterate_succ_apply'] at hnx
          simp only [ne_eq, hvx', H.edge_inj] at hnx
          have hnm':=(hmm n' · hnx)
          exact Nat.le_of_not_lt hnm'
        }
      }
      · {
        have hnm':=(hnm m.succ · hmv')
        exact Nat.le_of_not_lt hnm'
      }
    }
    have hmx:∀k < n, (H.skip_edge' x)^[k] u = H.edge^[k] u:=by{
      intro k hk
      induction k with
      | zero => rfl
      | succ k' ih => {
        have ih':=ih (Nat.lt_trans (Nat.lt_succ_self _) hk)
        rw[iterate_succ_apply']
        rw[iterate_succ_apply', ←ih']
        rw[skip_edge'_val, ih']
        unfold skip_edge''
        simp only [h1, ↓reduceIte]
        simp only [←iterate_succ_apply']
        simp only [hnm _ hk, ↓reduceIte]
        rw[ite_eq_right_iff]
        intro hn
        rw[Eq.comm, ←faceinv_eq_iff_eq_face, faceinv_eq, comp_apply] at hn
        rw[iterate_succ_apply', edge_inj] at hn
        exfalso
        apply hex
        unfold cross_edge
        rw[hn]
        apply H.cedge_equivalence.trans (y:=u)
        · {
          simp only [← hnx]
          apply H.cedge_equivalence.symm
          apply funReflTransGen_iff_iterate.mpr
          exact ⟨n, rfl⟩
        }
        · {
          apply funReflTransGen_iff_iterate.mpr
          exact ⟨k', rfl⟩
        }
      }
    }
    apply funReflTransGen_iff_iterate.mpr
    use m
    rw[walkupe_edge, Subtype.ext_iff, hmx _ (hmn ▸ Nat.lt_succ_self m)]
    exact hmv
  }

theorem cclink_iff_exists_path_start_nodeinv_or_face {x : α} {u : {a // a ≠ x}}
  : H.cclink x u ↔ ∃p, (x::p).Nodup ∧ List.IsChain H.clink (x::p) ∧ (x::p).getLast? = some u ∧ (
    (p.head? = some (H.nodeinv x) ∧ H.face x ∉ p ∧ H.edge x ≠ x)
    ∨ (p.head? = some (H.face x) ∧ H.nodeinv x ∉ p ∧ H.edge x ≠ x)
    ∨ (p.head? = some (H.nodeinv x) ∧ H.edge x = x)
  ):=by{
    unfold cclink
    constructor
    · {
      rw[ReflTransGen_iff_isChain_minimal_nodup_option]
      intro ⟨l, h0, h1, h2, h3, h4⟩
      match l with
      | a::l' => {
        simp only [List.nodup_cons, List.head?_cons, Option.some.injEq, ne_eq] at h0 h1 h2 h3
        use l'
        simp only [List.nodup_cons, h2 ▸ h0, not_false_eq_true, and_self, h2 ▸ h1, h2 ▸ h3, ne_eq,
          Option.pure_def, Option.bind_eq_bind, Option.bind_some, true_and]
        have hl':l' ≠ []:=by{
          intro hl'
          simp[hl', Eq.comm (a:=a)] at h3
          simp[h2, u.prop] at h3
        }
        match l' with
        | b::l'' => {
          rw[List.isChain_cons_cons] at h1
          have h1':=h1.left
          simp only [clink, h2, union_iff, fromFun] at h1'
          simp only [List.head?_cons, Option.some.injEq, List.mem_cons, not_or]
          cases em (H.nodeinv x = H.face x) with
          | inl hnfx => {
            apply Or.inr
            apply Or.inr
            rw[hnfx, or_self] at h1'
            rw[nodeinv_eq, comp_apply, face_inj] at hnfx
            simp[nodeinv_eq, hnfx, h1']
          }
          | inr hnfx => {
            rw[←or_assoc]
            apply Or.inl
            have hnfx':H.edge x ≠ x:=by{
              rw[nodeinv_eq, comp_apply, face_inj] at hnfx
              exact hnfx
            }
            simp only [hnfx', not_false_eq_true, and_true]
            apply h1'.imp
            · {
              intro hnx
              simp only [hnx, true_and]
              apply And.intro (hnfx ∘ hnx.trans ∘ Eq.symm)
              apply (em (l'' = [])).elim (by{intro h; simp[h]})
              intro hl''_n hfx
              let k:=l''.idxOf (H.face x)
              let lk:=l''.drop k
              have hk:k < l''.length:=by{
                unfold k
                apply List.idxOf_lt_length_of_mem
                exact hfx
              }
              have hlk:lk ≠ []:=by{
                unfold lk
                simp[hk]
              }
              have hl'':l'' = (b::l'').drop 1:=rfl
              have h4':=h4 (x::lk) ⟨by{
                rw[List.isChain_cons_iff_of_ne_nil hlk]
                unfold lk
                simp only [List.head_drop]
                unfold k
                simp only [List.getElem_idxOf]
                rw[hl'', List.drop_drop]
                apply (And.intro · (List.isChain_drop h1.right))
                simp[clink, fromFun, union_iff]
              },by{simp},by{
                unfold lk
                rw[List.getLast?_cons_of_ne_nil hlk]
                unfold lk
                rw[List.getLast?_drop]
                simp[hk]
                simp[List.getLast?_cons_of_ne_nil hl''_n] at h3
                simp[h3]
              }⟩
              unfold lk at h4'
              simp at h4'
              omega
            }
            · {
              intro hnx
              simp only [hnx, true_and]
              apply And.intro (hnfx ∘ (Eq.trans · hnx.symm))
              apply (em (l'' = [])).elim (by{intro h; simp[h]})
              intro hl''_n hfx
              let k:=l''.idxOf (H.nodeinv x)
              let lk:=l''.drop k
              have hk:k < l''.length:=by{
                unfold k
                apply List.idxOf_lt_length_of_mem
                exact hfx
              }
              have hlk:lk ≠ []:=by{
                unfold lk
                simp[hk]
              }
              have hl'':l'' = (b::l'').drop 1:=rfl
              have h4':=h4 (x::lk) ⟨by{
                rw[List.isChain_cons_iff_of_ne_nil hlk]
                unfold lk
                simp only [List.head_drop]
                unfold k
                simp only [List.getElem_idxOf]
                rw[hl'', List.drop_drop]
                apply (And.intro · (List.isChain_drop h1.right))
                simp[clink, fromFun, union_iff]
              },by{simp},by{
                unfold lk
                rw[List.getLast?_cons_of_ne_nil hlk]
                unfold lk
                rw[List.getLast?_drop]
                simp[hk]
                simp[List.getLast?_cons_of_ne_nil hl''_n] at h3
                simp[h3]
              }⟩
              unfold lk at h4'
              simp at h4'
              omega
            }
          }
        }
      }
    }
    · {
      rw[ReflTransGen_iff_isChain_option]
      intro ⟨p, h0, h1, h2, h3⟩
      use x::p
      simp[h1, h2]
    }
  }

theorem walkupE_isChain_clink_of_isChain_clink_map_val {x : α} {l : List {a // a ≠ x}}
  : List.IsChain H.clink (l.map Subtype.val) → List.IsChain (H.WalkupE x).clink l:=by{
    intro h
    match l with
    | [] | [_] => simp
    | a::b::l' => {
      simp only [ne_eq, List.isChain_cons_cons]
      simp only [ne_eq, List.isChain_cons_cons, List.map_cons] at h
      rw[←List.map_cons] at h
      apply (h.imp · walkupE_isChain_clink_of_isChain_clink_map_val)
      exact walkupE_clink_of_clink
    }
  }

theorem cclink_face_iff_of_edge_self {x : α} {u : {a // a ≠ x}} (hex : H.edge x = x)
  (hfx : H.face x ≠ x) : H.cclink x u ↔ (H.WalkupE x).cclink ⟨H.face x, hfx⟩ u:=by{
    constructor
    · {
      intro h
      rw[cclink_iff_exists_path_start_nodeinv_or_face] at h
      have ⟨p, h0, h1, h2, h3⟩:=h
      simp only [hex, ne_eq, not_true_eq_false, and_false, and_true, false_or] at h3
      have hp:p ≠ []:=by{intro hp; simp[hp] at h3}
      rw[List.getLast?_cons_of_ne_nil hp] at h2
      unfold cclink
      rw[ReflTransGen_iff_isChain_option]
      rw[List.nodup_cons] at h0
      use p.attach.map (fun ⟨a, ha⟩ => ⟨a, h0.left ∘ (· ▸ ha)⟩)
      rw[List.isChain_cons_iff_of_ne_nil hp] at h1
      have hnf:H.nodeinv x = H.face x:=by{
        rw[nodeinv_eq, comp_apply, face_inj]
        exact hex
      }
      constructor
      · {
        apply walkupE_isChain_clink_of_isChain_clink_map_val
        simp[h1.right]
      }
      constructor
      · {
        match p with
        | a::p' => {
          simp at h3
          simp[h3, hnf]
        }
      }
      · {
        have ⟨p', a, hl'⟩:=List.ne_nil_iff_exists_concat.mp hp
        simp[←hl'] at h2
        simp[←hl', h2]
      }
    }
    · {
      intro h
      have h':=cclink_of_cclink_WalkupE h
      apply (ReflTransGen.head · h')
      simp[clink, union_iff, fromFun]
    }
  }

theorem cclink_edge_or_edgeinv_iff_of_not_edge_self {x : α} {u : {a // a ≠ x}} (hx : H.edge x ≠ x)
  : H.cclink x u ↔ (H.WalkupE x).cclink ⟨H.edge x, hx⟩ u
  ∨ (H.WalkupE x).cclink ⟨H.edgeinv x, hx ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ u:=by{
    constructor
    · {
      rw[cclink_iff_exists_path_start_nodeinv_or_face]
      simp only [List.nodup_cons, ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hx,
        not_false_eq_true, and_true, and_false, or_false, forall_exists_index, and_imp]
      have hx':=hx ∘ H.edge_eq_self_iff_edgeinv_eq_self.mpr
      intro l h0 h1 h2 h3 h4
      have hnf:H.nodeinv x ≠ H.face x:=by{
        rw[nodeinv_eq, comp_apply, ne_eq, face_inj]
        exact hx
      }
      have hnf':H.nodeinv x ≠ x ∨ H.face x ≠ x:=by{
        cases em (H.face x = x) with
        | inl hfx => {
          apply Or.inl
          intro hnx
          apply hx
          rw[nodeinv_eq, comp_apply] at hnx
          nth_rw 2 [←hfx] at hnx
          rw[face_inj] at hnx
          exact hnx
        }
        | inr hfx => apply Or.inr hfx
      }
      have hl:l ≠ []:=by{
        intro hl
        simp[hl, Eq.comm (a:=x), u.prop] at h3
      }
      have hl':=h2
      rw[List.isChain_cons_iff_of_ne_nil hl] at hl'
      rw[List.head?_eq_some_head hl] at h4
      simp only [Option.some_inj] at h4
      apply h4.imp
      · {
        intro h
        have hnf'':H.nodeinv x ≠ x:=by{
          match l with
          | y::l' => {
            rw[List.mem_cons, not_or] at h0
            rw[List.head_cons] at h
            exact Ne.symm (h.left ▸ h0.left)
          }
        }
        have hcn:(H.WalkupE x).cclink ⟨H.nodeinv x, hnf''⟩ u:=by{
          unfold cclink
          rw[ReflTransGen_iff_isChain_option]
          let l':List {a // a ≠ x}:=l.attach.map fun ⟨a, ha⟩ => ⟨a, fun h => h0 (h ▸ ha)⟩
          use l'
          constructor
          · {
            apply walkupE_isChain_clink_of_isChain_clink_map_val
            unfold l'
            rw[List.map_map]
            simp only [ne_eq, comp_apply, List.map_subtype, List.unattach_attach, List.map_id_fun',
              id_eq]
            exact hl'.right
          }
          constructor
          · {
            unfold l'
            match l with
            | y :: ly => {
              simp at h
              simp[h]
            }
          }
          · {
            have ⟨ly, y, hly⟩:=List.ne_nil_iff_exists_concat.mp hl
            unfold l'
            rw[←hly, ←List.cons_append, List.getLast?_concat, Option.some_inj] at h3
            simp[←hly, h3]
          }
        }
        apply ((H.WalkupE x).cclink_equivalence.trans · hcn)
        have hnf'':H.node x ≠ x:=by{
          rw[nodeinv_eq, comp_apply] at hnf''
          rw[ne_eq, ←node_inj, nfe_cancel] at hnf''
          exact Ne.symm hnf''
        }
        apply ReflTransGen.tail (b:=⟨H.node x, hnf''⟩)
        · {
          apply (H.WalkupE x).cclink_equivalence.symm
          rw[cclink_iff_cglink]
          apply ReflTransGen.single
          rw[glink_iff]
          apply Or.inl
          rw[walkupe_edge]
          ext
          rw[skip_edge'_val]
          simp only
          unfold skip_edge''
          simp[hx, fen_cancel]
        }
        · {
          simp only [clink, union_iff, fromFun]
          apply Or.inl
          rw[nodeinv_eq_iff_eq_node, walkupe_node]
          rw[skip_eq_of_apply_eq H.node_injective (by{simp[nodeinv_eq, nfe_cancel]})]
          simp[nodeinv_eq, nfe_cancel]
        }
      }
      · {
        intro h
        have hnf'':H.face x ≠ x:=by{
          match l with
          | y::l' => {
            rw[List.mem_cons, not_or] at h0
            rw[List.head_cons] at h
            exact Ne.symm (h.left ▸ h0.left)
          }
        }
        have hcn:(H.WalkupE x).cclink ⟨H.face x, hnf''⟩ u:=by{
          unfold cclink
          rw[ReflTransGen_iff_isChain_option]
          let l':List {a // a ≠ x}:=l.attach.map fun ⟨a, ha⟩ => ⟨a, fun h => h0 (h ▸ ha)⟩
          use l'
          constructor
          · {
            apply walkupE_isChain_clink_of_isChain_clink_map_val
            unfold l'
            rw[List.map_map]
            simp only [ne_eq, comp_apply, List.map_subtype, List.unattach_attach, List.map_id_fun',
              id_eq]
            exact hl'.right
          }
          constructor
          · {
            unfold l'
            match l with
            | y :: ly => {
              simp at h
              simp[h]
            }
          }
          · {
            have ⟨ly, y, hly⟩:=List.ne_nil_iff_exists_concat.mp hl
            unfold l'
            rw[←hly, ←List.cons_append, List.getLast?_concat, Option.some_inj] at h3
            simp[←hly, h3]
          }
        }
        apply ((H.WalkupE x).cclink_equivalence.trans · hcn)
        rw[cclink_iff_cglink]
        apply (H.WalkupE x).cglink_equivalence.symm
        apply ReflTransGen.single
        rw [glink_iff]
        apply Or.inr ∘ Or.inl
        rw[walkupe_node]
        ext
        rw[skip_val]
        unfold skip'
        simp[edgeinv_eq] at hx'
        simp[hx', edgeinv_eq]
      }
    }
    · {
      intro h
      cases h with
      | inl h => {
        have h':=cclink_of_cclink_WalkupE h
        apply (H.cclink_equivalence.trans · h')
        rw[cclink_iff_cglink]
        apply ReflTransGen.single
        simp[glink, union_iff, fromFun]
      }
      | inr h => {
        have h':=cclink_of_cclink_WalkupE h
        apply (H.cclink_equivalence.trans · h')
        rw[cclink_iff_cglink]
        apply H.cglink_equivalence.symm
        apply ReflTransGen.single
        simp[glink, union_iff, fromFun, edgeinv_eq, enf_cancel]
      }
    }
  }

theorem walkupe_cclink_of_not_cclink' {x : α} {u v : {a // a ≠ x}}
  (hxv : ¬H.cclink x v) :
  (H.WalkupE x).cclink u v ↔ H.cclink u v:=by{
    constructor
    · exact cclink_of_cclink_WalkupE
    intro h
    unfold cclink at h
    rw[ReflTransGen_iff_isChain_option] at h
    have ⟨l, h0, h1, h2⟩:=h
    unfold cclink
    rw[ReflTransGen_iff_isChain_option]
    let l':List {a // a ≠ x}:=l.attachWith _ (by{
      intro a hl
      intro hax
      apply hxv
      unfold cclink
      rw[ReflTransGen_iff_isChain_option]
      use l.drop (l.idxOf x)
      simp[List.getElem?_idxOf (hax ▸ hl)]
      simp[List.getLast?_drop, List.idxOf_lt_length_of_mem (hax ▸ hl), h2]
      simp[List.isChain_drop h0]
    })
    use l'
    have hl:l ≠ []:=by{intro hl; simp[hl] at h1}
    constructor
    · {
      unfold l'
      apply walkupE_isChain_clink_of_isChain_clink_map_val
      simp[h0]
    }
    constructor
    · {
      unfold l'
      match l with
      | _::_ => simp at h1; simp[h1]
    }
    · {
      unfold l'
      have ⟨q, a, hqa⟩:=List.ne_nil_iff_exists_concat.mp hl
      simp[←hqa] at h2
      simp[←hqa, h2]
    }
  }
theorem walkupe_cclink_of_not_cclink {x : α} {u v : {a // a ≠ x}}
  (hxu : ¬H.cclink x u) :
  (H.WalkupE x).cclink u v ↔ H.cclink u v:=by{
    rw[cclink_equivalence.symmetric.iff]
    rw[walkupe_cclink_of_not_cclink' hxu]
    rw[cclink_equivalence.symmetric.iff]
  }

theorem walkupe_cedge_node_of_cedge_of_not_crossedge {x : α}
  {u : {a // a ≠ x}} (hux : H.cedge u x) (hx : ¬H.cross_edge x)
  : (H.WalkupE x).cedge u ⟨H.node x, not_node_self_of_not_cross_edge hx⟩ := by{
    have hex:H.edge x ≠ x:=by{
      apply cedge_equivalence.symm at hux
      unfold cedge at hux
      intro hex
      simp[funReflTransGen_iff_iterate, iterate_fixed hex, Ne.symm u.prop] at hux
    }
    have hnx:H.node x ≠ x:=not_node_self_of_not_cross_edge hx
    have hcex:=not_cross_edge_walkupe_cedge hx (u:=⟨H.edge x, hex⟩) rfl
      (v:=⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩) rfl
    have hcenx:(H.WalkupE x).cedge ⟨H.node x, hnx⟩ ⟨H.edge x, hex⟩:=by{
      apply ReflTransGen.single
      rw[walkupe_edge, fromFun]
      ext
      rw[skip_edge'_val]
      unfold skip_edge''
      simp[fen_cancel, hex]
    }
    have ⟨n, hn⟩:=Relation.funReflTransGen_iff_iterate_minimal.mp hux
    have hn':n ≠ 0:=by{
      intro hn'
      simp[hn', u.prop] at hn
    }
    match n with | n' + 1 => {
      have hn'u : H.edge^[n'] ↑u = H.edgeinv x ∧ ∀ m < n', H.edge^[m] u ≠ H.edgeinv x:=by{
        constructor
        · {
          apply Eq.symm
          rw[edgeinv_eq_iff_eq_edge]
          rw[iterate_succ_apply'] at hn
          rw[hn.left]
        }
        · {
          intro m hm hmu
          apply hn.right (m + 1) (Nat.succ_lt_succ hm)
          rw[iterate_succ_apply', hmu, edgeinv_eq, comp_apply, enf_cancel]
        }
      }
      have hcex':=cedge_equivalence.trans hcenx hcex
      apply cedge_equivalence.symm at hcex'
      apply (cedge_equivalence.trans · hcex')
      unfold cedge
      rw[funReflTransGen_iff_iterate]
      use n'
      have h:∀m ≤ n', ((H.WalkupE x).edge^[m] u).val = H.edge^[m] u:=by{
        intro m hmn
        induction m with
        | zero => simp
        | succ m' ih => {
          have ih':=ih (Nat.le_of_succ_le hmn)
          rw[iterate_succ_apply']
          nth_rw 1 [walkupe_edge]
          rw[skip_edge'_val, ih']
          unfold skip_edge''
          simp only [hex, ↓reduceIte]
          rw[←iterate_succ_apply' H.edge]
          rw[apply_ite (· = _)]
          have h:=hn.right (m' + 1) (Nat.succ_lt_succ (Nat.lt_of_succ_le hmn))
          simp only [h, ↓reduceIte]
          simp only [Nat.succ_eq_add_one, ne_eq, iterate_succ, comp_apply, if_true_right]
          intro hn
          exfalso
          apply hx
          unfold cross_edge
          rw[←node_inj] at hn
          rw[←iterate_succ_apply, iterate_succ_apply', nfe_cancel] at hn
          apply (cedge_equivalence.symm hux).trans
          rw[funReflTransGen_iff_iterate]
          exact ⟨m', hn⟩
        }
      }
      ext
      simp[h n' (by{simp}), hn'u]
    }
  }
theorem walkupe_cedge_node_of_cedge_node_of_not_crossedge {x : α}
  {u : {a // a ≠ x}} (hux : H.cedge u (H.node x)) (hx : ¬H.cross_edge x)
  : (H.WalkupE x).cedge u ⟨H.node x, not_node_self_of_not_cross_edge hx⟩
  := by{
    have hnx:H.node x ≠ x:=not_node_self_of_not_cross_edge hx
    unfold cedge at hux
    rw[funReflTransGen_iff_iterate_minimal] at hux
    have ⟨n, hn⟩:=hux
    rw[cedge, funReflTransGen_iff_iterate]
    use n
    induction n generalizing u with
    | zero => {simp at hn; simp[Subtype.ext_iff, hn]}
    | succ n' ih => {
      have heu : H.edge u ≠ x:=by{
        intro heu
        apply hx
        unfold cross_edge
        rw[←hn.left]
        simp only [←heu]
        rw[iterate_succ_apply]
        apply funReflTransGen.iterate
      }
      have hnu : u ≠ H.node x:=by{
        exact hn.right 0 (by{simp})
      }
      have hu : (H.WalkupE x).edge u = ⟨H.edge u, heu⟩ := by{
        rw[walkupe_edge]
        ext
        rw[skip_edge'_val]
        simp only
        rw[skip_edge'']
        simp only [ne_eq, ite_eq_left_iff]
        intro hex
        simp only [←node_inj (x:=H.face (H.edge u.val)) (y:=x), nfe_cancel]
        simp only [hnu, heu, ↓reduceIte]
      }
      have ih':=@ih ⟨H.edge u, heu⟩
        ⟨n', by{
          simp only [ne_eq, iterate_succ, comp_apply, Order.lt_add_one_iff] at hn
          apply hn.imp_right
          intro h m hmn'
          have h':=h (m + 1) (Nat.succ_le_of_lt hmn')
          exact h'
        }⟩
        (by{
          simp only [ne_eq, iterate_succ, comp_apply, Order.lt_add_one_iff] at hn
          apply hn.imp_right
          intro h m hmn'
          have h':=h (m + 1) (Nat.succ_le_of_lt hmn')
          exact h'
        })
      rw[←hu] at ih'
      exact ih'
    }
  }

theorem edge_not_cedge_inv_of_not_glink_of_cross_edge {x : α}
    (hgx : ¬H.glink x x) (hcex : H.cross_edge x)
  : ¬(H.WalkupE x).cedge ⟨H.edge x, not_edge_self_of_glink hgx⟩
  ⟨H.edgeinv x, not_edgeinv_self_of_glink hgx⟩ := by{
    have hex:=not_edge_self_of_glink hgx
    have hex':=not_edgeinv_self_of_glink hgx
    have hnx:=not_node_self_of_glink hgx
    have hfx:=not_face_self_of_glink hgx
    unfold cross_edge at hcex
    have hcex':H.cedge (H.edge x) (H.node x) := by{
      apply (cedge_equivalence.trans · hcex)
      apply cedge_equivalence.symm
      apply ReflTransGen.single
      rfl
    }
    rw[cedge, funReflTransGen_iff_iterate_minimal] at hcex'
    have ⟨n, hne, hnn⟩:=hcex'
    have hnn0:∀m > 0, m < n → H.edge^[m] (H.edge x) ≠ H.edge x:=by{
      intro m hmp hmn hen
      apply hnn (n - m) (Nat.sub_lt_of_pos_le hmp (Nat.le_of_lt hmn))
      rw[←hen, ←iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmn), hne]
    }
    have hen:H.edge (H.node x) ≠ x:=by{
      apply Ne.symm
      rw[ne_eq, ←edgeinv_eq_iff_eq_edge, edgeinv_eq, comp_apply, node_inj]
      exact hfx
    }
    have hnn1:∀m < n, H.edge^[m] (H.edge x) ≠ x := by{
      intro m hmp hmn
      cases lt_or_eq_of_le (Nat.succ_le_of_lt hmp) with
      | inl hmp => {
        have hnn0':=hnn0 m.succ (by{simp}) hmp
        rw[←iterate_succ_apply, iterate_succ_apply'] at hnn0'
        rw[ne_eq, edge_inj] at hnn0'
        rw[←iterate_succ_apply] at hmn
        contradiction
      }
      | inr hmp => {
        have hnn':=hnn 0 (by{rw[←hmp]; simp})
        simp only [iterate_zero, id_eq, ne_eq] at hnn'
        rw[←hmp, iterate_succ_apply', hmn] at hne
        contradiction
      }
    }
    have hnn1':∀m ≤ n + 1, H.edge^[m] (H.edge x) ≠ x := by{
      intro m hmn
      cases lt_or_eq_of_le hmn with
      | inl hmn => {
        cases lt_or_eq_of_le (Nat.le_of_lt_succ hmn) with
        | inl hmn => {
          exact hnn1 m hmn
        }
        | inr hmn => {
          rw[hmn, hne]
          exact hnx
        }
      }
      | inr hmn => {
        rw[hmn, iterate_succ_apply', hne]
        exact hen
      }
    }
    have hnn0':∀m > 0, m < n + 1 → H.edge^[m] (H.edge x) ≠ H.edge x:=by{
      simp only [←iterate_succ_apply, iterate_succ_apply', ne_eq, edge_inj]
      intro m hmp hmn
      match m with
      | m' + 1 => {
        rw[iterate_succ_apply]
        apply hnn1'
        exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_lt hmn)
      }
    }
    have hnn2:∀m < n, H.edge^[m] (H.edge x) ≠ H.edgeinv x := by{
      intro m hmp hmn
      cases lt_or_eq_of_le (Nat.succ_le_of_lt hmp) with
      | inl hmp => {
        have hnn0':=hnn1 m.succ hmp
        rw[←iterate_succ_apply, iterate_succ_apply'] at hnn0'
        rw[←iterate_succ_apply] at hmn
        rw[hmn, edgeinv_eq, comp_apply, enf_cancel] at hnn0'
        contradiction
      }
      | inr hmp => {
        rw[←hmp, iterate_succ_apply', hmn, edgeinv_eq, comp_apply, enf_cancel] at hne
        rw[←hne] at hnx
        contradiction
      }
    }
    have hnn2':∀m ≤ n, H.edge^[m] (H.edge x) ≠ H.edgeinv x := by{
      intro m hmn
      cases lt_or_eq_of_le hmn with
      | inl hmn => {
        exact hnn2 m hmn
      }
      | inr hmn => {
        rw[ne_eq, hmn, hne, Eq.comm, edgeinv_eq_iff_eq_edge, Eq.comm]
        exact hen
      }
    }
    have hnn3 : ∀m ≤ n, ((H.WalkupE x).edge^[m] ⟨H.edge x, hex⟩).val = H.edge^[m] (H.edge x):=by{
      intro m hmn
      induction m with
      | zero => simp
      | succ m' ih => {
        rw[iterate_succ_apply']
        nth_rw 1 [walkupe_edge]
        rw[skip_edge'_val, ih (Nat.le_of_succ_le hmn)]
        rw[←iterate_succ_apply]
        rw[←iterate_succ_apply]
        unfold skip_edge''
        rw[←iterate_succ_apply' H.edge]
        simp only [hex, ↓reduceIte]
        have hm:m'.succ.succ ≤ n + 1:=by{
          apply Nat.succ_le_succ
          exact hmn
        }
        have hnn1'':=hnn1' _ (Nat.le_trans (Nat.le_succ _) hm)
        rw[←iterate_succ_apply] at hnn1''
        simp only [hnn1'', ↓reduceIte]
        rw[ite_cond_eq_false]
        simp only [eq_iff_iff, iff_false]
        rw[iterate_succ_apply', ←node_inj, nfe_cancel]
        have hnn':=hnn m' (Nat.lt_of_succ_le hmn)
        exact hnn'
      }
    }
    have hnn3': ∀m, (h:m ≤ n) → (H.WalkupE x).edge^[m] ⟨H.edge x, hex⟩ = ⟨H.edge^[m] (H.edge x), by{
      rw[←hnn3]
      · apply ((H.WalkupE x).edge^[m] ⟨H.edge x, hex⟩).prop
      · apply h
    }⟩:=by{
      simp only [Subtype.ext_iff]
      exact hnn3
    }
    have hen':(H.WalkupE x).edge ⟨H.node x, hnx⟩ = ⟨H.edge x, hex⟩:=by{
      rw[walkupe_edge]
      ext
      rw[skip_edge'_val]
      unfold skip_edge''
      simp only [hex, fen_cancel, ↓reduceIte]
    }
    have hen'':minimalPeriod (H.WalkupE x).edge ⟨H.edge x, hex⟩ = n + 1:=by{
      have hx':IsPeriodicPt (H.WalkupE x).edge (n + 1) ⟨H.edge x, hex⟩:=by{
        unfold IsPeriodicPt IsFixedPt
        rw[iterate_succ_apply']
        rw[hnn3' _ (by rfl)]
        simp only [hne, hen']
      }
      have hx:⟨H.edge x, hex⟩ ∈ periodicPts (H.WalkupE x).edge:=by{
        apply mem_periodicPts.mpr
        use n + 1
        apply And.intro (by{simp})
        exact hx'
      }
      unfold minimalPeriod
      simp only [hx, ↓reduceDIte]
      simp only [Nat.find_eq_iff]
      constructor
      · simp[hx']
      · {
        intro m hm
        simp only [gt_iff_lt, ne_eq, not_and]
        intro hmp
        unfold IsPeriodicPt IsFixedPt
        apply Nat.le_of_lt_succ at hm
        rw[Subtype.ext_iff, hnn3 m hm]
        apply hnn0' _ hmp (Nat.lt_succ_of_le hm)
      }
    }
    have henp:=fun k => iterate_mod_minimalPeriod_eq (f:=(H.WalkupE x).edge) (x:=⟨H.edge x, hex⟩)
      (n:=k)
    rw[hen''] at henp
    rw[cedge, funReflTransGen_iff_iterate]
    simp only [ne_eq, not_exists]
    intro k
    rw[←henp]
    rw[hnn3' _ (by{apply Nat.le_of_lt_succ; apply Nat.mod_lt; simp})]
    simp only [Subtype.ext_iff]
    apply hnn2'
    apply Nat.le_of_lt_succ; apply Nat.mod_lt; simp
  }

theorem walkupe_cedge_edge_of_glink_of_not_edge_self_of_cedge {x : α} {u : {a // a ≠ x}}
  (hgx : H.glink x x) (hex : H.edge x ≠ x) (hu : H.cedge u.val x)
  : (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ := by{
    have hgx':=hgx.resolve_left hex
    simp only [union_iff, fromFun] at hgx'
    have hy':H.cedge x u.val → (H.WalkupE x).cedge u ⟨H.edge x, hex⟩:=by{
      intro hy'
      apply cedge_equivalence.symm at hy'
      rw[cedge, funReflTransGen_iff_iterate_minimal] at hy'
      have ⟨n, hn⟩:=hy'
      apply ReflTransGen.tail (b:=⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩)
      · {
        have hnz:n ≠ 0:=by{
          intro hnz
          simp[hnz, u.prop] at hn
        }
        match n with
        | n' + 1 => {
          apply funReflTransGen_iff_iterate.mpr
          use n'
          have hn':H.edge^[n'] u.val = H.edgeinv x ∧ ∀m < n', H.edge^[m] u.val ≠ H.edgeinv x:=by{
            simp only [ne_eq]
            rw[←edge_inj, ←iterate_succ_apply' H.edge]
            nth_rw 1 [edgeinv_eq, comp_apply, enf_cancel]
            apply hn.imp_right
            intro hn' m hmn
            rw[←edge_inj, ←iterate_succ_apply' H.edge]
            rw[edgeinv_eq, comp_apply, enf_cancel]
            apply hn'
            exact Nat.succ_lt_succ hmn
          }
          have h:∀m ≤ n', ((H.WalkupE x).edge^[m] u).val = H.edge^[m] u.val:=by{
            intro m hmn
            induction m with
            | zero => simp
            | succ m' ih => {
              rw[iterate_succ_apply']
              nth_rw 1 [walkupe_edge]
              rw[skip_edge'_eq_of_glink hgx]
              rw[skip_val]
              rw[ih (Nat.le_of_succ_le hmn)]
              unfold skip'
              rw[ite_cond_eq_false]
              · rw[←iterate_succ_apply' H.edge]
              · {
                simp only [ne_eq, eq_iff_iff, iff_false]
                rw[Nat.succ_le_iff] at hmn
                rw[←iterate_succ_apply' H.edge]
                exact hn.right _ (Nat.succ_lt_succ hmn)
              }
            }
          }
          ext
          rw[h n' (by rfl)]
          exact hn'.left
        }
      }
      · {
        simp only [walkupe_edge]
        ext
        simp only [skip_edge'_eq_of_glink hgx, skip_val]
        unfold skip'
        simp[edgeinv_eq, enf_cancel]
      }
    }
    exact hy' (cedge_equivalence.symm hu)
  }
theorem walkupe_cedge_edge_of_glink_of_not_edge_self_of_cedge_node {x : α} {u : {a // a ≠ x}}
  (hgx : H.glink x x) (hex : H.edge x ≠ x) (hu : H.cedge u.val (H.node x))
  : (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ := by{
    have hgx':=hgx.resolve_left hex
    simp only [union_iff, fromFun] at hgx'
    have hy':H.cedge u.val x → (H.WalkupE x).cedge u ⟨H.edge x, hex⟩:=
      walkupe_cedge_edge_of_glink_of_not_edge_self_of_cedge hgx hex
    cases hgx' with
    | inl hgx' => {
      rw[hgx'] at hu
      exact hy' hu
    }
    | inr hgx' => {
      have hnx:H.node x = H.edgeinv x:=by{
        rw[edgeinv_eq, comp_apply, hgx']
      }
      rw[hnx] at hu
      apply hy'
      apply cedge_equivalence.trans hu
      apply ReflTransGen.single
      simp[fromFun, edgeinv_eq, enf_cancel]
    }
  }

theorem walkupe_cedge_edge_or_edgeinv_of_not_glink_of_cedge {x : α} {u : {a // a ≠ x}}
  (hgx : ¬H.glink x x) (hux : H.cedge u.val x)
  : (H.WalkupE x).cedge u ⟨H.edge x, not_edge_self_of_glink hgx⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, not_edgeinv_self_of_glink hgx⟩ := by{
    have hex:=not_edge_self_of_glink hgx
    have hnx:=not_node_self_of_glink hgx
    have hex':=not_edgeinv_self_of_glink hgx
    have hfx:=not_face_self_of_glink hgx
    unfold cedge at hux
    rw[funReflTransGen_iff_iterate_minimal] at hux
    have ⟨n, hne, hnn⟩:=hux
    have hn:n ≠ 0:=by{
      intro hn
      simp[hn, u.prop] at hne
    }
    match n with
    | n' + 1 => {
      have hne': H.edge^[n'] u.val = H.edgeinv x:=by{
        rw[←edge_inj]
        rw[edgeinv_eq, comp_apply, enf_cancel, ←iterate_succ_apply' H.edge, hne]
      }
      have hnn':∀m < n', H.edge^[m] u.val ≠ H.edgeinv x:=by{
        intro m hmn'
        rw[ne_eq, ←edge_inj, edgeinv_eq, comp_apply, enf_cancel]
        rw[←iterate_succ_apply' H.edge]
        apply hnn
        apply Nat.succ_lt_succ hmn'
      }
      cases em (∃m < n', H.edge^[m] u.val = H.node x) with
      | inl hcex => {
        have ⟨m, hmn, hme⟩:=hcex
        left
        have hen : H.cedge u.val (H.node x) := by{
          rw[cedge, funReflTransGen_iff_iterate]
          use m
        }
        rw[cedge, funReflTransGen_iff_iterate_minimal] at hen
        have ⟨k, hke, hkn⟩:=hen
        have hkm:k = m:=by{
          apply le_antisymm
          · {
            apply le_of_not_gt
            intro hmk
            have hkn':=hkn _ hmk
            exact hkn' hme
          }
          · {
            apply le_of_not_gt
            intro hmk
            have hmnk:n' - m + k < n':=by{
              rw[←Nat.sub_add_comm (Nat.le_of_lt hmn)]
              rw[←Nat.sub_sub_right _ (Nat.le_of_lt hmk)]
              apply Nat.sub_lt_of_pos_le
              · apply Nat.sub_pos_of_lt hmk
              apply Nat.le_trans (Nat.sub_le _ _)
              apply Nat.le_of_lt hmn
            }
            have hnn0:=hnn' _ hmnk
            rw[←hne'] at hnn0
            apply hnn0
            have h0:n' = n' - (m - k) + (m - k):=by{
              rw[Nat.sub_add_cancel]
              apply Nat.le_trans (Nat.sub_le _ _)
              apply Nat.le_of_lt hmn
            }
            nth_rw 2 [h0]
            rw[←Nat.sub_add_comm (Nat.le_of_lt hmn)]
            rw[←Nat.sub_sub_right _ (Nat.le_of_lt hmk)]
            apply H.edge_injective.iterate k
            rw[←iterate_add_apply, ←iterate_add_apply, Nat.add_comm k, Nat.add_comm k]
            rw[Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hmk)]
            rw[iterate_add_apply, iterate_add_apply, hme, hke]
          }
        }
        have ih : ∀i ≤ k, ((H.WalkupE x).edge^[i] u).val = H.edge^[i] u.val:=by{
          intro i hik
          induction i with
          | zero => simp
          | succ i' ih => {
            rw[iterate_succ_apply']
            nth_rw 1 [walkupe_edge]
            rw[skip_edge'_val, ih (Nat.le_of_succ_le hik)]
            unfold skip_edge''
            simp only [hex, ↓reduceIte]
            have h0:H.face (H.edge (H.edge^[i'] u.val)) ≠ x:=by{
              rw[ne_eq, ←node_inj, nfe_cancel]
              apply hkn
              exact Nat.lt_of_succ_le hik
            }
            simp only [h0, ↓reduceIte]
            have h1:H.edge (H.edge^[i'] u.val) ≠ x:=by{
              rw[←iterate_succ_apply' H.edge]
              apply hnn
              apply Nat.lt_succ_of_le
              exact Nat.le_trans hik (Nat.le_of_lt (hkm ▸ hmn))
            }
            simp only [h1, ↓reduceIte]
            rw[←iterate_succ_apply' H.edge]
          }
        }
        rw[cedge, funReflTransGen_iff_iterate]
        use k + 1
        rw[iterate_succ_apply']
        ext
        nth_rw 1 [walkupe_edge]
        rw[skip_edge'_val, ih k (by rfl), hke]
        unfold skip_edge''
        simp only [hex, ↓reduceIte, fen_cancel]
      }
      | inr hcex => {
        simp only [ne_eq, not_exists, not_and] at hcex
        have ih:∀m ≤ n', ((H.WalkupE x).edge^[m] u).val = H.edge^[m] u.val:=by{
          intro m hmn
          induction m with
          | zero => simp
          | succ m' ih => {
            rw[iterate_succ_apply']
            nth_rw 1 [walkupe_edge]
            rw[skip_edge'_val, ih (Nat.le_of_succ_le hmn)]
            unfold skip_edge''
            simp only [hex, ↓reduceIte]
            have h0:H.face (H.edge (H.edge^[m'] u.val)) ≠ x:=by{
              nth_rw 2 [←H.fen_cancel x]
              rw[ne_eq, face_inj, edge_inj]
              apply hcex
              exact Nat.lt_of_succ_le hmn
            }
            simp only [h0, ↓reduceIte]
            have h1:H.edge (H.edge^[m'] u.val) ≠ x:=by{
              rw[ne_eq, ←iterate_succ_apply' H.edge]
              apply hnn
              apply Nat.lt_succ_of_le hmn
            }
            simp only [h1, ↓reduceIte]
            rw[←iterate_succ_apply' H.edge]
          }
        }
        right
        rw[cedge, funReflTransGen_iff_iterate]
        use n'
        ext
        rw[ih n' (by rfl)]
        rw[hne']
      }
    }
  }
theorem walkupe_cedge_edge_or_edgeinv_of_not_glink_of_cedge_node {x : α} {u : {a // a ≠ x}}
  (hgx : ¬H.glink x x) (hux : H.cedge u.val (H.node x))
  : (H.WalkupE x).cedge u ⟨H.edge x, not_edge_self_of_glink hgx⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, not_edgeinv_self_of_glink hgx⟩ := by{
    have hex:=not_edge_self_of_glink hgx
    cases em (H.cross_edge x) with
    | inl hcex => {
      unfold cross_edge at hcex
      have hux':=cedge_equivalence.trans hux (cedge_equivalence.symm hcex)
      exact walkupe_cedge_edge_or_edgeinv_of_not_glink_of_cedge hgx hux'
    }
    | inr hcex => {
      have hux':=walkupe_cedge_node_of_cedge_node_of_not_crossedge hux hcex
      left
      apply hux'.trans
      apply ReflTransGen.single
      rw[walkupe_edge]
      simp[fromFun, skip_edge', skip_edge'', fen_cancel, hex]
    }
  }
theorem walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_cedge {x : α} {u : {a // a ≠ x}}
  (hex : H.edge x ≠ x) (hux : H.cedge u.val x)
  : (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ := by{
    cases em (H.glink x x) with
    | inl hgx => {
      left
      exact walkupe_cedge_edge_of_glink_of_not_edge_self_of_cedge hgx hex hux
    }
    | inr hgx => {
      exact walkupe_cedge_edge_or_edgeinv_of_not_glink_of_cedge hgx hux
    }
  }
theorem walkupe_cedge_edge_or_edgeinv_of_not_edge_self_of_cedge_node {x : α} {u : {a // a ≠ x}}
  (hex : H.edge x ≠ x) (hux : H.cedge u.val (H.node x))
  : (H.WalkupE x).cedge u ⟨H.edge x, hex⟩ ∨
  (H.WalkupE x).cedge u ⟨H.edgeinv x, hex ∘ edge_eq_self_iff_edgeinv_eq_self.mpr⟩ := by{
    cases em (H.glink x x) with
    | inl hgx => {
      left
      exact walkupe_cedge_edge_of_glink_of_not_edge_self_of_cedge_node hgx hex hux
    }
    | inr hgx => {
      exact walkupe_cedge_edge_or_edgeinv_of_not_glink_of_cedge_node hgx hux
    }
  }
theorem cross_edge_iff_not_edge_self_of_not_isbarb_of_glink {x : α} (hbx : ¬H.isbarb x)
  (hgx : H.glink x x) : H.cross_edge x ↔ H.edge x ≠ x:=by{
    constructor
    · {
      intro h0 h1
      rw[cross_edge, cedge, funReflTransGen_iff_iterate] at h0
      simp only [iterate_fixed h1, exists_const] at h0
      simp only [isbarb_iff_all_perm_self, not_and] at hbx
      simp only [h1, ← h0, forall_const] at hbx
      apply hbx
      nth_rw 1 [←h1, h0, fen_cancel]
    }
    · {
      intro h0
      have hgx':=(glink_iff.mp hgx).resolve_left h0
      unfold cross_edge
      cases hgx' with
      | inl hnx => {
        rw[hnx]
        apply ReflTransGen.refl
      }
      | inr hfx => {
        apply cedge_equivalence.symm
        nth_rw 1 [←hfx]
        nth_rw 2 [←enf_cancel x]
        apply ReflTransGen.single
        rfl
      }
    }
  }
theorem cross_edge_of_isbarb {x : α} (hb : H.isbarb x)
  : H.cross_edge x := by{
    simp[isbarb_iff_all_perm_self] at hb
    simp[cross_edge, hb, cedge_equivalence.refl]
  }

@[reducible] def WalkupN (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  (H.permN.WalkupE x).permF
@[reducible] def WalkupF (H : Hypermap α) (x : α) : Hypermap {a // a ≠ x} :=
  (H.permF.WalkupE x).permN

theorem walkupe_nodeinv {x : α} : (H.WalkupE x).nodeinv = skip H.nodeinv_injective x:=by{
  rw[nodeinv, ←Fintype.skip_bijInv_comm H.node_bijective]
  congr
}
theorem walkupe_faceinv {x : α} : (H.WalkupE x).faceinv = skip H.faceinv_injective x:=by{
  rw[faceinv, ←Fintype.skip_bijInv_comm H.face_bijective]
  congr
}

theorem walkupe_cface {x : α} {a b : {a // a ≠ x}} : (H.WalkupE x).cface a b ↔ H.cface a b := by{
  unfold cface
  rw[walkupe_face]
  rw[funReflTransGen_skip]
}
theorem walkupe_cnode {x : α} {a b : {a // a ≠ x}} : (H.WalkupE x).cnode a b ↔ H.cnode a b := by{
  unfold cnode
  rw[walkupe_node]
  rw[funReflTransGen_skip]
}

section walkupe2
lemma walkupe_node_self_of_node_period_two {x : α} (hnx : node x ≠ x)
  (hn2x : node (node x) = x)
  : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ := by{
  simp[walkupe_node, Subtype.ext_iff, skip_val, skip', hn2x]
}
lemma walkupe_face_edge_self_of_node_period_two {x : α} (hnx : node x ≠ x)
  (hn2x : node (node x) = x)
  : (H.WalkupE x).face ((H.WalkupE x).edge ⟨node x, hnx⟩) = ⟨node x, hnx⟩ := by{
  rw[← comp_apply (f:=(H.WalkupE x).face), ← nodeinv_eq, nodeinv_eq_iff_eq_node]
  rw[walkupe_node_self_of_node_period_two hnx hn2x]
}
lemma walkupe2_edge_val_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x)
  (hane : a ≠ edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = H.edge a := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true] at h1nx
    rcases eq_or_ne (edge x) x with hex | hex
    · rw[if_pos hex]
    rw[if_neg hex]
    rw[if_neg hex] at h1nx
    rw[← comp_apply (f:=face), ← nodeinv_eq]
    simp only [H.nodeinv_eq_iff_eq_node, if_neg hanx]
    rw[apply_ite (· = _), edge_inj, edge_inj]
    simp only [ne_eq, if_true_right, Ne.symm hanx]
    rw[← H.edge_injective.eq_iff]
    simp[Hp, h1nx, hanx]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  have haex' : edge a.val.val ≠ x := by{
    contrapose hae
    apply H.edge_injective
    simp[hae, Hp]
  }
  have hanex' : edge a.val.val ≠ node x := by{
    contrapose hane
    apply H.edge_injective
    simp[hane, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val ≠ ⟨node x, hnx⟩ := by{
    simp[Subtype.ext_iff, walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx', haex', hanex']
  }
  rw[if_neg h2]
  simp only [walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx', if_false, haex']
}
lemma walkupe2_edge_val_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a ≠ edge x)
  (hane : a ≠ edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = ⟨⟨H.edge a, by{
    apply H.edge_injective.ne_iff.mp
    rw[plain_iff_edge_edge] at Hp
    simp[Hp, hae]
  }⟩, by{
    simp only [ne_eq, Subtype.ext_iff]
    rw[← H.edge_injective.eq_iff]
    rw[plain_iff_edge_edge] at Hp
    simpa[Hp]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_of_plain_of_node_period_two Hp hnx hn2x hae hane]
}
lemma walkupe2_edge_val_edge_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a = edge x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = edge (node x) := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true, Hp, if_false] at h1nx
    simp only[Hp, if_false, hanx']
    simp only[hae, Hp, if_true]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have haex' : edge a.val.val = x := by{
    apply H.edge_injective
    simp[hae, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val ≠ ⟨node x, hnx⟩ := by{
    simp[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge'', Hp, hanx']
    simp[haex', Hp]
  }
  rw[if_neg h2]
  simp[walkupe_edge, skip_edge'_val, skip_edge'', Hp, hanx']
  simp[haex']
}
lemma walkupe2_edge_val_edge_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (hae : a = edge x)
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a =
  ⟨⟨edge (node x), by{
    rw[plain_iff_edge_edge] at Hp
    apply H.edge_injective.ne_iff.mp
    have ha := a.prop
    simp[Subtype.ext_iff, hae] at ha
    simp[Hp, Ne.symm ha]
  }⟩, by{
    rw[plain_iff_edge_edge] at Hp
    simp[Subtype.ext_iff, Hp]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_edge_of_plain_of_node_period_two Hp hnx hn2x hae]
}
lemma walkupe2_edge_val_edge_node_of_plain_of_node_period_two (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (haen : a = edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a = edge x := by{
  rw[walkupe_edge, skip_edge'_val, skip_edge'']
  have hax := a.val.prop
  have hanx := a.prop
  simp only [ne_eq, Subtype.ext_iff] at hanx
  rw[plain_iff_edge_edge] at Hp
  have hanx' : face (edge a.val.val) ≠ x := by{
    contrapose hanx
    simp[← hanx, nfe_cancel]
  }
  rcases eq_or_ne ((H.WalkupE x).edge ⟨node x, hnx⟩) ⟨node x, hnx⟩ with h1nx | h1nx
  · {
    rw[if_pos h1nx]
    rw[walkupe_edge, skip_edge'_val, skip_edge'']
    rw[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge''] at h1nx
    simp only[fen_cancel, if_true, Hp, if_false] at h1nx
    simp only[Hp, if_false, hanx']
    simp only[haen, Hp, hnx, if_false, h1nx]
  }
  rw[if_neg h1nx]
  have h0 : (H.WalkupE x).face ((H.WalkupE x).edge a.val) ≠ ⟨node x, hnx⟩ := by{
    have h := walkupe_face_edge_self_of_node_period_two hnx hn2x
    nth_rw 2 [← h]
    simp[face_inj, edge_inj, a.prop]
  }
  have h1 : (H.WalkupE x).node ⟨node x, hnx⟩ = ⟨node x, hnx⟩ :=
    walkupe_node_self_of_node_period_two hnx hn2x
  rw[if_neg h0, h1, apply_ite Subtype.val]
  have haenx' : edge a.val.val = node x := by{
    apply H.edge_injective
    simp[haen, Hp]
  }
  have h2 : (H.WalkupE x).edge a.val = ⟨node x, hnx⟩ := by{
    simp[walkupe_edge, Subtype.ext_iff, skip_edge'_val, skip_edge'', Hp, hanx']
    simp[haenx', hnx]
  }
  rw[if_pos h2]
  simp[walkupe_edge, skip_edge'_val, skip_edge'', Hp, fen_cancel]
}
lemma walkupe2_edge_val_edge_node_of_plain_of_node_period_two' (Hp : H.plain)
  {x : α} (hnx : node x ≠ x) (hn2x : node (node x) = x)
  {a : {a : {a // a ≠ x}  // a ≠ ⟨_, hnx⟩}} (haen : a = edge (node x))
  : ((H.WalkupE x).WalkupE ⟨_, hnx⟩).edge a =
  ⟨⟨edge x, by{
    rw[plain_iff_edge_edge] at Hp
    simp[Hp]
  }⟩, by{
    rw[plain_iff_edge_edge] at Hp
    simp only [ne_eq, Subtype.ext_iff]
    apply H.edge_injective.ne_iff.mp
    have ha := a.val.prop
    simp[haen] at ha
    simp[Hp, Ne.symm ha]
  }⟩ := by{
  simp[Subtype.ext_iff, walkupe2_edge_val_edge_node_of_plain_of_node_period_two Hp hnx hn2x haen]
}
lemma walkupe2_cedge_closure (Hp : H.plain)
  {x : α}
  {a b : α} (ha : a ≠ x) (han : a ≠ node x) (hae : a ≠ edge x) (haen : a ≠ edge (node x))
  (hab : H.cedge a b) :
  b ≠ x ∧ b ≠ node x ∧ b ≠ edge x ∧ b ≠ edge (node x) := by{
  rw[Hp.cedge_cases_iff] at hab
  rcases hab with hab | hab
  · simp[← hab, ha, han, hae, haen]
  simp[← hab, Hp.edge_eq_eq_eq_edge, Hp.edge_edge, ha, han, hae, haen]
}
end walkupe2
end Hypermap
