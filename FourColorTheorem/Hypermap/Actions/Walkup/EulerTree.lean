import Init.Data.Nat.Lemmas
import FourColorTheorem.Hypermap.Actions.Walkup.Skip
import FourColorTheorem.Hypermap.Actions.Walkup.Gcomp
import FourColorTheorem.Hypermap.Actions.Walkup.Ecomp
import FourColorTheorem.Hypermap.Actions.Walkup.Jordan

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem glink_self_of_clink_self {x : α} (hcx : H.clink x x) : H.glink x x:=by{
  rw[glink_iff]
  right
  rw[clink, union_iff, fromFun, fromFun, nodeinv_eq_iff_eq_node] at hcx
  apply hcx.imp_left
  apply Eq.symm
}

theorem euler_tree_node_lemma {x : α} (hy : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∀y, H.cedge x y → H.cedge y (H.node y) := by{
    intro a ha
    exact (hy a ha).right
  }
theorem euler_tree_cnode_lemma {x : α} (hy : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∀a b, H.cedge x a → H.cnode a b → H.cedge x b := by{
    intro a b ha hb
    rw[cnode, funReflTransGen_iff_iterate] at hb
    have ⟨n, hn⟩:=hb
    induction n generalizing b with
    | zero => simp at hn; simp[←hn, ha]
    | succ n' ih => {
      have ih:=ih (H.node^[n'] a) ⟨n', rfl⟩ rfl
      apply ih.trans
      rw[←hn, iterate_succ_apply']
      apply euler_tree_node_lemma hy
      exact ih
    }
  }
theorem euler_tree_face_lemma {x : α} (hy : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∀a, H.cedge x a → H.cedge a (H.face a) := by{
    intro a ha
    have h1:H.cedge a (H.edgeinv a):=by{
      apply cedge_equivalence.symm
      apply ReflTransGen.single
      simp[fromFun, edgeinv_rightinv]
    }
    have h2:H.cnode (H.node (H.face a)) (H.face a):=by{
      apply cnode_equivalence.symm
      apply ReflTransGen.single
      simp[fromFun]
    }
    rw[edgeinv_eq, comp_apply] at h1
    have h3:=euler_tree_cnode_lemma hy _ _ (ha.trans h1) h2
    exact (cedge_equivalence.symm ha).trans h3
  }
theorem euler_tree_cface_lemma {x : α} (hy : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∀a b, H.cedge x a → H.cface a b → H.cedge x b := by{
    intro a b ha hb
    rw[cface, funReflTransGen_iff_iterate] at hb
    have ⟨n, hn⟩:=hb
    induction n generalizing b with
    | zero => simp at hn; simp[←hn, ha]
    | succ n' ih => {
      have ih:=ih (H.face^[n'] a) ⟨n', rfl⟩ rfl
      apply ih.trans
      rw[←hn, iterate_succ_apply']
      apply euler_tree_face_lemma hy
      exact ih
    }
  }
theorem exists_edge_fpath (x : α)
  : ∃p, ∃(hpn : p ≠ []), H.cedge x (p.head hpn) ∧ p.IsChain (fromFun H.edge)
  ∧ H.simpleList p ∧ H.cface (p.getLast hpn) (H.edgeinv (p.head hpn)):=by{
    let p':=(List.range (minimalPeriod H.edge x + 1)).map (H.edge^[·] x)
    have hp'c : p'.IsChain (fromFun H.edge) := by{
      simp[List.isChain_iff_getElem, p', fromFun, ←iterate_succ_apply']
    }
    have hp'e : ∀a ∈ p', H.cedge x a:=by{
      simp only [List.mem_iff_getElem, forall_exists_index]
      intro a i hi hia
      simp only [← hia, List.getElem_map, List.getElem_range, p']
      apply funReflTransGen.iterate
    }
    have hp'n : p' ≠ [] := by{
      simp[p']
    }
    have hp'h : p'.head hp'n = x :=by{
      simp[p']
    }
    have hp'l : p'.getLast hp'n = x:=by{
      simp[p']
    }
    have hp'_length : p'.length > 1:=by{
      simp[p', H.edge_injective.minimalPeriod_pos]
    }
    have hp'c_lemma : ∀i, (p'.take i).IsChain (fromFun H.edge) := hp'c.take
    have h0:∃i > 0, ∃(hi : i < p'.length), H.simpleList (p'.take i) := by{
      use 1
      simp[hp'_length, List.take_one, List.head?_eq_some_head hp'n, simpleList]
    }
    have hp's : ¬H.simpleList p':=by{
      intro hp's
      have hp'd:=nodup_of_simpleList hp's
      match p' with
      | _::_::_ => {
        rw[List.nodup_cons] at hp'd
        apply hp'd.left
        rw[List.head_cons] at hp'h
        rw[List.getLast_cons_cons] at hp'l
        rw[hp'h, ←hp'l]
        apply List.getLast_mem
      }
    }
    have h1:∃i > 0, ∃(hi : i < p'.length), H.simpleList (p'.take i)
    ∧ ¬H.simpleList (p'.take (i + 1)) := by{
      have h0':∃i < p'.length, ∃(hi : p'.length - i < p'.length),
        H.simpleList (p'.take (p'.length - i)) := by{
        have ⟨i, hi, hip, hips⟩:=h0
        use p'.length - i
        simp[hi, Nat.lt_trans (Nat.zero_lt_succ 0) hp'_length, hip]
        simp[Nat.sub_sub_eq_min, min_eq_right_of_lt hip, hips]
      }
      have h0'':=exists_minimal_of_wellFoundedLT _ h0'
      simp only [tsub_lt_self_iff, exists_prop, minimal_iff, and_imp] at h0''
      have ⟨j, hj⟩:=h0''
      use p'.length - j
      simp only [gt_iff_lt, tsub_pos_iff_lt, hj, true_and, tsub_lt_self_iff, and_self, exists_const]
      intro h
      have hj1:j > 1:=by{
        apply Nat.lt_of_le_of_ne
        · exact hj.left.right.left.right
        intro hj1
        simp only [← hj1] at h
        rw[←Nat.pred_eq_sub_one, ←Nat.succ_eq_add_one, Nat.succ_pred (by{
          intro h; simp[h] at hj
        }), List.take_length] at h
        revert h
        exact hp's
      }
      have hj':=hj.right (y:=j - 1) (
        Nat.lt_of_le_of_lt (Nat.pred_le _) hj.left.left
      ) (hj.left.right.left.left) (Nat.sub_pos_of_lt hj1) (by{
        rw[Nat.sub_sub_right _ (Nat.le_of_lt hj1), Nat.sub_add_comm (Nat.le_of_lt hj.left.left)]
        exact h
      }) (Nat.pred_le _)
      rw[Eq.comm, ←Nat.pred_eq_sub_one, Nat.pred_eq_self_iff] at hj'
      simp[hj'] at hj1
    }
    have ⟨i, hi, hip, hips, hipns⟩:=h1
    simp only [simpleList, List.map_take] at hipns
    have hipns':∃j, ∃(hji:j < i), ((p'.map (Quotient.mk H.fsetoid)).take (i + 1))[j]'(by{
      simp[Nat.le_of_lt hji, Nat.lt_trans hji hip]
    })
      = ((p'.map (Quotient.mk H.fsetoid)).take (i + 1))[i]'(by{
        simp[hip]
      }) := by{
        apply of_not_not
        intro hj'
        simp only [List.getElem_take, List.getElem_map, not_exists] at hj'
        apply hipns
        rw[List.take_add_one]
        have htmp:=List.getElem?_eq_some_getElem_iff (by{
          simp[hip]
        }: i < (p'.map (Quotient.mk H.fsetoid)).length)
        rw[iff_true] at htmp
        rw[htmp, Option.toList_some, ←List.concat_eq_append, List.nodup_concat]
        rw[simpleList] at hips
        rw[←List.map_take]
        refine ⟨?_, hips⟩
        rw[List.getElem_map]
        intro h
        rw[List.mem_map] at h
        have ⟨a, ha⟩:=h
        rw[List.mem_iff_getElem] at ha
        have ⟨k, hk, hk1⟩:=ha.left
        rw[List.length_take, min_eq_left_of_lt hip] at hk
        have hj'':=hj' k hk
        rw[List.getElem_take] at hk1
        rw[hk1] at hj''
        exact hj'' ha.right
      }
    have ⟨j, hji, hj'⟩:=hipns'
    use (p'.take (i + 1)).drop (j + 1)
    simp only [List.head_drop, List.getElem_take, List.getLast_drop, ne_eq, List.drop_eq_nil_iff,
      List.length_take, inf_le_iff, add_le_add_iff_right, not_or, not_le, hji,
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hji) hip, and_self, exists_true_left]
    apply And.intro (hp'e _ (List.getElem_mem _))
    apply And.intro ((hp'c.take _).drop _)
    rw[and_comm]
    constructor
    · {
      rw[List.getLast_take, Nat.add_sub_cancel,
      (iff_true _).mp (List.getElem?_eq_some_getElem_iff hip)]
      rw[Option.getD_some]
      simp only [List.getElem_take, List.getElem_map, Quotient.eq_iff_equiv] at hj'
      change H.cface p'[j] p'[i] at hj'
      apply cface_equivalence.symm at hj'
      apply (Eq.mp · hj')
      congr
      rw[eq_edgeinv_iff_edge_eq]
      rw[List.isChain_iff_getElem] at hp'c
      apply hp'c
    }
    rw[simpleList] at hips
    have hips':=List.nodup_drop hips (k:=j + 1)
    rw[List.drop_take, Nat.sub_add_comm (Nat.succ_le_of_lt hji), List.take_add_one]
    rw[←List.map_drop, List.drop_take] at hips'
    rw[simpleList, List.map_append]
    rw[(iff_true _).mp (List.getElem?_eq_some_getElem_iff (by{
      simp only [Nat.succ_eq_add_one, List.length_drop]
      apply Nat.sub_lt_sub_right
      · exact Nat.succ_le_of_lt hji
      exact hip
    })), Option.toList_some, List.map_singleton, ←List.concat_eq_append]
    rw[List.nodup_concat]
    refine ⟨?_, hips'⟩
    rw[List.mem_map]
    simp only [Nat.succ_eq_add_one, List.getElem_drop, Nat.add_sub_cancel' (Nat.succ_le_of_lt hji),
      not_exists, not_and]
    simp at hj'
    simp only [← List.drop_take, ← hj']
    have hp''d:=List.nodup_drop hips (k:=j)
    rw[←List.cons_head_tail (l:=List.drop j (List.map (Quotient.mk H.fsetoid) (List.take i p')))
    (by{simp[hji, Nat.lt_trans hji hip]})] at hp''d
    rw[←List.drop_one, List.drop_drop] at hp''d
    rw[List.head_drop, List.getElem_map, List.nodup_cons] at hp''d
    rw[←List.map_drop] at hp''d
    intro x hx hxj
    apply hp''d.left
    rw[List.mem_map]
    use x
    apply And.intro hx
    simp[hxj]
  }
theorem nodup_clink_path_from_isChain_edge {p : List α} (hpn : p ≠ [])
  (hpc : List.IsChain (fromFun edge) p)
  (hps : H.simpleList p) : ∃p', ∃(hp'n : p' ≠ []), p'.head hp'n = H.face (p.head hpn) ∧
  p'.getLast hp'n = p.getLast hpn ∧ p'.Nodup
  ∧ p'.IsChain H.clink ∧ (∀x, x ∈ p'.map (Quotient.mk H.fsetoid) ↔
  x ∈ p.map (Quotient.mk H.fsetoid))
  ∧ (∀x ∈ p, ∀ y, y ∈ (p'.take (p'.idxOf x + 1)).drop (p'.idxOf (H.face x)) ↔
  H.face y ∈ (p'.take (p'.idxOf x + 1)).drop (p'.idxOf (H.face x)))
  ∧ (∀x ∈ p, ∀y, H.cface x y ↔ y ∈ (p'.take (p'.idxOf x + 1)).drop (p'.idxOf (H.face x)))
  ∧ (∀x ∈ p, ∀ y ∈ p, p.idxOf x < p.idxOf y → ∀u, H.cface x u
  → ∀v, H.cface y v → p'.idxOf u < p'.idxOf v)
  ∧ (∀y ∈ p', ∃x ∈ p, H.cface x y)
  ∧ (∀x ∈ p, ((p'.take (p'.idxOf x + 1)).drop
  (p'.idxOf (H.face x))).IsChain (fromFun H.face)) := by{
    have hpd:=nodup_of_simpleList hps
    match p with
    | [a] => {
      rw[List.head_singleton, List.getLast_singleton]
      have hc: H.cface (H.face a) a:=by{
        apply cface_equivalence.symm
        apply ReflTransGen.single
        rfl
      }
      rw[cface, funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup_option] at hc
      have ⟨l, hl⟩:=hc
      use l
      have hln:l ≠ []:=by{intro hln; simp[hln] at hl}
      use hln
      rw[List.head?_eq_some_head hln, List.getLast?_eq_some_getLast hln,
        Option.some_inj, Option.some_inj] at hl
      refine ⟨hl.right.right.left, hl.right.right.right.left, hl.left, ?_⟩
      apply And.intro (by{
        apply hl.right.left.imp
        intro a b hab
        simp only [clink, union_iff]
        right; assumption
      })
      rw[and_comm]
      constructor
      · {
        have h:List.IsChain (fromFun H.face) (a::l) := by{
          rw[List.isChain_cons_iff_of_ne_nil hln]
          rw[hl.right.right.left]
          exact ⟨rfl, hl.right.left⟩
        }
        have h':=List.tail_eq_dropLast_map_of_isChain_fromFun h
        rw[List.tail_cons] at h'
        constructor
        · {
          intro x hx y
          rw[List.mem_singleton] at hx
          have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff
            H.face_injective hln hl.right.left (by{simp[hl]})
          simp only [hx, ←hl.right.right.left]
          simp only [←hl.right.right.right.left]
          simp only [List.idxOf_head, List.drop_zero]
          simp only [List.idxOf_getLast_of_nodup _ hl.left]
          simp only [Nat.sub_add_cancel (List.length_pos_of_ne_nil hln), List.take_length]
          rw[←h0, ←h0]
          change H.cface (l.head hln) y ↔ H.cface (l.head hln) (H.face y)
          simp only [cface_equivalence.comm (a:=l.head hln)]
          rw[cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface y (H.face y))]
        }
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        rw[cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface a (H.face a))]
        rw[←hl.right.right.left, List.idxOf_head, List.drop_zero]
        rw[←hl.right.right.right.left, List.idxOf_getLast_of_nodup _ hl.left, Nat.sub_add_cancel
        (List.length_pos_of_ne_nil hln), List.take_length]
        constructor
        · {
          intro y
          have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff H.face_injective hln
            hl.right.left (by {simp[hl]}) y
          exact h0
        }
        constructor
        · simp
        constructor
        · {
          intro y hy
          use a
          simp only [hl, true_and]
          rw[cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface a (H.face a))]
          have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff H.face_injective hln
              hl.right.left (by {simp[hl]}) y
          rw[hl.right.right.left] at h0
          exact h0.mpr hy
        }
        exact hl.right.left
      }
      intro q
      rw[List.map_singleton, List.mem_singleton]
      have h:∀q' ∈ (List.map (Quotient.mk H.fsetoid) l), q' = ⟦a⟧ := by{
        intro q' hq'
        rw[List.mem_map] at hq'
        have ⟨b, hb⟩:=hq'
        rw[←hb.right, Quotient.eq_iff_equiv]
        change H.cface b a
        refine cface_equivalence.trans ?_
          (cface_equivalence.symm (ReflTransGen.single (a:=a) (b:=H.face a) rfl))
        apply ReflTransGen_of_isChain_of_mem_of_symm hl.right.left hb.left (by{
          rw[←hl.right.right.left]; apply List.head_mem
        }) ⟨fun _ _ => H.cface_equivalence.symm⟩
      }
      apply Iff.intro (h _)
      intro hq
      simp only [hq, List.mem_map]
      use (l.head hln)
      simp only [Quotient.eq_iff_equiv]
      apply And.intro (List.head_mem _)
      symm
      rw[hl.right.right.left]
      apply ReflTransGen.single
      rfl
    }
    | a::b::p' => {
      rw[List.isChain_cons_cons] at hpc
      rw[simpleList, List.map_cons, List.nodup_cons, ←simpleList] at hps
      have ⟨q, hqn, hqh, hql, hqd, hqc, hqq, hqf, hqm, hqi, hqsurj, hqcf⟩:=
        nodup_clink_path_from_isChain_edge (p:=(b::p')) (by { simp }) hpc.right hps.right
      have hca: H.cface (H.face a) a:=by{
        apply cface_equivalence.symm
        apply ReflTransGen.single
        rfl
      }
      rw[cface, funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup_option] at hca
      have ⟨l, hl⟩:=hca
      have hln:l ≠ []:=by{intro hln; simp[hln] at hl}
      use l ++ q
      use (by{simp[hln]})
      rw[List.head?_eq_some_head hln, List.getLast?_eq_some_getLast hln,
        Option.some_inj, Option.some_inj] at hl
      rw[List.head_cons, List.getLast_cons_cons, List.head_append_left hln,
        List.getLast_append_right hqn]
      refine ⟨hl.right.right.left, hql, ?_⟩
      rw[List.head_cons] at hqh
      have hq'd:(l++q).Nodup:=by{
        rw[List.nodup_append']
        refine ⟨hl.left, hqd, ?_⟩
        intro c hcl hcq
        have hqq:=(hqq ⟦c⟧).mp (by{simp only [List.mem_map]; use c})
        apply hps.left
        apply (Eq.mp · hqq)
        apply congrArg (· ∈ _)
        rw[Quotient.eq_iff_equiv]
        change H.cface c a
        refine cface_equivalence.trans ?_
          (cface_equivalence.symm (ReflTransGen.single (a:=a) (b:=H.face a) rfl))
        apply ReflTransGen_of_isChain_of_mem_of_symm hl.right.left hcl
          (hl.right.right.left ▸ List.head_mem _)
        exact ⟨fun _ _ => cface_equivalence.symm⟩
      }
      constructor
      · exact hq'd
      constructor
      · {
        rw[List.isChain_append, List.getLast?_eq_some_getLast hln]
        rw[List.head?_eq_some_head hqn]
        refine ⟨hl.right.left.imp (by{intro a b h; simp only [clink, union_iff]; exact Or.inr h}),
          hqc, ?_⟩
        simp only [Option.mem_def, Option.some.injEq, forall_eq', hl, hqh]
        rw[fromFun] at hpc
        rw[←hpc.left]
        rw[clink, union_iff]
        left
        rw[fromFun, nodeinv_eq, comp_apply]
      }
      constructor
      · {
        intro x
        rw[List.map_append, List.mem_append, List.map_cons, List.mem_cons]
        apply or_congr
        · {
          have h:∀q' ∈ (List.map (Quotient.mk H.fsetoid) l), q' = ⟦a⟧ := by{
            intro q' hq'
            rw[List.mem_map] at hq'
            have ⟨b, hb⟩:=hq'
            rw[←hb.right, Quotient.eq_iff_equiv]
            change H.cface b a
            refine cface_equivalence.trans ?_
              (cface_equivalence.symm (ReflTransGen.single (a:=a) (b:=H.face a) rfl))
            apply ReflTransGen_of_isChain_of_mem_of_symm hl.right.left hb.left (by{
              rw[←hl.right.right.left]; apply List.head_mem
            }) ⟨fun _ _ => H.cface_equivalence.symm⟩
          }
          apply Iff.intro (h _)
          intro hq
          simp only [hq, List.mem_map]
          use (l.head hln)
          simp only [Quotient.eq_iff_equiv]
          apply And.intro (List.head_mem _)
          symm
          rw[hl.right.right.left]
          apply ReflTransGen.single
          rfl
        }
        · exact hqq x
      }
      constructor
      · {
        intro x hx y
        rw[List.mem_cons] at hx
        cases hx with
        | inl hx => {
          have hxm:x ∈ l:=by{
            rw[hx, ←hl.right.right.right.left]
            apply List.getLast_mem
          }
          have hxm':H.face x ∈ l:=by{
            rw[hx, ←hl.right.right.left]
            apply List.head_mem
          }
          rw[List.idxOf_append_of_mem hxm]
          rw[List.idxOf_append_of_mem hxm']
          rw[hx, ←hl.right.right.left, List.idxOf_head, List.drop_zero]
          rw[←hl.right.right.right.left, List.idxOf_getLast_of_nodup _ hl.left]
          rw[Nat.sub_add_cancel (List.length_pos_of_ne_nil hln)]
          rw[List.take_append_length]
          have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff
            H.face_injective hln hl.right.left (by{simp[hl]})
          rw[←h0, ←h0]
          change H.cface (l.head hln) y ↔ H.cface (l.head hln) (H.face y)
          simp only [cface_equivalence.comm (a:=l.head hln)]
          rw[cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface y (H.face y))]
        }
        | inr hx => {
          have ih:=hqf x hx y
          have hxm:x ∈ q:=by{
            have hqm':=(hqm x hx x).mp ReflTransGen.refl
            apply List.mem_of_mem_drop at hqm'
            apply List.mem_of_mem_take at hqm'
            exact hqm'
          }
          have hxm':x ∉ l:=by{
            rw[List.nodup_append_comm, List.nodup_append'] at hq'd
            apply hq'd.right.right hxm
          }
          have hxm'' : H.face x ∉ l:=by{
            have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff
              H.face_injective hln hl.right.left
              (by{simp[hl]})
            rw[←h0]
            rw[←h0] at hxm'
            change ¬H.cface _ _
            change ¬H.cface _ _ at hxm'
            rw[cface_equivalence.comm]
            rw[cface_equivalence.comm] at hxm'
            intro h
            apply hxm'
            refine ReflTransGen.head ?_ h
            rfl
          }
          rw[List.idxOf_append_of_notMem hxm', Nat.add_assoc, List.take_length_add_append]
          rw[List.idxOf_append_of_notMem hxm'', List.drop_length_add_append]
          exact ih
        }
      }
      constructor
      · {
        intro x hx
        rw[List.mem_cons] at hx
        cases hx with
        | inl hx => {
          rw[hx]
          intro y
          rw[←hl.right.right.left, List.idxOf_append_of_mem (List.head_mem _)]
          rw[List.idxOf_head, List.drop_zero, ←hl.right.right.right.left]
          rw[List.idxOf_append_of_mem (List.getLast_mem _),
          List.idxOf_getLast_of_nodup _ hl.left]
          rw[Nat.sub_add_cancel (List.length_pos_of_ne_nil hln), List.take_append_length]
          rw[hl.right.right.right.left,
          cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface a (H.face a))]
          rw[←hl.right.right.left]
          apply List.isChain_fromFun_injective_refltransgen_univ_iff
            H.face_injective hln hl.right.left
          simp[hl]
        }
        | inr hx => {
          have h2:H.face x ∉ l:=by{
            have hqm':=(hqm _ hx (H.face x)).mp (ReflTransGen.single rfl)
            rw[List.nodup_append_comm] at hq'd
            rw[List.nodup_append'] at hq'd
            apply hq'd.right.right
            exact List.mem_of_mem_take (List.mem_of_mem_drop hqm')
          }
          have h1:x ∉ l := by{
            intro h1
            apply h2
            have h3:=List.isChain_fromFun_injective_univ H.face_injective hln hl.right.left
              (by{simp[hl]})
            exact h3 _ h1
          }
          rw[List.idxOf_append_of_notMem h1, List.idxOf_append_of_notMem h2]
          rw[Nat.add_assoc, List.take_length_add_append, List.drop_length_add_append]
          apply hqm
          exact hx
        }
      }
      constructor
      · {
        intro x hx y hy hixy u hu v hv
        rw[List.mem_cons] at hx hy
        have hy': y ≠ a:=by{
          intro hy
          simp[hy] at hixy
        }
        have hy:=hy.resolve_left hy'
        rw[List.idxOf_cons_ne _ hy'.symm] at hixy
        have hvm : v ∈ q := by{
          have hqm':=(hqm y hy v).mp hv
          exact List.mem_of_mem_take (List.mem_of_mem_drop hqm')
        }
        have hvm' : v ∉ l := by{
          rw[List.nodup_append_comm] at hq'd
          rw[List.nodup_append'] at hq'd
          apply hq'd.right.right
          exact hvm
        }
        rw[List.idxOf_append_of_notMem hvm']
        cases hx with
        | inl hx => {
          simp only [hx, List.idxOf_cons_self] at hixy
          have hum : u ∈ l := by{
            have h0:=List.isChain_fromFun_injective_refltransgen_univ H.face_injective hln
              hl.right.left (by{simp[hl]})
            apply h0
            simp only [hl, ← hx]
            change H.cface (H.face x) u
            rw[←cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface x (H.face x))]
            exact hu
          }
          rw[List.idxOf_append_of_mem hum]
          apply Nat.lt_add_right
          exact List.idxOf_lt_length_of_mem hum
        }
        | inr hx => {
          have hx' : x ≠ a:=by{
            rw[List.nodup_cons] at hpd
            intro hx'
            apply hpd.left
            rw[←hx']
            exact hx
          }
          rw[List.idxOf_cons_ne _ hx'.symm] at hixy
          apply Nat.lt_of_succ_lt_succ at hixy
          have hum : u ∈ q := by{
            have hqm':=(hqm x hx u).mp hu
            exact List.mem_of_mem_take (List.mem_of_mem_drop hqm')
          }
          have hum' : u ∉ l := by{
            rw[List.nodup_append_comm] at hq'd
            rw[List.nodup_append'] at hq'd
            apply hq'd.right.right
            exact hum
          }
          rw[List.idxOf_append_of_notMem hum']
          apply Nat.add_lt_add_left
          apply hqi x hx y hy hixy u hu v hv
        }
      }
      constructor
      · {
        intro y hy
        rw[List.mem_append] at hy
        cases hy with
        | inl hy => {
          use a
          simp only [List.mem_cons, true_or, true_and]
          rw[cface_pred_eq_of_cface (ReflTransGen.single rfl:H.cface a (H.face a))]
          have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff H.face_injective
            hln hl.right.left (by{simp[hl]}) y
          rw[hl.right.right.left] at h0
          exact h0.mpr hy
        }
        | inr hy => {
          have ⟨x, hx⟩:=hqsurj y hy
          use x
          simp[hx]
        }
      }
      · {
        intro x hx
        rw[List.mem_cons] at hx
        cases hx with
        | inl hx => {
          rw[hx, ←hl.right.right.left, ←hl.right.right.right.left]
          rw[List.idxOf_append_of_mem (List.head_mem _), List.idxOf_head, List.drop_zero]
          rw[List.idxOf_append_of_mem (List.getLast_mem _),
          List.idxOf_getLast_of_nodup _ hl.left]
          rw[Nat.sub_add_cancel (List.length_pos_of_ne_nil hln), List.take_append_length]
          exact hl.right.left
        }
        | inr hx => {
          have h2:H.face x ∉ l:=by{
            have hqm':=(hqm _ hx (H.face x)).mp (ReflTransGen.single rfl)
            rw[List.nodup_append_comm] at hq'd
            rw[List.nodup_append'] at hq'd
            apply hq'd.right.right
            exact List.mem_of_mem_take (List.mem_of_mem_drop hqm')
          }
          have h1:x ∉ l := by{
            intro h1
            apply h2
            have h3:=List.isChain_fromFun_injective_univ H.face_injective hln hl.right.left
              (by{simp[hl]})
            exact h3 _ h1
          }
          rw[List.idxOf_append_of_notMem h1, List.idxOf_append_of_notMem h2]
          rw[Nat.add_assoc, List.take_length_add_append, List.drop_length_add_append]
          apply hqcf
          exact hx
        }
      }
    }
  }
theorem exists_edge_fpath_contour_between_edge_fpath (x : α)
  : ∃p, ∃(hpn : p ≠ []), H.cedge x (p.head hpn) ∧ p.IsChain (fromFun H.edge)
  ∧ H.simpleList p ∧ H.cface (p.getLast hpn) (H.edgeinv (p.head hpn)) ∧
  ∃p', ∃(hp'n : p' ≠ []), p'.head hp'n = H.face (p.head hpn)
  ∧ p'.getLast hp'n = H.edgeinv (p.head hpn) ∧ p'.Nodup ∧ p'.IsChain H.clink
  ∧ (∀x, x ∈ p'.map (Quotient.mk H.fsetoid) ↔ x ∈ p.map (Quotient.mk H.fsetoid))
  ∧ (∀x, H.face x ∈ p' → x ∈ (p.getLast hpn :: p').dropLast) := by{
    have ⟨p, hpn, hpe, hpc, hps, hpf⟩:=H.exists_edge_fpath x
    refine ⟨p, hpn, hpe, hpc, hps, hpf, ?_⟩
    have hpd:=nodup_of_simpleList hps
    have ⟨q, hqn, hqh, hql, hqd, hqc, hqq, hqf, hqm, hqi, hqsurj, hqcf⟩:=
      H.nodup_clink_path_from_isChain_edge hpn hpc hps
    use q.take (q.idxOf (H.edgeinv (p.head hpn)) + 1)
    have hq'n:List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1) q ≠ []:=by{
      simp[hqn]
    }
    have h0:H.edgeinv (p.head hpn) ∈ q:=by{
      have hqm':=(hqm (p.getLast hpn) (List.getLast_mem _) _).mp hpf
      exact List.mem_of_mem_take (List.mem_of_mem_drop hqm')
    }
    use hq'n
    rw[List.head_take, List.getLast_take, Nat.add_sub_cancel]
    rw[List.getElem?_idxOf h0, Option.getD_some, edgeinv_injective.eq_iff]
    refine ⟨hqh, rfl, ?_⟩
    constructor
    · {
      apply List.nodup_take
      exact hqd
    }
    constructor
    · {
      apply List.isChain_take
      exact hqc
    }
    constructor
    · {
      intro qx
      constructor
      · {
        intro hqx
        rw[←hqq]
        rw[List.map_take] at hqx
        exact List.mem_of_mem_take hqx
      }
      · {
        intro hqx
        rw[←List.concat_dropLast_getLast hpn, List.map_append] at hqx
        rw[List.map_singleton, List.mem_append, List.mem_singleton] at hqx
        cases hqx with
        | inl hqx => {
          rw[←Quotient.out_eq qx] at hqx
          rw[List.mem_map] at hqx
          have ⟨a, ha, haq⟩:=hqx
          rw[Quotient.eq_iff_equiv] at haq
          have hqm':=(hqm a (List.mem_of_mem_dropLast ha) qx.out).mp haq
          have hqm'':=List.mem_of_mem_drop hqm'
          rw[←Quotient.out_eq qx, List.mem_map]
          use qx.out
          refine ⟨?_, rfl⟩
          apply List.mem_take_of_mem_take_le hqm''
          apply Nat.succ_le_succ
          apply Nat.le_of_lt
          have hqi':=hqi a (List.mem_of_mem_dropLast ha) (p.getLast hpn) (List.getLast_mem _) (
            by{
              rw[List.idxOf_getLast_of_nodup _ hpd]
              have h0:List.idxOf a p.dropLast = p.idxOf a:=by{
                nth_rw 2 [←List.concat_dropLast_getLast hpn]
                rw[List.idxOf_append_of_mem ha]
              }
              rw[←h0]
              rw[←List.length_dropLast]
              apply List.idxOf_lt_length_of_mem ha
            }
          ) a ReflTransGen.refl (H.edgeinv (p.head hpn)) hpf
          exact hqi'
        }
        | inr hqx => {
          rw[hqx]
          rw[List.mem_map]
          use H.edgeinv (p.head hpn)
          constructor
          · {
            refine (Eq.mp ?_ (List.getLast_mem
            (l:=List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1) q) (by{simp[hqn]})))
            apply congrArg (· ∈ _)
            rw[List.getLast_take, Nat.add_sub_cancel, List.getElem?_idxOf h0]
            simp
          }
          symm
          rw[Quotient.eq_iff_equiv]
          exact hpf
        }
      }
    }
    · {
      intro a hfa
      have h1:q.idxOf (H.face (p.getLast hpn)) ≤ q.idxOf (H.edgeinv (p.head hpn)):=by{
        have hqm':=(hqm (p.getLast hpn) (List.getLast_mem _) (H.edgeinv (p.head hpn))).mp hpf
        have hqm'' : H.edgeinv (p.head hpn) ∈ List.drop (q.idxOf (H.face (p.getLast hpn))) q := by{
          rw[List.drop_take] at hqm'
          exact List.mem_of_mem_take hqm'
        }
        apply List.idxOf_ge_of_mem_drop_of_nodup
        · exact hqm''
        · exact hqd
      }
      have h2:List.drop (List.idxOf (face (p.getLast hpn)) q)
          (List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1) q) ≠ [] := by{
        simp only [ne_eq, List.drop_eq_nil_iff, List.length_take, inf_le_iff,
          not_or, not_le]
        rw[Nat.lt_succ_iff]
        apply And.intro h1
        apply List.idxOf_lt_length_of_mem
        have hqm':=(hqm (p.getLast hpn) (List.getLast_mem _) (H.face (p.getLast hpn))).mp
          (ReflTransGen.single rfl)
        apply List.mem_of_mem_drop at hqm'
        apply List.mem_of_mem_take at hqm'
        exact hqm'
      }
      rw[←List.take_append_drop (q.idxOf (H.face (p.getLast hpn))) (List.take _ _)] at hfa
      rw[List.mem_append] at hfa
      rw[←List.take_append_drop (List.idxOf (face (p.getLast hpn)) q)
      (List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1) q)]
      rw[←List.cons_append, List.dropLast_append_of_ne_nil h2]
      rw[List.mem_append, List.mem_cons, or_assoc, or_left_comm]
      rw[←List.mem_cons]
      cases em (H.face a ∈ q.take (q.idxOf (H.face (p.getLast hpn)))) with
      | inl hfa' => {
        left
        have hfa'':¬H.cface (H.face a) (p.getLast hpn) := by{
          intro hfa''
          have hqm':=(hqm (p.getLast hpn) (List.getLast_mem _) (H.face a)).mp
            (cface_equivalence.symm hfa'')
          nth_rw 2 [←hql] at hqm'
          rw[List.idxOf_getLast_of_nodup _ hqd] at hqm'
          rw[Nat.sub_add_cancel (List.length_pos_of_ne_nil hqn)] at hqm'
          rw[List.take_length] at hqm'
          rw[←List.take_append_drop (List.idxOf (H.face (p.getLast hpn)) q) q] at hqd
          rw[List.nodup_append'] at hqd
          exact hqd.right.right hfa' hqm'
        }
        rw[List.take_take, min_eq_left_of_lt (by{
          apply Nat.lt_succ_of_le
          exact h1
        })]
        have ⟨b, hb⟩:=hqsurj (H.face a) (List.mem_of_mem_take hfa')
        have hqf':=hqf b hb.left a
        have hqm':=(hqm b hb.left (H.face a)).mp hb.right
        rw[←hqf'] at hqm'
        have hqm'':=List.mem_of_mem_drop hqm'
        apply List.mem_take_of_mem_take_le hqm''
        apply Nat.succ_le_of_lt
        refine hqi b hb.left (p.getLast hpn) (List.getLast_mem _) ?_ b ReflTransGen.refl
          (H.face (p.getLast hpn)) (ReflTransGen.single rfl)
        have hb':b ∈ p.dropLast:=by{
          rw[←List.concat_dropLast_getLast hpn, List.mem_append, List.mem_singleton] at hb
          apply hb.left.resolve_right
          intro hb'
          apply hfa''
          apply cface_equivalence.symm
          rw[←hb']
          exact hb.right
        }
        nth_rw 1 [←List.concat_dropLast_getLast hpn]
        rw[List.idxOf_append_of_mem hb']
        rw[List.idxOf_getLast_of_nodup _ hpd]
        rw[←List.length_dropLast]
        apply List.idxOf_lt_length_of_mem hb'
      }
      | inr hfa' => {
        right
        have hfa'': H.face a ∈ (List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1)
          q).drop (q.idxOf (H.face (p.getLast hpn))) := by{
          apply hfa.resolve_left
          rw[List.take_take, min_eq_left_of_lt (by{
            apply Nat.lt_succ_of_le
            exact h1
          })]
          exact hfa'
        }
        rw[←List.cons_head_tail h2] at hfa''
        rw[List.mem_cons] at hfa''
        rw[List.mem_cons]
        apply hfa''.imp
        · {
          rw[List.head_drop]
          rw[List.getElem_take]
          rw[List.getElem_idxOf]
          rw[face_inj]
          exact id
        }
        · {
          have hq'cf := hqcf (p.getLast hpn) (List.getLast_mem _)
          have h3:(List.drop (List.idxOf (face (p.getLast hpn)) q)
            (List.take (List.idxOf (H.edgeinv (p.head hpn)) q + 1) q)) <+:
            (List.drop (List.idxOf (face (p.getLast hpn)) q)
            (List.take (List.idxOf (p.getLast hpn) q + 1) q)):=by{
              rw[List.drop_take, List.drop_take]
              apply List.take_prefix_take_left
              apply Nat.sub_le_sub_right
              apply Nat.succ_le_succ
              rw[←hql, List.idxOf_getLast_of_nodup _ hqd]
              apply Nat.le_pred_of_lt
              apply List.idxOf_lt_length_of_mem
              exact h0
            }
          have hq''cf := hq'cf.prefix h3
          rw[List.tail_eq_dropLast_map_of_isChain_fromFun hq''cf]
          rw[List.mem_map_of_injective H.face_injective]
          exact id
        }
      }
    }
  }

theorem cross_edge_exists_fpath_contor_between_edge_fpath_exists_disjoint_fpath {x : α}
  (hce : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∃p1, ∃(hp1n : p1 ≠ []), H.cedge x (p1.head hp1n) ∧ p1.IsChain (fromFun H.edge)
  ∧ H.simpleList p1 ∧ H.cface (p1.getLast hp1n) (H.edgeinv (p1.head hp1n)) ∧
  ∃q1, ∃(hq1n : q1 ≠ []), q1.head hq1n = H.face (p1.head hp1n)
  ∧ q1.getLast hq1n = H.edgeinv (p1.head hp1n) ∧ q1.Nodup ∧ q1.IsChain H.clink
  ∧ (∀x, x ∈ q1.map (Quotient.mk H.fsetoid) ↔ x ∈ p1.map (Quotient.mk H.fsetoid))
  ∧ (∀x, H.face x ∈ q1 → x ∈ (p1.getLast hp1n :: q1).dropLast) ∧ ∃p2, ∃(hp2n : p2 ≠ []),
  p2.head hp2n = H.edgeinv (p1.head hp1n) ∧ p2.getLast hp2n = H.face (p1.head hp1n)
  ∧ p2.IsChain (fromFun H.edgeinv) ∧ p2.Nodup ∧ p2.Disjoint p1
  := by{
    have ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, hq1⟩:=H.exists_edge_fpath_contour_between_edge_fpath x
    have ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f⟩:=hq1
    refine ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, ?_⟩
    refine ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f, ?_⟩
    have hp1d:=nodup_of_simpleList hp1s
    have h_lemma : minimalPeriod H.edgeinv = minimalPeriod H.edge := by{
      rw[edgeinv, Fintype.bijInv_minimalPeriod]
    }
    have h0 : H.face (p1.head hp1n) ∉ p1 := by{
      intro h
      rw[simpleList] at hp1s
      match p1 with
      | a::p1' => {
        simp only [List.head_cons, List.mem_cons] at h
        simp only [List.head_cons] at hp1e
        have hce':=hce a hp1e
        rw[clink, union_iff, fromFun, not_or, fromFun] at hce'
        simp only [hce', false_or] at h
        rw[List.map_cons, List.nodup_cons] at hp1s
        apply hp1s.left
        have hp1s':=(List.mem_map (f:=Quotient.mk H.fsetoid)).mpr ⟨H.face a, h, rfl⟩
        apply (Eq.mp · hp1s')
        apply congrArg (· ∈ _)
        rw[Quotient.eq_iff_equiv]
        symm
        apply ReflTransGen.single
        rfl
      }
    }
    have hc0 : H.cedge (p1.head hp1n) (H.edgeinv (p1.head hp1n)) := by{
      apply cedge_equivalence.symm
      apply ReflTransGen.single
      rw[fromFun, edgeinv_rightinv]
    }
    have hc1 : H.cedge (p1.head hp1n) (H.face (p1.head hp1n)) := by{
      apply euler_tree_face_lemma hce
      exact hp1e
    }
    have hc2 := cedge_equivalence.trans (cedge_equivalence.symm hc0) hc1
    have hce': ∀ y, H.cedge (p1.head hp1n) y → ¬H.clink y y ∧ H.cross_edge y := by{
      rw[cedge_pred_eq_of_cedge hp1e] at hce
      exact hce
    }
    have h1 : H.edgeinv (p1.head hp1n) ≠ H.face (p1.head hp1n) := by{
      rw[edgeinv_eq, comp_apply]
      have hce'':=hce' (H.face (p1.head hp1n)) hc1
      rw[clink, union_iff, fromFun, not_or, fromFun] at hce''
      rw[nodeinv_eq_iff_eq_node] at hce''
      exact Ne.symm hce''.left.left
    }
    have h2 : funReflTransGen H.edgeinv (H.edgeinv (p1.head hp1n)) (H.face (p1.head hp1n))
      := funReflTransGen_bijInv H.edge_bijective hc2
    rw[funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup_option] at h2
    have ⟨l, hld, hlc, hlh, hll, hlm⟩:=h2
    have hln:l ≠ []:=by{intro hln; simp[hln] at hlh}
    rw[List.head?_eq_some_head hln, Option.some_inj] at hlh
    rw[List.getLast?_eq_some_getLast hln, Option.some_inj] at hll
    use l
    use hln
    refine ⟨hlh, hll, hlc, hld, ?_⟩
    have hlc':=(List.isChain_bijInv_iff_isChain_reverse H.edge_bijective).mp hlc
    have ⟨l', hl'd, hl'c, hl'h, hl'l, hl'm⟩:=ReflTransGen_iff_isChain_minimal_nodup_option.mp hc0
    have hl'n : l' ≠ [] := by{intro hl'n; simp[hl'n] at hl'h}
    rw[List.head?_eq_some_head hl'n, Option.some_inj] at hl'h
    rw[List.getLast?_eq_some_getLast hl'n, Option.some_inj] at hl'l
    have h3 : p1 <+: l' :=by{
      refine List.prefix_isChain_fromFun_of_head_eq_of_mem_getLast_of_nodup hp1n hl'n
        hl'h.symm ?_ hp1c hl'c hp1d
      have h3:=List.isChain_fromFun_injective_refltransgen_univ_iff H.edge_injective hl'n
        hl'c (by{rw[hl'l, hl'h, edgeinv_rightinv]})
      rw[←h3, hl'h]
      rw[funReflTransGen, ReflTransGen_iff_isChain_option]
      use p1
      apply And.intro hp1c
      apply And.intro (List.head?_eq_some_head _)
      apply List.getLast?_eq_some_getLast _
    }
    rw[←List.disjoint_reverse_left, List.disjoint_comm]
    rw[List.prefix_iff_eq_append] at h3
    have h4 : H.face (p1.head hp1n) ∈ l' := by{
      have h4:=List.isChain_fromFun_injective_refltransgen_univ_iff H.edge_injective hl'n
        hl'c (by{rw[hl'l, hl'h, edgeinv_rightinv]})
      rw[←h4, hl'h]
      exact hc1
    }
    rw[←h3, List.mem_append] at h4
    apply (Or.resolve_left · h0) at h4
    have hl'n':=List.ne_nil_of_mem h4
    have h5 : l.reverse <:+ l'.drop p1.length := by{
      apply List.suffix_isChain_fromFun_injective_of_getLast_eq_of_mem_head_of_nodup
        H.edge_injective (by{simp[hln]}) hl'n' (by{simp[hlh, hl'l]}) ?_ hlc'
        (List.isChain_drop hl'c) (by{simp[hld]})
      rw[List.head_reverse, hll]
      exact h4
    }
    rw[←h3, List.nodup_append'] at hl'd
    apply List.disjoint_of_subset_right ?_ hl'd.right.right
    apply h5.subset
  }

theorem cross_edge_exists_fpath_contor_between_edge_fpath_exists_disjoint_fpath' {x : α}
  (hce : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∃p1, ∃(hp1n : p1 ≠ []), H.cedge x (p1.head hp1n) ∧ p1.IsChain (fromFun H.edge)
  ∧ H.simpleList p1 ∧ H.cface (p1.getLast hp1n) (H.edgeinv (p1.head hp1n)) ∧
  ∃q1, ∃(hq1n : q1 ≠ []), q1.head hq1n = H.face (p1.head hp1n)
  ∧ q1.getLast hq1n = H.edgeinv (p1.head hp1n) ∧ q1.Nodup ∧ q1.IsChain H.clink
  ∧ (∀x, x ∈ q1.map (Quotient.mk H.fsetoid) ↔ x ∈ p1.map (Quotient.mk H.fsetoid))
  ∧ (∀x, H.face x ∈ q1 → x ∈ (p1.getLast hp1n :: q1).dropLast) ∧ ∃p2, ∃(hp2n : p2 ≠ []),
  p2.head hp2n = H.edgeinv (H.edgeinv (p1.head hp1n)) ∧ p2.getLast hp2n = H.face (p1.head hp1n)
  ∧ p2.IsChain (fromFun H.edgeinv) ∧ p2.Nodup ∧ p2.Disjoint p1
  := by{
    have ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, hq1⟩:=H.exists_edge_fpath_contour_between_edge_fpath x
    have ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f⟩:=hq1
    refine ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, ?_⟩
    refine ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f, ?_⟩
    have hp1d:=nodup_of_simpleList hp1s
    have h_lemma : minimalPeriod H.edgeinv = minimalPeriod H.edge := by{
      rw[edgeinv, Fintype.bijInv_minimalPeriod]
    }
    have h0 : H.face (p1.head hp1n) ∉ p1 := by{
      intro h
      rw[simpleList] at hp1s
      match p1 with
      | a::p1' => {
        simp only [List.head_cons, List.mem_cons] at h
        simp only [List.head_cons] at hp1e
        have hce':=hce a hp1e
        rw[clink, union_iff, fromFun, not_or, fromFun] at hce'
        simp only [hce', false_or] at h
        rw[List.map_cons, List.nodup_cons] at hp1s
        apply hp1s.left
        have hp1s':=(List.mem_map (f:=Quotient.mk H.fsetoid)).mpr ⟨H.face a, h, rfl⟩
        apply (Eq.mp · hp1s')
        apply congrArg (· ∈ _)
        rw[Quotient.eq_iff_equiv]
        symm
        apply ReflTransGen.single
        rfl
      }
    }
    have hc0 : H.cedge (p1.head hp1n) (H.edgeinv (p1.head hp1n)) := by{
      apply cedge_equivalence.symm
      apply ReflTransGen.single
      rw[fromFun, edgeinv_rightinv]
    }
    have hc1 : H.cedge (p1.head hp1n) (H.face (p1.head hp1n)) := by{
      apply euler_tree_face_lemma hce
      exact hp1e
    }
    have hc2 := cedge_equivalence.trans (cedge_equivalence.symm hc0) hc1
    have hce': ∀ y, H.cedge (p1.head hp1n) y → ¬H.clink y y ∧ H.cross_edge y := by{
      rw[cedge_pred_eq_of_cedge hp1e] at hce
      exact hce
    }
    have h1 : H.edgeinv (p1.head hp1n) ≠ H.face (p1.head hp1n) := by{
      rw[edgeinv_eq, comp_apply]
      have hce'':=hce' (H.face (p1.head hp1n)) hc1
      rw[clink, union_iff, fromFun, not_or, fromFun] at hce''
      rw[nodeinv_eq_iff_eq_node] at hce''
      exact Ne.symm hce''.left.left
    }
    have h2 : funReflTransGen H.edgeinv (H.edgeinv (p1.head hp1n)) (H.face (p1.head hp1n))
      := funReflTransGen_bijInv H.edge_bijective hc2
    have h3 : funReflTransGen H.edgeinv (H.edgeinv (H.edgeinv (p1.head hp1n)))
      (H.face (p1.head hp1n))
      := by{
        apply funReflTransGen_symm_of_injective H.edgeinv_injective
        apply funReflTransGen_symm_of_injective H.edgeinv_injective at h2
        apply ReflTransGen.tail h2
        rfl
      }
    rw[funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup_option] at h3
    have ⟨l, hld, hlc, hlh, hll, hlm⟩:=h3
    have hln:l ≠ []:=by{intro hln; simp[hln] at hlh}
    rw[List.head?_eq_some_head hln, Option.some_inj] at hlh
    rw[List.getLast?_eq_some_getLast hln, Option.some_inj] at hll
    use l
    use hln
    refine ⟨hlh, hll, hlc, hld, ?_⟩
    have hlc':=(List.isChain_bijInv_iff_isChain_reverse H.edge_bijective).mp hlc
    have ⟨l', hl'd, hl'c, hl'h, hl'l, hl'm⟩:=ReflTransGen_iff_isChain_minimal_nodup_option.mp hc0
    have hl'n : l' ≠ [] := by{intro hl'n; simp[hl'n] at hl'h}
    rw[List.head?_eq_some_head hl'n, Option.some_inj] at hl'h
    rw[List.getLast?_eq_some_getLast hl'n, Option.some_inj] at hl'l
    have h3 : p1 <+: l' :=by{
      refine List.prefix_isChain_fromFun_of_head_eq_of_mem_getLast_of_nodup hp1n hl'n
        hl'h.symm ?_ hp1c hl'c hp1d
      have h3:=List.isChain_fromFun_injective_refltransgen_univ_iff H.edge_injective hl'n
        hl'c (by{rw[hl'l, hl'h, edgeinv_rightinv]})
      rw[←h3, hl'h]
      rw[funReflTransGen, ReflTransGen_iff_isChain_option]
      use p1
      apply And.intro hp1c
      apply And.intro (List.head?_eq_some_head _)
      apply List.getLast?_eq_some_getLast _
    }
    rw[←List.disjoint_reverse_left, List.disjoint_comm]
    rw[List.prefix_iff_eq_append] at h3
    have h4 : H.face (p1.head hp1n) ∈ l' := by{
      have h4:=List.isChain_fromFun_injective_refltransgen_univ_iff H.edge_injective hl'n
        hl'c (by{rw[hl'l, hl'h, edgeinv_rightinv]})
      rw[←h4, hl'h]
      exact hc1
    }
    rw[←h3, List.mem_append] at h4
    apply (Or.resolve_left · h0) at h4
    have hl'n':=List.ne_nil_of_mem h4
    have h4': H.face (p1.head hp1n) ∈ (l'.drop p1.length).dropLast:=by{
      rw[←List.dropLast_append_getLast hl'n'] at h4
      rw[List.mem_append, List.mem_singleton] at h4
      apply h4.resolve_right
      rw[List.getLast_drop, hl'l]
      exact h1.symm
    }
    have hl''n':=List.ne_nil_of_mem h4'
    have hl''l : (l'.drop p1.length).dropLast.getLast hl''n' = H.edgeinv (H.edgeinv (p1.head hp1n))
      := by{
        have h':=hl'c.drop p1.length
        rw[←List.dropLast_append_getLast hl'n'] at h'
        rw[List.isChain_concat_iff_of_ne_nil hl''n'] at h'
        rw[fromFun, ←eq_edgeinv_iff_edge_eq] at h'
        rw[h'.right, edgeinv_injective.eq_iff]
        rw[List.getLast_drop, hl'l]
      }
    have h5 : l.reverse <:+ (l'.drop p1.length).dropLast := by{
      apply List.suffix_isChain_fromFun_injective_of_getLast_eq_of_mem_head_of_nodup
        H.edge_injective (by{simp[hln]}) hl''n' ?_ (by{simp[h4', hll]}) hlc'
        ((List.isChain_drop hl'c).dropLast) (by{simp[hld]})
      simp[hl''l, hlh]
    }
    rw[←h3, List.nodup_append'] at hl'd
    apply List.disjoint_of_subset_right ?_ hl'd.right.right
    apply h5.subset.trans
    apply List.dropLast_subset
  }

theorem cross_edge_exists_moebius_path_lemma {x : α}
  (hce : ∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y)
  : ∃p1, ∃(hp1n : p1 ≠ []), H.cedge x (p1.head hp1n) ∧ p1.IsChain (fromFun H.edge)
  ∧ H.simpleList p1 ∧ H.cface (p1.getLast hp1n) (H.edgeinv (p1.head hp1n)) ∧
  ∃q1, ∃(hq1n : q1 ≠ []), q1.head hq1n = H.face (p1.head hp1n)
  ∧ q1.getLast hq1n = H.edgeinv (p1.head hp1n) ∧ q1.Nodup ∧ q1.IsChain H.clink
  ∧ (∀x, x ∈ q1.map (Quotient.mk H.fsetoid) ↔ x ∈ p1.map (Quotient.mk H.fsetoid))
  ∧ (∀x, H.face x ∈ q1 → x ∈ (p1.getLast hp1n :: q1).dropLast) ∧ ∃p2, ∃(hp2n : p2 ≠ []),
  p2.head hp2n = H.edgeinv (H.edgeinv (p1.head hp1n)) ∧ p2.getLast hp2n = H.face (p1.head hp1n)
  ∧ p2.IsChain (fromFun H.edgeinv) ∧ p2.Nodup ∧ p2.Disjoint p1 ∧ ∃q2, ∃(hq2n : q2 ≠ []),
  q2.head hq2n = H.nodeinv (p2.head hp2n) ∧ q2.getLast hq2n = p2.getLast hp2n
  ∧ q2.IsChain H.clink ∧ (∀x ∈ p2, (q2.drop
  ((p2.take (p2.idxOf x)).map (minimalPeriod H.nodeinv)).sum).take (minimalPeriod H.nodeinv x)
  = (List.range (minimalPeriod H.nodeinv x)).map (H.nodeinv^[·] (H.nodeinv x))) ∧
  q2.length = (p2.map (minimalPeriod H.nodeinv)).sum ∧ (∀i, (hiq2 : i < q2.length) →
  (∀n, ((p2.take n).map (minimalPeriod H.nodeinv)).sum ≠ i) → H.nodeinv q2[i - 1] = q2[i])
   := by{
    have ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, hq1⟩:=
      H.cross_edge_exists_fpath_contor_between_edge_fpath_exists_disjoint_fpath' hce
    have ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f, hp2⟩:=hq1
    have ⟨p2, hp2n, hp2h, hp2l, hp2c, hp2d, hp2dj⟩:=hp2
    refine ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, ?_⟩
    refine ⟨q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f, ?_⟩
    refine ⟨p2, hp2n, hp2h, hp2l, hp2c, hp2d, hp2dj, ?_⟩
    use (p2.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
    (H.nodeinv^[·] (H.nodeinv a)))).flatten
    have hq2n:(p2.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
      (H.nodeinv^[·] (H.nodeinv a)))).flatten ≠ []:=by{
      simp only [ne_eq, List.flatten_eq_nil_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, List.map_eq_nil_iff, List.range_eq_nil,
        Nat.ne_zero_of_lt H.nodeinv_injective.minimalPeriod_pos, imp_false, not_forall,
        Decidable.not_not]
      use p2.head hp2n
      apply List.head_mem
    }
    use hq2n
    have hq2hn:(p2.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
      (H.nodeinv^[·] (H.nodeinv a)))).head (by{simp[hp2n]}) ≠ []:=by{
        simp[Nat.ne_zero_of_lt H.nodeinv_injective.minimalPeriod_pos]
      }
    constructor
    · {
      rw[List.head_flatten_eq_head_head hq2n hq2hn]
      simp
    }
    have hq2ln:(p2.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
      (H.nodeinv^[·] (H.nodeinv a)))).getLast (by{simp[hp2n]}) ≠ []:=by{
        simp[Nat.ne_zero_of_lt H.nodeinv_injective.minimalPeriod_pos]
      }
    have h0:∀a, minimalPeriod H.nodeinv (H.nodeinv a) = minimalPeriod H.nodeinv a:=by{
      intro a
      apply minimalPeriod_eq_of_funReflTransGen_injective H.nodeinv_injective
      apply funReflTransGen_symm_of_injective H.nodeinv_injective
      apply ReflTransGen.single
      rfl
    }
    constructor
    · {
      rw[List.getLast_flatten_eq_getLast_getLast hq2n hq2ln]
      simp only [List.getLast_map, List.getLast_range]
      rw[←iterate_succ_apply, Nat.succ_eq_add_one]
      rw[Nat.sub_add_cancel H.nodeinv_injective.minimalPeriod_pos]
      simp[h0]
    }
    have h1:∀a, List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
      (List.range (minimalPeriod H.nodeinv a)) ≠ []:=by{
        simp[Nat.ne_zero_of_lt H.nodeinv_injective.minimalPeriod_pos]
      }
    have h2:∀a, (List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
      (List.range (minimalPeriod H.nodeinv a))).head (h1 a) = H.nodeinv a:=by{
        simp
      }
    have h3:∀a, (List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
      (List.range (minimalPeriod H.nodeinv a))).IsChain (fromFun H.nodeinv):=by{
        intro a
        apply List.isChain_map_iterate_range_fromFun
      }
    have h4:∀a, (List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
      (List.range (minimalPeriod H.nodeinv a))).getLast (h1 a) = a:=by{
        simp only [List.getLast_map, List.getLast_range]
        intro a
        rw[←iterate_succ_apply, Nat.succ_eq_add_one]
        rw[Nat.sub_add_cancel H.nodeinv_injective.minimalPeriod_pos]
        simp only [iterate_minimalPeriod]
      }
    have h5:∀a b, H.cnode a b ↔ b ∈ (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
      (H.nodeinv^[·] (H.nodeinv a)):=by{
        have hn:∀a, funReflTransGen H.nodeinv a (H.nodeinv a):=fun _ => ReflTransGen.single rfl
        intro a
        rw[cnode, ←funReflTransGen_bijInv_iff H.node_bijective, ←nodeinv]
        have h:funReflTransGen H.nodeinv a = funReflTransGen H.nodeinv (H.nodeinv a):=by{
          rw[Equivalence.pred_eq_iff
          (Finite.funReflTransGen_injective_equivalence H.nodeinv_injective)]
          apply funReflTransGen.single
        }
        rw[h]
        nth_rw 1 [←h2]
        rw[h0]
        apply List.isChain_fromFun_injective_refltransgen_univ_iff H.nodeinv_injective
          (h1 _) (h3 _)
        rw[h2, h4]
      }
    have hq2c_lemma:∀p:List α, p.IsChain (fromFun H.edgeinv) →
        (p.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
        (H.nodeinv^[·] (H.nodeinv a)))).flatten.IsChain (H.clink):=by{
          intro p hp
          induction p with
          | nil => simp
          | cons a p' ih => {
            rw[List.map_cons, List.flatten_cons]
            rw[List.isChain_append]
            constructor
            · {
              rw[h0]
              apply (h3 _).imp
              simp[fromFun, clink, union_iff]
            }
            constructor
            · {
              apply ih
              exact hp.of_cons
            }
            · {
              simp only [h0]
              simp only [List.getLast?_eq_some_getLast (h1 _), Option.mem_some]
              simp only [forall_eq', h4]
              cases p' with
              | nil => simp
              | cons a' p'' => {
                rw[List.isChain_cons_cons, fromFun] at hp
                rw[List.map_cons, List.flatten_cons, List.head?_append]
                rw[List.head?_eq_some_head (h1 _), Option.some_or]
                simp only [Option.mem_some, forall_eq', h2]
                rw[←hp.left, nodeinv_eq, edgeinv_eq]
                simp[enf_cancel, clink, union_iff, fromFun]
              }
            }
          }
      }
    have hq2c:(p2.map (fun a => (List.range (minimalPeriod H.nodeinv (H.nodeinv a))).map
      (H.nodeinv^[·] (H.nodeinv a)))).flatten.IsChain (H.clink) := by{
      apply hq2c_lemma
      exact hp2c
    }
    constructor
    · exact hq2c
    have hq2f_lemma:∀p : List α, p.Nodup → p.IsChain (fromFun H.edgeinv) → (∀ x ∈ p,
    List.take (minimalPeriod H.nodeinv x) (List.drop (List.map (minimalPeriod H.nodeinv)
    (List.take (List.idxOf x p) p)).sum (List.map (fun a ↦ List.map
    (fun x ↦ H.nodeinv^[x] (H.nodeinv a)) (List.range (minimalPeriod H.nodeinv (H.nodeinv a))))
    p).flatten) = List.map (fun x_1 ↦ (H.nodeinv)^[x_1] (H.nodeinv x)) (List.range
    (minimalPeriod H.nodeinv x))) := by{
        intro p hpd hp
        induction p with
        | nil => simp
        | cons a p' ih => {
          intro a' ha'
          rw[List.mem_cons] at ha'
          rw[List.map_cons, List.flatten_cons]
          cases ha' with
          | inl ha' => {
            rw[ha', List.idxOf_cons_self, List.take_zero, List.map_nil, List.sum_nil]
            rw[List.drop_zero]
            have h:(List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
              (List.range (minimalPeriod H.nodeinv (H.nodeinv a)))).length =
              minimalPeriod H.nodeinv a:=by{
                simp[h0]
              }
            nth_rw 1 [←h]
            rw[List.take_append_length]
            rw[h0]
          }
          | inr ha' => {
            rw[List.nodup_cons] at hpd
            have ha'':a' ≠ a:=by{
              intro ha''
              apply hpd.left
              exact ha'' ▸ ha'
            }
            have ih':=ih hpd.right hp.of_cons a' ha'
            rw[List.idxOf_cons_ne _ ha''.symm, List.take_succ_cons, List.map_cons]
            rw[List.sum_cons]
            have h:(List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a))
            (List.range (minimalPeriod H.nodeinv (H.nodeinv a)))).length =
            minimalPeriod H.nodeinv a:=by{
              simp[h0]
            }
            nth_rw 1 [←h]
            rw[List.drop_length_add_append]
            apply ih'
          }
        }
      }
    constructor
    · {
      apply hq2f_lemma
      · exact hp2d
      · exact hp2c
    }
    constructor
    · {
      rw[List.length_flatten]
      apply congrArg
      simp only [h0]
      rw[List.map_map]
      apply congrArg p2.map
      ext _
      simp
    }
    · {
      have h_lemma : ∀p : List α, ∀ (i : ℕ) (hiq : i < (List.map (fun a ↦
      List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a)) (List.range (minimalPeriod H.nodeinv
      (H.nodeinv a)))) p).flatten.length), (∀ (n : ℕ), (List.map (minimalPeriod H.nodeinv)
      (List.take n p)).sum ≠ i) → H.nodeinv (List.map (fun a ↦ List.map (fun x ↦ H.nodeinv^[x]
      (H.nodeinv a)) (List.range (minimalPeriod H.nodeinv (H.nodeinv a)))) p).flatten[i - 1] =
      (List.map (fun a ↦ List.map (fun x ↦ H.nodeinv^[x] (H.nodeinv a)) (List.range
      (minimalPeriod H.nodeinv (H.nodeinv a)))) p).flatten[i] := by{
        intro p
        induction p with
        | nil => simp
        | cons a p' ih => {
          simp only [List.map_cons, List.flatten_cons]
          intro i hiq hin
          rw[List.length_append, List.length_map, List.length_range] at hiq
          cases lt_or_ge i (minimalPeriod H.nodeinv a) with
          | inl hia => {
            have hi : i ≠ 0 := by{
              intro hi
              apply hin 0
              simp[hi]
            }
            have hi':=Nat.pos_of_ne_zero hi
            rw[List.getElem_append_left (by{
              simp only [h0, List.length_map, List.length_range];
              exact Nat.lt_of_le_of_lt (Nat.pred_le _) hia
            })]
            rw[List.getElem_append_left (by{simp[h0, hia]})]
            simp only [h0, List.getElem_map, List.getElem_range]
            rw[←iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hi']
            simp[←iterate_succ_apply']
          }
          | inr hia => {
            simp only [h0]
            have hi : minimalPeriod H.nodeinv a ≤ i - 1 := by{
              have hin':=hin 1
              simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, add_zero, ne_eq] at hin'
              apply Nat.le_pred_of_lt
              apply Nat.lt_of_le_of_ne hia hin'
            }
            rw[List.getElem_append_right (by{simp[hi]})]
            rw[List.getElem_append_right (by{simp[hia]})]
            simp only [List.length_map, List.length_range]
            simp only [Nat.sub_sub (m:=1), Nat.add_comm 1, ←Nat.sub_sub]
            have hin':∀ (n : ℕ), (List.map (minimalPeriod H.nodeinv) (List.take n p')).sum
              ≠ i - minimalPeriod H.nodeinv a := by{
              intro n hinn
              have hin':=hin (n + 1)
              apply hin'
              simp at hinn
              simp[hinn, Nat.add_comm _ (_ - _), Nat.sub_add_cancel hia]
            }
            have ih':=ih (i - minimalPeriod H.nodeinv a) (by{
              apply Nat.sub_lt_left_of_lt_add hia
              simp only [List.length_flatten, List.map_map, h0]
              simp only [List.length_flatten, List.map_map, h0] at hiq
              exact hiq
            }) hin'
            simp[h0] at ih'
            simp[ih']
          }
        }
      }
      apply h_lemma
    }
  }

theorem euler_tree (hj : H.jordan) (x : α)
  : ¬∀ y, H.cedge x y → ¬H.clink y y ∧ H.cross_edge y := by{
  intro htree_x
  have hn_lemma := euler_tree_node_lemma htree_x
  have hcn_lemma := euler_tree_cnode_lemma htree_x
  have hf_lemma := euler_tree_face_lemma htree_x
  have hcf_lemma := euler_tree_cface_lemma htree_x
  have ⟨p1, hp1n, hp1e, hp1c, hp1s, hp1f, q1, hq1n, hq1h, hq1l, hq1d, hq1c, hq1q, hq1f,
    p2, hp2n, hp2h, hp2l, hp2c, hp2d, hp2dj, q2, hq2n, hq2h, hq2l, hq2c, hq2f, hq2len,
    hq2i⟩:=
    H.cross_edge_exists_moebius_path_lemma htree_x
  have hecf : ∃x ∈ q2, x ∈ q1:=by{
    use q2.getLast hq2n
    apply And.intro (List.getLast_mem _)
    rw[hq2l, hp2l, ←hq1h]
    apply List.head_mem
  }
  have hc0 : H.cedge (p1.head hp1n) (H.edgeinv (p1.head hp1n)) := by{
      apply cedge_equivalence.symm
      apply ReflTransGen.single
      rw[fromFun, edgeinv_rightinv]
  }
  have hc1 : H.cedge (p1.head hp1n) (H.face (p1.head hp1n)) := by{
    apply euler_tree_face_lemma htree_x
    exact hp1e
  }
  have hc2 := cedge_equivalence.trans (cedge_equivalence.symm hc0) hc1
  have htree_p1h : ∀y, H.cedge (p1.head hp1n) y → ¬H.clink y y ∧ H.cross_edge y:=by{
    rw[←cedge_pred_eq_of_cedge (x:=x)]
    · apply htree_x
    exact hp1e
  }
  rw[List.exists_mem_iff_exists_getElem_minimal] at hecf
  have ⟨i, hi, hiq, him⟩:=hecf
  have hc_lemma_f : H.face (q1.getLast hq1n) = q2.head hq2n := by{
    rw[hq2h, hq1l, hp2h]
    rw[nodeinv_eq, comp_apply, edgeinv_rightinv]
  }
  have hc_lemma_c : H.clink (q1.getLast hq1n) (q2.head hq2n) := by{
    rw[clink, union_iff]
    right
    exact hc_lemma_f
  }
  have hp1_lemma : H.edgeinv (p1.head hp1n) ≠ p1.getLast hp1n:=by{
    intro h
    rw[edgeinv_eq_iff_eq_edge] at h
    have h0:=List.isChain_fromFun_injective_refltransgen_univ_iff H.edge_injective hp1n hp1c h
    rw[simpleList, List.nodup_iff_getElem_ne_getElem'] at hp1s
    have h0':=(h0 _).mp hc1
    have h':=htree_p1h (p1.head hp1n) ReflTransGen.refl
    rw[clink, union_iff, fromFun, not_or, fromFun] at h'
    have ⟨i, hi, hip⟩:=List.mem_iff_getElem.mp (List.head_mem hp1n)
    have ⟨j, hj, hjp⟩:=List.mem_iff_getElem.mp h0'
    have hij:i ≠ j:=by{
      intro hij
      simp [hij, hjp, h'] at hip
    }
    have hp1s':=hp1s i j hij (by{simp[hi]}) (by{simp[hj]})
    simp only [List.getElem_map, hip, hjp] at hp1s'
    apply hp1s'
    rw[Quotient.eq_iff_equiv]
    apply ReflTransGen.single
    rfl
  }
  have hi_lemma : ∀n, ((p2.take n).map (minimalPeriod H.nodeinv)).sum ≠ i:=by{
    have hi_lemma : ∀i, (hiq2 : i < q2.length) → q2[i] ∈ q1 → (∀j, (hji : j < i)
    → q2[j] ∉ q1) → ∀n, ((p2.take n).map (minimalPeriod H.nodeinv)).sum ≠ i := by{
      intro i hiq2 hiq2q1 hiq2m
      have hi_lemma_0 : i ≠ 0 := by{
        intro hi_lemma_0
        rw[List.head_eq_getElem_zero] at hc_lemma_f
        simp only [hi_lemma_0] at hiq2q1
        have hq1f':=hq1f (q1.getLast hq1n) (by{rw[hc_lemma_f]; exact hiq2q1})
        rw[List.dropLast_cons_of_ne_nil hq1n] at hq1f'
        rw[List.mem_cons] at hq1f'
        rw[←List.dropLast_append_getLast hq1n, ←List.concat_eq_append] at hq1d
        rw[List.nodup_concat] at hq1d
        apply (Or.resolve_right · hq1d.left) at hq1f'
        rw[hq1l] at hq1f'
        contradiction
      }
      have h:(∀n, n < p2.length → ((p2.take n).map (minimalPeriod H.nodeinv)).sum ≠ i)
      → ∀n, ((p2.take n).map (minimalPeriod H.nodeinv)).sum ≠ i:=by{
        intro h n
        cases lt_or_ge n p2.length with
        | inl hn => exact h _ hn
        | inr hn => {
          rw[List.take_of_length_le hn]
          rw[←hq2len]
          symm
          exact ne_of_lt hiq2
        }
      }
      apply h
      intro n hn
      induction n with
      | zero => {
        simp only [List.take_zero, List.map_nil, List.sum_nil, ne_eq]
        exact hi_lemma_0.symm
      }
      | succ n' ih => {
        rw[List.take_add_one, List.map_append]
        rw[List.getElem?_eq_some_getElem (Nat.lt_of_succ_lt hn)]
        rw[Option.toList_some, List.map_singleton, List.sum_append]
        rw[List.sum_singleton]
        intro hi'
        have hi'':i > 0:=by{
          rw[←hi']
          apply Nat.add_pos_right
          exact H.nodeinv_injective.minimalPeriod_pos
        }
        apply hiq2m (i - 1) (Nat.pred_lt_of_lt hi'')
        have hq2f':=hq2f p2[n' + 1] (List.getElem_mem _)
        have hq2i : q2[i] =
          (List.take (minimalPeriod H.nodeinv p2[n' + 1])
          (List.drop (List.map (minimalPeriod H.nodeinv)
          (List.take (List.idxOf p2[n' + 1] p2) p2)).sum q2))[0]'(by{
            simp only [List.map_take, List.length_take, List.length_drop, lt_inf_iff,
              H.nodeinv_injective.minimalPeriod_pos, tsub_pos_iff_lt, true_and]
            rw[hq2len]
            nth_rw 2 [←List.take_append_drop (p2.idxOf p2[n' + 1]) (p2.map _)]
            rw[List.sum_append]
            apply Nat.lt_add_of_pos_right
            rw[List.sum_pos_iff_exists_pos_nat]
            have h':List.drop (List.idxOf p2[n' + 1] p2)
              (List.map (minimalPeriod H.nodeinv) p2) ≠ []:=by{
              simp only [ne_eq, List.drop_eq_nil_iff, List.length_map, not_le]
              apply List.idxOf_lt_length_of_mem
              apply List.getElem_mem
            }
            use List.head _ h'
            apply And.intro (List.head_mem _)
            simp[H.nodeinv_injective.minimalPeriod_pos]
          })
        := by{
          simp only [←hi']
          simp only [List.map_take, List.Nodup.idxOf_getElem hp2d, List.take_add_one,
            List.map_append, List.sum_append, List.getElem_take, List.getElem_drop, add_zero]
          simp only [List.getElem?_eq_some_getElem (Nat.lt_of_succ_lt hn)]
          simp only [Option.toList_some, List.map_singleton, List.sum_singleton]
        }
        simp only [hq2f'] at hq2i
        simp only [List.getElem_map, List.getElem_range, iterate_zero, id_eq] at hq2i
        have hq2f'':=hq2f p2[n'] (List.getElem_mem _)
        have hq2i' : q2[i - 1] = (List.take (minimalPeriod H.nodeinv p2[n'])
          (List.drop (List.map (minimalPeriod H.nodeinv)
          (List.take (List.idxOf p2[n'] p2) p2)).sum q2)).getLast
          (by{
            simp only [List.map_take, ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff, not_or,
              not_le]
            apply And.intro (Nat.ne_zero_of_lt H.nodeinv_injective.minimalPeriod_pos)
            rw[hq2len]
            nth_rw 2 [←List.take_append_drop (p2.idxOf p2[n']) (p2.map _)]
            rw[List.sum_append]
            apply Nat.lt_add_of_pos_right
            rw[List.sum_pos_iff_exists_pos_nat]
            have h':List.drop (List.idxOf p2[n'] p2)
              (List.map (minimalPeriod H.nodeinv) p2) ≠ []:=by{
              simp only [ne_eq, List.drop_eq_nil_iff, List.length_map, not_le]
              apply List.idxOf_lt_length_of_mem
              apply List.getElem_mem
            }
            use List.head _ h'
            apply And.intro (List.head_mem _)
            simp[H.nodeinv_injective.minimalPeriod_pos]
          }):=by{
            simp only [←hi']
            simp only [List.map_take, List.Nodup.idxOf_getElem hp2d]
            rw[List.getLast_eq_getElem]
            simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop]
            congr
            rw[Nat.add_sub_assoc H.nodeinv_injective.minimalPeriod_pos]
            congr
            rw[min_eq_left]
            apply Nat.le_sub_of_add_le'
            have h' : (List.take (n' + 1)
            (List.map (minimalPeriod H.nodeinv) p2)).sum ≤ q2.length := by{
              rw[hq2len]
              nth_rw 2 [←List.take_append_drop (p2.idxOf p2[n' + 1]) (p2.map _)]
              rw[List.sum_append]
              simp only [List.Nodup.idxOf_getElem hp2d]
              apply Nat.le_add_right
            }
            rw[List.take_add_one, List.getElem?_eq_some_getElem
            (by{simp[Nat.lt_of_succ_lt hn]})] at h'
            rw[Option.toList_some, List.sum_append, List.sum_singleton, List.getElem_map] at h'
            exact h'
          }
        simp only [hq2f''] at hq2i'
        simp only [List.getLast_map, List.getLast_range] at hq2i'
        simp only [←iterate_succ_apply, Nat.succ_eq_add_one] at hq2i'
        simp only [Nat.sub_add_cancel H.nodeinv_injective.minimalPeriod_pos] at hq2i'
        simp only [iterate_minimalPeriod] at hq2i'
        rw[hq2i']
        rw[hq2i] at hiq2q1
        have hp2':=List.isChain_iff_getElem.mp hp2c n' hn
        rw[←hp2', nodeinv_eq, edgeinv_eq, comp_apply, comp_apply, enf_cancel] at hiq2q1
        have hq1f':=hq1f _ hiq2q1
        rw[List.dropLast_cons_of_ne_nil hq1n, List.mem_cons] at hq1f'
        have h1: p2[n'] ≠ p1.getLast hp1n := by{
          intro h1
          have hp2dj':=@hp2dj p2[n'] (List.getElem_mem _)
          apply hp2dj'
          rw[h1]
          apply List.getLast_mem
        }
        apply (Or.resolve_left · h1) at hq1f'
        exact List.mem_of_mem_dropLast hq1f'
      }
    }
    intro n
    apply hi_lemma
    · exact hiq
    · exact him
  }
  have hi_lemma_0 : i > 0 := by{
    have hi_lemma':=hi_lemma 0
    simp only [List.take_zero, List.map_nil, List.sum_nil, ne_eq] at hi_lemma'
    exact Nat.pos_of_ne_zero (Ne.symm hi_lemma')
  }
  have hi_nodeinv_lemma : H.nodeinv q2[i - 1] = q2[i] := by{
    apply hq2i
    exact hi_lemma
  }
  have hq2'c : List.IsChain H.clink (q2.take i) := List.isChain_take hq2c
  have hq2'n : q2.take i ≠ [] := by{
    simp[Nat.ne_zero_of_lt hi_lemma_0, hq2n]
  }
  have hq2'h : (q2.take i).head hq2'n = q2.head hq2n := by{
    rw[List.head_take]
  }
  have hq2'l : (q2.take i).getLast hq2'n = q2[i - 1] := by{
    rw[List.getLast_take, List.getElem?_eq_some_getElem, Option.getD_some]
  }
  have hq2'dj : (q2.take i).Disjoint q1:=by{
    intro x hqx
    rw[List.mem_take_iff_getElem] at hqx
    have ⟨j, hji, hjp⟩:=hqx
    rw[←hjp]
    rw[min_eq_left_of_lt hi] at hji
    exact him j hji
  }
  have ⟨l, hl⟩:=List.isChain_exists_shorterChain_option hq2'c
  apply hj (q1 ++ l)
  unfold moebius_path
  rw[dite_cond_eq_false (by{simp[hq1n]})]
  rw[List.head?_eq_some_head hq2'n, List.getLast?_eq_some_getLast hq2'n] at hl
  have hln : l ≠ [] := by{intro hln; simp[hln] at hl}
  rw[List.head?_eq_some_head hln, Option.some_inj] at hl
  rw[List.getLast?_eq_some_getLast hln, Option.some_inj] at hl
  have hjd : (q1 ++ l).Nodup := by{
    rw[List.nodup_append']
    apply And.intro hq1d
    apply And.intro hl.right.left
    apply List.disjoint_of_subset_right hl.left.subset
    exact hq2'dj.symm
  }
  constructor
  · apply hjd
  constructor
  · {
    rw[List.isChain_append]
    apply And.intro hq1c
    apply And.intro hl.right.right.left
    simp only [List.getLast?_eq_some_getLast hq1n, List.head?_eq_some_head hln,
    Option.mem_some, forall_eq']
    rw[hl.right.right.right.left, hq2'h]
    exact hc_lemma_c
  }
  · {
    rw[List.getLast_append_right hln, hl.right.right.right.right, hq2'l]
    rw[List.head_append_left hq1n, hq1h, hi_nodeinv_lemma]
    rw[←List.cons_head_tail hq1n, List.mem_cons] at hiq
    cases hiq with
    | inl hiq => {
      rw[hq1h] at hiq
      exfalso
      rw[nodeinv_eq_iff_eq_node, hiq] at hi_nodeinv_lemma
      have h0:q2[i - 1] ∈ q2.take i := by{
        rw[List.mem_take_iff_getElem]
        use (i - 1)
        simp only [lt_inf_iff, tsub_lt_self_iff, hi_lemma_0, zero_lt_one, and_self, true_and,
          exists_prop, and_true]
        apply Nat.lt_of_le_of_lt (Nat.pred_le _) hi
      }
      apply hq2'dj h0
      rw[hi_nodeinv_lemma]
      rw[edgeinv_eq, comp_apply] at hq1l
      rw[←hq1l]
      apply List.getLast_mem
    }
    | inr hiq => {
      rw[List.tail_append_of_ne_nil hq1n, List.idxOf_append_of_mem hiq]
      rw[List.drop_append_of_le_length List.idxOf_le_length, List.mem_append]
      left
      rw[←comp_apply (f:=H.node), ←edgeinv_eq, ←hq1l]
      have h2:List.drop (List.idxOf q2[i] q1.tail) q1.tail ≠ []:=by{
        simp only [ne_eq, List.drop_eq_nil_iff, not_le]
        apply List.idxOf_lt_length_of_mem hiq
      }
      have h3:(List.drop (List.idxOf q2[i] q1.tail) q1.tail).getLast h2 = q1.getLast hq1n:=by{
        rw[List.getLast_drop, List.getLast_tail]
      }
      rw[←h3]
      apply List.getLast_mem
    }
  }
}
end Hypermap
