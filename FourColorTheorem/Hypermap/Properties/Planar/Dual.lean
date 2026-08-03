import FourColorTheorem.Hypermap.Actions.Dual
import FourColorTheorem.Hypermap.Properties.Planar.Euler
import FourColorTheorem.Hypermap.Properties.Planar.Jordan

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

theorem dual_euler_lhs : H.dual.euler_lhs = H.euler_lhs := by{unfold euler_lhs;simp[dual_gcomp]}
theorem dual_euler_rhs : H.dual.euler_rhs = H.euler_rhs := by{
  unfold euler_rhs
  simp[dual_ecomp, dual_ncomp, dual_fcomp, Nat.add_comm]
}
theorem dual_genus : H.dual.genus = H.genus := by{unfold genus;simp[dual_euler_lhs, dual_euler_rhs]}
theorem dual_planar : H.dual.planar ↔ H.planar := by{unfold planar;simp[dual_genus]}


theorem dual_jordan_imp (hJ : H.jordan) : H.dual.jordan := by{
  intro q hq
  have hq':q ≠ []:=moebius_path_ne_nil hq
  match q with
  | x::q' => {
    have hfy:=last_nodeinv_mem_moebius_path_tail_cons hq
    have hqn0 := moebius_path_not_eq_cons hq
    have hqn1 := moebius_path_not_eq'_cons hq
    rw[dual_nodeinv] at hqn0 hfy
    rw[dual_node] at hqn1
    unfold moebius_path at hq
    simp only [reduceCtorEq, ↓reduceDIte, List.tail_cons, List.getLast_cons_eq_getLastD] at hq
    rw[dual_nodeinv, dual_node, dual_clink] at hq
    let y:=q'.getLastD x
    let k:=(List.idxOf (face y) q')
    let q1:=q'.take k
    let q23:=q'.drop k
    have q1_append_q23:q' = q1 ++ q23:=by{
      unfold q1 q23
      rw[List.take_append_drop]
    }
    have hx'q23:H.faceinv x ∈ q23:=hq.right.right
    have ⟨q2, q3, hq23⟩:=List.mem_iff_append.mp hx'q23
    have hq3:q3 ≠ []:=by{
      intro hq3
      simp[hq3] at hq23
      simp only [hq23] at q1_append_q23
      rw[q1_append_q23, ←List.append_assoc, List.getLastD_concat] at hqn1
      contradiction
    }
    have hy:y ∈ q3:=by{
      unfold y
      rw[q1_append_q23, hq23, ←List.append_assoc, List.getLastD_append_cons]
      have hy:=List.getLastD_mem_cons (l:=q3) (a:=H.faceinv x)
      rw[List.mem_cons] at hy
      apply hy.resolve_left
      rw[q1_append_q23, hq23, ←List.append_assoc, List.getLastD_append_cons] at hqn1
      exact hqn1.symm
    }
    have hq23':q23 ≠ []:=List.ne_nil_of_mem hq.right.right
    have hq23'':q23.head hq23' = H.face y:=by{
      unfold q23
      unfold k
      rw[List.drop_idxOf_head]
      exact hfy
    }
    let q2':= q2 ++ [H.faceinv x]
    have hq2':q2' ≠ []:=by{unfold q2'; simp}
    have hq23''':q23 = q2' ++ q3:=by{unfold q2'; simp[hq23]}
    have hq2:q2'.head hq2' = H.face y:=by{
      simp[hq23'''] at hq23''
      simp[hq2'] at hq23''
      simp[hq23'']
    }
    have hq1':q1.getLastD x ≠ y:=by{
      have hqn:=hq.left
      rw[q1_append_q23, hq23'''] at hqn
      rw[←List.cons_append] at hqn
      rw[List.nodup_append] at hqn
      exact hqn.right.right (q1.getLastD x) List.getLastD_mem_cons y (List.mem_append_right _ hy)
    }
    have hq1:q1.getLastD x = H.node (H.face y):=by{
      match q2' with
      | w::q2'' => {
        rw[List.head_cons] at hq2
        have hq'':=And.intro hq.left hq.right.left
        rw[q1_append_q23, hq23'''] at hq''
        simp only [List.cons_append, List.nodup_cons,
          List.mem_append, List.mem_cons, not_or] at hq''
        rw[List.nodup_append] at hq''
        simp only [List.nodup_cons, List.mem_append, not_or,
          List.mem_cons, ne_eq, forall_eq_or_imp] at hq''
        rw[←List.cons_append] at hq''
        have hq''':=List.isChain_append.mp hq''.right
        rw[List.getLast?_cons_eq_getLastD, List.head?_cons] at hq'''
        simp only [Option.mem_def, Option.some.injEq, forall_eq'] at hq'''
        have hqc:=hq'''.right.right
        unfold clink fromFun at hqc
        rw[union_iff, hq2] at hqc
        cases hqc with
        | inl hqc => {
          rw[nodeinv_eq] at hqc
          have hqc':=congrArg H.node hqc
          simp[nfe_cancel] at hqc'
          simp[hqc']
        }
        | inr hqc => {
          rw[H.face_injective.eq_iff] at hqc
          contradiction
        }
      }
    }
    match hq2'':q2', q3 with
    | y'::q2'', z::q3' => {
      have hq3z:q3'.getLastD z = y:=by{
        unfold y
        rw[q1_append_q23, hq23''', ←List.append_assoc, List.getLastD_append_cons]
      }
      have hq2y':q2''.getLastD y' = H.faceinv x:=by{
        rw[←List.getLast_cons_eq_getLastD]
        simp only[←hq2'']
        unfold q2'
        simp
      }
      have hz:z = H.nodeinv (H.faceinv x):=by{
        have hqn:=hq.left
        have hqc:=hq.right.left
        rw[q1_append_q23, hq23''', ←List.cons_append] at hqc hqn
        have hqc':=(List.isChain_append.mp (List.isChain_append.mp hqc).right.left).right.right
        simp only [List.getLast?_cons_eq_getLastD, Option.mem_def,
          Option.some.injEq, List.head?_cons, forall_eq', hq2y'] at hqc'
        unfold clink fromFun at hqc'
        simp only [union_iff, Eq.comm] at hqc'
        apply hqc'.resolve_right
        rw[faceinv_eq, comp_apply, fen_cancel]
        intro hzx
        simp[hzx] at hqn
      }
      rw[List.head_cons] at hq2
      apply hJ (z::q3' ++ (y'::q2'') ++ x::q1)
      simp only [List.cons_append]
      unfold moebius_path
      constructor
      · {
        have hqn:=hq.left
        rw[q1_append_q23, hq23'''] at hqn
        simp only [←List.cons_append, List.nodup_append, List.mem_append] at hqn
        simp only [←List.cons_append, List.nodup_append, List.mem_append]
        simp only [ne_eq]
        simp only [ne_eq] at hqn
        simp only [hqn, true_and]
        constructor
        · {
          intro z' hz'
          intro y' hy'
          have hqn':=hqn.right.left.right.right y' hy' z' hz'
          rw[Eq.comm] at hqn'
          exact hqn'
        }
        · {
          intro a ha b hb
          rw[or_comm] at ha
          have hqn':=hqn.right.right b hb a ha
          rw[Eq.comm] at hqn'
          exact hqn'
        }
      }
      constructor
      · {
        have hqc:=hq.right.left
        simp only [←List.cons_append, List.isChain_append,
          List.head?_cons, Option.mem_def, Option.some_inj, forall_eq']
        simp only [List.getLast?_cons_eq_getLastD, Option.some_inj]
        rw[List.cons_append, List.getLast?_cons_eq_getLastD, List.getLastD_append_cons]
        simp only [Option.some_inj, forall_eq']
        rw[q1_append_q23, hq23'''] at hqc
        simp only [←List.cons_append, List.isChain_append, List.head?_cons,
          Option.mem_def, Option.some_inj, forall_eq'] at hqc
        simp only [List.getLast?_cons_eq_getLastD, Option.some_inj, forall_eq'] at hqc
        rw[List.cons_append, List.head?_cons] at hqc
        simp only [Option.some_inj, forall_eq'] at hqc
        simp only [hqc, true_and]
        rw[hq3z, hq2y', hq2]
        unfold clink fromFun
        simp[union_iff, faceinv_eq, nodeinv_eq, fen_cancel]
      }
      · {
        have hqn:=hq.left
        rw[q1_append_q23, hq23'''] at hqn
        simp only [←List.cons_append, List.nodup_append, List.mem_append] at hqn
        simp only [ne_eq] at hqn
        have hqn':=hqn.right.left.right.right y' (by{simp}) y'
        simp only [List.mem_cons, not_true_eq_false, imp_false, not_or] at hqn'
        rw[hq2] at hqn'
        rw[List.head_cons, List.tail_cons, List.getLast_cons_eq_getLastD]
        rw[List.getLastD_append_cons, hq1, nodeinv_eq, comp_apply, fen_cancel, hq2]
        rw[List.append_assoc, List.cons_append]
        have hd:List.drop (List.idxOf (face y) (q3' ++ face y::(q2'' ++ x :: q1)))
          (q3' ++ face y::(q2'' ++ x :: q1)) = face y::(q2'' ++ x :: q1):=by{
          apply (Eq.trans · (List.drop_append_length (l₁:=q3')))
          congr
          rw[List.idxOf_append_of_notMem hqn'.right]
          simp
        }
        rw[hd, hz, nodeinv_eq, comp_apply, nfe_cancel]
        rw[←List.cons_append, ←hq2, ←hq2'']
        unfold q2'
        simp
      }
    }
  }
}
theorem dual_jordan : H.dual.jordan ↔ H.jordan := by{
  constructor
  · {
    intro h
    have h':=dual_jordan_imp h
    have h'': H.dual.dual.jordan ↔ H.jordan:=by{rw[dual_dual]}
    exact h''.mp h'
  }
  · exact dual_jordan_imp
}

end Hypermap
