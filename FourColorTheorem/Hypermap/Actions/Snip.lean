import FourColorTheorem.Hypermap.Actions.Walkup
import FourColorTheorem.Hypermap.Actions.Patch
import FourColorTheorem.Hypermap.Properties.Planar

open Relation
open Function

namespace Hypermap

section

variable {α : Type _} [Fintype α] [DecidableEq α]
variable (H : Hypermap α)
variable (r : List α)

def dlink (x y : α) := x ∉ r ∧ H.clink x y
def dconnect (x y : α) := ReflTransGen (H.dlink r) (H.nodeinv y) x
-- 给定一个集合，有不经过该集合的，与集合上某个元素相连的路径
def diskN := {x | ∃y ∈ r, H.dconnect r x y}
def diskE := {x | x ∈ H.diskN r ∧ x ∉ r}
def diskF := H.diskN r \ H.fband r
def diskFC := (H.diskN r)ᶜ \ H.fband r

end

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {H : Hypermap α}
variable {r : List α}

@[inline] instance dlink.instDecidable :
  DecidableRel (H.dlink r) := by{
  unfold dlink
  intro x y
  simp only
  infer_instance
}
@[inline] instance dconnect.instDecidable :
  DecidableRel (H.dconnect r) := by{
  unfold dconnect
  intro x y
  simp only
  apply ReflTransGen.finDec
}
@[inline] instance diskN.instDecidableMem {x : α} :
  Decidable (x ∈ H.diskN r) := by{
  unfold diskN
  rw[Set.mem_setOf]
  infer_instance
}
@[inline] instance diskE.instDecidableMem {x : α} :
  Decidable (x ∈ H.diskE r) := by{
  unfold diskE
  rw[Set.mem_setOf]
  infer_instance
}

theorem dlink_rotate_eq (n : ℕ)
: H.dlink (r.rotate n) = H.dlink r := by{
  ext x y
  unfold dlink
  simp
}
theorem dlink.rotate {x y : α} (hxy : H.dlink r x y) (n : ℕ)
: H.dlink (r.rotate n) x y := by{
  rwa[dlink_rotate_eq]
}
theorem dconnect_rotate_eq (n : ℕ)
: H.dconnect (r.rotate n) = H.dconnect r := by{
  ext x y
  unfold dconnect
  rw[dlink_rotate_eq]
}
theorem dconnect.rotate (n : ℕ) {x y : α} (hxy : H.dconnect r x y)
: H.dconnect (r.rotate n) x y := by{
  rwa[dconnect_rotate_eq]
}
theorem diskN_rotate_eq (n : ℕ)
: H.diskN (r.rotate n) = H.diskN r := by{
  ext x
  unfold diskN
  rw[Set.mem_setOf]
  simp[dconnect_rotate_eq]
}
theorem mem_diskN_rotate {x : α} {n : ℕ}
: x ∈ H.diskN r → x ∈ H.diskN (r.rotate n) := by{
  intro hx
  rw[diskN_rotate_eq]
  exact hx
}
theorem diskE_rotate_eq (n : ℕ)
: H.diskE (r.rotate n) = H.diskE r := by{
  ext x
  change _ ∧ _ ↔ _ ∧ _
  simp[diskN_rotate_eq]
}
theorem mem_diskE_rotate {x : α} {n : ℕ}
: x ∈ H.diskE r → x ∈ H.diskE (r.rotate n) := by{
  intro hx
  rw[diskE_rotate_eq]
  exact hx
}
theorem diskF_rotate_eq (n : ℕ)
: H.diskF (r.rotate n) = H.diskF r := by{
  ext x
  change _ ∧ _ ↔ _ ∧ _
  simp[diskN_rotate_eq, fband_rotate]
}
theorem mem_diskF_rotate {x : α} {n : ℕ}
: x ∈ H.diskF r → x ∈ H.diskF (r.rotate n) := by{
  intro hx
  rw[diskF_rotate_eq]
  exact hx
}
theorem diskFC_rotate_eq (n : ℕ)
: H.diskFC (r.rotate n) = H.diskFC r := by{
  ext x
  change _ ∧ _ ↔ _ ∧ _
  simp[diskN_rotate_eq, fband_rotate]
}
theorem mem_diskFC_rotate {x : α} {n : ℕ}
: x ∈ H.diskFC r → x ∈ H.diskFC (r.rotate n) := by{
  intro hx
  rw[diskFC_rotate_eq]
  exact hx
}

theorem cclink_of_dconnect {x y : α} (hd : H.dconnect r x y)
  : H.cclink (H.nodeinv y) x := by{
  unfold dconnect at hd
  induction hd with
  | refl => apply ReflTransGen.refl
  | tail hh ht ih => {
    unfold dlink at ht
    apply ih.tail ht.2
  }
}
theorem diskN_nodeinv_close : ∀x ∈ H.diskN r, H.nodeinv x ∈ H.diskN r := by{
  intro x ⟨y, hyr, hdxy⟩
  rcases em' (x ∈ r) with hxr | hxr
  · {
    refine ⟨y, hyr, ?_⟩
    unfold dconnect at *
    apply hdxy.tail
    unfold dlink clink
    rw[union_iff, fromFun]
    simp[hxr]
  }
  refine ⟨x, hxr, ?_⟩
  apply ReflTransGen.refl
}
theorem diskN_cnode_close : ∀x ∈ H.diskN r, ∀y, H.cnode x y → y ∈ H.diskN r := by{
  intro x hx y hxy
  rw[cnode, ← funReflTransGen_bijInv_iff H.node_bijective, funReflTransGen_iff_iterate] at hxy
  change ∃_, H.nodeinv^[_] _ = _ at hxy
  have ⟨n, hn⟩:=hxy
  clear hxy
  induction n generalizing x with
  | zero => simp at hn; simp[hn ▸ hx]
  | succ n' ih => {
    exact ih (H.nodeinv x) (diskN_nodeinv_close _ hx) (by{rw[← iterate_succ_apply, hn]})
  }
}
theorem diskN_node_close : ∀x ∈ H.diskN r, node x ∈ H.diskN r := by{
  intro x hx
  apply diskN_cnode_close x hx
  apply funReflTransGen.single
}
theorem diskN_cnode_close_iff {x y : α} (hxy : H.cnode x y) : x ∈ H.diskN r ↔ y ∈ H.diskN r := by{
  constructor
  · intro h; exact diskN_cnode_close _ h _ hxy
  · {
    intro h
    apply H.cnode_Symm.symm at hxy
    exact diskN_cnode_close _ h _ hxy
  }
}
theorem subset_diskN {x : α} (hx : x ∈ r) : x ∈ H.diskN r := by{
  have h' : H.nodeinv x ∈ H.diskN r := by{
    refine ⟨x, hx, ?_⟩
    unfold dconnect
    apply ReflTransGen.refl
  }
  apply diskN_cnode_close _ h'
  apply ReflTransGen.single
  rw[fromFun, nodeinv_rightinv]
}
theorem subset_diskEC {x : α} (hx : x ∈ r) : x ∉ H.diskE r := by{
  unfold diskE
  rw[Set.mem_setOf]
  simp[hx]
}
theorem diskE_subset_diskN : H.diskE r ⊆ H.diskN r := by{
  intro x hx
  exact hx.1
}
theorem mem_diskN_iff_diskE {x : α} : x ∈ H.diskN r ↔ x ∈ r ∨ x ∈ H.diskE r := by{
  unfold diskE
  rw[Set.mem_setOf]
  constructor
  · intro h; simp only [h, true_and]; apply em
  · intro h; apply h.elim subset_diskN And.left
}
theorem diskN_node_closure : Closure (fromFun H.node) (H.diskN r) := by{
  unfold Closure
  change ∀ x ∈ H.diskN r, ∀ (y : α), H.cnode x y → y ∈ H.diskN r
  intro x hx y hxy
  rwa[← diskN_cnode_close_iff hxy]
}

variable (scycRr : H.simpleCycle H.rlink r)
theorem diskF_face_closure : Closure (fromFun H.face) (H.diskF r) := by{
  rw[closure_iff_single]
  intro x hx y hxy
  rw[← hxy]
  clear! y
  unfold diskF at *
  rw[Set.mem_diff] at *
  rw[and_comm]
  constructor
  · {
    apply And.right at hx
    contrapose hx
    refine fband_cface_close ?_ hx
    apply H.cface_equivalence.symm
    apply funReflTransGen.single
  }
  unfold diskN at *
  rw[Set.mem_setOf] at *
  rcases hx with ⟨⟨y, hyr, hxy⟩, hxr⟩
  unfold dconnect at hxy
  use y, hyr
  unfold dconnect
  apply hxy.tail
  unfold dlink
  rw[clink, union_iff, fromFun, fromFun]
  simp only [or_true, and_true]
  contrapose hxr
  apply subset_fband
  assumption
}
theorem diskF_cface_close : ∀x ∈ H.diskF r, ∀y, H.cface x y → y ∈ H.diskF r := by{
  exact diskF_face_closure
}
theorem diskF_cface_close_iff {x y : α} (hxy : H.cface x y)
: x ∈ H.diskF r ↔ y ∈ H.diskF r := by{
  constructor
  · intro h; exact diskF_cface_close _ h _ hxy
  · {
    intro h
    apply H.cface_Symm.symm at hxy
    exact diskF_cface_close _ h _ hxy
  }
}
theorem diskFC_face_closure : Closure (fromFun H.face) (H.diskFC r) := by{
  rw[closure_iff_single]
  intro x hx y hxy
  rw[← hxy]
  clear! y
  unfold diskFC at *
  rw[Set.mem_diff, Set.mem_compl_iff] at *
  rw[and_comm]
  constructor
  · {
    apply And.right at hx
    contrapose hx
    refine fband_cface_close ?_ hx
    apply H.cface_equivalence.symm
    apply funReflTransGen.single
  }
  rcases hx with ⟨hxn, hnr⟩
  contrapose hxn
  have hnr' : face x ∉ H.fband r := by{
    contrapose hnr
    apply H.fband_cface_close ?_ hnr
    apply H.cface_equivalence.symm
    apply funReflTransGen.single
  }
  have hxf : face x ∈ H.diskF r := ⟨hxn, hnr'⟩
  have hxf' := diskF_face_closure (face x) hxf x (by{
    apply H.cface_equivalence.symm
    apply funReflTransGen.single
  })
  exact hxf'.left
}
theorem diskFC_cface_close : ∀x ∈ H.diskFC r, ∀y, H.cface x y → y ∈ H.diskFC r := by{
  exact diskFC_face_closure
}
theorem diskFC_cface_close_iff {x y : α} (hxy : H.cface x y)
: x ∈ H.diskFC r ↔ y ∈ H.diskFC r := by{
  constructor
  · intro h; exact diskFC_cface_close _ h _ hxy
  · {
    intro h
    apply H.cface_Symm.symm at hxy
    exact diskFC_cface_close _ h _ hxy
  }
}

structure properSnipRing (r : List α) extends H.Planar where
  simple_cycle : H.simpleCycle H.rlink r
theorem properSnipRing.cycle (hpr : H.properSnipRing r)
: List.IsCycleChain H.rlink r := hpr.simple_cycle.cycle
theorem properSnipRing.simple (hpr : H.properSnipRing r)
: H.simpleList r := hpr.simple_cycle.simple
theorem properSnipRing.nodup (hpr : H.properSnipRing r)
: r.Nodup := hpr.simple_cycle.nodup
theorem properSnipRing.rotate (hpr : H.properSnipRing r) (n : ℕ)
: H.properSnipRing (r.rotate n) := by{
  constructor
  · apply hpr.toPlanar
  · apply hpr.simple_cycle.rotate
}

theorem diskE_edge_closure (Hp : H.properSnipRing r)
: Closure (fromFun H.edge) (H.diskE r) := by{
  rw[closure_iff_single]
  intro x hx y hxy
  rw[← hxy]
  clear! y
  unfold diskE at *
  rw[Set.mem_setOf] at *
  suffices H : ∃x' ∈ H.diskN r, ∃p,
    (x'::p).IsChain (fromFun H.face) ∧
    (x'::p).getLast (by{simp}) = edge x ∧ r.Disjoint (x' :: p) by{
    rcases H with ⟨x', hx'n, p, hpc, hpl, hpr⟩
    rw[and_comm]
    constructor
    · {
      rw[← hpl]
      apply hpr.symm
      simp
    }
    unfold diskN
    rw[Set.mem_setOf]
    rw[← hpl]
    unfold dconnect
    have ⟨y, hyr, hyx'⟩:=hx'n
    use y, hyr
    apply hyx'.trans
    rw[ReflTransGen_iff_isChain]
    use p
    rw[and_comm]
    constructor
    · rw[← List.getLast_cons_eq_getLastD]
    clear hpl
    clear! y
    clear! x
    induction p generalizing x' with
    | nil => simp
    | cons y' p' ih => {
      rw[List.isChain_cons_cons] at *
      unfold dlink
      unfold fromFun at hpc
      symm at hpr
      simp only [List.disjoint_cons_left] at hpr
      simp only [hpr, not_false_eq_true, true_and]
      unfold clink
      rw[union_iff, fromFun, fromFun]
      simp only [hpc, or_true, true_and]
      apply ih _ ?_ hpc.right (by{symm; simp[hpr]})
      simp only [← hpc.left, true_and] at *
      clear! y'
      have ⟨z, hz, hzx'⟩ := hx'n
      unfold dconnect at hzx'
      use z, hz
      apply hzx'.tail
      unfold dlink
      apply And.intro hpr.1
      rw[clink, union_iff]
      right; rfl
    }
  }
  generalize hx'x : face (edge x) = x'
  have hxx' : x = node x' := by{
    rw[← hx'x, nfe_cancel]
  }
  have hx'f : H.cface x' (edge x) := by{
    rw[← hx'x, cface_face]
    apply ReflTransGen.refl
  }
  have hx'n : x' ∈ H.diskN r := by{
    rw[← hx'x]
    apply diskN_cnode_close _ hx.1
    nth_rw 1 [← nfe_cancel x]
    rw[cnode_node]
    apply ReflTransGen.refl
  }
  rw[cface, funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup] at hx'f
  rcases hx'f with ⟨q, hq⟩
  rcases em (r.Disjoint (x'::q)) with hrq | hrq
  · {
    rw[← List.getLast_cons_eq_getLastD] at hq
    use x', hx'n, q, hq.2.1, hq.2.2.1
  }
  rw[List.disjoint_comm, List.Disjoint] at hrq
  push_neg at hrq
  rw[List.exists_mem_iff_exists_getElem_minimal] at hrq
  simp only[and_true] at hrq
  rcases hrq with ⟨i, hi, hir, him⟩
  set y := (x' :: q)[i]
  -- 调整r位置到r1，准备清理r相关定理
  generalize hr1r : r.rotate (r.idxOf y) = r1
  have hrn : r ≠ [] := List.ne_nil_of_mem hir
  have hr1n : r1 ≠ [] := by{rw[← hr1r]; simpa}
  have hr1h : r1.head hr1n = y := by{
    simp only [← hr1r]
    rw[List.head_rotate_idxOf]
    exact hir
  }
  clear hrn
  have hr1_mem {x : α} : x ∈ r1 ↔ x ∈ r := by{
    rw[← hr1r]
    simp
  }
  have hr1_disjoint {l : List α} : r.Disjoint l ↔ r1.Disjoint l := by{
    rw[← hr1r]
    rw[List.disjoint_rotate_left]
  }
  simp only [← hr1_mem, hr1_disjoint] at *
  clear hr1_mem
  have Hp' : H.properSnipRing r1 := by{
    rw[← hr1r]
    apply Hp.rotate
  }
  clear Hp
  have heq : H.diskN r = H.diskN r1 := by{
    rw[← hr1r]
    simp[diskN_rotate_eq]
  }
  simp only [heq] at *
  clear heq
  clear hr1r
  clear! r
  have hcface : ∀w, H.cface w x' ↔ w ∈ x' :: q := by{
    intro x
    rw[cface_equivalence.comm]
    rw[cface]
    change funReflTransGen face (List.head (x' :: q) (by{simp})) _ ↔ _
    apply List.isChain_fromFun_injective_refltransgen_univ_iff
    · apply H.face_injective
    · apply hq.2.1
    rw[List.getLast_cons_eq_getLastD, hq.2.2.1, List.head_cons, ← hx'x]
  }
  generalize hz_def : r1.getLast hr1n = z
  generalize hz'_def : face (edge z) = z'
  have zRy : H.rlink z (r1.head hr1n) := by{
    rw[hr1h]
    have Hp'' := Hp'.cycle
    unfold List.IsCycleChain at Hp''
    simp only [hr1n, ↓reduceDIte, hr1h] at Hp''
    rw[← hz_def]
    exact Hp''.2
  }
  have z'Ry : H.cface z' (r1.head hr1n) := by{
    rw[hr1h, ← hz'_def]
    rw[H.cface_face]
    rw[hr1h] at zRy
    exact zRy
  }
  unfold rlink at zRy
  have hz'q : z' ∈ q := by{
    have hz'q : z' ∈ x' :: q := by{
      rw[← hcface]
      rw[← hz'_def]
      rw[cface_face]
      apply cface_equivalence.trans zRy
      rw[hcface, hr1h]
      apply List.getElem_mem
    }
    rw[List.mem_cons] at hz'q
    apply Or.resolve_left hz'q
    clear hz'q
    rw[← hz'_def]
    rw[← hx'x]
    simp only [H.face_inj, H.edge_inj]
    intro hzx
    have hzr : z ∈ r1 := by{
      have hzr1 : z ∈ r1 := by{
        rw[← hz_def]
        apply List.getLast_mem
      }
      simp at hzr1
      assumption
    }
    exact hx.2 (hzx ▸ hzr)
  }
  have hzr : z ∈ r1 := by{
    have := List.getLast_mem hr1n
    rw[hz_def] at this
    exact this
  }
  have hz'n : z' ∈ H.diskN r1 := by{
    rw[← hz'_def]
    apply diskN_cnode_close z (by{rw[← hz_def]; apply subset_diskN; rwa[hz_def]})
    apply cnode_equivalence.symm
    apply ReflTransGen.single
    exact nfe_cancel _
  }
  let q2 := (x'::q).drop ((x'::q).idxOf z' + 1)
  have hz'q2 : z' :: q2 = (x'::q).drop ((x'::q).idxOf z') := by{
    have : (x'::q).drop ((x'::q).idxOf z') ≠ [] := by{
      simp only [ne_eq, List.drop_eq_nil_iff, List.length_cons, not_le]
      apply List.idxOf_lt_length_of_mem
      simp[hz'q]
    }
    rw[← List.cons_head_tail this]
    simp only [List.head_drop, List.getElem_idxOf, List.tail_drop, List.drop_succ_cons,
      List.cons.injEq, true_and]
    unfold q2
    rw[List.drop_succ_cons]
  }
  have hz'q2l : (z' :: q2).getLast (by{simp}) = edge x := by{
    simp only [hz'q2]
    rw[List.getLast_drop]
    rw[List.getLast_cons_eq_getLastD]
    exact hq.2.2.1
  }
  have hz'q2c : (z' :: q2).IsChain (fromFun H.face) := by{
    simp only [hz'q2]
    apply hq.2.1.drop
  }
  rcases lt_or_ge i ((x' :: q).idxOf z') with hiz' | hiz'
  · {
    use z', hz'n, q2, hz'q2c, hz'q2l
    symm
    rw[List.Disjoint]
    intro w hw hwr
    have := List.take_append_drop (List.idxOf z' (x' :: q)) (x' :: q)
    have hy : y ∉ z' :: q2 := by{
      have hy : y ∈ x' :: q := by{unfold y; simp}
      have hd := hq.1
      rw[← this, ← hz'q2] at hd hy
      rw[List.nodup_append'] at hd
      apply hd.2.2
      unfold y
      rw[List.mem_take_iff_getElem]
      use i
      simp at hi
      simp[hiz', hi]
    }
    have hywc : H.cface y w := by{
      rw[List.mem_iff_getElem] at hw
      have ⟨j, hj, hjw⟩:=hw
      rw[cface, funReflTransGen, ReflTransGen_iff_isChain_option]
      use ((x'::q).take ((x'::q).idxOf z' + j + 1)).drop i
      constructor
      · {
        apply List.IsChain.drop
        apply hq.2.1.take
      }
      constructor
      · {
        rw[List.head?_eq_getElem?, List.getElem?_drop]
        simp only [Nat.add_zero]
        rw[List.getElem?_take, if_pos, List.getElem?_eq_getElem]
        · omega
      }
      · {
        rw[List.getLast?_drop, if_neg]
        · {
          rw[List.getLast?_take, if_neg (by{simp})]
          simp only [Nat.add_sub_cancel]
          nth_rw 1 [← this]
          rw[List.getElem?_append_right]
          · {
            rw[← hz'q2]
            rw[List.length_take]
            rw[min_eq_left (by{apply List.idxOf_le_length})]
            rw[Nat.add_sub_cancel_left]
            rw[List.getElem?_eq_getElem hj, Option.some_or, hjw]
          }
          · simp
        }
        · {
          rw[not_le]
          simp only [List.length_cons, Order.lt_add_one_iff] at hi
          simp
          omega
        }
      }
    }
    have ih := Hp'.simple.cface_nodup _ hir _ hwr hywc
    rw[ih] at hy
    contradiction
  }
  exfalso
  generalize hq1q : (x' :: q).take ((x' :: q).idxOf z') = q1
  have hz'x' : z' ≠ x' := by{
    have := hq.1
    simp only [List.nodup_cons] at this
    intro hz'x
    have := hz'x.symm ▸ this.1
    contradiction
  }
  have hq1n : q1 ≠ [] := by{
    rw[← hq1q]
    simp only [ne_eq, List.take_eq_nil_iff, reduceCtorEq, or_false]
    rw[List.idxOf_cons_ne]
    · simp
    exact hz'x'.symm
  }
  have hq1h : q1.head hq1n = x' := by{
    simp only [← hq1q]
    rw[List.head_take]
    simp
  }
  have hq1z' : q1 ++ [z'] = (x' :: q).take ((x' :: q).idxOf z' + 1) := by{
    rw[List.take_succ_eq_append_getElem, List.getElem_idxOf, hq1q]
    apply List.idxOf_lt_length_of_mem
    simp[hz'q]
  }
  have hq1c : (q1 ++ [z']).IsChain (fromFun H.face) := by{
    rw[hq1z']
    apply hq.2.1.take
  }
  have hq1r : r1.Disjoint q1 := by{
    symm
    rw[List.Disjoint]
    intro w hw
    rw[List.mem_iff_getElem] at hw
    have ⟨j, hj, hjw⟩ := hw
    rw[← hjw]
    simp only [← hq1q]
    rw[List.getElem_take]
    apply him
    apply lt_of_lt_of_le hj
    rw[← hq1q]
    simp[hiz']
  }
  have hq1d : q1.Nodup := by{
    rw[← hq1q]
    apply List.nodup_take
    exact hq.1
  }
  let rclink : α → α := fun x => face (if x ∈ r1 then edge x else x)
  have clink_rclink (x : α) : H.clink x (rclink x) := by{
    unfold clink rclink
    simp only [union_iff, fromFun, apply_ite H.face]
    rw[apply_ite (_ = ·), apply_ite (_ = ·), nodeinv_apply]
    rcases em (x ∈ r1) with hr1 | hr1 <;> simp[hr1]
  }
  have rclink_of_face {l : List α} (hld : l.dropLast.Disjoint r1) (hl : l.IsChain (fromFun H.face))
  : l.IsChain (fromFun rclink) := by{
    induction l with
    | nil => simp
    | cons x l' ih => {
      match l' with
      | [] => simp
      | y :: l'' => {
        rw[List.dropLast_cons₂, List.disjoint_cons_left] at hld
        rw[List.isChain_cons_cons] at hl
        specialize ih hld.2 hl.2
        rw[List.isChain_cons_cons]
        refine ⟨?_, ih⟩
        unfold rclink fromFun
        simp only
        rw[if_neg hld.1]
        exact hl.1
      }
    }
  }
  have cFpL {w : α} {c : List α} :
    (w :: c).IsChain (fromFun H.face) →
    ∀w' ∈ w :: c, H.cface ((w :: c).getLast (by{simp})) w' := by{
    intro hwcc
    have hwcc' := List.isChain_fromFun_getLast (by{simp}) hwcc
    intro w' hw'
    specialize hwcc' _ hw'
    rwa[H.cface_equivalence.comm]
  }
  have sFCr {w : α} {c : List α} :
    (w :: c).Nodup → (w :: c).getLast (by{simp}) ∈ r1
    → (w :: c).IsChain (fromFun H.face) → (w :: c).IsChain (fromFun rclink) := by{
    intro hwcd hwclr hwccf
    apply rclink_of_face ?_ hwccf
    intro w' hw'wcdl hw'r1
    have hwccf' := cFpL hwccf
    rw[← List.dropLast_concat_getLast (l := w :: c) (by{simp})] at hwcd
    rw[List.nodup_append', List.disjoint_singleton] at hwcd
    specialize hwccf' _ (List.mem_of_mem_dropLast hw'wcdl)
    have IH := Hp'.simple.cface_nodup _ hwclr _ hw'r1 hwccf'
    rw[IH] at hwcd
    exact hwcd.2.2 hw'wcdl
  }
  have r1'y : y ∉ r1.tail := by{
    have hr1d := Hp'.nodup
    rw[← List.cons_head_tail hr1n, List.nodup_cons, hr1h] at hr1d
    exact hr1d.1
  }
  have hq2y : y ∈ z' :: q2 := by{
    rw[hz'q2]
    rw[List.mem_iff_getElem]
    use i - List.idxOf z' (x' :: q)
    use (by{
      simp only [List.length_drop]
      apply Nat.sub_lt_sub_right hiz'
      omega
    })
    rw[List.getElem_drop]
    simp only [Nat.add_sub_cancel' hiz']
    rfl
  }
  have hq1z'cf : ∀w' ∈ q1 ++ [z'], H.cface z' w' := by{
    have IH := cFpL (w := (q1 ++ [z']).head (by{simp})) (c := (q1 ++ [z']).tail)
    simp only [List.cons_head_tail, hq1c, ne_eq,
    List.cons_ne_self, not_false_eq_true, List.getLast_append_of_ne_nil,
      List.getLast_singleton, forall_const] at IH
    assumption
  }
  have ⟨c, z'Cc, Uc, Lc, sr1c, Uq1c⟩ : ∃c, (z'::c).IsChain (fromFun rclink)
    ∧ (z' :: c).Nodup ∧ (z'::c).getLast (fun h => nomatch h) = z
    ∧ (∀w ∈ r1, w ∈ z' :: c)
    ∧ (z' :: c).Disjoint q1 := by{
    suffices H
      : ∃c2, (y :: c2).IsChain (fromFun rclink) ∧ c2.Nodup
      ∧ (y :: c2).getLast (by{simp}) = z ∧ (∀w ∈ r1.tail, w ∈ c2)
      ∧ H.fband c2 ⊆ H.fband r1.tail by{
      rcases H with ⟨c2, yRc2, Uc2, Lc2, sr1c2, sFc2r1⟩
      have c2F'y {w : α} : w ∈ c2 → ¬H.cface y w := by{
        intro c2t
        contrapose r1'y
        have sFc2r1' := sFc2r1 (H.subset_fband c2t)
        rw[H.mem_fband_iff] at sFc2r1'
        rcases sFc2r1' with ⟨u, hu, huw⟩
        have IH := Hp'.simple.cface_nodup _ (List.mem_of_mem_tail hu) y (by{simp[← hr1h]})
          (H.cface_equivalence.symm (r1'y.trans huw))
        exact IH ▸ hu
      }
      have c2Dq1 : c2.Disjoint q1 := by{
        intro w hwc2 hwq1
        specialize c2F'y hwc2
        apply c2F'y
        specialize hq1z'cf w (by{simp[hwq1]})
        rw[hr1h] at z'Ry
        exact (cface_equivalence.symm z'Ry).trans hq1z'cf
      }
      let c1 := (z' :: q2).take ((z' :: q2).idxOf y + 1)
      have hc1d : c1.Nodup := by{
        unfold c1
        apply List.nodup_take
        rw[hz'q2]
        apply List.nodup_drop
        exact hq.1
      }
      have hz'c1 : z' :: c1.tail = c1 := by{
        unfold c1
        rw[List.take_succ_cons]
        congr
      }
      have hc1n : c1 ≠ [] := by{
        unfold c1
        simp
      }
      have hc1l : c1.getLast hc1n = y := by{
        unfold c1
        rw[List.take_getLast]
        simp only [List.length_cons, Nat.add_min_add_right, add_tsub_cancel_right]
        have : (z' :: q2).idxOf y ≤ q2.length := by{
          have : (z' :: q2).idxOf y < (z' :: q2).length := by{
            apply List.idxOf_lt_length_of_mem
            exact hq2y
          }
          simp at this
          simp[this]
        }
        simp[this]
      }
      have hc1f : c1.IsChain (fromFun H.face) := by{
        apply List.isChain_take
        exact hz'q2c
      }
      have hc1c : c1.IsChain (fromFun rclink) := by{
        apply sFCr hc1d
        · {
          simp only [← List.take_succ_cons]
          change c1.getLast hc1n ∈ _
          simp only [hc1l, ← hr1h, List.head_mem]
        }
        · {
          simpa [← List.take_succ_cons]
        }
      }
      have hc1cf : ∀w' ∈ c1, H.cface (c1.getLast hc1n) w' := cFpL hc1f
      simp only [hc1l] at hc1cf
      have hc1dc2 : c1.Disjoint c2 := by{
        intro w' hwc1 hwc2
        specialize c2F'y hwc2
        specialize hc1cf _ hwc1
        contradiction
      }
      have hc1dq1 : c1.Disjoint q1 := by{
        unfold c1
        rw[← hq1q]
        have h0 : List.take (List.idxOf z' (x' :: q)) (x' :: q)
          ++ List.take (List.idxOf y (z' :: q2) + 1) (z' :: q2)
          = List.take (List.idxOf z' (x' :: q) + List.idxOf y (z' :: q2) + 1) (x' :: q)
        := by{
          rw[Nat.add_assoc, List.take_add (i := (x' :: q).idxOf z')]
          congr
        }
        have h1 : ((x' :: q).take (List.idxOf z' (x' :: q) + List.idxOf y (z' :: q2) + 1)).Nodup
        := by{
          apply List.nodup_take
          exact hq.1
        }
        rw[← h0, List.nodup_append', List.disjoint_comm] at h1
        exact h1.2.2
      }
      use c1.tail ++ c2
      simp only [← List.cons_append]
      simp only [hz'c1]
      constructor
      · {
        rw[← List.dropLast_concat_getLast hc1n]
        rw[List.isChain_concat_append, List.dropLast_concat_getLast]
        rw[hc1l]
        exact ⟨hc1c, yRc2⟩
      }
      constructor
      · {
        rw[List.nodup_append']
        exact ⟨hc1d, Uc2, hc1dc2⟩
      }
      constructor
      · {
        rcases eq_or_ne c2 [] with hc2n | hc2n
        · {
          simp only [hc2n, List.not_mem_nil, imp_false] at sr1c2
          rw[← List.eq_nil_iff_forall_not_mem] at sr1c2
          simp only [hc2n, List.append_nil, hc1l, ← hr1h]
          match r1 with | [_] => simp[← hz_def]
        }
        rw[List.getLast_cons hc2n] at Lc2
        rwa[List.getLast_append_right hc2n]
      }
      constructor
      · {
        intro w hwr1
        rw[← List.cons_head_tail hr1n, List.mem_cons, hr1h] at hwr1
        rw[List.mem_append]
        rcases hwr1 with hwr1 | hwr1
        · left;simp[hwr1, ← hc1l]
        · right; exact sr1c2 _ hwr1
      }
      · {
        rw[List.disjoint_append_left]
        exact ⟨hc1dq1, c2Dq1⟩
      }
    }
    clear! z' q1 q2
    generalize y = y' at *
    clear! i x' q x
    clear zRy hzr
    match hr1 : r1 with | y :: r1' => {
      simp only [List.head_cons] at hr1h
      simp only [← hr1h] at *
      simp only [List.tail_cons]
      change ∃ c2,
      List.IsChain (fromFun rclink) (y :: c2) ∧
        c2.Nodup ∧ (y :: c2).getLast (by{simp}) = z ∧
        (∀ w ∈ r1', w ∈ c2) ∧ H.fband c2 ⊆ H.fband r1'
      clear hr1h hir
      clear! y'
      rw[List.tail_cons] at r1'y
      have hyr1'd := Hp'.nodup
      have hyr1'c := Hp'.cycle.isChain
      have hyr1's := Hp'.simple
      clear Hp'
      clear rclink_of_face
      clear r1'y
      change (y :: r1').getLast (by{simp}) = z at hz_def
      clear! hr1n
      have hr1y : y :: r1' ⊆ r1 := by{simp[hr1]}
      clear hr1
      induction r1' generalizing y with
      | nil => {
        use []
        simp at hz_def
        simp[hz_def]
      }
      | cons y' r1'' ih => {
        rw[List.getLast_cons_cons] at hz_def
        rw[List.isChain_cons_cons] at hyr1'c
        specialize ih y' (by{
          intro w c hwcd hwcl hwcc
          apply sFCr hwcd (by simp[hwcl]) hwcc
        }) (by{simp at hyr1'd; simp[hyr1'd]}) hyr1'c.right (by{
          exact hyr1's.of_cons
        }) hz_def
          (by{
            intro x hx
            apply hr1y
            simp[hx]
          })
        rcases ih with ⟨c2, zRc2, Uc2, Lc2, sr1c2, sc2r1⟩
        have hfyy' := hyr1'c.1
        unfold rlink at hfyy'
        rw[← cface_face] at hfyy'
        rw[cface, funReflTransGen, ReflTransGen_iff_isChain_minimal_nodup] at hfyy'
        rcases hfyy' with ⟨c1, Uc1, Cc1, Lc1, Mc1⟩
        rw[← List.getLast_cons_eq_getLastD] at Lc1
        have c1Dc2 : (face (edge y) :: c1).Disjoint c2 := by{
          intro x hxc1 hxc2
          have cFpL' := cFpL Cc1 _ hxc1
          rw[Lc1] at cFpL'
          have hyr1's' := hyr1's.cface_nodup
          have sc2r1' := sc2r1 (H.subset_fband hxc2)
          rw[H.mem_fband_iff] at sc2r1'
          rcases sc2r1' with ⟨z, hzr1'', hzx⟩
          have cFpL'' : H.cface _ _ := cFpL'.trans hzx
          specialize hyr1's' _ (by{simp}) _ (by{simp[hzr1'']}) cFpL''
          simp[hyr1's', hzr1''] at hyr1'd
        }
        use face (edge y) :: c1 ++ c2
        constructor
        · {
          rw[List.cons_append, List.isChain_cons_cons, ← List.cons_append]
          constructor
          · {
            unfold fromFun rclink
            rw[if_pos]
            apply hr1y; simp
          }
          rw[← List.dropLast_concat_getLast (l := face (edge y) :: c1) (by{simp})]
          rw[List.isChain_concat_append, List.dropLast_concat_getLast, Lc1]
          refine ⟨?_, zRc2⟩
          apply sFCr Uc1 (by{simp[Lc1]}) Cc1
        }
        constructor
        · {
          rw[List.nodup_append']
          exact ⟨Uc1, Uc2, c1Dc2⟩
        }
        constructor
        · {
          rw[List.getLast_cons (by{simp})]
          suffices H : ((face (edge y) :: c1).dropLast ++
            [(face (edge y) :: c1).getLast (by{simp})] ++ c2).getLast (by{simp}) = z
            by{
              simp only [List.dropLast_concat_getLast] at H
              exact H
            }
          simp[Lc1, Lc2]
        }
        constructor
        · {
          intro w hw
          rw[List.mem_cons] at hw
          rw[List.mem_append]
          rcases hw with hw | hw
          · left; rw[hw, ← Lc1]; apply List.getLast_mem
          · right; exact sr1c2 _ hw
        }
        · {
          intro w hw
          rw[H.mem_fband_iff] at *
          rcases hw with ⟨w', hw', hww'⟩
          rw[List.mem_append] at hw'
          rcases hw' with hw' | hw'
          · {
            use y', (by{simp})
            specialize cFpL Cc1 _ hw'
            rw[Lc1] at cFpL
            exact hww'.trans (H.cface_equivalence.symm cFpL)
          }
          have hw'' : w ∈ H.fband c2 := by{
            rw[H.mem_fband_iff]
            use w'
          }
          specialize sc2r1 hw''
          rw[H.mem_fband_iff] at sc2r1
          rcases sc2r1 with ⟨w'', hw''⟩
          use w''
          simp[hw'']
        }
      }
    }
  }
  have z'Ccf : ∀w ∈ z' :: c, w ∉ r1 → face w ∈ z' :: c := by{
    intro w hwzc hwr1
    have hr1d := Hp'.nodup
    have Lc' : (z' :: c).getLast (by{simp}) ∈ r1 := by{
      rw[Lc, ← hz_def]
      apply List.getLast_mem
    }
    clear! z q1 q2 i
    clear z'Ry hz'n hz'q hz'x' sr1c
    induction c generalizing z' with
    | nil => {
      rw[List.mem_singleton] at hwzc
      rw[List.getLast_singleton, ← hwzc] at Lc'
      contradiction
    }
    | cons z'' c' ih => {
      rw[List.mem_cons] at hwzc
      rcases hwzc with hwzc | hwzc
      · {
        rw[List.isChain_cons_cons] at z'Cc
        apply And.left at z'Cc
        unfold fromFun rclink at z'Cc
        rw[← hwzc, if_neg hwr1] at z'Cc
        simp[z'Cc]
      }
      rw[List.getLast_cons_cons] at Lc'
      specialize ih z'' z'Cc.of_cons Uc.of_cons hwzc Lc'
      simp[ih]
    }
  }
  clear hr1_disjoint
  have ⟨x1, c_nx1, p, x1Cp, Lp, Upc⟩ : ∃x1, node x1 ∈ z' :: c
    ∧ ∃p, (x1 :: p).IsChain H.clink ∧ (x1 :: p).getLast (fun h => nomatch h) = x'
    ∧ (x1 :: p).Disjoint (z' :: c) := by{
    rcases hx with ⟨dNx, xr1⟩
    rcases dNx with ⟨x0, rx0, hxp⟩
    rw[dconnect, ReflTransGen_iff_isChain] at hxp
    rcases hxp with ⟨p, x0'Dp, Lp⟩
    generalize hx0'_def : H.nodeinv x0 = x0'
    rw[hx0'_def] at x0'Dp Lp
    have cycCc : (z' :: c).IsCycleChain (fromFun rclink) := by{
      unfold List.IsCycleChain
      rw[dif_neg (by{simp}), Lc, List.head_cons]
      apply And.intro z'Cc
      unfold fromFun rclink
      rw[if_pos, ← hz'_def]
      rw[← hz_def]
      apply List.getLast_mem
    }
    have rx0' : ¬(x0' :: p).Disjoint (z' :: c) := by{
      have cx0 : x0 ∈ z' :: c := sr1c _ rx0
      have : rclink x0 = x0' := by{unfold rclink;rw[if_pos rx0, ← hx0'_def, nodeinv_apply]}
      rw[List.Disjoint]
      push_neg
      use x0', (by{simp})
      rw[and_true]
      have cycCc' := List.forall_mem_of_isCycleChain cycCc cx0 1
      rw[iterate_one, this] at cycCc'
      exact cycCc'
    }
    clear rx0
    clear! x0
    induction p generalizing x0' with
    | nil => {
      simp only [List.getLastD_eq_getLast?, List.getLast?_nil, Option.getD_none] at Lp
      rw[List.singleton_disjoint, not_not] at rx0'
      have cx : x ∈ z' :: c := Lp ▸ rx0'
      use x'
      constructor
      · rwa[← hx'x, nfe_cancel]
      use []
      refine ⟨by{simp}, by{simp}, ?_⟩
      rw[List.singleton_disjoint]
      apply Uq1c.symm
      rw[← hq1h]
      apply List.head_mem
    }
    | cons x1 p' ih => {
      rcases em' ((x1 :: p').Disjoint (z' :: c)) with hdisj | hdisj
      · {
        rw[List.getLastD_cons] at Lp
        rw[List.isChain_cons_cons] at x0'Dp
        specialize ih x1 Lp x0'Dp.2 hdisj
        exact ih
      }
      use x1
      rw[List.isChain_cons_cons] at x0'Dp
      rcases x0'Dp with ⟨⟨hx0'r1, hcx0'x1⟩, x1Dp⟩
      rw[clink, union_iff, fromFun, fromFun, nodeinv_eq_iff_eq_node] at hcx0'x1
      have hf'x0'x1 : face x0' ≠ x1 := by{
        rw[List.disjoint_cons_left, not_and] at rx0'
        apply swap at rx0'
        specialize rx0' hdisj
        apply not_not.mp at rx0'
        have : face x0' ∈ z' :: c := by{
          exact z'Ccf _ rx0' hx0'r1
        }
        contrapose this
        apply hdisj
        rw[this]
        simp
      }
      apply (Or.resolve_right · hf'x0'x1) at hcx0'x1
      rw[← hcx0'x1]
      rw[List.disjoint_cons_left, not_and] at rx0'
      apply swap at rx0'
      specialize rx0' hdisj
      apply not_not.mp at rx0'
      apply And.intro rx0'
      use p' ++ [x']
      rw[List.getLastD_cons] at Lp
      split_ands
      · {
        rw[← List.cons_append, List.isChain_concat_iff_of_ne_nil (by{simp})]
        rw[List.getLast_cons_eq_getLastD, Lp]
        constructor
        · {
          apply x1Dp.subset
          unfold dlink
          intro _ _
          apply And.right
        }
        · {
          rw[clink, union_iff, fromFun]
          left
          rw[← hx'x, nodeinv_apply]
        }
      }
      · simp
      · {
        rw[← List.cons_append, List.disjoint_append_left]
        apply And.intro hdisj
        rw[List.singleton_disjoint]
        apply Uq1c.symm
        rw[← hq1h]
        apply List.head_mem
      }
    }
  }
  have z'Cc' : (z' :: c).IsChain H.clink := by{
    apply z'Cc.subset
    intro x y (hxy : _ = _)
    rw[← hxy]
    apply clink_rclink
  }
  have ⟨c0, x1Cc0, Lc0, Ucc0⟩ : ∃c0, (x1 :: c0).IsChain H.clink
    ∧ H.clink ((x1 :: c0).getLast (fun h => nomatch h)) z'
    ∧ (x1 :: c0).Disjoint (z' :: c) := by{
    use p ++ q1.tail
    have : x1 :: p ++ q1.tail = (x1 :: p).dropLast ++ q1 := by{
      nth_rw 1 [← List.dropLast_concat_getLast (l := x1 :: p) (by{simp})]
      rw[List.append_assoc, Lp, ← hq1h, List.singleton_append, List.cons_head_tail]
    }
    constructor
    · {
      rw[← List.cons_append, ← List.dropLast_append_getLast (l := x1 :: p) (by{simp})]
      rw[List.isChain_concat_append, List.dropLast_append_getLast]
      rw[Lp, ← hq1h, List.cons_head_tail]
      refine ⟨x1Cp, ?_⟩
      apply hq1c.left_of_append.subset
      intro x y (hxy : _ = _)
      simp[clink, union_iff, fromFun, hxy]
    }
    constructor
    · {
      simp only [← List.cons_append, this]
      rw[List.getLast_append_right hq1n]
      rw[List.isChain_concat_iff_of_ne_nil hq1n] at hq1c
      have hq1c' : _ = _ := hq1c.right
      rw[← hq1c']
      simp[clink, union_iff, fromFun]
    }
    · {
      rw[← List.cons_append, List.disjoint_append_left]
      refine And.intro Upc (List.disjoint_tail_left Uq1c.symm)
    }
  }
  have ⟨c1, x1Cc1, Uc1, Lc1, Ucc1⟩ : ∃c1, (x1 :: c1).IsChain H.clink ∧ (x1 :: c1).Nodup
    ∧ H.clink ((x1 :: c1).getLast (fun h => nomatch h)) z'
    ∧ (x1 :: c1).Disjoint (z' :: c) := by{
    have ⟨c1, hc1n, x1Cc1, Uc1, Hc1, Lc1, Ucc1⟩
      := List.exists_isChain_disjoint_shorten x1Cc0 Ucc0 (by{simp})
    use c1.tail
    have ih : x1 :: c1.tail = c1 := by{
      simp at Hc1
      simp[← Hc1]
    }
    simp only [ih]
    refine ⟨x1Cc1, Uc1, ?_, Ucc1⟩
    rwa[Lc1]
  }
  apply Hp'.toPlanar.jordan (x1 :: c1 ++ z' :: c)
  unfold moebius_path
  rw[dif_neg (by{simp})]
  split_ands
  · {
    rw[List.nodup_append']
    exact ⟨Uc1, Uc, Ucc1⟩
  }
  · {
    rw[List.isChain_append_cons, List.isChain_concat_iff_of_ne_nil (by{simp})]
    exact ⟨⟨x1Cc1, Lc1⟩, z'Cc'⟩
  }
  · {
    simp only [List.cons_append, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false,
      not_false_eq_true, List.getLast_cons, List.getLast_append_of_ne_nil, List.tail_cons,
      List.head_cons, Lc, nodeinv_apply, hz'_def]
    have : List.idxOf z' (c1 ++ z' :: c) = c1.length := by{
      rw[List.idxOf_append_of_notMem, List.idxOf_cons_self, add_zero]
      symm at Ucc1
      specialize Ucc1 (by{simp} : z' ∈ z' :: c)
      simp at Ucc1
      simp[Ucc1]
    }
    rw[this, List.drop_append_length]
    simp[c_nx1]
  }
}
theorem diskE_cedge_close (Hp : H.properSnipRing r)
: ∀x ∈ H.diskE r, ∀y, H.cedge x y → y ∈ H.diskE r := by{
  exact diskE_edge_closure Hp
}
theorem diskE_cedge_close_iff (Hp : H.properSnipRing r)
{x y : α} (hxy : H.cedge x y)
: x ∈ H.diskE r ↔ y ∈ H.diskE r := by{
  constructor
  · intro h; exact diskE_cedge_close Hp _ h _ hxy
  · {
    intro h
    apply H.cedge_Symm.symm at hxy
    exact diskE_cedge_close Hp _ h _ hxy
  }
}

section

abbrev dDart (r : List α):= {x // x ∈ H.diskN r}
@[inline] instance dDart.instFintype
: Fintype (H.dDart r) := by{
  apply Subtype.fintype
}
def snipd_edge (r : List α) : α → α :=
  fun x => if hxr : x ∈ r then r.next x hxr else edge x
def snipd_face (r : List α) : α → α :=
  fun x => if hxr : x ∈ r then face (edge (r.prev x hxr)) else face x
lemma dedge_subproof (Hp : H.properSnipRing r) {u : H.dDart r}
: H.snipd_edge r u.val ∈ H.diskN r := by{
  unfold snipd_edge
  split
  · apply subset_diskN; apply List.next_mem
  apply diskE_subset_diskN
  apply diskE_cedge_close Hp u.val ?_ _ (funReflTransGen.single _ _)
  exact ⟨u.prop, by assumption⟩
}
lemma dface_subproof (Hp : H.properSnipRing r) {u : H.dDart r}
: H.snipd_face r u.val ∈ H.diskN r := by{
  unfold snipd_face
  split
  · {
    apply diskN_cnode_close (r.prev u.val (by assumption)) ?_ _ (by{
      apply cnode_equivalence.symm
      apply ReflTransGen.single
      exact nfe_cancel _
    })
    apply subset_diskN; apply List.prev_mem
  }
  apply diskN_cnode_close (node (face u.val)) ?_ _ (by{
    apply cnode_equivalence.symm
    apply funReflTransGen.single
  })
  apply diskE_subset_diskN
  apply diskE_cedge_close Hp u.val ?_ _ (by{
    apply cedge_equivalence.symm
    apply ReflTransGen.single
    exact enf_cancel _
  })
  exact ⟨u.prop, by assumption⟩
}
lemma dnode_subproof {u : H.dDart r} : node u.val ∈ H.diskN r := by{
  apply diskN_cnode_close _ u.prop
  apply funReflTransGen.single
}

abbrev rDart (r : List α):= {x // x ∉ H.diskE r}
@[inline] instance rDart.instFintype : Fintype (H.rDart r) := by{
  apply Subtype.fintype
}
def snipr_face (r : List α) : α → α :=
  fun x => if hxr : node (face x) ∈ r then r.next (node (face x)) hxr else face x
def snipr_node (r : List α) : α → α :=
  fun x => if hxr : x ∈ r then r.prev x hxr else node x
lemma redge_subproof (Hp : H.properSnipRing r) {u : H.rDart r}
: edge u.val ∉ H.diskE r := by{
  have hu := u.prop
  contrapose hu
  apply diskE_cedge_close Hp _ hu
  apply cedge_equivalence.symm
  apply funReflTransGen.single
}
lemma rface_subproof (Hp : H.properSnipRing r) {u : H.rDart r}
: H.snipr_face r u.val ∉ H.diskE r := by{
  unfold snipr_face
  split
  · apply subset_diskEC; apply List.next_mem
  intro ⟨hl, hr⟩
  have hl' : node (face u.val) ∈ H.diskN r := by{
    apply diskN_node_close
    assumption
  }
  have hl'' : node (face u.val) ∈ H.diskE r :=
    ⟨hl', by assumption⟩
  have hu : u.val ∈ H.diskE r := by{
    apply diskE_cedge_close Hp _ hl''
    apply ReflTransGen.single
    exact enf_cancel _
  }
  exact u.prop hu
}
lemma rnode_subproof {u : H.rDart r}
: H.snipr_node r u.val ∉ H.diskE r := by{
  unfold snipr_node
  split
  · apply subset_diskEC; apply List.prev_mem
  change ¬(_ ∧ _)
  push_neg
  have hu := u.prop
  change ¬(_ ∧ _) at hu
  push_neg at hu
  intro h
  have h' : u.val ∈ H.diskN r := by{
    apply diskN_cnode_close _ h
    apply cnode_equivalence.symm
    apply funReflTransGen.single
  }
  specialize hu h'
  contradiction
}

namespace properSnipRing

def dedge {Hp : H.properSnipRing r}
: H.dDart r → H.dDart r := fun u => ⟨_, dedge_subproof Hp (u:=u)⟩
def dface {Hp : H.properSnipRing r}
: H.dDart r → H.dDart r := fun u => ⟨_, dface_subproof Hp (u:=u)⟩
def dnode {_ : H.properSnipRing r}
: H.dDart r → H.dDart r := fun u => ⟨_, dnode_subproof (u:=u)⟩
lemma snipd_enf_cancel {Hp : H.properSnipRing r}
: ∀u : H.dDart r, Hp.dedge (Hp.dnode (Hp.dface u)) = u := by{
  intro u
  unfold dface dnode dedge snipd_face snipd_edge
  simp only
  rcases em (u.val ∈ r) with hu | hu
  · {
    simp[hu, nfe_cancel, List.prev_mem _ _ _]
    simp[List.next_prev r Hp.nodup]
  }
  simp only [hu, ↓reduceDIte, enf_cancel, Subtype.ext_iff]
  rw[dif_neg]
  have hu' : u.val ∈ H.diskE r := ⟨u.prop, hu⟩
  suffices H : node (face u.val) ∈ H.diskE r by{exact H.2}
  apply diskE_cedge_close Hp _ hu'
  apply cedge_equivalence.symm
  apply ReflTransGen.single
  exact enf_cancel _
}
@[reducible] def snipDisk (Hp : H.properSnipRing r) : Hypermap (H.dDart r) where
  edge := dedge
  node := dnode
  face := dface
  enf_cancel := Hp.snipd_enf_cancel
def snipDiskRing (_ : H.properSnipRing r) : List (H.dDart r) := r.pmap
(P := (· ∈ H.diskN r)) (fun x hx => ⟨x, hx⟩) (fun _ => H.subset_diskN)
theorem mem_snipDiskRing_iff {Hp : H.properSnipRing r} {x : H.dDart r}
: x ∈ Hp.snipDiskRing ↔ x.val ∈ r := by{
  unfold snipDiskRing
  rw[List.mem_pmap]
  constructor
  · {
    intro ⟨a, ha, hax⟩
    rwa[← hax]
  }
  · {
    intro hx
    use x.val, hx
  }
}
theorem cface_of_snipDisk_cface {Hp : H.properSnipRing r} {x y : H.dDart r}
: Hp.snipDisk.cface x y → H.cface x y := by{
  intro h
  induction h with
  | refl => apply ReflTransGen.refl
  | @tail b c hh ht ih => {
    apply ih.trans
    change dface _ = _ at ht
    unfold dface at ht
    simp only [Subtype.ext_iff, snipd_face] at ht
    split at ht
    · {
      have Hp' := Hp.cycle
      rw[List.isCycleChain_iff_prev_of_nodup Hp.nodup] at Hp'
      specialize Hp' b (by assumption)
      unfold rlink at Hp'
      rw[← cface_face, ht] at Hp'
      exact cface_equivalence.symm Hp'
    }
    · {
      apply ReflTransGen.single
      exact ht
    }
  }
}

def redge {Hp : H.properSnipRing r}
: H.rDart r → H.rDart r := fun u => ⟨_, redge_subproof Hp (u:=u)⟩
def rface {Hp : H.properSnipRing r}
: H.rDart r → H.rDart r := fun u => ⟨_, rface_subproof Hp (u:=u)⟩
def rnode {_ : H.properSnipRing r}
: H.rDart r → H.rDart r := fun u => ⟨_, rnode_subproof (u:=u)⟩
lemma snipr_enf_cancel {Hp : H.properSnipRing r}
: ∀u : H.rDart r, Hp.redge (Hp.rnode (Hp.rface u)) = u := by{
  intro ⟨u, hu⟩
  simp only [redge, rface, rnode, snipr_face, snipr_node]
  simp only [Subtype.ext_iff]
  rcases em (node (face u) ∈ r) with hnfu | hnfu
  · {
    simp only [dif_pos hnfu, dif_pos (List.next_mem _ _ _)]
    simp only [List.prev_next _ Hp.nodup, enf_cancel]
  }
  simp only [dif_neg hnfu]
  rw[dif_neg, enf_cancel]
  contrapose hu
  have hu' : face u ∈ H.diskN r := subset_diskN hu
  have hu'' : node (face u) ∈ H.diskN r := by{
    apply diskN_node_close
    assumption
  }
  have hu''' : node (face u) ∈ H.diskE r :=
    ⟨hu'', hnfu⟩
  rw[← enf_cancel u]
  apply diskE_cedge_close Hp _ hu'''
  apply funReflTransGen.single
}
@[reducible] def snipRem (Hp : H.properSnipRing r) : Hypermap (H.rDart r) where
  edge := redge
  node := rnode
  face := rface
  enf_cancel := Hp.snipr_enf_cancel
def snipRemRing (_ : H.properSnipRing r) : List (H.rDart r) := r.reverse.pmap
(P := (· ∉ H.diskE r)) (fun x hx => ⟨x, hx⟩) (fun _ => by{
  rw[List.mem_reverse]
  apply H.subset_diskEC
})
theorem mem_snipRemRing_iff {Hp : H.properSnipRing r} {x : H.rDart r}
: x ∈ Hp.snipRemRing ↔ x.val ∈ r := by{
  unfold snipRemRing
  rw[List.mem_pmap]
  simp only [List.mem_reverse]
  constructor
  · {
    intro ⟨a, ha, hax⟩
    rwa[← hax]
  }
  · {
    intro hx
    use x.val, hx
  }
}

theorem snip_patch {Hp : H.properSnipRing r}
: Patch H Hp.snipDisk Hp.snipRem Subtype.val Subtype.val
  Hp.snipDiskRing Hp.snipRemRing := by{
  constructor
  · exact Subtype.val_injective
  · exact Subtype.val_injective
  · {
    change Hp.snipDisk.simpleCycle (fromFun Hp.dedge) _
    unfold snipDiskRing
    unfold simpleCycle
    constructor
    · {
      rw[List.isCycleChain_iff_next_of_nodup]
      · {
        intro x hx
        change _ = _
        apply Subtype.val_injective
        rw[← List.map_next_apply Subtype.val_injective]
        simp only [List.map_pmap, List.pmap_eq_map]
        change _ = (r.map id).next _ _
        simp only [List.map_id]
        unfold dedge snipd_edge
        simp only
        rw[dif_pos]
      }
      · {
        apply List.Nodup.pmap
        · simp
        · exact Hp.nodup
      }
    }
    · {
      unfold simpleList
      rw[List.map_pmap]
      apply List.Nodup.pmap''
      · {
        intro a b har hbr hab
        rw[Quotient.eq] at hab
        apply cface_of_snipDisk_cface at hab
        exact Hp.simple.cface_nodup _ har _ hbr hab
      }
      · exact Hp.nodup
    }
  }
  · {
    constructor
    · {
      unfold snipRemRing
      rw[List.isCycleChain_iff_next_of_nodup]
      · {
        intro x hx
        change _ = _
        apply Subtype.val_injective
        rw[← List.map_next_apply Subtype.val_injective]
        simp only [List.map_pmap, List.pmap_eq_map]
        change _ = (r.reverse.map id).next _ _
        simp only [List.map_id]
        rw[List.mem_pmap] at hx
        rcases hx with ⟨y, hy, hyx⟩
        rw[List.mem_reverse] at hy
        simp only [← hyx]
        rw[List.next_reverse_eq_prev _ Hp.nodup _ hy]
        change (rnode _).val = _
        unfold rnode snipr_node
        simp[hy]
      }
      · {
        apply List.Nodup.pmap
        · simp
        · rw[List.nodup_reverse]; exact Hp.nodup
      }
    }
    · {
      unfold snipRemRing
      rw[List.pmap_reverse, List.nodup_reverse]
      apply List.Nodup.pmap''
      · {
        intro a b ha hb
        apply Subtype.ext_iff.mp
      }
      · exact Hp.nodup
    }
  }
  · {
    unfold snipRemRing snipDiskRing
    rw[List.pmap_reverse, List.map_reverse, List.reverse_inj]
    rw[List.map_pmap, List.map_pmap]
    simp only
    rw[List.pmap_eq_map, List.pmap_eq_map]
  }
  · {
    intro x
    constructor
    · {
      intro ⟨y, hyx⟩
      have hy := y.prop
      change ¬(_ ∧ _) at hy
      rw[not_and_or, not_not] at hy
      rcases hy with hy | hy
      · {
        left
        intro z hzx
        have hz := z.prop
        rw[hzx] at hz
        rw[hyx] at hy
        contradiction
      }
      · {
        right
        rw[List.mem_map]
        simp only [mem_snipDiskRing_iff]
        use ⟨y.val, H.subset_diskN hy⟩
      }
    }
    · {
      intro IH
      rcases IH with IH | IH
      · {
        rcases em (x ∈ H.diskN r) with hx | hx
        · specialize IH ⟨x, hx⟩; contradiction
        have hx' : x ∉ H.diskE r := by{
          contrapose hx
          exact hx.1
        }
        use ⟨x, hx'⟩
      }
      · {
        rw[List.mem_map] at IH
        simp only [mem_snipDiskRing_iff] at IH
        rcases IH with ⟨y, hy, hyx⟩
        rw[hyx] at hy
        have hy' : x ∉ H.diskE r := by{
          change ¬(_ ∧ _)
          simp[hy]
        }
        use ⟨x, hy'⟩
      }
    }
  }
  · {
    simp only [Hp.mem_snipDiskRing_iff]
    intro x hx
    change (dedge _).val = edge _
    unfold dedge snipd_edge
    simp only
    rw[dif_neg hx]
  }
  · {
    intro x
    change (Hp.dnode _).val = _
    rw[dnode]
  }
  · {
    intro x
    change (Hp.redge _).val = _
    rw[redge]
  }
  · {
    simp only [Hp.mem_snipRemRing_iff]
    intro x hx
    change (rnode _).val = node _
    unfold rnode snipr_node
    simp only
    rw[dif_neg hx]
  }
}

theorem snipDisk_planar {Hp : H.properSnipRing r}
: Hp.snipDisk.Planar := by{
  have Hp' := Hp.toPlanar
  have Hp'' := Hp.snip_patch
  rw[Hp''.planar_patch_iff] at Hp'
  exact Hp'.1
}
theorem snipRem_planar {Hp : H.properSnipRing r}
: Hp.snipRem.Planar := by{
  have Hp' := Hp.toPlanar
  have Hp'' := Hp.snip_patch
  rw[Hp''.planar_patch_iff] at Hp'
  exact Hp'.2
}
end properSnipRing
end
end Hypermap
