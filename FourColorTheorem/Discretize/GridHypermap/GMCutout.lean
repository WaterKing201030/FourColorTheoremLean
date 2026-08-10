import FourColorTheorem.Discretize.GridHypermap.GMDisk

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

-- 将 GMcutout 从 Prop 修改为 Type 1，打包所有的存在性数据
structure GMCutout (hgp : GridMapProper ab0 cm0) (E : Set (Fin n)) where
  α : Type _
  [fintype_α : Fintype α]
  [dec_eq_α : DecidableEq α]
  G : Hypermap α
  h : α → hgp.GMDart
  r : Fin n → List α
  map_planar : G.Planar
  enc_injective : Injective h
  enc_morph_edge : ∀ x, h (G.edge x) = hgp.GMDartHypermap.edge (h x)
  enc_morph_cface : ∀ x y, G.cface x y ↔ hgp.GMDartHypermap.cface (h x) (h y)
  enc_morph_node : ∀ x, (∀ i ∈ E, x ∉ r i) → h (G.node x) = hgp.GMDartHypermap.node (h x)
  ring_def : ∀ i, ((r i).map h).reverse = hgp.GMring i
  ring_proper : ∀ i ∈ E, List.IsCycleChain (fromFun G.node) (r i) ∧ (r i).Nodup

@[inline] instance GMCutout.instFintype {hgp : GridMapProper ab0 cm0} {E : Set (Fin n)}
  {C : GMCutout hgp E} : Fintype C.α := C.fintype_α
@[inline] instance GMCutout.instDecidableEq {hgp : GridMapProper ab0 cm0} {E : Set (Fin n)}
  {C : GMCutout hgp E} : DecidableEq C.α := C.dec_eq_α
theorem GMCutout.r_ne_nil {hgp : GridMapProper ab0 cm0} {E : Set (Fin n)}
(C : GMCutout hgp E) (i : Fin n) : C.r i ≠ [] := by{
  have IH := C.ring_def i
  have IH' := hgp.GMring_ne_nil (i := i)
  intro h
  simp[h] at IH
  contradiction
}

theorem exists_cutout (hgp : GridMapProper ab0 cm0) :
  Nonempty (GMCutout hgp Set.univ) := by {
  have h_univ : (Set.univ : Set (Fin n)) = (Finset.univ : Finset (Fin n)) := by ext; simp
  rw [h_univ]
  generalize (Finset.univ : Finset (Fin n)) = E'
  clear h_univ
  induction E' using Finset.induction_on with
  | empty => exact ⟨{
      α := hgp.GMDart
      G := hgp.GMDartHypermap
      h := id
      r := fun i => (hgp.GMring i).reverse
      map_planar := hgp.GMDartHypermap_planar
      enc_injective := injective_id
      enc_morph_edge := fun x => rfl
      enc_morph_cface := fun x y => Iff.rfl
      enc_morph_node := fun x _ => rfl
      ring_def := fun i => by {simp}
      ring_proper := fun i hi => by{simp at hi}
    }⟩
  | insert j E' hj_not_in ih => {
    rcases ih with ⟨⟨β, G, h, r, planG, Ih, hE, hF, hN, Dr, cycNr⟩⟩
    generalize hmj_def : {x | h x ∈ hgp.GMDartHypermap.diskN (hgp.GMring j)}.toFinset = mj
    have h_r : ∀i x, h x ∈ hgp.GMring i ↔ x ∈ (r i).reverse := by{
      intro i x
      rw[List.mem_reverse]
      rw[← Dr, List.mem_reverse, List.mem_map_of_injective Ih]
    }
    have cycRrj : G.simpleCycle G.rlink (r j).reverse := by{
      have cycRrj := hgp.GMring_simpleCycle (i := j)
      rw[← Dr j, ← List.map_reverse] at cycRrj
      rcases cycRrj with ⟨cycRrj, UFrj⟩
      unfold List.IsCycleChain at cycRrj
      have hrjn : (r j).reverse ≠ [] := by{
        specialize Dr j
        have hrjn := hgp.GMring_ne_nil (i := j)
        rw[← Dr] at hrjn
        simp at hrjn
        simp[hrjn]
      }
      constructor
      · {
        unfold List.IsCycleChain
        rw[dif_neg hrjn]
        rw[dif_neg (by{simp at hrjn; simp[hrjn]})] at cycRrj
        rw[List.IsChain_map, List.getLast_map, List.head_map] at cycRrj
        constructor
        · {
          apply cycRrj.1.subset
          intro x y hxy
          unfold InvImage Hypermap.rlink at hxy
          rw[← hE, ← hF] at hxy
          exact hxy
        }
        · {
          unfold Hypermap.rlink at cycRrj
          rw[← hE, ← hF] at cycRrj
          exact cycRrj.2
        }
      }
      · {
        unfold Hypermap.simpleList at UFrj
        unfold Hypermap.simpleList
        rw[List.map_map] at UFrj
        rw[List.nodup_iff_getElem_ne_getElem] at UFrj
        rw[List.nodup_iff_getElem_ne_getElem]
        intro i j hij hjl
        simp only [List.map_reverse, List.length_reverse, List.length_map] at hjl
        specialize UFrj i j hij (by{simp[hjl]})
        rw[List.getElem_map, List.getElem_map]
        rw[List.getElem_map, List.getElem_map, comp_apply, comp_apply] at UFrj
        contrapose UFrj
        rw[Quotient.eq] at UFrj
        change G.cface _ _ at UFrj
        rw[hF] at UFrj
        rwa[Quotient.eq]
      }
    }
    have r'mj : ∀i x, i ≠ j → x ∈ mj → x ∉ r i := by{
      intro i x j'i mj_x ri'x
      have ri'x' := (h_r i x).mpr (by{simpa})
      rw[← hmj_def, Set.mem_toFinset, Set.mem_setOf] at mj_x
      change _ ∈ hgp.GMdisk _ at mj_x
      exact (hgp.GMdisk_disjoint j'i).notMem_of_mem_left (hgp.GMRing_subset_GMDisk ri'x') mj_x
    }
    have mj_hN : ∀x ∈ mj, h (G.node x) = hgp.GMDartHypermap.node (h x) := by{
      intro x mj_x
      rw[← hN]
      intro i hiE
      apply r'mj _ _ ?_ mj_x
      contrapose hj_not_in
      rwa[← hj_not_in]
    }
    have mjN : Closure (fromFun G.node) mj := by{
      rw[closure_iff_single]
      unfold fromFun
      intro x hx y hxy
      apply congrArg h at hxy
      rw[mj_hN _ hx] at hxy
      rw[← hmj_def]
      simp only [Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw[← hmj_def, Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf] at hx
      rw[← hxy]
      apply Hypermap.diskN_node_close _ hx
    }
    have propersnip_j : G.properSnipRing (r j).reverse := ⟨planG, cycRrj⟩
    have h_mj : G.diskN (r j).reverse ⊆ mj := by{
      intro a ⟨z, rj_z, hzx⟩
      rw[Hypermap.dconnect, ReflTransGen_iff_isChain] at hzx
      rcases hzx with ⟨s, xDs, Ls⟩
      rw[← Ls]
      generalize hzx : G.nodeinv z = x at xDs
      have mj_x : x ∈ mj := by{
        change x ∈ (mj : Set β)
        rw[← hzx]
        apply mjN z ?_ _ (by{
          apply Hypermap.cnode_equivalence.symm
          apply ReflTransGen.single
          exact Hypermap.nodeinv_rightinv _
        })
        rw[← hmj_def, Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf]
        change h z ∈ hgp.GMdisk _
        rw[← h_r] at rj_z
        apply hgp.GMRing_subset_GMDisk
        exact rj_z
      }
      clear rj_z hzx Ls
      induction s generalizing x with
      | nil => simp[mj_x]
      | cons y s IHs => {
        specialize IHs y xDs.of_cons
        rw[List.isChain_cons_cons] at xDs
        have xDy := xDs.1
        unfold Hypermap.dlink at xDy
        rcases xDy with ⟨xr, xDy⟩
        rw[Hypermap.clink, union_iff, fromFun, fromFun] at xDy
        rw[List.getLastD_cons]
        rcases xDy with xDy | xDy
        · {
          apply IHs
          apply mjN x mj_x
          rw[← xDy]
          apply Hypermap.cnode_equivalence.symm
          apply ReflTransGen.single
          apply Hypermap.nodeinv_rightinv
        }
        rw[← hmj_def, Set.mem_toFinset, Set.mem_setOf, Hypermap.mem_diskN_iff_diskE] at mj_x
        symm at mj_x
        rcases mj_x with mj_x | mj_x
        · {
          apply IHs
          rw[← Hypermap.eq_faceinv_iff_face_eq, Hypermap.faceinv_apply] at xDy
          have mjx' := Hypermap.diskE_edge_closure
            ⟨hgp.GMDartHypermap_planar, hgp.GMring_simpleCycle⟩
            _ (xDy ▸ mj_x) (h (G.node y)) (by{
              rw[hE]
              change Hypermap.cedge _ _ _
              rw[Hypermap.cedge_edge]
              apply funReflTransGen.refl
            })
          have mjx' := mjx'.1
          have mjx'' := mjN (G.node y) (by{
            rwa[← hmj_def, Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf]
          }) y (by{
            change G.cnode _ _
            rw[G.cnode_node]
            apply funReflTransGen.refl
          })
          exact mjx''
        }
        rw[h_r] at mj_x
        contradiction
      }
    }
    have patch_j := propersnip_j.snip_patch
    let Gj := propersnip_j.snipRem
    have Ihj := patch_j.rem_hom_injective
    have cycNrj := patch_j.rem_border_cycle
    have hjN := patch_j.rem_node_morph
    have hrj_lemma : ∀i, i ≠ j → ∀x ∈ r i, x ∉ G.diskE (r j).reverse := by{
      intro i hij x hxri
      rw[G.diskE_reverse_eq]
      change ¬(_ ∧ _)
      push_neg
      intro hxrj
      have hxmj : x ∈ mj := by{
        apply h_mj
        rwa[Hypermap.diskN_reverse_eq]
      }
      specialize r'mj i x hij hxmj
      contradiction
    }
    have hrj_lemma' : ∀x ∈ r j, x ∉ G.diskE (r j).reverse := by{
      intro x hxrj
      rw[G.diskE_reverse_eq]
      change ¬(_ ∧ _)
      push_neg
      simp[hxrj]
    }
    have hrj_lemma'' : ∀i, ∀x ∈ r i, x ∉ G.diskE (r j).reverse := by{
      intro i
      rcases eq_or_ne i j with hij | hij
      · simpa[hij]
      · specialize hrj_lemma _ hij; simpa
    }
    have ⟨rj, Drj⟩ : ∃rj : Fin n → List (G.rDart (r j).reverse), ∀i, (rj i).map Subtype.val = r i
    := by{
      let rj : Fin n → List (G.rDart (r j).reverse) := fun i =>
        (r i).pmap Subtype.mk (hrj_lemma'' i)
      use rj
      intro i
      unfold rj
      simp[List.map_pmap]
    }
    have hjF : ∀x y, G.cface x.val y.val ↔ Gj.cface x y :=
      fun _ _ => patch_j.rem_cface_iff.symm
    have h_rj : ∀i x, x.val ∈ r i ↔ x ∈ rj i := by{
      intro i x
      rw[← Drj, List.mem_map_of_injective Subtype.val_injective]
    }
    have hDr : ∀i j, i ≠ j → (r i).Disjoint (r j) := by{
      intro i j hij x hxi hxj
      have IH := (hgp.GMdisk_disjoint hij).notMem_of_mem_left
      unfold GMdisk at IH
      rw[← List.mem_reverse, ← h_r] at hxi hxj
      exact IH (Hypermap.subset_diskN hxi) (Hypermap.subset_diskN hxj)
    }
    exact ⟨{
      α := G.rDart (r j).reverse,
      G := Gj,
      h := h ∘ Subtype.val,
      r := rj,
      map_planar := propersnip_j.snipRem_planar,
      enc_injective := Injective.comp Ih Subtype.val_injective,
      enc_morph_edge := by{
        intro x
        rw[comp_apply, comp_apply]
        change h (Hypermap.properSnipRing.redge _).val = _
        unfold Hypermap.properSnipRing.redge
        simp only
        rw[hE]
      },
      enc_morph_cface := by{
        intro x y
        rw[comp_apply, comp_apply, ← hF, hjF]
      },
      enc_morph_node := by{
        intro x hiex
        rw[comp_apply, comp_apply]
        change h (Hypermap.properSnipRing.rnode _).val = _
        unfold Hypermap.properSnipRing.rnode Hypermap.snipr_node
        simp only
        rw[dif_neg (by{
          specialize hiex j (by{simp})
          simp[h_rj, hiex]
        })]
        rw[hN]
        intro i hiE'
        specialize hiex i (by{simp[hiE']})
        rwa[h_rj]
      },
      ring_def := by{
        intro i
        rw[← List.map_map, Drj i, Dr i]
      }
      ring_proper := by{
        intro i hiE'
        simp only [Finset.coe_insert, Set.mem_insert_iff, SetLike.mem_coe] at hiE'
        rcases eq_or_ne i j with hij | hij
        · {
          have ih := patch_j.rem_border_cycle
          unfold Hypermap.properSnipRing.snipRemRing at ih
          simp only [List.reverse_reverse] at ih
          have ih' : ∀ a ∈ r j, (fun x ↦ x ∉ G.diskE (r j).reverse) a := by{
            apply hrj_lemma''
          }
          have ih'' : (r j).pmap Subtype.mk ih' = rj j := by{
            apply List.map_injective_iff.mpr Subtype.val_injective
            rw[List.map_pmap, Drj]
            simp
          }
          simp only [ih''] at ih
          simpa[hij]
        }
        apply (Or.resolve_left · hij) at hiE'
        specialize cycNr _ hiE'
        constructor
        · {
          rw[← Drj, List.IsCycleChain_map] at cycNr
          apply cycNr.1.subset'
          intro x y hxrji hyrji (hxy : _ = _)
          change Hypermap.properSnipRing.rnode _ = _
          rw[← h_rj] at hxrji hyrji
          unfold Hypermap.properSnipRing.rnode
          simp only [Subtype.ext_iff, Hypermap.snipr_node]
          rwa[dif_neg]
          rw[List.mem_reverse]
          exact hDr _ _ hij hxrji
        }
        · {
          rw[← List.nodup_map_iff Subtype.val_injective, Drj]
          exact cycNr.2
        }
      }
    }⟩
  }
}



end GridMapProper
end GridPlane
