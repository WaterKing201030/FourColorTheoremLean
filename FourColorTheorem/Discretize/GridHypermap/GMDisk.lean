import FourColorTheorem.Discretize.GridHypermap.GMRing
import FourColorTheorem.Hypermap.Actions.Snip

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

noncomputable def GMdisk (hgp : GridMapProper ab0 cm0) (i : Fin n) : Set hgp.GMDart :=
  hgp.GMDartHypermap.diskN (hgp.GMring i)
theorem GMRing_subset_GMDisk {hgp : GridMapProper ab0 cm0} {i : Fin n}
{d : hgp.GMDart} (hd : d ∈ hgp.GMring i) : d ∈ hgp.GMdisk i := by{
  apply Hypermap.subset_diskN
  exact hd
}
theorem GMdisk_def {hgp : GridMapProper ab0 cm0} {i : Fin n}
: hgp.GMdisk i ⊆ {d | d.val.half ∈ hgp.extendCMatte i} := by{
  intro u ⟨nv, ri_nv, h⟩
  rw[Set.mem_setOf]
  rw[Hypermap.dconnect, ReflTransGen_iff_isChain_option] at h
  have ⟨s', vDs, shh, shl⟩:=h
  clear h
  match s' with
  | [] => simp at shh
  | v::s => {
    clear s'
    simp only [List.head?_cons, Option.some.injEq] at shh
    rw[List.getLast?_eq_some_getLast (by{simp}), Option.some_inj] at shl
    rw[← shl]
    clear! u
    have mi_u : v.val.half ∈ hgp.extendCMatte i := by{
      rw[shh, hgp.GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner (by{
        exact GMring_subset_GMInner ri_nv
      }), face_half]
      rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border] at ri_nv
      exact ri_nv.left
    }
    clear! nv
    generalize hvu : v = u
    simp only[hvu] at *
    clear hvu v
    revert vDs; intro uDs
    induction s generalizing u with
    | nil => simp[mi_u]
    | cons v s IHs => {
      rw[List.getLast_cons_cons]
      rw[List.isChain_cons_cons] at uDs
      have ⟨⟨r'u, uCv⟩, vDs⟩:=uDs
      clear uDs
      apply IHs
      · {
        clear IHs
        unfold Hypermap.clink at uCv
        simp only [union_iff, fromFun] at uCv
        rcases uCv with Du | Du
        · {
          rw[← Du, GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner, face_half]
          · exact mi_u
          rw[mem_GMInner_iff]
          apply CM_subset_CMBBox mi_u
        }
        rw[← Du]
        clear Du
        rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border, border,
        Set.mem_setOf, not_and, not_not] at r'u
        specialize r'u mi_u
        rw[← fen_cancel (Subtype.val _), face_half,
          ← GMDartHypermap_node_val_eq_en_of_mem_GMInner]
        · {
          rw[← comp_apply (f:= hgp.GMDartHypermap.node), ← Hypermap.edgeinv_eq,
          Hypermap.Plain.edgeinv_eq_edge GMDartHypermap_plain, GMDartHypermap_edge_val_eq]
          exact r'u
        }
        · {
          rw[
            funReflTransGen_GMnode_inner_closed_iff
              (funReflTransGen.single GMnode (hgp.GMDartHypermap.face u))
          ]
          change hgp.GMDartHypermap.node _ ∈ _
          rw[← comp_apply (f:=hgp.GMDartHypermap.node), ← Hypermap.edgeinv_eq,
          Hypermap.Plain.edgeinv_eq_edge GMDartHypermap_plain, mem_GMInner_iff,
          GMDartHypermap_edge_val_eq]
          exact CM_subset_CMBBox r'u
        }
      }
      · exact vDs
    }
  }
}
theorem GMdisk_disjoint {hgp : GridMapProper ab0 cm0} {i j : Fin n} (hij : i ≠ j)
: Disjoint (hgp.GMdisk i) (hgp.GMdisk j) := by{
  rw[Set.disjoint_iff_forall_ne]
  intro x hxi y hxj hxy
  rw[hxy.symm] at hxj
  clear! y
  have hxi' := GMdisk_def hxi
  have hxj' := GMdisk_def hxj
  rw[Set.mem_setOf] at hxi' hxj'
  have h := hgp.extendCMatte_proper i j ⟨x.val.half, hxi', hxj'⟩
  exact hij h
}

end GridMapProper
end GridPlane
