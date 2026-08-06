import FourColorTheorem.Discretize.GridHypermap.GMInner

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

section nodecard

noncomputable def GMInnerDartNode {hgp : GridMapProper ab0 cm0}
: hgp.GMInnerDart → hgp.GMInnerDart :=
  fun ⟨u, hu⟩ => ⟨GMnode u, GMnode_inner_closed hu⟩
theorem GMInnerDartNode_injective {hgp : GridMapProper ab0 cm0}
: Injective hgp.GMInnerDartNode := by{
  intro ⟨u0, hu0⟩ ⟨u1, hu1⟩ hu01
  rw[GMInnerDartNode, GMInnerDartNode, Subtype.ext_iff] at hu01
  change (GMDartHypermap hgp).node u0 = (GMDartHypermap hgp).node u1 at hu01
  simp only[hgp.GMDartHypermap.node_inj] at hu01
  simp[hu01]
}
noncomputable def GMInnerDartCNodeEquivalence {hgp : GridMapProper ab0 cm0} :=
  Finite.funReflTransGen_injective_equivalence
  (@GMInnerDartNode_injective _ _ _ hgp)
def GMInnerDartNsetoid {hgp : GridMapProper ab0 cm0} : Setoid hgp.GMInnerDart :=
  ⟨_, GMInnerDartCNodeEquivalence⟩
@[inline] noncomputable instance instDecidableGMInnerDartNsetoid {hgp : GridMapProper ab0 cm0}
: DecidableRel hgp.GMInnerDartNsetoid := by{
  apply Fintype.injective_setoid.decidable
  apply GMInnerDartNode_injective
}
theorem GMInnerDartNode_val_val_eq_en {hgp : GridMapProper ab0 cm0} {u : hgp.GMInnerDart} :
  (GMInnerDartNode u).val.val = edge (node u.val.val) := by{
    rw[← GMnode_val_of_mem_GMInner u.prop, ← Subtype.ext_iff]
    rw[GMInnerDartNode]
  }
theorem GMInnerDartNsetoid_iff_half_eq {hgp : GridMapProper ab0 cm0} {u0 u1 : hgp.GMInnerDart} :
funReflTransGen hgp.GMInnerDartNode u0 u1 ↔ u0.val.val.half = u1.val.val.half := by{
  constructor
  · {
    intro h
    induction h with
    | refl => rfl
    | tail hh ht ih => {
      rw[ih]
      rw[fromFun, Subtype.ext_iff, Subtype.ext_iff, GMInnerDartNode_val_val_eq_en] at ht
      rw[← face_inj, fen_cancel] at ht
      rw[ht, face_half]
    }
  }
  · {
    intro h
    rw[half_eq_cases_face] at h
    rcases h with h | h | h | h
    · {
      rw[Subtype.ext (Subtype.ext h)]
      apply funReflTransGen.refl
    }
    · {
      nth_rw 1 [← fen_cancel ↑↑u0, face_inj, ← GMnode_val_of_mem_GMInner u0.prop,
      ← Subtype.ext_iff] at h
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, GMInnerDartNode]
      exact h
    }
    · {
      apply ReflTransGen.head (b:=GMInnerDartNode u0)
      · rfl
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, Subtype.ext_iff, GMInnerDartNode_val_val_eq_en,
      ← face_inj, fen_cancel, GMInnerDartNode_val_val_eq_en, ← face_inj, fen_cancel, h]
    }
    · {
      rw[face_3, ← GMnode_val_of_mem_GMInner u1.prop, ← Subtype.ext_iff] at h
      apply (GMInnerDartCNodeEquivalence).symm
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, GMInnerDartNode, h]
    }
  }
}
theorem GMDartHypermapNsetoid_iff_half_eq_of_inner {hgp : GridMapProper ab0 cm0}
{u0 u1 : hgp.GMDart} (hu0 : u0 ∈ hgp.GMInner)
  (hu1 : u1 ∈ hgp.GMInner) : funReflTransGen GMnode u0 u1 ↔ u0.val.half = u1.val.half := by{
    have ih := GMInnerDartNsetoid_iff_half_eq (u0:=⟨u0, hu0⟩) (u1:=⟨u1, hu1⟩)
    rw[←ih]
    clear ih
    constructor
    · {
      intro h
      induction h with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        have hb : b ∈ hgp.GMInner := by{
          apply funReflTransGen_GMnode_inner_closed hh hu0
        }
        apply ReflTransGen.tail (b:=⟨b, hb⟩)
        · exact ih hb
        rw[fromFun] at ht
        simp only [fromFun, GMInnerDartNode, ht]
      }
    }
    · {
      intro h
      generalize hu0' : (⟨u0, hu0⟩ : hgp.GMInnerDart) = u0'
      generalize hu1' : (⟨u1, hu1⟩ : hgp.GMInnerDart) = u1'
      have hu0'v : u0'.val = u0 := by{simp[← hu0']}
      have hu1'v : u1'.val = u1 := by{simp[← hu1']}
      rw[← hu0'v, ← hu1'v]
      rw[hu0', hu1'] at h
      clear! u0 u1
      induction h with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        apply ih.tail
        rw[fromFun, Subtype.ext_iff, GMInnerDartNode] at ht
        exact ht
      }
    }
  }
theorem GMDartHypermap_inner_ncomp {hgp : GridMapProper ab0 cm0}
: Fintype.nComp hgp.GMInnerDartNsetoid = hgp.extendBBox.area := by{
  rw[← GRectangle.enum_length, ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
  apply Fintype.card_congr
  let f : Quotient hgp.GMInnerDartNsetoid → { x // x ∈ hgp.extendBBox.enum } :=
    fun q => ⟨q.out.val.val.half, by{
      have hq := q.out.prop
      rw[mem_GMInner_iff] at hq
      rw[GRectangle.mem_enum_iff]
      exact hq
    }⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro q1 q2 hq12
    unfold f at hq12
    rw[Subtype.ext_iff] at hq12
    simp only at hq12
    rw[← GMInnerDartNsetoid_iff_half_eq] at hq12
    rw[← Quotient.out_equiv_out]
    exact hq12
  }
  · {
    intro ⟨p, hp⟩
    rw[GRectangle.mem_enum_iff] at hp
    use ⟦⟨⟨2 • p, by{simp[mem_GMGrid_iff, GPoint.half_double, hp]}⟩,
      by{simp[mem_GMInner_iff, GPoint.half_double, hp]}⟩⟧
    unfold f
    rw[Subtype.ext_iff]
    simp only
    have hp' : funReflTransGen _ _ _ := Quotient.mk_out (s:=GMInnerDartNsetoid)
      ⟨⟨2 • p, by{
        rw[hgp.mem_GMGrid_iff, GPoint.half_double]
        exact Or.inl hp
      }⟩,
      by{simp[mem_GMInner_iff, GPoint.half_double, hp]}⟩
    rw[GMInnerDartNsetoid_iff_half_eq] at hp'
    rw[hp']
    simp[GPoint.half_double]
  }
}

theorem GMDartHypermap_ncomp_ge {hgp : GridMapProper ab0 cm0}
  : hgp.GMDartHypermap.ncomp ≥ hgp.extendBBox.area := by{
    rw[← GMDartHypermap_inner_ncomp]
    rw[Hypermap.ncomp, Fintype.nComp, Fintype.nComp, ge_iff_le]
    let f : Quotient hgp.GMInnerDartNsetoid → Quotient (hgp.GMDartHypermap).nsetoid :=
      fun q => ⟦q.out.val⟧
    apply Fintype.card_le_of_injective f
    intro q1 q2 hq12
    unfold f at hq12
    rw[Quotient.eq] at hq12
    rw[← Quotient.out_equiv_out]
    change funReflTransGen _ _ _
    change funReflTransGen GMnode _ _ at hq12
    match hq1 : q1.out, hq2 : q2.out with
    | ⟨u1, hu1⟩, ⟨u2, hu2⟩ => {
      simp only [hq1, hq2] at hq12
      clear! q1 q2
      induction hq12 with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        have hb : b ∈ hgp.GMInner := funReflTransGen_GMnode_inner_closed hh hu1
        specialize ih hb
        apply ReflTransGen.tail ih
        rw[fromFun] at ht
        rw[fromFun, Subtype.ext_iff, GMInnerDartNode]
        exact ht
      }
    }
  }
end nodecard


end GridMapProper
end GridPlane
