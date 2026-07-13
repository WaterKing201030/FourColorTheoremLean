import FourColorTheorem.Utils.Relations.Basic
import FourColorTheorem.Utils.Relations.Chain
import Mathlib.Order.BooleanAlgebra.Basic

open Relation
open Function

variable {α : Type _} {β : Type _}

def Relation.Closure (e : α → α → Prop) (D : Set α)
  := ∀x ∈ D, ∀y, ReflTransGen e x y → y ∈ D

theorem Relation.compl_closure_of_equivalence {e : α → α → Prop} {D : Set α}
  (he : Equivalence e) : Closure e Dᶜ ↔ Closure e D := by{
  suffices H : ∀e (D : Set α), Equivalence e → (Closure e D → Closure e Dᶜ)
    by{
      constructor
      · {
        nth_rw 2 [← compl_compl D]
        apply H; exact he
      }
      · apply H; exact he
    }
  intro e D he heD
  unfold Closure at *
  simp only [Set.mem_compl_iff]
  intro x hxD y hxy hyD
  have he' := (ReflTransGen_equivalence_of_symm he.symm).symm hxy
  have heD':=heD _ hyD x he'
  exact hxD heD'
}
theorem Relation.compl_closure_of_equivalence' {e : α → α → Prop} {D : Set α}
  (he : Equivalence (ReflTransGen e)) : Closure e Dᶜ ↔ Closure e D := by{
  suffices H : ∀e (D : Set α), Equivalence (ReflTransGen e) → (Closure e D → Closure e Dᶜ)
    by{
      constructor
      · {
        nth_rw 2 [← compl_compl D]
        apply H; exact he
      }
      · apply H; exact he
    }
  intro e D he heD
  unfold Closure at *
  simp only [Set.mem_compl_iff]
  intro x hxD y hxy hyD
  have he' := he.symm hxy
  have heD':=heD _ hyD x he'
  exact hxD heD'
}
theorem Relation.closure_iff_single {e : α → α → Prop} {D : Set α}
  : Closure e D ↔ ∀x ∈ D, ∀y, e x y → y ∈ D := by{
    unfold Closure
    constructor
    · {
      intro ih x hx _ hxy
      exact ih _ hx _ (ReflTransGen.single hxy)
    }
    · {
      intro IH x hx y hxy
      induction hxy with
      | refl => exact hx
      | tail hh ht ih => exact IH _ ih _ ht
    }
  }
@[simp] theorem Relation.closure_empty {e : α → α → Prop} : Closure e ∅ := by{
  unfold Closure
  simp
}
@[simp] theorem Relation.closure_univ {e : α → α → Prop} : Closure e Set.univ := by{
  unfold Closure
  simp
}
theorem Relation.closure_union {e : α → α → Prop} {D1 D2 : Set α} (eClo1 : Closure e D1)
  (eClo2 : Closure e D2) : Closure e (D1 ∪ D2) := by{
    intro x hx y hxy
    rcases hx with hx | hx
    · left; exact eClo1 _ hx _ hxy
    · right; exact eClo2 _ hx _ hxy
  }
theorem Relation.reflTransGen_closure_iff {e : α → α → Prop} {D : Set α}
  : Closure (ReflTransGen e) D ↔ Closure e D := by{
    unfold Closure
    simp only [reflTransGen_idem]
  }
abbrev Relation.ClosureBorder (r : α → α → Prop) (D : Set α) : Set α :=
  {x | (∃y ∈ D, ReflTransGen r y x) ∧ (∃y ∈ Dᶜ, ReflTransGen r y x)}

theorem Relation.closure_iff_border_empty {r : α → α → Prop} {D : Set α} (rEquiv : Equivalence r)
  : Closure r D ↔ ClosureBorder r D = ∅ := by{
    simp only [Set.mem_compl_iff, Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_and,
      not_exists, forall_exists_index, and_imp]
    unfold Closure
    constructor
    · {
      intro IH x y hy hyx z hz hzx
      apply hz
      apply IH _ ?_ _ ((ReflTransGen_Symm_of_Symm ⟨fun _ _ => rEquiv.symm⟩).symm _ _ hzx)
      apply IH _ hy _ hyx
    }
    · {
      intro IH x hx y hxy
      specialize IH y x hx hxy y
      rw[not_imp_not] at IH
      exact IH (by rfl)
    }
  }

structure Relation.AdjunctionOn
  (f : β → α) (e : α → α → Prop) (e' : β → β → Prop) (D : Set α) : Prop where
  unit : ∀x ∈ D, ∃x', ReflTransGen e x (f x')
  functor : ∀x' y', f x' ∈ D → (ReflTransGen e' x' y' ↔ ReflTransGen e (f x') (f y'))
  closure : Closure e D
  symm_e : Std.Symm (ReflTransGen e)
  symm_e' : Std.Symm (ReflTransGen e')

def Relation.Adjunction (f : β → α) (e : α → α → Prop) (e' : β → β → Prop) : Prop :=
  AdjunctionOn f e e' Set.univ

theorem Relation.AdjunctionOn.intro
  {h : β → α} {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (eClo : ∀ x ∈ D, ∀ y, ReflTransGen e x y → y ∈ D)
  (eSymm : Std.Symm (ReflTransGen e)) (e'Symm : Std.Symm (ReflTransGen e'))
  (h' : ∀ x, x ∈ D → β)
  (h0 : ∀ x a_x, ReflTransGen e x (h (h' x a_x)) ∧
  ∀ y a_y, e x y → ReflTransGen e' (h' x a_x) (h' y a_y))
  (h1 : ∀ x' a_x, ReflTransGen e' x' (h' (h x') a_x) ∧
  ∀ y', e' x' y' → ReflTransGen e (h x') (h y'))
  : AdjunctionOn h e e' D := by{
    apply AdjunctionOn.mk
    · {
      intro x hxd
      specialize h0 x hxd
      refine ⟨h' x hxd, h0.left⟩
    }
    · {
      intro x' y' hx'D
      have ⟨h1x', h1x'r⟩ := h1 x' hx'D
      constructor
      · {
        intro h
        induction h with
        | refl => rfl
        | tail hh ht ih => {
          apply ih.trans
          apply (h1 _ (eClo _ hx'D _ ih)).right
          exact ht
        }
      }
      intro he
      have ⟨h0x', h0x'r⟩ := h0 _ hx'D
      have hy'D := eClo _ hx'D _ he
      have ih : ∀y, (hyD : y ∈ D) → ∀z, (Dz : z ∈ D) → ReflTransGen e z y
        → ReflTransGen e' (h' z Dz) (h' y hyD) := by{
        intro y hyD z Dz hzy
        induction hzy with
        | refl => rfl
        | tail hh ht ih => {
          have hbD := eClo _ Dz _ hh
          specialize ih hbD
          apply ih.trans
          apply (h0 _ hbD).right
          exact ht
        }
      }
      have ih' := ih _ hy'D _ hx'D he
      have h1y':=(h1 _ hy'D).left
      exact h1x'.trans (ih'.trans (e'Symm.symm _ _ h1y'))
    }
    · exact eClo
    · exact eSymm
    · exact e'Symm
  }

theorem Relation.adjunctionOn_of_strict {f : β → α} {e : α → α → Prop} {e' : β → β → Prop}
{D : Set α} (eClo : Closure e D)
(eSymm : Std.Symm (ReflTransGen e)) (e'Symm : Std.Symm (ReflTransGen e'))
(fInj : Injective f) (fCod : ∀ y ∈ D, ∃ x, f x = y)
(hbase : ∀ x y, f x ∈ D → (e' x y ↔ e (f x) (f y))) : AdjunctionOn f e e' D := by{
  let f' : ∀ x, x ∈ D → β := fun _ hx => Classical.choose (fCod _ hx)
  have hf'f : ∀x, (Dx : x ∈ D) → f (f' x Dx) = x := by{
    intro x Dx
    unfold f'
    exact Classical.choose_spec (fCod _ Dx)
  }
  have hff': ∀x, (Dx : f x ∈ D) → f' (f x) Dx = x := by{
    intro x Dx
    unfold f'
    have h0 := Classical.choose_spec (fCod _ Dx)
    exact fInj h0
  }
  apply AdjunctionOn.intro eClo eSymm e'Symm f'
  · {
    intro x hxD
    simp only [hf'f]
    apply And.intro (by rfl)
    intro y hyD hxy
    apply ReflTransGen.single
    rw[hbase _ _ ?_]
    · simp[hf'f, hxy]
    · simp[hf'f, hxD]
  }
  · {
    intro x hxD
    simp only [hff']
    apply And.intro (by rfl)
    intro y hxy
    apply ReflTransGen.single
    rw[← hbase _ _ hxD]
    · exact hxy
  }
}

theorem Relation.adjunctionOn_reflTransGen_left_iff
  {h : β → α} {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} : AdjunctionOn h (ReflTransGen e) e' D ↔ AdjunctionOn h e e' D
  := by{
    constructor
    · {
      intro h
      apply AdjunctionOn.mk
      · have h' := h.unit; simp only [reflTransGen_idem] at h'; exact h'
      · have h' := h.functor; simp only [reflTransGen_idem] at h'; exact h'
      · have h' := h.closure; unfold Closure at h'; simp only [reflTransGen_idem] at h'; exact h'
      · have h' := h.symm_e; simp only [reflTransGen_idem] at h'; exact h'
      · have h' := h.symm_e'; exact h'
    }
    · {
      intro h
      apply AdjunctionOn.mk
      · have h' := h.unit; simp only [reflTransGen_idem]; exact h'
      · have h' := h.functor; simp only [reflTransGen_idem]; exact h'
      · have h' := h.closure; unfold Closure; simp only [reflTransGen_idem]; exact h'
      · have h' := h.symm_e; simp only [reflTransGen_idem]; exact h'
      · have h' := h.symm_e'; exact h'
    }
  }
theorem Relation.adjunctionOn_reflTransGen_right_iff
  {h : β → α} {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} : AdjunctionOn h e (ReflTransGen e') D ↔ AdjunctionOn h e e' D
  := by{
    constructor
    · {
      intro h
      apply AdjunctionOn.mk
      · have h' := h.unit; exact h'
      · have h' := h.functor; simp only [reflTransGen_idem] at h'; exact h'
      · have h' := h.closure; exact h'
      · have h' := h.symm_e; exact h'
      · have h' := h.symm_e'; simp only [reflTransGen_idem] at h'; exact h'
    }
    · {
      intro h
      apply AdjunctionOn.mk
      · have h' := h.unit; exact h'
      · have h' := h.functor; simp only [reflTransGen_idem]; exact h'
      · have h' := h.closure; exact h'
      · have h' := h.symm_e; exact h'
      · have h' := h.symm_e'; simp only [reflTransGen_idem]; exact h'
    }
  }

theorem Relation.AdjunctionOn.closure' {h : β → α} {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D) :
  ∀x, h x ∈ D → ∀y, ReflTransGen e' x y → h y ∈ D := by{
    intro x hx y hxy
    apply A.closure _ hx (h y)
    exact (A.functor _ y hx).mp hxy
  }
instance Relation.AdjunctionOn.equivalence_reflTransGen_e {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D) : Equivalence (ReflTransGen e) where
  refl := fun _ => ReflTransGen.refl
  trans := ReflTransGen.trans
  symm := fun {_ _} => A.symm_e.symm _ _
instance Relation.AdjunctionOn.equivalence_reflTransGen_e' {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D) : Equivalence (ReflTransGen e') where
  refl := fun _ => ReflTransGen.refl
  trans := ReflTransGen.trans
  symm := fun {_ _} => A.symm_e'.symm _ _
abbrev Relation.AdjunctionOn.subtype_setoid_e {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D) : Setoid {x // x ∈ D} :=
  Setoid.mk _ A.equivalence_reflTransGen_e.ofSubtype
abbrev Relation.AdjunctionOn.subtype_setoid_e' {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D) : Setoid {x // h x ∈ D} :=
  Setoid.mk _ A.equivalence_reflTransGen_e'.ofSubtype
def Relation.AdjunctionOn.subtype_quotient {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D)
  := Quotient A.subtype_setoid_e
def Relation.AdjunctionOn.subtype_quotient' {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D)
  := Quotient A.subtype_setoid_e'
noncomputable def Relation.AdjunctionOn.subtype_quotient_equiv {h : β → α}
  {e : α → α → Prop} {e' : β → β → Prop}
  {D : Set α} (A : AdjunctionOn h e e' D)
  : A.subtype_quotient ≃ A.subtype_quotient' := by{
    symm
    let f : A.subtype_quotient' → A.subtype_quotient :=
      fun q => ⟦⟨h q.out.val, q.out.prop⟩⟧
    apply Equiv.ofBijective f
    constructor
    · {
      intro qx qy hqxy
      rw[← Quotient.out_eq qx, ← Quotient.out_eq qy]
      apply Quotient.eq.mpr
      change ReflTransGen e' _ _
      unfold f at hqxy
      apply Quotient.eq.mp at hqxy
      change ReflTransGen e _ _ at hqxy
      simp only at hqxy
      have ih := A.functor qx.out.val qy.out.val qx.out.prop
      exact ih.mpr hqxy
    }
    · {
      intro qy
      have ⟨x, hx⟩ := A.unit qy.out.val qy.out.prop
      have hx' := A.closure _ qy.out.prop _ hx
      use ⟦⟨x, hx'⟩⟧
      unfold f
      apply Quotient.mk_eq_iff_out.mpr
      change ReflTransGen e _ _
      simp only
      apply A.symm_e.symm at hx
      apply ReflTransGen.trans ?_ hx
      rw[← A.functor _ _ (Quotient.mk A.subtype_setoid_e' ⟨x, hx'⟩).out.prop]
      change A.subtype_setoid_e' _ ⟨x, hx'⟩
      apply Quotient.eq.mp
      rw[Quotient.out_eq]
    }
  }
theorem Relation.adjunctionOn_refl {e : α → α → Prop} {D : Set α}
  (eClo : Closure e D) (eSymm : Std.Symm (ReflTransGen e)) :
  AdjunctionOn id e e D where
  unit := by{
    intro x hx
    use x
    simp; rfl
  }
  functor := by{simp}
  closure := eClo
  symm_e := eSymm
  symm_e' := eSymm

def Relation.LiftOn (r : α → α → Prop) (D : Set α) : {x // x ∈ D} → {x // x ∈ D} → Prop :=
  fun x y => r x.val y.val
@[inline] instance Relation.instDecidableLiftOn {r : α → α → Prop} [DecidableRel r] {D : Set α} :
  DecidableRel (LiftOn r D) := by{
    intro x y
    unfold LiftOn
    infer_instance
  }
theorem Relation.LiftOn_Symm_of_Symm {e : α → α → Prop} {D : Set α} (eSymm : Std.Symm e)
  : Std.Symm (LiftOn e D) := ⟨by{
    intro x y hxy
    unfold LiftOn at *
    exact eSymm.symm _ _ hxy
  }⟩
theorem Relation.LiftOn_equivalence_of_equivalence {e : α → α → Prop} (D : Set α)
  (eEquiv : Equivalence e) : Equivalence (LiftOn e D) where
  refl := by{
    intro x
    unfold LiftOn
    apply eEquiv.refl
  }
  symm := by{
    intro x y hxy
    unfold LiftOn at *
    exact eEquiv.symm hxy
  }
  trans := by{
    intro x y z hxy hyz
    unfold LiftOn at *
    exact eEquiv.trans hxy hyz
  }
@[inline] instance Relation.instDecidableLiftOnSetoid {r : Setoid α} [DecidableRel r] {D : Set α} :
  DecidableRel (⟨_, LiftOn_equivalence_of_equivalence D r.iseqv⟩ : Setoid {x // x ∈ D}) := by{
    intro x y
    unfold LiftOn
    infer_instance
  }
theorem Relation.ReflTransGen_LiftOn_iff_isChain_option
  {e : α → α → Prop} {D : Set α} {x y : {x // x ∈ D}}
  : ReflTransGen (LiftOn e D) x y ↔
  ∃p : List α, p.IsChain e ∧ p.head? = some x.val ∧ p.getLast? = some y.val
  ∧ (∀x ∈ p, x ∈ D) := by{
    rw[ReflTransGen_iff_isChain_option]
    constructor
    · {
      intro ⟨l, hl0, hl1, hl2⟩
      use l.map Subtype.val
      rw[List.head?_map, List.getLast?_map, hl1, hl2, Option.map_some, Option.map_some]
      simp only [true_and]
      constructor
      · {
        apply List.isChain_map_of_isChain _ ?_ hl0
        unfold LiftOn
        simp
      }
      intro x hx
      rw[List.mem_map] at hx
      have ⟨x', hx'0, hx'1⟩:=hx
      exact hx'1 ▸ x'.prop
    }
    · {
      intro ⟨p, hp0, hp1, hp2, hp3⟩
      use List.pmap (P := (· ∈ D)) (f := fun x (hx : x ∈ D) => (⟨x, hx⟩ : {x // x ∈ D})) p hp3
      simp only [List.head?_pmap, List.head?_attach, hp1, Option.pbind_some, Option.map_some,
        Subtype.coe_eta, List.getLast?_pmap, List.getLast?_attach, hp2,
        and_true]
      apply List.isChain_pmap_of_isChain ?_ hp0 hp3
      intro a b ha hb hab
      unfold LiftOn
      simp[hab]
    }
  }
theorem Relation.ReflTransGen_LiftOn_of {e : α → α → Prop} {D : Set α} {x y : {x // x ∈ D}}
  (hxy : ReflTransGen (LiftOn e D) x y) : ReflTransGen e x.val y.val := by{
    induction hxy with
    | refl => rfl
    | tail hh ht ih => {
      apply ih.tail
      simp only [LiftOn] at ht
      exact ht
    }
  }
theorem Relation.adjunctionOn_liftOn_of_Symm {e : α → α → Prop} {D : Set α}
  (eClo : Closure e D) (eSymm : Std.Symm e)
  : AdjunctionOn Subtype.val e (LiftOn e D) D := by{
    apply adjunctionOn_of_strict
    · exact eClo
    · {
      apply ReflTransGen_Symm_of_Symm
      exact eSymm
    }
    · {
      apply ReflTransGen_Symm_of_Symm
      apply LiftOn_Symm_of_Symm
      exact eSymm
    }
    · exact Subtype.val_injective
    · exact fun y hy => ⟨⟨y, hy⟩, rfl⟩
    intro x y hx
    simp[LiftOn]
  }
