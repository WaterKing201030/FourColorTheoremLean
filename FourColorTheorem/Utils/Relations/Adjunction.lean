import FourColorTheorem.Utils.Relations.Basic
import FourColorTheorem.Utils.Relations.Chain

open Relation
open Function

variable {α : Type _} {β : Type _}

def Relation.Closure (e : α → α → Prop) (D : Set α)
  := ∀x ∈ D, ∀y, ReflTransGen e x y → y ∈ D

structure Relation.AdjunctionOn
  (f : β → α) (e : α → α → Prop) (e' : β → β → Prop) (D : Set α) : Prop where
  unit : ∀x ∈ D, ∃x', ReflTransGen e x (f x')
  functor : ∀x' y', f x' ∈ D → (ReflTransGen e' x' y' ↔ ReflTransGen e (f x') (f y'))
  closure : ∀x ∈ D, ∀y, ReflTransGen e x y → y ∈ D
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
{D : Set α} (eClo : ∀ x ∈ D, ∀ y, ReflTransGen e x y → y ∈ D)
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
