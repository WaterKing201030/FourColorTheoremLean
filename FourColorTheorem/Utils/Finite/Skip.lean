import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Finite.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Inv
import Init.Data.Nat.Lemmas
import FourColorTheorem.Utils.Relations
import FourColorTheorem.Utils.Classical
import FourColorTheorem.Utils.Finite.BijInv


open Relation
open Function

section Fintype
variable {α : Type _}
variable [DecidableEq α]
def Function.skip' (f : α → α) (x : α) : α → α:=
  fun z => if f z = x then f (f z) else f z
theorem Function.skip'_ne {f : α → α} {x y : α} (hf : Injective f) (hy : y ≠ x)
  : skip' f x y ≠ x := by{
    cases (inferInstance:DecidableEq α) (f y) x with
    | isTrue hfu => {
      unfold skip'
      simp only [ne_eq, hfu, ↓reduceIte]
      nth_grewrite 2 [←hfu]
      rw[Eq.comm, hf.eq_iff]
      exact hy
    }
    | isFalse hfu => {
      unfold skip'
      simp only [ne_eq, hfu, ↓reduceIte, not_false_eq_true]
    }
  }
theorem Function.skip'_eq_of_apply_eq {f : α → α} {x y : α} (hy : f y = x)
  : skip' f x y = f (f y) := by{simp[skip', hy]}
theorem Function.skip'_eq_of_apply_ne {f : α → α} {x y : α} (hy : f y ≠ x)
  : skip' f x y = f y := by{simp[skip', hy]}
theorem Relation.funReflTransGen_skip'_ne {f : α → α} {x y z : α}
  (hf : Injective f) (hy : y ≠ x) (hyz : funReflTransGen (skip' f x) y z) : z ≠ x:=by{
    rw[funReflTransGen_iff_iterate] at hyz
    have ⟨n, hn⟩:=hyz
    induction n generalizing z with
    | zero => simp at hn; simp[hn] at hy; simp[hy]
    | succ n' ih => {
      have ih':=@ih ((skip' f x)^[n'] y) ⟨n', rfl⟩ rfl
      rw[←hn, iterate_succ_apply']
      apply skip'_ne hf ih'
    }
  }
lemma Function.skip_proof {f : α → α} {x : α} {u : {a : α // a ≠ x}} (hf : Injective f)
  : skip' f x u.val ≠ x:=by{
    exact skip'_ne hf u.prop
  }
def Function.skip {f : α → α} (hf : Injective f) (x : α) :
  {a : α // a ≠ x} → {a : α // a ≠ x} :=
  fun u => ⟨skip' f x u.val, skip_proof hf⟩
theorem Function.skip_injective {f : α → α} (hf : Injective f) (x : α)
  :Injective (skip hf x):=by{
    intro u v huv
    unfold skip skip' at huv
    simp only [ne_eq, Subtype.mk.injEq] at huv
    cases (inferInstance:DecidableEq α) (f u) x with
    | isTrue hux => cases (inferInstance:DecidableEq α) (f v) x with
      | isTrue hvx => {
        have h:=hux.trans hvx.symm
        simp[hf.eq_iff] at h
        ext
        simp[h]
      }
      | isFalse hvx => {
        have hv:=v.prop.symm
        simp only [hux, ↓reduceIte, hvx, hf.eq_iff] at huv
        contradiction
      }
    | isFalse hux => cases (inferInstance:DecidableEq α) (f v) x with
      | isTrue hvx => {
        have hv:=u.prop
        simp only [hux, ↓reduceIte, hvx, hf.eq_iff] at huv
        contradiction
      }
      | isFalse hvx => {
        simp[hux, hvx] at huv
        simp[hf.eq_iff] at huv
        ext
        simp[huv]
      }
  }
theorem Function.skip_iff_skip' {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : skip hf x u = v ↔ skip' f x u = v:=by{
    unfold skip
    simp[Subtype.ext_iff]
  }

theorem Relation.funReflTransGen_skip_iff_skip' {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : funReflTransGen (skip hf x) u v
     ↔ funReflTransGen (skip' f x) u v:=by{
      unfold funReflTransGen
      constructor
      · exact ReflTransGen.lift Subtype.val fun _ _ => (skip_iff_skip' hf).mp
      · {
        intro h
        generalize h_u : u.val = u_val at h
        generalize h_v : v.val = v_val at h
        induction h generalizing u v with
        | refl =>
          change ReflTransGen (fromFun (skip hf x)) ⟨u.val, u.prop⟩ ⟨v.val, v.prop⟩
          simp only [h_u, h_v]
          rfl
        | @tail b c huw hwv ih => {
          have hb:b ≠ x:=by{
            apply funReflTransGen_skip'_ne hf u.prop
            rw[h_u]
            exact huw
          }
          have ih':=ih (v:=⟨b, hb⟩) h_u rfl
          apply ih'.tail
          unfold fromFun
          unfold fromFun at hwv
          rw[skip_iff_skip']
          simp[h_v, hwv]
        }
      }
  }
theorem Relation.funReflTransGen_skip {f : α → α} (hf : Injective f) {x : α}
  {u v : {a : α // a ≠ x}} : funReflTransGen (skip hf x) u v
  ↔ funReflTransGen f u v:=by{
    constructor
    · {
      unfold funReflTransGen
      intro h
      induction h with
      | refl => rfl
      | @tail c b hac hcb ih => {
        apply ih.trans
        unfold fromFun at hcb
        rw[skip_iff_skip'] at hcb
        unfold skip' at hcb
        match (inferInstance:DecidableEq α) (f c.val) x with
        | isTrue hfcx => {
          simp[hfcx] at hcb
          have hfcx':=ReflTransGen.single (r:=fromFun f) hfcx
          simp[hfcx'.tail hcb]
        }
        | isFalse hfcx => {
          simp[hfcx] at hcb
          apply ReflTransGen.single
          simp[fromFun, hcb]
        }
      }
    }
    · {
      rw[funReflTransGen_skip_iff_skip']
      intro h
      generalize hu : u.val = u_val at h
      generalize hv : v.val = v_val at h
      let inst':DecidableEq α:=inferInstance
      induction h generalizing u v with
      | refl => apply ReflTransGen.refl
      | @tail b c huw hwv ih => {
        cases inst' b x with
        | isTrue hb => {
          have huw':funReflTransGen f u_val b:=huw
          rw[funReflTransGen_iff_iterate_minimal] at huw'
          have ⟨n, hn, hn'⟩:=huw'
          unfold fromFun at hwv
          match n with
          | 0 => simp[←hu, hb, u.prop] at hn
          | n' + 1 => {
            rw[iterate_succ_apply'] at hn
            simp only [Nat.lt_succ_iff] at hn'
            apply ReflTransGen.tail (b:=f^[n'] u_val)
            · {
              have h_step : ∀ m < n', skip' f x (f^[m] u_val) = f (f^[m] u_val) := by
                intro m hm
                unfold skip'
                have h_not_x : f (f^[m] u_val) ≠ x := by
                  rw [←iterate_succ_apply' f m]
                  exact hb ▸ hn' m.succ (Nat.succ_le_of_lt hm)
                simp [h_not_x]
              have h_step'':∀m ≤ n', ReflTransGen (fromFun (skip' f x)) u_val (f^[m] u_val):=by{
                intro m hmn
                induction m with
                | zero => rfl
                | succ m' ihm => {
                  apply ReflTransGen.tail (b:=f^[m'] u_val)
                  · {
                    apply ihm
                    exact Nat.le_of_succ_le hmn
                  }
                  · {
                    unfold fromFun
                    rw[h_step _ (Nat.lt_of_succ_le hmn), iterate_succ_apply']
                  }
                }
              }
              exact h_step'' n' (by rfl)
            }
            · {
              unfold fromFun skip'
              simp[hn, hb]
              simp[←hb, hwv]
            }
          }
        }
        | isFalse hb => {
          have ih':=ih (v:=⟨b, hb⟩) hu rfl
          apply ih'.tail
          unfold skip'
          unfold fromFun at hwv
          simp[hwv, ←hv, v.prop]
        }
      }
    }
  }
theorem Function.skip_eq_of_apply_ne {f : α → α} {x : α} (hf : Injective f) {u : {a // a ≠ x}}
  (hu : f u ≠ x) : skip hf x u = ⟨f u, hu⟩ := by{
    unfold skip
    simp only [ne_eq, Subtype.mk.injEq]
    exact skip'_eq_of_apply_ne hu
  }
theorem Function.skip_eq_of_apply_eq {f : α → α} {x : α} (hf : Injective f) {u : {a // a ≠ x}}
  (hu : f u = x) : skip hf x u = ⟨f (f u), by{
    rw[hu]
    intro hn
    have hn':=hu.trans hn.symm
    rw[hf.eq_iff] at hn'
    exact u.prop hn'
  }⟩ := by{
    unfold skip
    simp only [ne_eq, Subtype.mk.injEq]
    exact skip'_eq_of_apply_eq hu
  }
theorem Function.skip_eq_of_eq {f : α → α} {x : α} (hf : Injective f)
  {u v : {a // a ≠ x}} (huv : f u = v) : skip hf x u = v:=by{
    have huv':=huv ▸ v.prop
    have huv'':=skip_eq_of_apply_ne hf huv'
    rw[huv'']
    simp[huv]
  }
theorem Function.skip_val {f : α → α} {x : α} (hf : Injective f)
  {u : {a // a ≠ x}} : (skip hf x u).val = skip' f x u:=by{
    unfold skip
    rfl
  }
variable [Fintype α]
theorem Finite.skip_bijective {α : Type _} [Finite α] [DecidableEq α] {f : α → α}
  (hf : Injective f) (x : α) : Bijective (skip hf x) :=
  let :Finite α:=inferInstance
  (skip_injective hf x).bijective_of_finite
def Fintype.skip_setoid {f : α → α} (hf : Injective f) (x : α)
  : Setoid {a // a ≠ x} :=
  Setoid.mk (funReflTransGen (skip hf x))
  (Finite.funReflTransGen_injective_equivalence (skip_injective hf x))
@[inline] instance Fintype.skip_setoid.finDec {f : α → α} (hf : Injective f) {x : α}
  : DecidableRel (skip_setoid hf x) :=
  fun _ _ => by{
    unfold skip_setoid
    apply funReflTransGen.finDec
  }
theorem Fintype.nComp_skip_setoid {f : α → α} {hf : Injective f} {x : α}
  : nComp (skip_setoid hf x) + (if f x = x then 1 else 0) = nComp (injective_setoid hf):= by{
    cases (inferInstance:DecidableEq α) (f x) x with
    | isTrue hx => {
      unfold nComp
      simp only [ne_eq, hx, ↓reduceIte]
      have e:Quotient (skip_setoid hf x) ⊕ Unit ≃ Quotient (injective_setoid hf):=by{
        have toFun_proof:∀ (a b : { a // a ≠ x }), (skip_setoid hf x) a b →
        (Quotient.mk (injective_setoid hf) ∘ Subtype.val) a =
        (Quotient.mk (injective_setoid hf) ∘ Subtype.val) b:=by{
          intro ⟨a, ha⟩ ⟨b, hb⟩ hab
          unfold skip_setoid at hab
          simp only [ne_eq, funReflTransGen_skip] at hab
          simp only [ne_eq, comp_apply, Quotient.eq_iff_equiv]
          exact hab
        }
        let toFun:Quotient (skip_setoid hf x) ⊕ Unit → Quotient (injective_setoid hf):=
          fun q => match q with
            | Sum.inl q' => Quotient.lift (Quotient.mk (injective_setoid hf) ∘ Subtype.val)
              toFun_proof q'
            | Sum.inr q' => Quotient.mk (injective_setoid hf) x
        have invFun_proof:∀ (a b : α), (injective_setoid hf) a b →
        (fun a ↦ if ha : a = x then Sum.inr () else Sum.inl ⟦Subtype.mk a ha⟧) a =
        (fun a ↦ if ha : a = x then Sum.inr () else Sum.inl ⟦(⟨a, ha⟩:{a // a ≠ x})⟧) b:=by{
          intro a b hab
          simp only [ne_eq, apply_dite, dite_eq_left_iff, reduceCtorEq, imp_false,
            Decidable.not_not]
          unfold injective_setoid at hab
          simp only at hab
          cases em (b = x) with
          | inl hbx => {
            simp[hbx]
            have hab':=funReflTransGen_symm_of_injective hf hab
            rw[hbx, funReflTransGen_idemp hx] at hab'
            simp[hab']
          }
          | inr hbx => {
            have hax:a ≠ x:=by{
              intro ha
              simp[ha, funReflTransGen_idemp hx] at hab
              simp[hab] at hbx
            }
            simp only [hax, ↓reduceDIte, Sum.inl.injEq, dite_then_false]
            simp only [Quotient.eq_iff_equiv, hbx, not_false_eq_true, exists_true_left]
            change (skip_setoid hf x) ⟨a, hax⟩ ⟨b, hbx⟩
            unfold skip_setoid
            simp[funReflTransGen_skip, hab]
          }
        }
        let invFun:Quotient (injective_setoid hf) → Quotient (skip_setoid hf x) ⊕ Unit:=
          Quotient.lift (fun a => if ha:a = x then Sum.inr () else
            Sum.inl (Quotient.mk (skip_setoid hf x) ⟨a, ha⟩)) invFun_proof
        have left_inv:LeftInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          match q with
          | Sum.inl q' => {
            simp only [ne_eq]
            rw[←Quotient.out_eq q', Quotient.lift_mk]
            simp[q'.out.prop]
          }
          | Sum.inr q' => simp
        }
        have right_inv:RightInverse invFun toFun:=by{
          intro q
          rw[←Quotient.out_eq q]
          unfold toFun invFun
          rw[Quotient.lift_mk]
          cases em (q.out = x) with
          | inl hqx | inr hqx => simp[hqx]
        }
        exact ⟨toFun, invFun, left_inv, right_inv⟩
      }
      have he:=ofEquiv_card e
      simp only [ne_eq, card_sum, card_unique] at he
      rw[Eq.comm] at he
      apply (Eq.mp · he)
      congr
      apply Subsingleton.elim
    }
    | isFalse hx => {
      simp only [ne_eq, hx, ↓reduceIte, add_zero]
      unfold nComp
      simp only
      have e:Quotient (skip_setoid hf x) ≃ Quotient (injective_setoid hf):=by{
        have toFun_proof:∀ (a b : { a // a ≠ x }), (skip_setoid hf x) a b →
          (Quotient.mk (injective_setoid hf) ∘ Subtype.val) a =
          (Quotient.mk (injective_setoid hf) ∘ Subtype.val) b :=by{
            intro a b hab
            unfold skip_setoid at hab
            simp only [ne_eq] at hab
            rw[funReflTransGen_skip] at hab
            simp only [ne_eq, comp_apply]
            rw[Quotient.eq_iff_equiv]
            exact hab
        }
        let toFun:Quotient (skip_setoid hf x) → Quotient (injective_setoid hf):=
          Quotient.lift (Quotient.mk (injective_setoid hf) ∘ Subtype.val) toFun_proof
        have invFun_proof:∀ (a b : α), (injective_setoid hf) a b →
        (Quotient.mk (skip_setoid hf x) ∘ fun a ↦ if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩) a =
        (Quotient.mk (skip_setoid hf x) ∘ fun a ↦ if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩) b:=by{
          intro a b hab
          unfold injective_setoid at hab
          simp only at hab
          simp only [ne_eq, comp_apply]
          rw[Quotient.eq_iff_equiv]
          change (skip_setoid hf x) (if ha : a = x then ⟨f x, hx⟩ else ⟨a, ha⟩)
            (if hb : b = x then ⟨f x, hx⟩ else ⟨b, hb⟩)
          unfold skip_setoid
          simp only [ne_eq]
          rw[funReflTransGen_skip]
          simp only [ne_eq, apply_dite, dite_eq_ite]
          rw[apply_ite (funReflTransGen f _)]
          simp only [apply_ite (funReflTransGen f), ite_apply]
          unfold funReflTransGen
          simp only [ReflTransGen.refl, if_true_left]
          unfold funReflTransGen at hab
          simp only [hab, if_true_right]
          cases em (b = x) with
          | inl hbx => {
            simp only [hbx, ↓reduceIte]
            simp only [← hbx]
            intro _
            apply ReflTransGen.tail hab
            rfl
          }
          | inr hbx => {
            simp only [hbx, ↓reduceIte]
            intro hax
            simp only [← hax]
            apply (ReflTransGen.trans · hab)
            apply (Finite.funReflTransGen_injective_equivalence hf).symm
            apply ReflTransGen.single
            rfl
          }
        }
        let invFun:Quotient (injective_setoid hf) → Quotient (skip_setoid hf x):=
          Quotient.lift (Quotient.mk (skip_setoid hf x) ∘
          (fun a => if ha:a = x then ⟨f x, hx⟩ else ⟨a, ha⟩)) invFun_proof
        have left_inv:LeftInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          rw[←Quotient.out_eq q]
          rw[Quotient.lift_mk]
          simp only [ne_eq, comp_apply, Quotient.lift_mk, Subtype.coe_eta, dite_eq_ite,
            Quotient.out_eq]
          rw[Eq.comm, ←Quotient.out_eq q]
          rw[Quotient.eq_iff_equiv]
          simp only [ne_eq, Quotient.out_eq, apply_ite, Setoid.refl, if_true_right]
          intro h
          change (skip_setoid hf x) q.out ⟨f x, hx⟩
          unfold skip_setoid
          simp only [ne_eq, funReflTransGen_skip]
          apply ReflTransGen.single
          exact h.symm ▸ rfl
        }
        have right_inv:RightInverse invFun toFun:=by{
          intro q
          unfold invFun toFun
          rw[←Quotient.out_eq q]
          rw[Quotient.lift_mk]
          simp only [ne_eq, comp_apply, Quotient.lift_mk, Quotient.out_eq]
          rw[Eq.comm, ←Quotient.out_eq q]
          rw[Quotient.eq_iff_equiv]
          rw[apply_dite Subtype.val]
          simp only [Quotient.out_eq, dite_eq_ite]
          simp only [apply_ite, Setoid.refl, if_true_right]
          intro h
          apply ReflTransGen.single
          exact h ▸ rfl
        }
        let e': Quotient (skip_setoid hf x) ≃ Quotient (injective_setoid hf) :={
          toFun:=toFun,
          invFun:=invFun,
          left_inv:=left_inv,
          right_inv:=right_inv
        }
        exact e'
      }
      have he:=ofEquiv_card e.symm
      apply (Eq.mp · he)
      congr
      apply Subsingleton.elim
    }
  }
theorem Fintype.bijInv_eq_iff_eq_apply {f : α → α} (hf : Bijective f) (x y : α)
  : bijInv hf x = y ↔ x = f y := by{
    nth_rw 1 [←hf.injective.eq_iff]
    rw[rightInverse_bijInv hf]
  }
theorem Fintype.eq_bijInv_iff_apply_eq {f : α → α} (hf : Bijective f) (x y : α)
  : x = bijInv hf y ↔ f x = y := by{
    rw[Eq.comm (a:=x), Eq.comm (b:=y)]
    exact bijInv_eq_iff_eq_apply hf y x
  }
theorem Fintype.skip_bijInv_comm {f : α → α} (hf : Bijective f) {x : α}
  : skip (bijective_bijInv hf).injective x = bijInv (Finite.skip_bijective hf.injective x) := by{
    apply funext
    intro u
    rw[eq_bijInv_iff_apply_eq]
    ext
    rw[skip_val, skip_val]
    unfold skip'
    simp only[bijInv_eq_iff_eq_apply]
    rw[apply_ite f]
    rw[rightInverse_bijInv hf]
    rw[rightInverse_bijInv hf]
    rw[apply_ite f]
    rw[rightInverse_bijInv hf]
    simp only [apply_ite (· = x), u.prop]
    simp only [ne_eq, if_false_right]
    cases em (u = f x) with
    | inl hux => {
      simp[hux]
      simp[leftInverse_bijInv hf x]
    }
    | inr hux => simp[hux]
  }
end Fintype
