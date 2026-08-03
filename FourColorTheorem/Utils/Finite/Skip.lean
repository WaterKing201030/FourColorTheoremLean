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
theorem Function.skip_iterate_of_not_funReflTransGen {f : α → α} {x : α} (hf : Injective f)
  {u : {a // a ≠ x}} (hux : ¬funReflTransGen f u x) (n : ℕ)
  : (skip hf x)^[n] u = f^[n] u := by{
    induction n generalizing u with
    | zero => simp
    | succ n' ih => {
      rw[iterate_succ_apply, iterate_succ_apply, skip_eq_of_apply_ne hf (by{
        contrapose hux
        nth_rw 2 [← hux]
        apply funReflTransGen.single
      })]
      apply ih
      simp only
      contrapose hux
      rw[funReflTransGen_iff_iterate] at *
      have ⟨n, hn⟩:=hux
      use n + 1
      rw[iterate_succ_apply, hn]
    }
  }
theorem Function.skip_iterate_of_lt_not_eq {f : α → α} {x : α} (hf : Injective f)
  {u : {a // a ≠ x}} {n : ℕ} (hux : ∀ m < n, f^[m] u ≠ x) {m : ℕ} (hm : m < n)
  : (skip hf x)^[m] u = f^[m] u := by{
    induction n generalizing u m with
    | zero => simp at hm
    | succ n' ih => {
      have hux' : ∀m < n', f^[m] (f u) ≠ x:=by{
        intro m hmn'
        specialize hux (m + 1) (by{simp[hmn']})
        rw[iterate_succ_apply] at hux
        exact hux
      }
      match m with
      | 0 => simp
      | m' + 1 => {
        simp only [Order.lt_add_one_iff, Order.add_one_le_iff] at hm
        have h0 : f u ≠ x := by{
          specialize hux 1 (by{simp[Nat.zero_lt_of_lt hm]})
          exact hux
        }
        specialize @ih ⟨f u, h0⟩ hux' m' hm
        rw[iterate_succ_apply, skip_eq_of_apply_ne hf h0, ih, iterate_succ_apply]
      }
    }
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

theorem Fintype.skip_minimalPeriod {α : Sort _} [DecidableEq α] [Fintype α] {f : α → α}
(hf : Injective f) {x : α} {a : {y // y ≠ x}}
  : minimalPeriod (skip hf x) a + (if funReflTransGen f x a then 1 else 0) = minimalPeriod f a
  := by{
  set y := a.val
  have hy : y ≠ x := a.prop
  let p := minimalPeriod f y
  let q := minimalPeriod (skip hf x) a
  -- f is bijective because it is injective on a finite type
  have hf_bi : Bijective f := by
    apply Finite.injective_iff_bijective.mp hf
  -- Symmetry of reachability for bijective functions
  have h_symm {x y : α}: funReflTransGen f x y ↔ funReflTransGen f y x := by
    rw[(funReflTransGen_Symm_of_injective hf).comm]
  cases em' (funReflTransGen f x y) with
  | inl H_not => {
    -- Case: x does not reach y. By symmetry, y does not reach x.
    have H_not_symm : ¬ funReflTransGen f y x := by
      rwa [← h_symm]
    -- For all n, the iterates under skip equal those under f.
    have h_iter_eq : ∀ n, (skip hf x)^[n] a = f^[n] y := by
      intro n
      exact skip_iterate_of_not_funReflTransGen hf H_not_symm n
    -- Hence minimal periods coincide.
    have h_q_eq_p : q = p := by
      unfold p q
      rw[minimalPeriod_eq_minimalPeriod_iff]
      intro n
      change _ = _ ↔ _ = _
      rw[Subtype.ext_iff, h_iter_eq]
    rw [if_neg H_not, add_zero]
    exact h_q_eq_p
  }
  | inr H => {
    -- Case: x reaches y. Then y reaches x.
    have H_symm : funReflTransGen f y x := h_symm.mp H
    rw [funReflTransGen_iff_iterate] at H_symm
    obtain ⟨n0, hn0⟩ := H_symm
    have hn0_pos : n0 > 0 := by
      rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt]
      rintro rfl
      rw [← hn0] at hy
      contradiction
    -- Let t be the least positive integer such that f^t(y) = x.
    let t := Nat.find (p:=fun m => f^[m] y = x) (Exists.intro n0 hn0)
    have ht : f^[t] y = x := Nat.find_spec (p:=fun m => f^[m] y = x) (Exists.intro n0 hn0)
    have ht_min : ∀ m < t, f^[m] y ≠ x :=
      fun _ => Nat.find_min (p:=fun m => f^[m] y = x) (Exists.intro n0 hn0)
    have ht_pos : t > 0 := by
      rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt]
      rintro h'
      rw[h'] at ht
      rw [← ht] at hy
      contradiction
    -- Also t < p, because x occurs in the cycle of y.
    have hfp : f^[p] y = y := isPeriodicPt_minimalPeriod f y
    have ht_lt_p : t < p := by
      apply lt_of_not_ge
      intro hge
      have ⟨r, hr⟩ := Nat.exists_eq_add_of_le hge
      rw [hr, add_comm, iterate_add_apply, hfp] at ht
      cases r with
      | zero => rw [iterate_zero_apply] at ht; exact hy ht
      | succ r' =>
        have hr_lt_t : r' + 1 < t := by
          rw[hr]
          apply Nat.lt_add_of_pos_left
          apply hf.minimalPeriod_pos
        specialize ht_min (r' + 1) hr_lt_t
        rw [← ht] at ht_min
        contradiction
    have h_f_pow_ne_x : ∀ m, t < m → m ≤ p → f^[m] y ≠ x := by
      intro m hm1 hm2 h_eq
      cases eq_or_lt_of_le hm2 with
      | inl h_eq_p =>
        -- m = p
        rw [h_eq_p, hfp] at h_eq      -- 由 f^p y = y，得到 y = x
        exact hy h_eq            -- 矛盾于 y ≠ x
      | inr h_lt_p =>
        -- t < m < p
        -- 利用最小周期性质：f^m y = f^t y（因为两者都等于 x）
        rw[← ht] at h_eq
        rw[← iterate_mod_minimalPeriod_eq, ← iterate_mod_minimalPeriod_eq (n:=t)] at h_eq
        have h_mod := (iterate_eq_iterate_iff_of_lt_minimalPeriod
          (Nat.mod_lt _ hf.minimalPeriod_pos) (Nat.mod_lt _ hf.minimalPeriod_pos)).mp h_eq
        -- 由于 0 < t < m < p，有 m % p = m，t % p = t
        have h_m_mod : m % p = m := Nat.mod_eq_of_lt h_lt_p
        have h_t_mod : t % p = t := Nat.mod_eq_of_lt ht_lt_p
        rw [h_m_mod, h_t_mod] at h_mod    -- 得到 m = t
        exact (lt_irrefl m) (h_mod ▸ hm1) -- m > t 与 m = t 矛盾
    -- We prove that for all n < p, skip^n(a) = f^{n + δ(n)}(y),
    -- where δ(n) = 0 if n < t, and δ(n) = 1 if n ≥ t.
    have h_skip_formula : ∀ n, n < p →
      (if n < t then (skip hf x)^[n] a = f^[n] y
       else (skip hf x)^[n] a = f^[n+1] y) := by
      intro n hn
      induction n with
      | zero =>
        cases lt_or_ge 0 t with
        | inl h_lt => rw [if_pos h_lt]; rfl
        | inr h_ge => exfalso; exact (not_lt_of_ge h_ge) (Nat.zero_lt_of_lt ht_pos)
      | succ n' ih =>
        have hn' : n' < p := by omega
        specialize ih hn'
        cases lt_or_ge n' t with
        | inl h_lt_t' =>
          rw [if_pos h_lt_t'] at ih
          cases lt_or_ge (n'+1) t with
          | inl h_lt_t_succ =>
            rw [if_pos h_lt_t_succ]
            rw [iterate_succ_apply', skip_val, ih, skip', if_neg, iterate_succ_apply']
            specialize ht_min _ h_lt_t_succ
            rwa[← iterate_succ_apply' f]
          | inr h_ge_t_succ =>
            have h_eq_t : n'+1 = t := by omega
            rw [if_neg (not_lt_of_ge h_ge_t_succ)]
            have ih' := Subtype.ext (a2:=⟨_, ih ▸ ((skip hf x)^[n'] a).prop⟩) ih
            rw [iterate_succ_apply', ih']
            simp only [iterate_succ_apply', skip_val, skip']
            rw[if_pos]
            rw[← ht, ← h_eq_t, iterate_succ_apply']
        | inr h_ge_t' =>
          rw [if_neg (not_lt_of_ge h_ge_t')] at ih
          cases lt_or_ge (n'+1) t with
          | inl h_lt_t_succ => exfalso; omega
          | inr h_ge_t_succ =>
            rw [if_neg (not_lt_of_ge h_ge_t_succ)]
            have ih' := Subtype.ext (a2:=⟨_, ih ▸ ((skip hf x)^[n'] a).prop⟩) ih
            rw [iterate_succ_apply', ih', skip_val, skip']
            simp only
            rw [← iterate_succ_apply f, iterate_succ_apply', iterate_succ_apply',
            iterate_succ_apply', if_neg]
            -- 需要 f^[n'+2] y ≠ x
            have := h_f_pow_ne_x (n'+2) (by omega) (by omega)
            simpa[iterate_succ_apply']
    -- Now show skip^{p-1}(a) = a.
    have h_skip_p_minus_1 : (skip hf x)^[p-1] a = a := by{
      have h_p_gt_0 : p > 0 := by
        apply hf.minimalPeriod_pos
      have h_p_minus_1_lt_p : p-1 < p := by omega
      have h_ge_t : p-1 ≥ t := by
        rwa[ge_iff_le, Nat.le_sub_one_iff_lt h_p_gt_0]
      specialize h_skip_formula _ h_p_minus_1_lt_p
      rw[ite_cond_eq_false _ _ (by{simp[h_ge_t]})] at h_skip_formula
      rw [Subtype.ext_iff, h_skip_formula, Nat.sub_add_cancel (by omega), hfp]
    }
    -- q divides p-1 because skip^{p-1}(a)=a and skip is injective (hence periodic).
    have h_q_dvd : q ∣ p-1 := by
      apply IsPeriodicPt.minimalPeriod_dvd h_skip_p_minus_1
    -- We also know q ≥ p-1? Actually we'll prove q = p-1 by contradiction.
    -- If q < p-1, derive contradiction.
    have h_q_ge : q ≥ p-1 := by
      apply le_of_not_gt
      intro h_gt
      have h_q_lt : q < p-1 := by omega
      have h_q_lt_p : q < p := by omega
      have h_case := h_skip_formula q h_q_lt_p
      -- a 是 skip 的周期点（因为 skip 是双射），所以 q > 0
      have h_skip_bi := Finite.skip_bijective hf x
      have h_q_pos : 0 < q := (skip_injective hf _).minimalPeriod_pos
      cases lt_or_ge q t with
      | inl h_lt_t =>
        -- q < t ⇒ skip^q(a) = f^q(y) = a.val = y，即 f^q(y)=y
        rw [if_pos h_lt_t] at h_case
        have h_eq : f^[q] y = y := by
          rw[iterate_minimalPeriod] at h_case
          exact h_case.symm
        -- 与 p 的最小性矛盾（0<q<p）
        have h' := IsPeriodicPt.minimalPeriod_le (by omega) h_eq
        exact not_lt_of_ge h' h_q_lt_p
      | inr h_ge_t =>
        -- q ≥ t ⇒ skip^q(a) = f^{q+1}(y) = a.val = y，即 f^{q+1}(y)=y
        rw [if_neg (not_lt_of_ge h_ge_t)] at h_case
        rw[iterate_minimalPeriod] at h_case
        have h_eq : f^[q+1] y = y := h_case.symm
        have h_q1_pos : q+1 > 0 := by omega
        have h_q1_lt_p : q+1 < p := by omega
        -- 最小性 ⇒ p ≤ q+1，但 q+1 < p，矛盾
        have h' := IsPeriodicPt.minimalPeriod_le (by omega) h_eq
        exact not_lt_of_ge h' (Nat.add_lt_of_lt_sub h_q_lt)
    -- Therefore q = p-1.
    have h_q_eq_p_minus_1 : q = p-1 := by
      apply le_antisymm
      · exact Nat.le_of_dvd (by omega) h_q_dvd
      · exact h_q_ge
    -- Finish: q + 1 = p.
    unfold q p at h_q_eq_p_minus_1
    rw [if_pos H, h_q_eq_p_minus_1, Nat.sub_add_cancel]
    exact hf.minimalPeriod_pos
  }
}

theorem Finite.skip_minimalPeriod_le {α : Sort _} [DecidableEq α] [Finite α] {f : α → α}
(hf : Injective f) {x : α} {a : {y // y ≠ x}}
  : minimalPeriod (skip hf x) a ≤ minimalPeriod f a := by{
  let := Fintype.ofFinite α
  rw[← Fintype.skip_minimalPeriod hf]
  simp
}

end Fintype
