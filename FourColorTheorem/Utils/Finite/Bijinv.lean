import FourColorTheorem.Utils.Finite.Basic
import FourColorTheorem.Utils.Finite.Period

open Function
open Relation

section Fintype
variable {α : Type _} [Fintype α]

theorem Fintype.bijInv_bijInv [DecidableEq α] {f : α → α} (hf : Bijective f)
  : bijInv (bijective_bijInv hf) = f:=by{
  ext x
  apply (bijective_bijInv hf).left
  rw[leftInverse_bijInv hf]
  rw[rightInverse_bijInv (bijective_bijInv hf)]
}
theorem Fintype.comp_bijInv [DecidableEq α] {f g : α → α} (hf : Bijective f) (hg : Bijective g)
  : bijInv (Function.Bijective.comp hf hg) = bijInv hg ∘ bijInv hf := by{
    ext x
    apply (Function.Bijective.comp hf hg).injective
    rw[rightInverse_bijInv (Function.Bijective.comp hf hg)]
    rw[comp_apply, comp_apply]
    rw[rightInverse_bijInv hg, rightInverse_bijInv hf]
  }
theorem Fintype.iterate_bijInv [DecidableEq α] {f : α → α} (hf : Bijective f) {n : ℕ}
  : bijInv (Bijective.iterate hf n) = (bijInv hf)^[n] := by{
    ext x
    rw[←(hf.left.iterate n).eq_iff]
    rw[rightInverse_bijInv (hf.iterate n)]
    induction n with
    | zero => simp
    | succ n' ih => {
      rw[iterate_succ, iterate_succ']
      simp only [comp_apply]
      rw[rightInverse_bijInv hf]
      exact ih
    }
  }
theorem Relation.fromFun_bijInv_iff [DecidableEq α]
  {f : α → α} (hf : Bijective f) {a b : α}
  : fromFun (Fintype.bijInv hf) a b ↔ fromFun f b a:=by{
    simp only [fromFun]
    rw[←Injective.eq_iff hf.left]
    rw[Fintype.rightInverse_bijInv hf]
    rw[Eq.comm]
  }
theorem List.isChain_bijInv_iff_isChain_reverse [DecidableEq α] {l : List α} {f : α → α}
  (hf : Bijective f)
  : List.IsChain (fromFun (Fintype.bijInv hf)) l ↔ List.IsChain (fromFun f) l.reverse := by{
    match l with
    | [] | [_] => simp
    | a :: b :: t => {
      rw[List.isChain_cons_cons]
      rw[List.reverse_cons, List.reverse_cons]
      rw[List.isChain_concat_append]
      rw[←List.reverse_cons]
      rw[and_comm]
      apply and_congr
      · apply isChain_bijInv_iff_isChain_reverse hf
      · {
        simp only [fromFun, isChain_cons_cons, IsChain.singleton, and_true]
        rw[←hf.injective.eq_iff, Fintype.rightInverse_bijInv hf, Eq.comm]
      }
    }
  }

theorem Relation.funReflTransGen_bijInv [DecidableEq α] {f : α → α}
  (hf : Bijective f) {a b : α} (hab : funReflTransGen f a b)
  : funReflTransGen (Fintype.bijInv hf) a b := by{
    induction hab with
    | refl => exact ReflTransGen.refl
    | @tail c b hac hcb ih => {
      apply ih.trans
      rw[←fromFun_bijInv_iff hf] at hcb
      have hcb':=ReflTransGen.single hcb
      have hcb'':=funReflTransGen_symm_of_injective (Fintype.bijective_bijInv hf).left hcb'
      exact hcb''
    }
  }

theorem Relation.funReflTransGen_bijInv_iff [DecidableEq α] {f : α → α}
  (hf : Bijective f) : funReflTransGen (Fintype.bijInv hf) = funReflTransGen f := by{
    ext a b
    unfold funReflTransGen
    apply (Iff.intro · (funReflTransGen_bijInv hf))
    intro hab
    have hab':=funReflTransGen_bijInv (Fintype.bijective_bijInv hf) hab
    rw[Fintype.bijInv_bijInv hf] at hab'
    exact hab'
  }

theorem Fintype.bijInv_IsFixedPt [DecidableEq α] {f : α → α} (hf : Bijective f)
  {x : α} : IsFixedPt (bijInv hf) x ↔ IsFixedPt f x:=by{
    unfold IsFixedPt
    rw[←hf.injective.eq_iff, rightInverse_bijInv hf, Eq.comm]
  }
theorem Fintype.bijInv_IsPeriodicPt [DecidableEq α] {f : α → α} (hf : Bijective f)
  {x : α} {n : ℕ} : IsPeriodicPt (bijInv hf) n x ↔ IsPeriodicPt f n x:=by{
    unfold IsPeriodicPt
    rw[←iterate_bijInv hf]
    exact bijInv_IsFixedPt (hf.iterate n)
  }
theorem Fintype.bijInv_minimalPeriod' [DecidableEq α] {f : α → α} (hf : Bijective f)
  : minimalPeriod' (bijInv hf) = minimalPeriod' f:=by{
    ext x
    rw[minimalPeriod'_eq_minimalPeriod]
    rw[minimalPeriod'_eq_minimalPeriod]
    rw[minimalPeriod_eq_minimalPeriod_iff]
    intro n
    exact bijInv_IsPeriodicPt hf
  }
theorem Fintype.bijInv_minimalPeriod [DecidableEq α] {f : α → α} (hf : Bijective f)
  : minimalPeriod (bijInv hf) = minimalPeriod f:=by{
    rw[←minimalPeriod'_eq_minimalPeriod]
    rw[←minimalPeriod'_eq_minimalPeriod]
    apply Fintype.bijInv_minimalPeriod' hf
  }

section conjugate
theorem Relation.funReflTransGen_conj [DecidableEq α] {f : α → α} (hf : Bijective f) (g : α → α)
  : funReflTransGen ((Fintype.bijInv hf) ∘ g ∘ f) = ReflTransGen (InvImage (fromFun g) f) := by{
    ext a b
    unfold funReflTransGen
    constructor
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hac hcb ih => {
        apply ih.tail
        simp only [InvImage, fromFun]
        simp only [fromFun, comp_apply] at hcb
        rw[←hf.injective.eq_iff] at hcb
        rw[Fintype.rightInverse_bijInv hf] at hcb
        exact hcb
      }
    }
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hac hcb ih => {
        apply ih.tail
        simp only [fromFun, comp_apply]
        simp only [fromFun, InvImage] at hcb
        rw[←hf.injective.eq_iff]
        rw[Fintype.rightInverse_bijInv hf]
        exact hcb
      }
    }
  }
end conjugate
end Fintype
