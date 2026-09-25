import FourColorTheorem.RealPlane.Indexed.Lemmas
import FourColorTheorem.RealPlane.Indexed.Map

/-! 在边界上构造长方形，这些长方形不和其他区域相交，也不和其他长方形相交 -/

open Function
open Relation

namespace RealPlane
namespace PlainMap

abbrev AdjIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
@[inline] instance AdjIndex.instFintype {n : ℕ}
: Fintype (AdjIndex n) := inferInstance
@[inline] instance AdjIndex.instMembership {n : ℕ}
: Membership (Fin n) (AdjIndex n) where
  mem := fun b a => a = b.val.1 ∨ a = b.val.2
theorem AdjIndex.mem_iff {n : ℕ} {i : Fin n} {e : AdjIndex n}
: i ∈ e ↔ i = e.val.1 ∨ i = e.val.2 := Iff.rfl
def AdjIndex.fst {n : ℕ} (e : AdjIndex n) := e.val.fst
def AdjIndex.snd {n : ℕ} (e : AdjIndex n) := e.val.snd
theorem AdjIndex.isLt {n : ℕ} (e : AdjIndex n)
: e.fst < e.snd := e.prop

def IndexedMap.adjacent {m0 : PlainMap} {n : ℕ}
(MR : IndexedMap m0 n) (e : AdjIndex n) : Prop :=
  m0.adjacent (MR e.fst) (MR e.snd)

abbrev ProperAdjIndex {m0 : PlainMap} {n : ℕ} (mr : IndexedMap m0 n)
:= {e : AdjIndex n // mr.adjacent e}
@[inline] noncomputable instance ProperAdjIndex.instFintype
{m0 : PlainMap} {n : ℕ} {mr : IndexedMap m0 n}
: Fintype (ProperAdjIndex mr) := by{
  unfold ProperAdjIndex
  classical
  apply Subtype.fintype
}

theorem IndexedMap.exists_boundary_point {m0 : PlainMap} {n : ℕ} (mr : IndexedMap m0 n)
: ∃f : ProperAdjIndex mr → Point,
∀e, f e ∈ m0.boundary (mr e.val.fst) (mr e.val.snd)
  ∧ ∀i, f e ∈ closure (m0 (mr i)) → i ∈ e.val
:= by{
  let f : ProperAdjIndex mr → Point := fun e =>
    Classical.choose (m0.exists_boundarypoint_of_adjacent e.prop)
  have hf :=
    fun e : ProperAdjIndex mr => Classical.choose_spec (m0.exists_boundarypoint_of_adjacent e.prop)
  use f
  unfold f
  intro e
  specialize hf e
  apply And.intro hf.1
  have hf' := hf.2
  intro i hi
  rw[AdjIndex.mem_iff]
  have hf'i := hf' (mr i) hi
  rw[Eq.comm (a := i), Eq.comm (a := i)]
  apply hf'i.imp <;> {
    intro h
    apply mr.some_injOn
    exact h
  }
}
lemma IndexedMap.exists_adjBox' {m0 : PlainMap} {n : ℕ} (mr : IndexedMap m0 n)
: ∃f : ProperAdjIndex mr → Rectangle,
∀e, (∃p ∈ f e, p ∈ m0.boundary (mr e.val.fst) (mr e.val.snd))
∧ (∀i, ∀z ∈ f e, z ∈ m0 (mr i) → i ∈ e.val)
:= by{
  let f : ProperAdjIndex mr → Rectangle :=
    fun e => Classical.choose (m0.exists_adjbox_of_finite_of_adjacent
      mr.finiteMap e.prop)
  use f
  intro e
  have he := Classical.choose_spec (m0.exists_adjbox_of_finite_of_adjacent
      mr.finiteMap e.prop)
  apply And.intro he.1
  have he' := he.2
  intro i z hz1 hz2
  specialize he' _ _ hz1 hz2
  rw[AdjIndex.mem_iff]
  apply he'.imp <;> {
    intro h
    symm
    apply mr.some_injOn
    exact h
  }
}
theorem IndexedMap.exists_adjBox {m0 : PlainMap} {n : ℕ} (mr : IndexedMap m0 n)
: ∃f : ProperAdjIndex mr → Rectangle,
∀e, (∃p ∈ f e, p ∈ m0.boundary (mr e.val.fst) (mr e.val.snd))
∧ (∀i, ∀z ∈ f e, z ∈ m0 (mr i) → i ∈ e.val)
∧ ∀e' p, p ∈ f e → p ∈ f e' → e = e'
:= by{
  have ⟨f, hf⟩ := mr.exists_adjBox'
  let equiv : Fin (Fintype.card (ProperAdjIndex mr)) → ProperAdjIndex mr :=
    (Fintype.equivFin (ProperAdjIndex mr)).symm
  have hequivI : Injective equiv := by{
    apply Equiv.injective
  }
  let fn : Fin (Fintype.card (ProperAdjIndex mr)) → Rectangle :=
    f ∘ equiv
  let kn : Fin (Fintype.card (ProperAdjIndex mr)) → Point :=
    fun i => Classical.choose (hf (equiv i)).1
  have hknI : Injective kn := by{
    unfold kn
    intro i j hij
    simp only at hij
    have hi := Classical.choose_spec (hf (equiv i)).1
    have hj := Classical.choose_spec (hf (equiv j)).1
    rw[← hij] at hj
    have hi' := rect_meet_of_mem_boudnary hi.2 _ hi.1
    have hj' := rect_meet_of_mem_boudnary hj.2 _ hi.1
    have ⟨z, hz⟩ := hj'.1
    have hfj1 := (hf (equiv i)).2 (equiv j).val.fst _ hz.1 hz.2
    have ⟨z', hz'⟩ := hj'.2
    have hfj2 := (hf (equiv i)).2 (equiv j).val.snd _ hz'.1 hz'.2
    rw[AdjIndex.mem_iff] at hfj1 hfj2
    have hi'' : (equiv i).val.val.1 < (equiv i).val.val.2 := (equiv i).val.isLt
    have hj'' : (equiv j).val.val.1 < (equiv j).val.val.2 := (equiv j).val.isLt
    apply hequivI
    rw[AdjIndex.fst] at hfj1
    rw[AdjIndex.snd] at hfj2
    ext <;> omega
  }
  have hknfn : ∀i, kn i ∈ fn i := by{
    intro i
    have hi := Classical.choose_spec (hf (equiv i)).1
    unfold kn fn
    rw[comp_apply]
    exact hi.1
  }
  have ⟨f', hf'⟩ := rect_fin_separable (f := fn) (k := kn)
    hknI hknfn
  let equiv' := Fintype.equivFin (ProperAdjIndex mr)
  use f' ∘ equiv'
  intro e
  constructor
  · {
    use kn (equiv' e)
    rw[comp_apply]
    apply And.intro (by{apply hf'.1})
    have h' := Classical.choose_spec (hf e).1
    apply Eq.mp ?_ h'.2
    unfold kn
    congr
    simp[equiv, equiv']
  }
  constructor
  · {
    intro i z hz hzi
    apply (hf e).2 i z ?_ hzi
    rw[comp_apply] at hz
    have hz' : z ∈ fn (equiv' e) := by{
      apply (hf'.2.1 _).subset
      exact hz
    }
    unfold fn at hz'
    simp only [comp_apply, Equiv.symm_apply_apply, equiv, equiv'] at hz'
    exact hz'
  }
  intro e' p hpe hpf
  rw[comp_apply] at hpe hpf
  have hf'' := hf'.2.2 _ _ _ hpe hpf
  unfold equiv' at hf''
  simp at hf''
  simp[hf'']
}

@[ext] structure IndexedMapWithAdjBox (m0 : PlainMap) (n : ℕ)
extends IndexedMap m0 n where
  adjbox : AdjIndex n → Rectangle
  adjbox_injOn : ∀e f p,
    p ∈ adjbox e → p ∈ adjbox f → e = f
  adj_iff_adjbox_nonempty : ∀e : AdjIndex n, toIndexedMap.adjacent e
    ↔ (adjbox e).Nonempty
  adj_iff_meet_box : ∀e, toIndexedMap.adjacent e
    ↔ (∀i, i ∈ e ↔ ∃p ∈ m0 (some i), p ∈ adjbox e)

theorem exists_indexedMapWithAdjBox {m0 : PlainMap}
  (hmF : m0.isFinite) :
  ∃n, Nonempty (IndexedMapWithAdjBox m0 n) := by{
  have ⟨n, ⟨mr⟩⟩ := m0.exists_indexedMap hmF
  use n
  let ⟨ab, hab⟩ := mr.exists_adjBox
  have habne : ∀e, (ab e).Nonempty := by{
    intro e
    rw[Rectangle.nonempty_iff_exists_mem]
    have ⟨p, hp, _⟩ := (hab e).1
    exact ⟨p, hp⟩
  }
  classical
  let ab' : AdjIndex n → Rectangle := fun e =>
    if he : mr.adjacent e then
      ab ⟨e, he⟩
    else
      Rectangle.null
  have hab'ne : ∀e, mr.adjacent e ↔ (ab' e).Nonempty := by{
    unfold ab'
    intro e
    split_ifs with h
    · simp[h, habne]
    · simp[Rectangle.null_not_nonempty, h]
  }
  apply Nonempty.intro
  exact {
    toIndexedMap := mr,
    adjbox := ab',
    adjbox_injOn := by{
      intro e f p hpe hpf
      unfold ab' at hpe hpf
      split_ifs at hpe with he <;>
        try simp only [Rectangle.notMem_null] at hpe
      split_ifs at hpf with hf <;>
        try simp only [Rectangle.notMem_null] at hpf
      have hab' := (hab ⟨e, he⟩).2.2 ⟨f, hf⟩ _ hpe hpf
      simp at hab'
      simp[hab']
    },
    adj_iff_adjbox_nonempty := hab'ne,
    adj_iff_meet_box := by{
      intro e
      constructor
      · {
        intro he i
        constructor
        · {
          intro hie
          have ⟨p, hp0, hp1⟩ := (hab ⟨e, he⟩).1
          have ⟨⟨p1, hp11, hp12⟩,⟨p2, hp21, hp22⟩⟩ :=
            rect_meet_of_mem_boudnary hp1 _ hp0
          rw[AdjIndex.mem_iff] at hie
          rcases hie with hie | hie
          · {
            use p1
            rw[hie]
            apply And.intro hp12
            unfold ab'
            simp[he, hp11]
          }
          · {
            use p2
            rw[hie]
            apply And.intro hp22
            unfold ab'
            simp[he, hp21]
          }
        }
        · {
          intro ⟨p, hp0, hp1⟩
          unfold ab' at hp1
          simp only [he, ↓reduceDIte] at hp1
          exact (hab ⟨e, he⟩).2.1 i _ hp1 hp0
        }
      }
      · {
        intro h
        rw[hab'ne]
        have ⟨p, _, hp⟩ := (h e.fst).mp
          (by{simp[AdjIndex.mem_iff, AdjIndex.fst]})
        apply Rectangle.nonempty_of_mem hp
      }
    }
  }
}

end PlainMap
end RealPlane
