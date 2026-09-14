import Mathlib.Algebra.Group.Action.Basic
import FourColorTheorem.Utils.Chain
import FourColorTheorem.GridPlane.Basic

open Function
open Relation

namespace GridPlane

structure Matte where
  disk : List GPixel
  ring : List GDart
  disk_ne_nil : disk ≠ []
  ring_cycle : ring.IsCycleChain mrlink
  ring_simple : (ring.map end0).Nodup
  mem_ring_iff_mem_disk_border : ∀x, x ∈ ring ↔ x ∈ border disk.toFinset

namespace Matte

@[inline] instance instCoeRegion : Coe Matte GRegion where
  coe M := M.disk.toFinset
theorem coe_iff (M : Matte) : M = {p | p ∈ M.disk} := by{simp}
@[inline] instance : Membership GPoint Matte where
  mem R x := x ∈ (R : Set GPoint)
theorem mem_def (M : Matte) x : x ∈ M ↔ x ∈ M.disk := by{
  change x ∈ (M : Set GPoint) ↔ _
  simp
}
@[inline] instance instDecidableMem {x : GPoint} {m : Matte} :
  Decidable (x ∈ m) := by{
  rw[mem_def]
  infer_instance
}
theorem noempty {m : Matte} : (m : GRegion) ≠ ∅ := by{
  rw[ne_eq, Set.eq_empty_iff_forall_notMem]
  push_neg
  simp only [List.coe_toFinset, Set.mem_setOf_eq]
  have h := m.disk_ne_nil
  apply List.exists_mem_of_ne_nil at h
  exact h
}
theorem exists_mem {m : Matte} : ∃p, p ∈ m := by{
  have h := m.noempty
  rw[ne_eq, Set.eq_empty_iff_forall_notMem] at h
  push_neg at h
  rcases h with ⟨z, hz⟩
  use z
  simp only [List.coe_toFinset, Set.mem_setOf_eq] at hz
  rwa[mem_def]
}
theorem disjoint_iff {m1 m2 : Matte}
: Disjoint (m1 : GRegion) (m2 : GRegion) ↔ m1.disk.Disjoint m2.disk
:= by{
  rw[Set.disjoint_iff, Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem]
  simp only [List.coe_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, not_and]
  rfl
}
theorem mem_border_iff {m : Matte} {d : GDart} :
  d ∈ border m.disk.toFinset ↔ d.half ∈ m ∧ (edge d).half ∉ m := by{
  simp[border, mem_def]
}

theorem edge_not_mem_ring_of_mem_ring {m : Matte} {p : GPoint} (hp : p ∈ m.ring)
  : edge p ∉ m.ring := by{
    rw[mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at *
    intro ⟨hl, _⟩
    apply hp.right
    exact hl
  }
theorem not_mem_ring_of_edge_mem_ring {m : Matte} {p : GPoint} (hp : edge p ∈ m.ring)
  : p ∉ m.ring := swap edge_not_mem_ring_of_mem_ring hp

theorem ring_nodup {m : Matte} : m.ring.Nodup :=
  List.Nodup.of_map _ m.ring_simple

lemma exists_border_of_disk_ne_nil {l : List GPixel} (hln : l ≠ [])
 : ∃x, x ∈ border l.toFinset := by{
  have ih : ∃d ∈ l, ⟨d.1, d.2 - 1⟩ ∉ l := by{
    let n := l.minOn Prod.snd hln
    use n
    apply And.intro List.minOn_mem
    intro h
    have hn:=List.min_map hln (f:=Prod.snd)
    change _ = n.2 at hn
    rw[List.min_eq_iff] at hn
    have hn':=hn.right (n.2 - 1) (by{
      simp only [List.mem_map]
      use ⟨n.1, n.2 - 1⟩
    })
    simp at hn'
  }
  have ⟨d, hd, hd0⟩:=ih
  use 2 • d
  rw[border, Set.mem_setOf, GPoint.half_double, edge_half, GPoint.mod2_double, GPoint.half_double]
  rw[add_zero, GPoint.zero_def, GPoint.ccw]
  match d with | ⟨dx, dy⟩ => simp[hd, hd0]
}
theorem ring_ne_nil {m : Matte} : m.ring ≠ [] := by{
  rw[ne_eq, List.eq_nil_iff_forall_not_mem, not_forall]
  simp only [not_not, mem_ring_iff_mem_disk_border]
  apply exists_border_of_disk_ne_nil
  exact m.disk_ne_nil
}

def adj (m1 m2 : Matte) : Prop := ∃p ∈ m2.ring, edge p ∈ m1.ring
@[symm] theorem adj_symm {m1 m2 : Matte} : m1.adj m2 → m2.adj m1 := by{
  intro ⟨p, hp2, hp1⟩
  use edge p
  apply And.intro hp1
  rw[edge_2]
  exact hp2
}
theorem adj_Symm : Std.Symm adj := ⟨fun _ _ => adj_symm⟩
theorem adj_Irrefl : Std.Irrefl adj where
  irrefl:=by{
    intro m
    unfold adj
    rw[not_exists]
    intro p hp
    rw[mem_ring_iff_mem_disk_border] at hp
    rw[border, Set.mem_setOf] at hp
    rw[mem_ring_iff_mem_disk_border] at hp
    rw[border, Set.mem_setOf] at hp
    exact hp.left.right hp.right.left
  }
theorem adj_irrefl : ∀m : Matte, ¬m.adj m := adj_Irrefl.irrefl

end Matte

end GridPlane
