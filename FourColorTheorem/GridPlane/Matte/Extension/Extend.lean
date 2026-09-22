import FourColorTheorem.GridPlane.Matte.Extension.Defs
import FourColorTheorem.GridPlane.Matte.Constructors.Extend1
import FourColorTheorem.GridPlane.Matte.Constructors.Extend2

/-! 可以用两种扩展方式构造Matte的扩展 -/

open Function
open Relation

namespace GridPlane
namespace Matte

namespace canExtendTo

theorem extend1 {m : Matte} {d : GDart} (ext1p : Extend1.ext1Hp m d)
  : m.canExtendTo (extend1 ext1p) :=by{
    rw[Extend1.ext1Hp] at ext1p
    apply canExtendTo.step (d:=d) (xm0:=m)
    · apply canExtendTo.refl
    · {
      rw[m.mem_ring_iff_mem_disk_border, border, Set.mem_ofPred, edge_2]
      simp only [List.coe_toFinset, Set.mem_ofPred_eq]
      rw[mem_def] at ext1p
      refine ⟨ext1p.left, ext1p.right.symm ?_⟩
      rw[GRectangle.mem_enum_iff]
      apply GRectangle.half_mem_ehex
    }
    · simp[mem_def, Matte.extend1, Extend1.ext1Disk]
  }
theorem extend2 {m : Matte} {d : GDart} (ext2p : Extend2.ext2Hp m d)
  : m.canExtendTo (extend2 ext2p) := by{
    rw[Extend2.ext2Hp] at ext2p
    apply canExtendTo.step (d:=d) (xm0:=m)
    · apply canExtendTo.refl
    · {
      rw[m.mem_ring_iff_mem_disk_border, border, Set.mem_ofPred, edge_2]
      simp only [List.coe_toFinset, Set.mem_ofPred_eq]
      rw[mem_def] at ext2p
      refine ⟨ext2p.left, ext2p.right.right.symm ?_⟩
      rw[GRectangle.mem_enum_iff]
      apply GRectangle.half_mem_equad
    }
    · simp[Matte.extend2, mem_def, Extend2.ext2Disk]
  }

end canExtendTo

theorem canExtendIn_of_extend1 {m : Matte} {r : GRectangle} {d : GDart}
  (ext1p : Extend1.ext1Hp m d) (hdr : d.half ∈ r) : canExtendIn m r d.half := by{
    use extend1 ext1p
    refine ⟨canExtendTo.extend1 ext1p, ?_, ?_⟩
    · {
      simp only [extend1, Extend1.ext1Disk]
      intro x
      simp only [List.mem_cons, List.mem_append]
      apply Or.imp_left
      intro h
      simp[h, GRectangle.mem_enum_iff, hdr]
    }
    · {
      rw[mem_def, extend1]
      simp[Extend1.ext1Disk]
    }
  }
theorem canExtendIn_of_extend2 {m : Matte} {r : GRectangle} {d : GDart}
  (ext2p : Extend2.ext2Hp m d) (hdr : d.half ∈ r) : canExtendIn m r d.half := by{
    use extend2 ext2p
    refine ⟨canExtendTo.extend2 ext2p, ?_, ?_⟩
    · {
      simp only [extend2, Extend2.ext2Disk]
      intro x
      simp only [List.mem_cons, List.mem_append]
      apply Or.imp_left
      intro h
      simp[h, GRectangle.mem_enum_iff, hdr]
    }
    · {
      rw[mem_def, extend2]
      simp[Extend2.ext2Disk]
    }
  }

lemma canExtendIn_ehex {m : Matte} {r : GRectangle}
  {p : GPixel} (hpr : p ∈ r) {d : GDart} (hdp : d.half = p)
  (hehex : m.disk.Disjoint (GRectangle.ehex d).enum)
  (ih : canExtendIn m (chopRect r (edge d)) (edge d).half)
  : canExtendIn m r p := by{
    have ⟨xm, hxme, hxms, hxmp⟩ := ih
    have hext1 : Extend1.ext1Hp xm d := by{
      rw[Extend1.ext1Hp]
      apply And.intro hxmp
      apply List.disjoint_of_subset_left hxms
      rw[List.disjoint_append_left]
      refine ⟨?_, hehex⟩
      rw[List.Disjoint]
      simp only [imp_false, GRectangle.mem_enum_iff, mem_chopRect_iff]
      intro a ⟨_, ha⟩
      have h:=GRectangle.ehex_disjoint_edge_chop (d:=d)
      intro ha'
      exact h _ ha' ha
    }
    use xm.extend1 hext1
    constructor
    · {
      exact hxme.trans (canExtendTo.extend1 hext1)
    }
    constructor
    · {
      rw[extend1]
      simp only [Extend1.ext1Disk]
      simp only [List.cons_subset, List.mem_append]
      constructor
      · {
        left
        simp only [hdp, GRectangle.mem_enum_iff, hpr]
      }
      · {
        apply List.Subset.trans hxms
        intro x
        simp only [List.mem_append]
        apply Or.imp_left
        simp only [GRectangle.mem_enum_iff]
        apply chopRect_subset_rect
      }
    }
    · {
      rw[extend1, mem_def]
      simp only [Extend1.ext1Disk, ←hdp, List.mem_cons, true_or]
    }
  }

end Matte
end GridPlane
