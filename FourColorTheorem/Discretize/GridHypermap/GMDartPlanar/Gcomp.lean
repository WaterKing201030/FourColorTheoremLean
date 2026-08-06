import FourColorTheorem.Discretize.GridHypermap.GMInner
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Fcomp
import FourColorTheorem.Discretize.GridHypermap.GMDartPlanar.Ncomp

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

section connected

noncomputable def C0 (hgp : GridMapProper ab0 cm0) : GDart
:= 2 • ⟨(hgp.extendBBox).hspan.lb, (hgp.extendBBox).vspan.lb⟩
theorem C0_mem_GMGrid {hgp : GridMapProper ab0 cm0} : hgp.C0 ∈ hgp.GMGrid := by{
  rw[mem_GMGrid_iff]
  left
  simp[C0, GPoint.half_double, GRectangle.mem_iff, GInterval.mem_iff,
  GRectangle.hspan_lt_of_proper hgp.extendBBox_proper,
  GRectangle.vspan_lt_of_proper hgp.extendBBox_proper]
}
theorem C0_mem_GInner {hgp : GridMapProper ab0 cm0} :
  ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ ∈ hgp.GMInner := by{
  rw[mem_GMInner_iff]
  simp[C0, GPoint.half_double, GRectangle.mem_iff, GInterval.mem_iff,
  GRectangle.hspan_lt_of_proper hgp.extendBBox_proper,
  GRectangle.vspan_lt_of_proper hgp.extendBBox_proper]
}
theorem GMDartHypermap_gsetoid_of_gsetoid_c0 {hgp : GridMapProper ab0 cm0}
: (∀x, hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x)
  → (∀x y, hgp.GMDartHypermap.gsetoid x y) := by{
    intro h x y
    have hx := h x
    have hy := h y
    symm at hx
    exact hgp.GMDartHypermap.gsetoid.iseqv.trans hx hy
  }
theorem GMDartHypermap_gsetoid_of_gsetoid_c0_inner {hgp : GridMapProper ab0 cm0}
: (∀x ∈ hgp.GMInner, hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x)
→ (∀x y, hgp.GMDartHypermap.gsetoid x y)
:= by{
    intro IH
    apply GMDartHypermap_gsetoid_of_gsetoid_c0
    intro x
    have hx := x.prop
    rw[mem_GMGrid_iff] at hx
    rcases em (x ∈ hgp.GMInner) with hx' | hx'
    · exact IH _ hx'
    rw[mem_GMInner_iff] at hx'
    apply (Or.resolve_left · hx') at hx
    have IH' := IH ⟨edge x, by{simp[mem_GMGrid_iff, hx]}⟩ (by{simp[mem_GMInner_iff, hx]})
    apply hgp.GMDartHypermap.gsetoid.iseqv.trans IH'
    apply hgp.GMDartHypermap.gsetoid.iseqv.symm
    apply Hypermap.cglink_of_cedge
    apply funReflTransGen.single
  }

theorem GMDartHypermap_gsetoid_half_eq {hgp : GridMapProper ab0 cm0}
: ∀x ∈ hgp.GMInner, ∀y ∈ hgp.GMInner, x.val.half = y.val.half
    → (hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x ↔
    hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ y)
    := by{
      intro x hx y hy hxy
      rw[← GMDartHypermapNsetoid_iff_half_eq_of_inner hx hy] at hxy
      change hgp.GMDartHypermap.cnode _ _ at hxy
      have hxy' : hgp.GMDartHypermap.gsetoid _ _ := Hypermap.cglink_of_cnode hxy
      constructor
      · intro h; exact h.trans hxy'
      · symm at hxy'; intro h; exact h.trans hxy'
    }
theorem GMDartHypermap_gsetoid_end0_eq {hgp : GridMapProper ab0 cm0}
: ∀x y : hgp.GMDart, end0 x = end0 y
    → (hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x ↔
    hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ y)
    := by{
      intro x y hxy
      rw[← GMDartHypermap_fsetoid_iff_end0] at hxy
      change hgp.GMDartHypermap.cface _ _ at hxy
      have hxy' : hgp.GMDartHypermap.gsetoid _ _ := Hypermap.cglink_of_cface hxy
      constructor
      · intro h; exact h.trans hxy'
      · symm at hxy'; intro h; exact h.trans hxy'
    }

section
theorem GMDartHypermap_gsetoid_x {hgp : GridMapProper ab0 cm0}
  (IH : ∀ x ∈ hgp.GMInner, x.val.x = hgp.C0.x →
    hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x) :
  ∀ x ∈ hgp.GMInner, (hgp.GMDartHypermap).gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x := by{
  intro x hx
  have hc0x : (hgp.C0).x = hgp.extendBBox.hspan.lb * 2 := by{
    simp[C0, two_nsmul, ← mul_two]
  }
  have hx_mem := hx
  rw[mem_GMInner_iff', GRectangle.zoom] at hx
  have h := Nat.recAux (motive := fun m =>
    ∀x ∈ hgp.GMInner, m = (x.val.x - hgp.extendBBox.hspan.lb * 2).toNat
    → hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x)
  apply h ?_ ?_ ((x.val.x - (hgp.extendBBox).hspan.lb * 2).toNat) x hx_mem rfl
  · {
    clear! x
    intro x hx_mem hx0
    have hx:=hx_mem
    simp only [mem_GMInner_iff', GRectangle.mem_iff, GInterval.mem_iff, GRectangle.zoom] at hx
    symm at hx0
    rw[Int.toNat_eq_zero, sub_le_iff_le_add, zero_add] at hx0
    have hx':=le_antisymm hx0 hx.left.left
    apply IH _ hx_mem
    simp[C0, hx', two_nsmul, ←mul_two]
  }
  · {
    clear! x
    clear h
    intro k hk x hx hkx
    have hkx' : x.val.x > hgp.extendBBox.hspan.lb * 2 := by{
      rw[gt_iff_lt, ← Int.sub_pos, Int.pos_iff_toNat_pos, ← hkx]
      simp
    }
    let x' : hgp.GMDart := ⟨⟨x.val.x - 1, x.val.y⟩, by{
      rw[mem_GMGrid_iff]
      left
      rw[← GRectangle.mem_zoom, GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }⟩
    have hx'_mem : x' ∈ hgp.GMInner := by{
      rw[mem_GMInner_iff', GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, x', Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }
    have hx'_eta : ⟨x'.val.x, x'.val.y⟩ = x'.val := rfl
    have hx'x : ⟨x'.val.x + 1, x'.val.y⟩ = x.val := by{simp[x']}
    have term_lemma' : (x'.val.x - hgp.extendBBox.hspan.lb * 2).toNat + 1 =
      (x.val.x - hgp.extendBBox.hspan.lb * 2).toNat
    := by{
      rw[← Int.toNat_add_nat]
      · simp only [Nat.cast_one, x']
        ring_nf
      · simp only [Int.sub_nonneg, Int.le_sub_one_iff, x']
        exact hkx'
    }
    rw[← term_lemma', Nat.succ_inj] at hkx
    have hk' := hk _ hx'_mem hkx
    have hx' := x_succ_end0_eq_or_half_eq (dx := x'.val.x) (dy := x'.val.y)
    simp only [hx'x, hx'_eta] at hx'
    rcases hx' with hx' | hx'
    · {
      have ih' := GMDartHypermap_gsetoid_end0_eq _ _ hx'
      exact ih'.mp hk'
    }
    · {
      have ih' := GMDartHypermap_gsetoid_half_eq _ hx'_mem _ hx hx'
      exact ih'.mp hk'
    }
  }
}

theorem GMDartHypermap_gsetoid_C0_y {hgp : GridMapProper ab0 cm0} :
  ∀ x ∈ hgp.GMInner, x.val.x = hgp.C0.x →
    hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x := by{
  intro x hx hxc0
  have hc0x : (hgp.C0).y = hgp.extendBBox.vspan.lb * 2 := by{
    simp[C0, two_nsmul, ← mul_two]
  }
  have hx_mem := hx
  rw[mem_GMInner_iff', GRectangle.zoom] at hx
  have h := Nat.recAux (motive := fun m =>
    ∀x ∈ hgp.GMInner, x.val.x = hgp.C0.x → m = (x.val.y - hgp.extendBBox.vspan.lb * 2).toNat
    → hgp.GMDartHypermap.gsetoid ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ x)
  apply h ?_ ?_ ((x.val.y - (hgp.extendBBox).vspan.lb * 2).toNat) x hx_mem hxc0 rfl
  · {
    clear! x
    intro x hx_mem hxc0 hx0
    have hx:=hx_mem
    simp only [mem_GMInner_iff', GRectangle.mem_iff, GInterval.mem_iff, GRectangle.zoom] at hx
    symm at hx0
    rw[Int.toNat_eq_zero, sub_le_iff_le_add, zero_add] at hx0
    have hx':=le_antisymm hx0 hx.right.left
    have h' : x = ⟨hgp.C0, hgp.C0_mem_GMGrid⟩ := by{
      simp[Subtype.ext_iff, GPoint.ext_iff, hxc0, hx', C0, two_nsmul, ← mul_two]
    }
    rw[h']
  }
  · {
    clear! x
    clear h
    intro k hk x hx hxc0 hkx
    have hkx' : x.val.y > hgp.extendBBox.vspan.lb * 2 := by{
      rw[gt_iff_lt, ← Int.sub_pos, Int.pos_iff_toNat_pos, ← hkx]
      simp
    }
    let x' : hgp.GMDart := ⟨⟨x.val.x, x.val.y - 1⟩, by{
      rw[mem_GMGrid_iff]
      left
      rw[← GRectangle.mem_zoom, GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }⟩
    have hx'_mem : x' ∈ hgp.GMInner := by{
      rw[mem_GMInner_iff', GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, x', Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }
    have hx'_eta : ⟨x'.val.x, x'.val.y⟩ = x'.val := rfl
    have hx'x : ⟨x'.val.x, x'.val.y + 1⟩ = x.val := by{simp[x']}
    have term_lemma' : (x'.val.y - hgp.extendBBox.vspan.lb * 2).toNat + 1 =
      (x.val.y - hgp.extendBBox.vspan.lb * 2).toNat
    := by{
      rw[← Int.toNat_add_nat]
      · simp only [Nat.cast_one, x']
        ring_nf
      · simp only [Int.sub_nonneg, Int.le_sub_one_iff, x']
        exact hkx'
    }
    rw[← term_lemma', Nat.succ_inj] at hkx
    have hk' := hk _ hx'_mem (by{simp[x', hxc0]}) hkx
    have hx' := y_succ_end0_eq_or_half_eq (dx := x'.val.x) (dy := x'.val.y)
    simp only [hx'x, hx'_eta] at hx'
    rcases hx' with hx' | hx'
    · {
      have ih' := GMDartHypermap_gsetoid_end0_eq _ _ hx'
      exact ih'.mp hk'
    }
    · {
      have ih' := GMDartHypermap_gsetoid_half_eq _ hx'_mem _ hx hx'
      exact ih'.mp hk'
    }
  }
}
end

theorem GMDartHypermap_connected {hgp : GridMapProper ab0 cm0}
: hgp.GMDartHypermap.connected := by{
  unfold Hypermap.connected
  unfold Hypermap.gcomp
  rw[Fintype.nComp_eq_one_iff_nonempty_all]
  apply And.intro GMDart_nonempty
  have hh := GRectangle.hspan_lt_of_proper hgp.extendBBox_proper
  have hv := GRectangle.vspan_lt_of_proper hgp.extendBBox_proper
  apply GMDartHypermap_gsetoid_of_gsetoid_c0_inner
  apply GMDartHypermap_gsetoid_x
  apply GMDartHypermap_gsetoid_C0_y
}
end connected

end GridMapProper
end GridPlane
