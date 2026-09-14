import FourColorTheorem.GridPlane.Matte.Defs
import FourColorTheorem.GridPlane.Matte.Constructors.Zoom
import FourColorTheorem.GridPlane.Matte.Extension.Extend
import FourColorTheorem.GridPlane.Matte.Coarse

open Function
open Relation

namespace GridPlane
namespace Matte

-- The working rectangle shrinks, while its intersection with the disk agrees
-- with that of the original coarse rectangle.
open GRectangle in
private theorem coarse_extends_aux (m : Matte) (r r0 : GRectangle) (p : GPixel)
    (hc : m.coarseIn r0) (hm : ∃ q ∈ r, q ∈ m)
    (hp : p ∈ r) (hp0 : p ∈ r0.inner)
    (hcover : ∀ q ∈ r0, q ∈ m → q ∈ r) (hsub : r ⊆ r0) :
    m.canExtendIn r p := by {
  classical
  by_cases hpm : p ∈ m
  · exact canExtendIn_of_mem r hpm
  have htouch : touch p ⊆ r0 :=
    GRectangle.mem_inner_iff_touch_subset.mp hp0
  have quad_mem : ∀ q ∈ r0, ∀ a ∈ equad q.nodeinvDart,
      a ∈ m → q ∈ m := by{
    intro q hq a ha ham
    exact (hc q a hq (equad_nodeinvDart_half_eq ha)).mp ham
  }
  have quad_disjoint : ∀ q ∈ r0, q ∉ m →
      m.disk.Disjoint (equad q.nodeinvDart).enum := by {
    intro q hq hqm a ham haq
    exact hqm (quad_mem q hq a (mem_enum_iff.mp haq)
      ((mem_def m a).mpr ham))
  }
  have hpquad := quad_disjoint p (inner_subset hp0) hpm
  have extend_hex (d : GDart) (hd : d.half = p)
      (hh : m.disk.Disjoint (ehex d).enum)
      (he : m.canExtendIn (chopRect r (edge d)) (edge d).half) :
      m.canExtendIn r p := canExtendIn_ehex hp hd hh he
  -- A disk pixel beyond a shifted cut supplies a smaller induction problem.
  have extend_cut (d : GDart) (hd : d.half = p)
      (hout : ∃ q ∈ r0, q ∈ m ∧ q ∉ chop1 d) : m.canExtendIn r p := by {
    obtain ⟨q, hq0, hqm, hqc⟩ := hout
    have hqr := hcover q hq0 hqm
    have hp01 : p ∈ (chop1Rect r0 d).inner := by
      rw [mem_chop1Rect_inner_iff_mem_inner_chopRect, mem_chopRect_iff]
      exact ⟨hp0, hd ▸ half_mem_chop⟩
    by_cases hm01 : ∃ a ∈ chop1Rect r0 d, a ∈ m
    · have harea : (chop1Rect r d).area < r.area :=
        GRectangle.area_lt_of_missing chop1Rect_subset_rect hqr (by
          rw [mem_chop1Rect_iff]; exact fun h => hqc h.2)
      apply canExtendIn_of_subset chop1Rect_subset_rect p
      apply coarse_extends_aux m (chop1Rect r d) (chop1Rect r0 d) p
      · exact coarseIn_of_subset chop1Rect_subset_rect hc
      · obtain ⟨a, ha, ham⟩ := hm01
        rw [mem_chop1Rect_iff] at ha
        exact ⟨a, mem_chop1Rect_iff.mpr ⟨hcover a ha.1 ham, ha.2⟩, ham⟩
      · exact mem_chop1Rect_iff.mpr ⟨hp, chop_subset_chop1 (hd ▸ half_mem_chop)⟩
      · exact hp01
      · intro a ha ham
        rw [mem_chop1Rect_iff] at ha ⊢
        exact ⟨hcover a ha.1 ham, ha.2⟩
      · intro a ha
        change a ∈ chop1Rect r d at ha
        change a ∈ chop1Rect r0 d
        rw [mem_chop1Rect_iff] at ha ⊢
        exact ⟨hsub ha.1, ha.2⟩
    · have hhex : m.disk.Disjoint (GRectangle.ehex d).enum := by
        intro a ham ha
        apply hm01
        have hat : a ∈ GRectangle.touch p := by
          have hat := (mem_chopRect_iff.mp (GRectangle.mem_enum_iff.mp ha)).1
          simpa only [hd] using hat
        exact ⟨a, (GRectangle.mem_inner_iff_touch_subset.mp hp01) hat,
          (mem_def m a).mpr ham⟩
      apply extend_hex d hd hhex
      have hqcut : q ∈ chopRect r (edge d) :=
        mem_chopRect_iff.mpr ⟨hqr, mem_edge_chop_iff.mpr
          (fun h => hqc (chop_subset_chop1 h))⟩
      have harea : (chopRect r (edge d)).area < r.area :=
        area_lt_of_missing chopRect_subset_rect hp (by
          rw [mem_chopRect_iff, mem_edge_chop_iff]
          exact fun h => h.2 (hd ▸ half_mem_chop))
      apply coarse_extends_aux m (chopRect r (edge d)) r0 (edge d).half hc
      · exact ⟨q, hqcut, hqm⟩
      · exact mem_chopRect_iff.mpr
          ⟨half_mem_rect_of_edge_mem_rect_of_mem_chopRect
            (by simpa only [edge_2, hd] using hp) hqcut,
            half_mem_chop⟩
      · exact edge_half_mem_inner_of_half_mem_inner_of_mem_rect_of_notMem_chop1
          (hd.symm ▸ hp0) hq0 hqc
      · intro a ha ham
        refine mem_chopRect_iff.mpr ⟨hcover a ha ham, mem_edge_chop_iff.mpr ?_⟩
        intro hac
        exact hm01 ⟨a, mem_chop1Rect_iff.mpr ⟨ha, chop_subset_chop1 hac⟩, ham⟩
      · exact GRectangle.subset_trans chopRect_subset_rect hsub
  }
  let d := p.nodeinvDart
  have hd : d.half = p := GPoint.nodeinvDart_half
  have hnp0 : node p ∈ r0 := htouch GRectangle.node_mem_touch
  have hfep0 : face (edge p) ∈ r0 := by
    apply htouch
    rw [← node_3]
    exact GRectangle.mem_touch_of_end0_eq_end0 (by rw [node_end0, node_end0, node_end0])
  -- An occupied hexagon forces an occupied adjacent coarse quadrant.
  -- One or two occupied neighbors then allow the corresponding constructor.
  by_cases hh : ∃ a ∈ GRectangle.ehex d, a ∈ m
  · obtain ⟨a, ha, ham⟩ := hh
    have hfa : a ∈ GRectangle.equad (edge (face d)) := by
      exact (GRectangle.mem_ehex_shift_iff_mem_equad_shift.mp (Or.inl ha)).resolve_left
        (fun h => hpquad ((mem_def m a).mp ham) (GRectangle.mem_enum_iff.mpr h))
    have hfem : (edge (face d)).half ∈ m := by
      have heq : (face (edge p)).nodeinvDart = edge (face d) := nodeinvDart_face_edge
      rw [← heq] at hfa
      have h := quad_mem _ hfep0 a hfa ham
      simpa only [← heq, GPoint.nodeinvDart_half] using h
    by_cases hhf : ∃ a ∈ GRectangle.ehex (face d), a ∈ m
    · obtain ⟨b, hb, hbm⟩ := hhf
      have hshift : face (edge (face (node p).nodeinvDart)) = face d := by
        rw [← nodeinvDart_face_edge, fen_cancel]
      have hbq : b ∈ GRectangle.equad (node p).nodeinvDart := by
        exact (GRectangle.mem_ehex_shift_iff_mem_equad_shift.mp
          (Or.inr (hshift.symm ▸ hb))).resolve_right (by
            rw [← nodeinvDart_face_edge, fen_cancel]
            exact fun h => hpquad ((mem_def m b).mp hbm) (GRectangle.mem_enum_iff.mpr h))
      have hnm := quad_mem _ hnp0 b hbq hbm
      have hext : Extend2.ext2Hp m d :=
        ⟨by simpa only [d, half_edge_nodeinvDart_eq_node] using hnm, hfem, hpquad⟩
      simpa only [hd] using canExtendIn_of_extend2 hext (hd.symm ▸ hp)
    · have hdis : m.disk.Disjoint (GRectangle.ehex (face d)).enum := by
        intro b hbm hb
        exact hhf ⟨b, GRectangle.mem_enum_iff.mp hb, (mem_def m b).mpr hbm⟩
      simpa only [face_half, hd] using
        canExtendIn_of_extend1 ⟨hfem, hdis⟩ (by simpa only [face_half, hd] using hp)
  · have hdis : m.disk.Disjoint (GRectangle.ehex d).enum := by
      intro a ham ha
      exact hh ⟨a, GRectangle.mem_enum_iff.mp ha, (mem_def m a).mpr ham⟩
    by_cases ht : ∃ a ∈ GRectangle.touch p, a ∈ m
    -- If the first neighbor is absent, coarseness supplies the opposite one.
    · apply extend_hex d hd hdis
      rw [half_edge_nodeinvDart_eq_node]
      by_cases hnm : node p ∈ m
      · exact canExtendIn_of_mem _ hnm
      have hnquad := quad_disjoint _ hnp0 hnm
      obtain ⟨a, hat, ham⟩ := ht
      have hn2m : node (node p) ∈ m := by
        apply (hc _ a (htouch node_node_mem_touch) ?_).mp ham
        apply touch_remaining_half hat
        · exact fun ha => hh ⟨a, ha, ham⟩
        · exact fun ha => hnquad ((mem_def m a).mp ham) (GRectangle.mem_enum_iff.mpr ha)
      have hnhex : m.disk.Disjoint (GRectangle.ehex (node p).nodeinvDart).enum := by
        intro b hbm hb
        have hb' := GRectangle.mem_ehex_shift_iff_mem_equad_shift.mp
          (Or.inl (GRectangle.mem_enum_iff.mp hb))
        rcases hb' with hb' | hb'
        · exact hnquad hbm (GRectangle.mem_enum_iff.mpr hb')
        · rw [← nodeinvDart_face_edge, fen_cancel] at hb'
          exact hpquad hbm (GRectangle.mem_enum_iff.mpr hb')
      have hnr : node p ∈ r := node_mem_of_mem_of_node_2_mem hp
        (hcover _ (htouch node_node_mem_touch) hn2m)
      have hncut : (node p).nodeinvDart.half ∈ chopRect r (edge d) := by
        rw [GPoint.nodeinvDart_half, mem_chopRect_iff]
        exact ⟨hnr, by rw [← half_edge_nodeinvDart_eq_node]; exact half_mem_chop⟩
      simpa only [GPoint.nodeinvDart_half] using
        canExtendIn_of_extend1 ⟨by simpa only [half_edge_nodeinvDart_eq_node] using hn2m,
          hnhex⟩ hncut
    -- With no disk pixel touching p, some shifted cut separates p from the disk.
    · obtain ⟨a, har, ham⟩ := hm
      have hat : a ∉ GRectangle.touch d.half := by
        rw [hd]
        exact fun ha => ht ⟨a, ha, ham⟩
      rw [touch_iff_four_chop1] at hat
      by_cases h0 : a ∈ chop1 d
      · by_cases h1 : a ∈ chop1 (face d)
        · by_cases h2 : a ∈ chop1 (face (face d))
          · exact extend_cut _ (by rw [face_half, face_half, face_half, hd])
              ⟨a, hsub har, ham, fun h3 => hat ⟨h0, h1, h2, h3⟩⟩
          · exact extend_cut _ (by rw [face_half, face_half, hd]) ⟨a, hsub har, ham, h2⟩
        · exact extend_cut _ (by rw [face_half, hd]) ⟨a, hsub har, ham, h1⟩
      · exact extend_cut _ hd ⟨a, hsub har, ham, h0⟩
}
termination_by r.area
decreasing_by all_goals assumption

theorem canExtendIn_of_coarseIn {m : Matte} {r : GRectangle}
    (r0Emh : m.coarseIn r) (m_r : ∃ p ∈ r, p ∈ m) :
    ∀ p ∈ r.inner, m.canExtendIn r p := by {
  intro p hp
  exact coarse_extends_aux m r r p r0Emh m_r (GRectangle.inner_subset hp) hp
    (fun _ h _ => h) (GRectangle.subset_refl r)
}

end Matte
end GridPlane
