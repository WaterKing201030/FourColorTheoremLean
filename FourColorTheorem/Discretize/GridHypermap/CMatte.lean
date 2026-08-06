import FourColorTheorem.Reals.Grid.Matte
import FourColorTheorem.Hypermap.Basic

namespace GridPlane

abbrev AdjIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev AdjBox (n : ℕ) := AdjIndex n → GRectangle
abbrev CMatte (n : ℕ) := Fin n → Matte
@[inline] instance AdjIndex.instFintype {n : ℕ} : Fintype (AdjIndex n) := by{
  classical
  apply Subtype.fintype
}
def AdjIndex.Mem {n : ℕ} (I : AdjIndex n) (x : Fin n) : Prop := x = I.val.1 ∨ x = I.val.2
@[inline] instance AdjIndex.instMembership {n : ℕ}
  : Membership (Fin n) (AdjIndex n) where mem := Mem
theorem AdjIndex.mem_iff {n : ℕ} (I : AdjIndex n) (x : Fin n)
  : x ∈ I ↔ x = I.val.1 ∨ x = I.val.2 := by rfl

def CMatte.proper {n : ℕ} (cm : CMatte n) :=
  -- 任意两个matte不存在相同像素
  ∀i j, (∃k ∈ cm i, k ∈ cm j) → i = j
def AdjBox.proper {n : ℕ} (ab : AdjBox n) :=
  -- ab提供相邻关系对应的长方形；若两个长方形存在相同像素，则表示的是同一个相邻关系
  -- 也就是任意相邻关系对应的长方形不相交
  ∀ e f p, p ∈ ab e → p ∈ ab f → e = f
def adjBox_cMatte_proper {n : ℕ} (ab : AdjBox n) (cm : CMatte n) :=
  -- 对ab中所有表示相邻的非空长方形
  -- 1. 对于相邻两侧的编号之一i，cm i和ab e的内部有交集
  -- 2. 若cm i和ab e有交集，则i在e内部
  ∀e i, (ab e).proper →
    (i ∈ e → ∃p ∈ cm i, p ∈ (ab e).inner)
     ∧ ((∃p ∈ cm i, p ∈ ab e) → i ∈ e)

structure GridMapProper {n : ℕ} (ab : AdjBox n) (cm : CMatte n) where
  ab_proper : ab.proper
  cm_proper : cm.proper
  abcm_proper : adjBox_cMatte_proper ab cm

def CMatte.zoom {n : ℕ} (cm : CMatte n) : CMatte n :=
  fun i => (cm i).zoom
def AdjBox.zoom {n : ℕ} (ab : AdjBox n) : AdjBox n :=
  fun e => (ab e).zoom

theorem CMatte.proper.zoom {n : ℕ} {cm : CMatte n} (cmP : cm.proper)
  : cm.zoom.proper := by {
    intro i j ⟨k, hki, hkj⟩
    rw[CMatte.zoom, Matte.mem_zoom_iff] at hki hkj
    exact cmP i j ⟨k.half, hki, hkj⟩
  }
theorem AdjBox.proper.zoom {n : ℕ} {ab : AdjBox n} (abP : ab.proper)
  : ab.zoom.proper := by{
    intro e f p hpe hpf
    rw[AdjBox.zoom, GRectangle.mem_zoom] at hpe hpf
    exact abP e f p.half hpe hpf
  }
theorem AdjBox.zoom_proper_rect_iff {n : ℕ} {ab : AdjBox n} {e : AdjIndex n}
  : (ab.zoom e).proper ↔ (ab e).proper := by{
    rw[zoom, GRectangle.zoom_proper_iff]
  }
theorem adjBox_cMatte_proper.zoom {n : ℕ} {ab : AdjBox n} {cm : CMatte n}
  (abcmP : adjBox_cMatte_proper ab cm) : adjBox_cMatte_proper ab.zoom cm.zoom := by{
    intro e i hei
    rw[AdjBox.zoom_proper_rect_iff] at hei
    have ⟨b_m, e_i⟩ := abcmP  e i hei
    constructor
    · {
      intro hie
      have ⟨p, hpm, hpb⟩:=b_m hie
      simp only [CMatte.zoom, AdjBox.zoom, Matte.mem_zoom_iff]
      use 2 • p
      simp only [GPoint.half_double, hpm, true_and]
      apply GRectangle.inner_zoom_subset_zoom_inner
      simp only [GRectangle.mem_zoom, GPoint.half_double, hpb]
    }
    · {
      intro ⟨p, hpm, hpb⟩
      rw[CMatte.zoom, Matte.mem_zoom_iff] at hpm
      rw[AdjBox.zoom, GRectangle.mem_zoom] at hpb
      exact e_i ⟨p.half, hpm, hpb⟩
    }
  }

theorem gridMapProper.zoom {n : ℕ} {ab : AdjBox n} {cm : CMatte n}
  (h : GridMapProper ab cm) : GridMapProper ab.zoom cm.zoom := by{
    constructor
    · exact h.ab_proper.zoom
    · exact h.cm_proper.zoom
    · exact h.abcm_proper.zoom
  }

section
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

lemma exists_extends_adj_cMatte (hgp : GridMapProper ab0 cm0)
  : ∃cm : CMatte n, cm.proper ∧
  ∀e : AdjIndex n, (ab0 e).proper → (cm e.val.1).adj (cm e.val.2) := by{
  have ⟨ab0P, cm0P, abcm0P⟩ := hgp
  let cm := cm0.zoom
  let ab := ab0.zoom
  have cmP : cm.proper := cm0P.zoom
  have abP : ab.proper := ab0P.zoom
  have ab0_adj : ∀e, (ab e).proper ↔ (ab0 e).proper := by
    intro e; apply AdjBox.zoom_proper_rect_iff
  let cm_apart_on (cm' : CMatte n) (e : AdjIndex n) :=
    (ab e).proper ∧ ¬(cm' e.val.1).adj (cm' e.val.2)
  let coarse_inner (b : GRectangle) (m : Matte) :=
    m.coarseIn b.toRegion ∧ ∃p ∈ b.inner, p ∈ m
  have cm_apart_contra {e : AdjIndex n} {i : Fin n} :
    cm_apart_on cm e → (i ∈ e → coarse_inner (ab e) (cm i)) ∧ ((∃p ∈ ab e, p ∈ cm i) → i ∈ e) := by{
      intro ⟨h0, h1⟩
      have h0':=(ab0_adj _).mp h0
      have ⟨b_m, e_i⟩ := abcm0P _ i h0'
      constructor
      · {
        intro hie
        have ⟨p, hpm, hpb⟩:=b_m hie
        apply And.intro Matte.coarseIn_zoom
        use 2 • p
        unfold ab cm
        rw[CMatte.zoom, AdjBox.zoom, Matte.mem_zoom_iff, GPoint.half_double]
        refine ⟨?_, hpm⟩
        apply GRectangle.inner_zoom_subset_zoom_inner
        rw[GRectangle.mem_zoom, GPoint.half_double]
        exact hpb
      }
      · {
        intro ⟨p, hpb, hpm⟩
        unfold ab AdjBox.zoom at hpb
        unfold cm CMatte.zoom at hpm
        rw[GRectangle.mem_zoom] at hpb
        rw[Matte.mem_zoom_iff] at hpm
        exact e_i ⟨p.half, hpm, hpb⟩
      }
    }
  generalize hcm : cm = cm
  simp only [hcm] at *
  clear! cm0
  clear hcm
  let BadAdjIndex (cm' : CMatte n) := {e // cm_apart_on cm' e}
  let BadAdjIndex_instFintype (cm' : CMatte n) : Fintype (BadAdjIndex cm') := by{
    classical
    apply Subtype.fintype
  }
  let BadAdjIndexCard (cm' : CMatte n) := Fintype.card (BadAdjIndex cm')
  generalize hnba : BadAdjIndexCard cm = nba
  induction nba using Nat.strongRec generalizing cm with
  | ind nba IHn => {
    rcases em (∀e, ¬cm_apart_on cm e) with cm_meet | cm_meet'
    · {
      refine ⟨cm, cmP, ?_⟩
      intro e he
      have hcm := cm_meet e
      unfold cm_apart_on at hcm
      simp only [ab0_adj, he, true_and, not_not] at hcm
      exact hcm
    }
    simp only [not_forall, not_not] at cm_meet'
    have ⟨e, cm'e⟩:=cm_meet'
    have ⟨cme_ab, ab_e⟩:=forall_and.mp (fun i => @cm_apart_contra e i cm'e)
    have e1'2 := e.property
    have cm1ab : ∃p ∈ (ab e).inner, p ∈ cm e.val.1 := by{
      exact (cme_ab e.val.1 (by{simp[AdjIndex.mem_iff]})).right
    }
    have ⟨cm2ref, cm2ab'⟩:=cme_ab e.val.2 (by{simp[AdjIndex.mem_iff]})
    have cm2ab : ∃p ∈ ab e, p ∈ cm e.val.2 := by{
      have ⟨p, hp0, hp1⟩:=cm2ab'
      exact ⟨p, GRectangle.inner_subset hp0, hp1⟩
    }
    have cm2'1 := ne_of_lt e1'2 ∘ cmP e.val.1 e.val.2
    simp only [imp_false, not_exists, not_and, Matte.mem_iff] at cm2'1
    rw[← List.Disjoint] at cm2'1
    symm at cm2'1
    have ⟨cm2, cm2cm, ab_cm2, cm12⟩:=Matte.extend_adj cm2ref cm2ab cm1ab cm2'1
    let xcm : CMatte n := fun i => if i = e.val.2 then cm2 else cm i
    have xcme2 : xcm e.val.2 = cm2 := by{simp[xcm]}
    have xcm'e2 {i : Fin n} (hi : i ≠ e.val.2) : xcm i = cm i := by{simp[xcm, hi]}
    have xcm_e : ¬cm_apart_on xcm e := by{
      unfold cm_apart_on
      rw[not_and, not_not]
      simp[cm'e.left]
      simp[xcme2, xcm'e2 (ne_of_lt e1'2), cm12]
    }
    have has'cm2 {i : Fin n} (e2'i : i ≠ e.val.2) : cm2.disk.Disjoint (cm i).disk := by{
      rw[List.Disjoint]
      intro p hp2 hpi
      have hp2' := ab_cm2 (Matte.mem_toRegion_iff_mem.mpr (Matte.mem_iff.mpr hp2))
      rw[Set.mem_diff, Set.mem_union] at hp2'
      simp only [Matte.mem_toRegion_iff_mem] at hp2'
      have e1'i : i ≠ e.val.1 := fun e1i => (e1i ▸ hp2'.right) hpi
      have e'i : i ∉ e := by{simp[AdjIndex.mem_iff, e2'i, e1'i]}
      have ab'i : (ab e).enum.Disjoint (cm i).disk := by{
        have ab_e' := e'i ∘ ab_e i
        simp only[← GRectangle.mem_enum_iff, Matte.mem_iff, imp_false, not_exists, not_and] at ab_e'
        exact ab_e'
      }
      have cm2'i : (cm e.val.2).disk.Disjoint (cm i).disk := by{
        have cmP' := e2'i.symm ∘ cmP e.val.2 i
        simp only [imp_false, not_exists, not_and, Matte.mem_iff] at cmP'
        exact cmP'
      }
      symm at ab'i cm2'i
      rw[← GRectangle.mem_iff_toRegion, ← GRectangle.mem_enum_iff] at hp2'
      exact hp2'.left.elim
        (ab'i hpi)
        (cm2'i hpi)
    }
    have madj_cm2 {i : Fin n} (e2'i : i ≠ e.val.2) :
      (cm i).adj (cm e.val.2) → (cm i).adj cm2 := by{
      intro ⟨d, cm2ed, cmi_d⟩
      refine ⟨d, ?_, cmi_d⟩
      rw[Matte.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at *
      apply And.intro (cm2cm cm2ed.left)
      apply List.Disjoint.symm (has'cm2 e2'i) cmi_d.left
    }
    have xcm'cm : ∀e, cm_apart_on xcm e → cm_apart_on cm e := by{
      intro f ⟨hf0, hf1⟩
      apply And.intro hf0
      rcases eq_or_ne f.val.1 e.val.2 with e2f1 | e2'f1
      · {
        rw[e2f1] at hf1
        simp only [xcme2, xcm'e2 (e2f1 ▸ ne_of_gt f.prop)] at hf1
        intro h
        apply hf1
        symm
        apply madj_cm2 (e2f1 ▸ ne_of_gt f.prop)
        rw[←e2f1]
        symm
        exact h
      }
      rcases eq_or_ne f.val.2 e.val.2 with e2f2 | e2'f2
      · {
        rw[e2f2] at hf1
        simp only [xcme2, xcm'e2 (e2f2 ▸ ne_of_lt f.prop)] at hf1
        intro h
        apply hf1
        apply madj_cm2 (e2f2 ▸ ne_of_lt f.prop) (e2f2 ▸ h)
      }
      unfold xcm at hf1
      simp[e2'f1, e2'f2] at hf1
      simp[hf1]
    }
    have xcmP : xcm.proper := by{
      intro i j ⟨k, ki, kj⟩
      apply of_not_not
      intro hij
      rcases eq_or_ne i e.val.2 with e2i | e2'i
      · {
        simp only [e2i, xcme2] at ki
        simp only [xcm'e2 (Ne.symm (e2i ▸ hij))] at kj
        exact @has'cm2 j (Ne.symm (e2i ▸ hij)) k ki kj
      }
      rcases eq_or_ne j e.val.2 with e2j | e2'j
      · {
        simp only [e2j, xcme2] at kj
        simp only [xcm'e2 (e2j ▸ hij)] at ki
        exact @has'cm2 i (e2j ▸ hij) k kj ki
      }
      simp only [xcm'e2 e2'i, xcm'e2 e2'j] at ki kj
      exact hij (cmP i j ⟨k, ki, kj⟩)
    }
    have mlt : BadAdjIndexCard xcm < nba := by{
      rw[← hnba]
      unfold BadAdjIndexCard
      let f :BadAdjIndex xcm → BadAdjIndex cm:= fun e => ⟨e.val, xcm'cm e.val e.prop⟩
      apply Fintype.card_lt_of_injective_not_surjective f
      · {
        intro e1 e2
        simp only [f]
        rw[Subtype.ext_iff]
        simp only
        apply Subtype.ext
      }
      · {
        unfold Function.Surjective
        simp only [not_forall, not_exists]
        use ⟨e, cm'e⟩
        intro ⟨x, hx⟩
        simp only [f]
        rw[Subtype.ext_iff]
        simp only
        intro hxe
        exact xcm_e (hxe ▸ hx)
      }
    }
    apply (IHn _ mlt _ xcmP · rfl)
    intro f i xcm'f
    have bf'e {p : GPoint} (hpabe : p ∈ ab e): p ∉ ab f := by{
      intro hpabf
      exact xcm_e (abP _ _ _ hpabe hpabf ▸ xcm'f)
    }
    have xcm'cm' := cm_apart_contra (e:=f) (i:=i) (xcm'cm f xcm'f)
    rcases ne_or_eq i e.val.2 with e2'i | e2i
    · simp only [xcm'e2 e2'i]; exact xcm'cm'
    simp only [e2i, xcme2]
    constructor
    · {
      intro he2f
      unfold coarse_inner
      have ⟨cm2ref_bf, cm2_bf⟩:=xcm'cm'.left (e2i ▸ he2f)
      constructor
      · {
        intro p bf_p q Dpq
        have IHpq :(∀p ∈ (ab f).toRegion, ∀q, q.half = p.half → p ∈ cm2 → q ∈ cm2)
          → (q ∈ cm2 ↔ p ∈ cm2) := by{
          intro h
          refine ⟨?_, h _ bf_p _ Dpq⟩
          apply h
          · {
            revert bf_p
            simp[AdjBox.zoom, ← GRectangle.mem_iff_toRegion, GRectangle.mem_zoom, Dpq,
              ab]
          }
          · exact Dpq.symm
        }
        apply IHpq
        clear! p q
        intro p bf_p q Dpq hp2
        have ⟨h0, h1⟩:=ab_cm2 (Matte.mem_toRegion_iff_mem.mpr hp2)
        have cm2ref_bf' := e2i ▸ cm2ref_bf _ bf_p q Dpq
        rw[Set.mem_union, Matte.mem_toRegion_iff_mem, ←cm2ref_bf'] at h0
        rw[← GRectangle.mem_iff_toRegion] at bf_p h0
        have bf'e' := imp_false.mp (bf'e · bf_p)
        have h0':=h0.resolve_left bf'e'
        exact cm2cm h0'
      }
      · {
        have ⟨p, hp0, hp1⟩:=cm2_bf
        exact ⟨p, hp0, cm2cm (e2i ▸ hp1)⟩
      }
    }
    · {
      intro ⟨p, hp0, hp1⟩
      have bf'e' := imp_false.mp (bf'e · hp0)
      have ab_cm2' := (ab_cm2 (Matte.mem_toRegion_iff_mem.mpr hp1)).left.resolve_left bf'e'
      rw[Matte.mem_toRegion_iff_mem] at ab_cm2'
      exact e2i ▸ (xcm'cm'.right ⟨p, hp0, e2i ▸ ab_cm2'⟩)
    }
  }
}

namespace GridMapProper
noncomputable def extendCMatte (hgp : GridMapProper ab0 cm0) : CMatte n :=
  Classical.choose (exists_extends_adj_cMatte hgp)

theorem extendCMatte_proper {hgp : GridMapProper ab0 cm0} : hgp.extendCMatte.proper := by{
  have h := Classical.choose_spec (exists_extends_adj_cMatte hgp)
  exact h.left
}
theorem extendCMatte_proper_adj {hgp : GridMapProper ab0 cm0}
  {e : AdjIndex n} (ep : (ab0 e).proper)
: (hgp.extendCMatte e.val.1).adj (hgp.extendCMatte e.val.2) := by{
  have h := Classical.choose_spec (exists_extends_adj_cMatte hgp)
  have h' := h.right _ ep
  exact h'
}

noncomputable def extendBBox (hgp : GridMapProper ab0 cm0) : GRectangle :=
  ((List.finRange n).flatMap (fun i => (hgp.extendCMatte i).disk)).foldl
    GRectangle.extend ⟨⟨0, 1⟩, ⟨0, 1⟩⟩

theorem CM_subset_CMBBox {hgp : GridMapProper ab0 cm0} {i : Fin n}
  : (hgp.extendCMatte i).toRegion ⊆ hgp.extendBBox.toRegion := by{
    intro p mi_p
    rw[extendBBox]
    have mi_p' : p ∈ (List.finRange n).flatMap (fun i => (hgp.extendCMatte i).disk) := by{
      simp only [List.mem_flatMap, List.mem_finRange, true_and]
      use i
      exact mi_p
    }
    generalize he : List.flatMap (fun i ↦ (hgp.extendCMatte i).disk) (List.finRange n) = e
    rw[he] at mi_p'
    clear! n
    generalize
      ({ hspan := { lb := 0, ub := 1 }, vspan := { lb := 0, ub := 1 } } : GRectangle) = r
    have h0 : ∀r e,  p ∈ r → p ∈ (List.foldl GRectangle.extend r e).toRegion := by{
      intro r e
      clear mi_p'
      induction e generalizing r with
      | nil => simp[GRectangle.mem_iff_toRegion]
      | cons a e' ih => {
        intro hr
        rw[List.foldl_cons]
        apply ih
        apply GRectangle.subset_extend
        apply hr
      }
    }
    induction e generalizing r with
    | nil => simp at mi_p'
    | cons a e' ih => {
      rw[List.mem_cons] at mi_p'
      rw[List.foldl_cons]
      rcases mi_p' with mi_p' | mi_p'
      · {
        rw[←mi_p']
        apply h0
        apply GRectangle.mem_extend
      }
      · apply ih mi_p'
    }
  }

theorem extendBBox_proper {hgp : GridMapProper ab0 cm0} : hgp.extendBBox.proper := by{
  rw[extendBBox]
  generalize (List.flatMap (fun i ↦ (hgp.extendCMatte i).disk) (List.finRange n)) = e
  generalize hr : (⟨⟨0, 1⟩, ⟨0, 1⟩⟩ : GRectangle) = r
  have hr' : r.proper := by{
    apply GRectangle.proper_of_mem (p:=⟨0, 0⟩)
    rw[← hr]
    trivial
  }
  clear hr
  induction e generalizing r with
  | nil => simp[hr']
  | cons a e' ih => {
    apply ih
    apply GRectangle.proper_of_subset GRectangle.subset_extend
    exact hr'
  }
}

theorem extendBBox_proper_exists {hgp : GridMapProper ab0 cm0}
: ((hgp.extendBBox).width > 0 ∧ (hgp.extendBBox).height > 0)
  ∧ ∃p0, (∀x y : ℤ, p0 + ⟨x, y⟩ ∈ hgp.extendBBox ↔
    (0 ≤ x ∧ x < (hgp.extendBBox).width) ∧ (0 ≤ y ∧ y < (hgp.extendBBox).height)) ∧
    ∀p ∈ hgp.extendBBox, ∃x y : ℕ, p = p0 + ⟨x, y⟩ ∧ x < (hgp.extendBBox).width
      ∧ y < (hgp.extendBBox).height := by{
  apply And.intro (GRectangle.proper_iff_pos.mp hgp.extendBBox_proper)
  apply GRectangle.exists_ld_corner_of_proper hgp.extendBBox_proper
}
end GridMapProper
end

end GridPlane
