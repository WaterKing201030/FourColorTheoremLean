import FourColorTheorem.Reals.Grid.Matte
import Mathlib.Data.Fintype.Prod
import FourColorTheorem.Hypermap.Basic
import FourColorTheorem.Hypermap.Snip

open Relation
open Function

namespace GridPlane

abbrev AdjIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev AdjBox (n : ℕ) := AdjIndex n → GRectangle
abbrev CMatte (n : ℕ) := Fin n → Matte

@[inline] instance AdjIndex.instFintype {n : ℕ} : Fintype (AdjIndex n) := by{
  classical
  apply Subtype.fintype
}

def CMatte.proper {n : ℕ} (cm : CMatte n) :=
  -- 任意两个matte不存在相同像素
  ∀i j, (∃k ∈ cm i, k ∈ cm j) → i = j
def AdjBox.proper {n : ℕ} (ab : AdjBox n) :=
  -- ab提供相邻关系对应的长方形；若两个长方形存在相同像素，则表示的是同一个相邻关系
  -- 也就是任意相邻关系对应的长方形不相交
  ∀ e f p, p ∈ ab e → p ∈ ab f → e = f

def AdjIndex.Mem {n : ℕ} (I : AdjIndex n) (x : Fin n) : Prop := x = I.val.1 ∨ x = I.val.2
@[inline] instance AdjIndex.instMembership {n : ℕ}
  : Membership (Fin n) (AdjIndex n) where mem := Mem
theorem AdjIndex.mem_iff {n : ℕ} (I : AdjIndex n) (x : Fin n)
  : x ∈ I ↔ x = I.val.1 ∨ x = I.val.2 := by rfl

def adjBox_cMatte_proper {n : ℕ} (ab : AdjBox n) (cm : CMatte n) :=
  -- 对ab中所有表示相邻的非空长方形
  -- 1. 对于相邻两侧的编号之一i，cm i和ab e的内部有交集
  -- 2. 若cm i和ab e有交集，则i在e内部
  ∀e i, (ab e).proper →
    (i ∈ e → ∃p ∈ cm i, p ∈ (ab e).inner)
     ∧ ((∃p ∈ cm i, p ∈ ab e) → i ∈ e)

def CMatte.zoom {n : ℕ} (cm : CMatte n) : CMatte n :=
  fun i => (cm i).zoom
def AdjBox.zoom {n : ℕ} (ab : AdjBox n) : AdjBox n :=
  fun e => (ab e).zoom

theorem CMatte.zoom_proper {n : ℕ} {cm : CMatte n} (cmP : cm.proper)
  : cm.zoom.proper := by {
    intro i j ⟨k, hki, hkj⟩
    rw[zoom, Matte.mem_zoom_iff] at hki hkj
    exact cmP i j ⟨k.half, hki, hkj⟩
  }
theorem AdjBox.zoom_proper {n : ℕ} {ab : AdjBox n} (abP : ab.proper)
  : ab.zoom.proper := by{
    intro e f p hpe hpf
    rw[zoom, GRectangle.mem_zoom] at hpe hpf
    exact abP e f p.half hpe hpf
  }
theorem AdjBox.zoom_proper_rect_iff {n : ℕ} {ab : AdjBox n} {e : AdjIndex n}
  : (ab.zoom e).proper ↔ (ab e).proper := by{
    rw[zoom, GRectangle.zoom_proper_iff]
  }
theorem zoom_adjBox_cMatte_proper {n : ℕ} {ab : AdjBox n} {cm : CMatte n}
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

section
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}
variable (ab0P : ab0.proper) (cm0P : cm0.proper)
variable (abcm0P : adjBox_cMatte_proper ab0 cm0)
include ab0P cm0P abcm0P

theorem exists_extends_adj_cMatte : ∃cm : CMatte n, cm.proper ∧
  ∀e : AdjIndex n, (ab0 e).proper → (cm e.val.1).adj (cm e.val.2) := by{
  let cm := cm0.zoom
  let ab := ab0.zoom
  have cmP : cm.proper := cm0.zoom_proper cm0P
  have abP : ab.proper := ab0.zoom_proper ab0P
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
end

section
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}
variable {ab0P : ab0.proper} {cm0P : cm0.proper}
variable {abcm0P : adjBox_cMatte_proper ab0 cm0}
include ab0P cm0P abcm0P
noncomputable def CM' : CMatte n :=
  Classical.choose (exists_extends_adj_cMatte ab0P cm0P abcm0P)
local notation "CM" => @CM' _ _ _ ab0P cm0P abcm0P
theorem CMP : (CM).proper := by{
  have h := Classical.choose_spec (exists_extends_adj_cMatte ab0P cm0P abcm0P)
  exact h.left
}
theorem ab_CMP {e : AdjIndex n} (ep : (ab0 e).proper) :
  (CM e.val.1).adj (CM e.val.2) := by{
    have h := Classical.choose_spec (exists_extends_adj_cMatte ab0P cm0P abcm0P)
    have h' := h.right _ ep
    exact h'
  }
noncomputable def CMBBox' : GRectangle :=
  ((List.finRange n).flatMap (fun i => (CM i).disk)).foldl
    GRectangle.extend ⟨⟨0, 1⟩, ⟨0, 1⟩⟩
local notation "CMBBox" => @CMBBox' _ _ _ ab0P cm0P abcm0P

theorem CM_subset_CMBBox {i : Fin n}
  : (CM i).toRegion ⊆ (CMBBox).toRegion := by{
    intro p mi_p
    rw[CMBBox']
    have mi_p' : p ∈ (List.finRange n).flatMap (fun i => (CM i).disk) := by{
      simp only [List.mem_flatMap, List.mem_finRange, true_and]
      use i
      exact mi_p
    }
    generalize he : List.flatMap (fun i ↦ (CM i).disk) (List.finRange n) = e
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

theorem CMBBox_proper : (CMBBox).proper := by{
  rw[CMBBox']
  generalize (List.flatMap (fun i ↦ (CM i).disk) (List.finRange n)) = e
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

theorem CMBBox_proper_exists : ((CMBBox).width > 0 ∧ (CMBBox).height > 0)
  ∧ ∃p0, (∀x y : ℤ, p0 + ⟨x, y⟩ ∈ CMBBox ↔
    (0 ≤ x ∧ x < (CMBBox).width) ∧ (0 ≤ y ∧ y < (CMBBox).height)) ∧
    ∀p ∈ CMBBox, ∃x y : ℕ, p = p0 + ⟨x, y⟩ ∧ x < (CMBBox).width ∧ y < (CMBBox).height := by{
  apply And.intro (GRectangle.proper_iff_pos.mp CMBBox_proper)
  apply GRectangle.exists_ld_corner_of_proper CMBBox_proper
}

noncomputable def GMGrid' : List GDart :=
  let inner : GRectangle := (CMBBox).zoom
  inner.enum ++ inner.enum.map edge
local notation "GMGrid" => @GMGrid' _ _ _ ab0P cm0P abcm0P

theorem mem_GMGrid_iff {d : GDart} : d ∈ GMGrid ↔ d.half ∈ CMBBox ∨ (edge d).half ∈ CMBBox
:= by{
  unfold GMGrid'
  rw[List.mem_append]
  apply or_congr
  · rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom]
  · {
    nth_rw 1 [← edge_2 (d:=d)]
    rw[List.mem_map_of_injective edge_injective]
    rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom]
  }
}
theorem edge_mem_GMGrid_iff {d : GDart} : edge d ∈ GMGrid ↔ d ∈ GMGrid := by{
  rw[mem_GMGrid_iff, mem_GMGrid_iff, or_comm, edge_2]
}

abbrev GMDart' := {d : GDart // d ∈ GMGrid}
local notation "GMDart" => @GMDart' _ _ _ ab0P cm0P abcm0P

def GMedge' : GMDart → GMDart :=
  fun ⟨d, hd⟩ => ⟨edge d, edge_mem_GMGrid_iff.mpr hd⟩
local notation "GMedge" => @GMedge' _ _ _ ab0P cm0P abcm0P
theorem GMedge_2 {d : GMDart} : GMedge (GMedge d) = d := by{
  match d with | ⟨d, hd⟩ => simp[GMedge', edge_2]
}

theorem GMDart_nonempty : Nonempty GMDart := by{
  refine Nonempty.intro ⟨2 • ⟨(CMBBox).hspan.lb, (CMBBox).vspan.lb⟩, ?_⟩
  rw[mem_GMGrid_iff]
  left
  rw[GPoint.half_double]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GRectangle.hspan_lt_of_proper CMBBox_proper,
  GRectangle.vspan_lt_of_proper CMBBox_proper]
}

noncomputable def GMface' (u : GMDart) : GMDart :=
  let t := [node (node (node u)), node (node u), node u].find?
    (· ∈ GMGrid)
  ⟨t.getD u.val, by{
    match ht : t with
    | none => exact u.prop
    | some d => {
      have ht':=(List.find?_eq_some_iff_getElem.mp ht).left
      rw[Option.getD_some]
      rw[decide_eq_true_eq] at ht'
      exact ht'
    }
  }⟩
local notation "GMface" => @GMface' _ _ _ ab0P cm0P abcm0P

noncomputable def GMnode' (u : GMDart) : GMDart :=
  let t := [edge (node u), edge (node (node u)), edge (node (node (node u)))].find?
    (· ∈ GMGrid)
  ⟨t.getD u.val, by{
    match ht : t with
    | none => exact u.prop
    | some d => {
      have ht':=(List.find?_eq_some_iff_getElem.mp ht).left
      rw[Option.getD_some]
      rw[decide_eq_true_eq] at ht'
      exact ht'
    }
  }⟩
local notation "GMnode" => @GMnode' _ _ _ ab0P cm0P abcm0P

theorem GM_enf_cancel : ∀u : GMDart, GMedge (GMnode (GMface u)) = u := by{
  intro u
  match hu : u with | ⟨d, hd⟩ => {
    rcases em (node (node (node d)) ∈ GMGrid) with h2f | h2f
    · {
      have h2f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node (node (node d))
        := List.find?_cons_of_pos (decide_eq_true h2f)
      simp only [GMface', h2f', Option.getD_some]
      have h2n : [edge d, edge (node d), edge (node (node d))].find?
        (fun x ↦ decide (x ∈ GMGrid)) = edge d := by{
          apply List.find?_cons_of_pos
          simp[edge_mem_GMGrid_iff, hd]
        }
      simp only[GMnode', node_4, h2n, Option.getD_some, GMedge', edge_2]
    }
    have h2n : edge (node (node (node d))) ∉ GMGrid := by{
      rw[edge_mem_GMGrid_iff]; exact h2f
    }
    rcases em (node (node d) ∈ GMGrid) with h1f | h1f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node (node d)
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_pos]; simp[h1f]
        · simp[h2f]
      }
      simp only [GMface', h1f', Option.getD_some]
      have h1n : [edge (node (node (node d))), edge d, edge (node d)].find?
        (fun x ↦ decide (x ∈ GMGrid)) = edge d := by{
          rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_pos]; simp[edge_mem_GMGrid_iff, hd]
          · simp[h2n]
        }
      simp only[GMnode', node_4, h1n, Option.getD_some, GMedge', edge_2]
    }
    have h1n : edge (node (node d)) ∉ GMGrid := by{
      rw[edge_mem_GMGrid_iff]; exact h1f
    }
    rcases em (node d ∈ GMGrid) with h0f | h0f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node d
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_pos]; simp[h0f]
          · simp[h1f]
        · simp[h2f]
      }
      simp only [GMface', h1f', Option.getD_some]
      have h1n : [edge (node (node d)), edge (node (node (node d))), edge d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = edge d := by{
          rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_neg]
            · rw[List.find?_cons_of_pos]; simp[edge_mem_GMGrid_iff, hd]
            · simp[h2n]
          · simp[h1n]
        }
      simp only[GMnode', node_4, h1n, Option.getD_some, GMedge', edge_2]
    }
    have h0n : edge (node d) ∉ GMGrid := by{
      rw[edge_mem_GMGrid_iff]
      exact h0f
    }
    simp only [←face_3, mem_GMGrid_iff, face_half, not_or] at h0n
    rw[node_3, mem_GMGrid_iff, face_half, not_or] at h2f
    rw[mem_GMGrid_iff] at hd
    exfalso
    apply hd.elim h0n.left h2f.left
  }
}

@[reducible] noncomputable def GMDartHypermap' : Hypermap GMDart :=
  ⟨GMedge, GMnode, GMface, GM_enf_cancel⟩
local notation "GMDartHypermap" => @GMDartHypermap' _ _ _ ab0P cm0P abcm0P

theorem GMDartHypermap_plain : (GMDartHypermap).plain := by{
  intro p _
  rw[Set.mem_setOf, minimalPeriod_eq_two_iff]
  change GMedge (GMedge p) = p ∧ GMedge p ≠ p
  rw [GMedge_2]
  simp only [true_and]
  simp[GMedge', Subtype.ext_iff, edge_ne]
}

def GMInner' : Set GMDart :=
  {u | u.val.half ∈ CMBBox}
local notation "GMInner" => @GMInner' _ _ _ ab0P cm0P abcm0P
theorem mem_GMInner_iff {u : GMDart} : u ∈ GMInner ↔ u.val.half ∈ CMBBox := by{
  unfold GMInner'
  rw[Set.mem_setOf]
}
theorem mem_GMInner_iff' {u : GMDart} : u ∈ GMInner ↔ u.val ∈ (CMBBox).zoom := by{
  rw[GRectangle.mem_zoom, mem_GMInner_iff]
}
theorem GMnode_val_of_mem_GMInner {u : GMDart} (hu : u ∈ GMInner)
  : (GMnode u).val = edge (node u) := by{
    rw[GMnode']
    simp only
    rw[List.find?_cons_of_pos, Option.getD_some]
    simp only [decide_eq_true_eq]
    rw[← face_3]
    rw[mem_GMGrid_iff]
    simp only [face_half]
    exact Or.inl hu
  }
theorem GMnode_inner_closed {u : GMDart} (hu : u ∈ GMInner) : GMnode u ∈ GMInner := by{
  rw[mem_GMInner_iff, GMnode_val_of_mem_GMInner hu, ←face_3]
  simp only [face_half]
  exact hu
}
theorem funReflTransGen_GMnode_inner_closed {u0 u1 : GMDart}
  (hu01 : funReflTransGen GMnode u0 u1) (hu0 : u0 ∈ GMInner) : u1 ∈ GMInner := by{
    induction hu01 with
    | refl => exact hu0
    | tail hh ht ih => rw[fromFun] at ht; rw[← ht]; exact GMnode_inner_closed ih
  }
theorem funReflTransGen_GMnode_inner_closed_iff {u0 u1 : GMDart}
  (hu01 : funReflTransGen GMnode u0 u1) : u0 ∈ GMInner ↔ u1 ∈ GMInner := by{
    constructor
    · apply funReflTransGen_GMnode_inner_closed; exact hu01
    · apply funReflTransGen_GMnode_inner_closed; apply (GMDartHypermap).cnode_Symm.symm ; exact hu01
  }
theorem GMface_end0 {u : GMDart} : end0 (GMface u) = end0 u := by{
  match u with | ⟨d, hd⟩ => {
    rcases em (node (node (node d)) ∈ GMGrid) with h2f | h2f
    · {
      have h2f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node (node (node d))
        := List.find?_cons_of_pos (decide_eq_true h2f)
      simp only [GMface', h2f', Option.getD_some, node_end0]
    }
    rcases em (node (node d) ∈ GMGrid) with h1f | h1f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node (node d)
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_pos]; simp[h1f]
        · simp[h2f]
      }
      simp only [GMface', h1f', Option.getD_some, node_end0]
    }
    rcases em (node d ∈ GMGrid) with h0f | h0f
    · {
      have h1f' : [node (node (node d)), node (node d), node d].find?
        (fun x ↦ decide (x ∈ GMGrid)) = node d
      := by{
        rw[List.find?_cons_of_neg]
        · rw[List.find?_cons_of_neg]
          · rw[List.find?_cons_of_pos]; simp[h0f]
          · simp[h1f]
        · simp[h2f]
      }
      simp only [GMface', h1f', Option.getD_some, node_end0]
    }
    have h0n : edge (node d) ∉ GMGrid := by{
      rw[edge_mem_GMGrid_iff]
      exact h0f
    }
    simp only [←face_3, mem_GMGrid_iff, face_half, not_or] at h0n
    rw[node_3, mem_GMGrid_iff, face_half, not_or] at h2f
    rw[mem_GMGrid_iff] at hd
    exfalso
    apply hd.elim h0n.left h2f.left
  }
}
section card

abbrev GMInnerDart' := {u // u ∈ GMInner}
local notation "GMInnerDart" => @GMInnerDart' _ _ _ ab0P cm0P abcm0P
abbrev GMOuterDart' := {u // u ∉ GMInner}
local notation "GMOuterDart" => @GMOuterDart' _ _ _ ab0P cm0P abcm0P

@[inline] noncomputable instance instFintypeGMInnerDart : Fintype GMInnerDart := by{
  classical
  apply Subtype.fintype
}
@[inline] noncomputable instance instFintypeGMOuterDart : Fintype GMOuterDart := by{
  classical
  apply Subtype.fintype
}

noncomputable instance GMDart_equiv_GMInnerDart_sum_GMOuterDart :
  GMDart ≃ GMInnerDart ⊕ GMOuterDart := by{
    classical
    let f : GMDart → GMInnerDart ⊕ GMOuterDart := fun u =>
      let inst : Decidable (u ∈ GMInner) := inferInstance
      match inst with
      | isTrue hu => Sum.inl ⟨u, hu⟩
      | isFalse hu => Sum.inr ⟨u, hu⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro u1 u2 hu
      unfold f at hu
      set inst1 : Decidable (u1 ∈ GMInner) := inferInstance
      set inst2 : Decidable (u2 ∈ GMInner) := inferInstance
      match h1 : inst1, h2 : inst2 with
      | isTrue _, isFalse _ | isFalse _, isTrue _ => simp at hu
      | isTrue _, isTrue _ | isFalse _, isFalse _ => simp at hu; simp[hu]
    }
    · {
      intro u'
      match u' with | Sum.inl ⟨u, hu⟩ | Sum.inr ⟨u, hu⟩ => {
        use u
        unfold f
        set inst : Decidable (u ∈ GMInner) := inferInstance
        match h : inst with
        | isTrue h' | isFalse h' => {
          simp only [reduceCtorEq]
          try contradiction
        }
      }
    }
  }

theorem GMInnerDart_card : Fintype.card GMInnerDart = (CMBBox).area * 4 := by{
  rw[← GRectangle.area_zoom, ← GRectangle.enum_length,
  ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
  apply Fintype.card_congr
  let f : GMInnerDart → { x // x ∈ CMBBox'.zoom.enum } :=
    fun ⟨⟨d, hd⟩, hu⟩ => ⟨d, by{
      simp only [mem_GMInner_iff] at hu
      simp only [GRectangle.mem_enum_iff, GRectangle.mem_zoom]
      exact hu
    }⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro u1 u2 hu
    match u1, u2 with
    | ⟨⟨d1, hd1⟩, hu1⟩, ⟨⟨d2, hd2⟩, hu2⟩ => {
      unfold f at hu
      simp at hu
      simp[hu]
    }
  }
  · {
    intro ⟨d, hd⟩
    rw[GRectangle.mem_enum_iff, GRectangle.mem_zoom] at hd
    use ⟨⟨d, by{simp[mem_GMGrid_iff, hd]}⟩, by{simp[mem_GMInner_iff, hd]}⟩
  }
}
noncomputable def GMLU' := (List.range (CMBBox).width).map
    (fun i => 2 • GPoint.mk ((CMBBox).hspan.lb + Int.ofNat i) ((CMBBox).vspan.ub) + ⟨0, 0⟩)
noncomputable def GMLD' := (List.range (CMBBox).width).map
    (fun i => 2 • GPoint.mk ((CMBBox).hspan.lb + Int.ofNat i) ((CMBBox).vspan.lb - 1) + ⟨1, 1⟩)
noncomputable def GMLR' := (List.range (CMBBox).height).map
    (fun i => 2 • GPoint.mk ((CMBBox).hspan.ub) ((CMBBox).vspan.lb + Int.ofNat i) + ⟨0, 1⟩)
noncomputable def GMLL' := (List.range (CMBBox).height).map
    (fun i => 2 • GPoint.mk ((CMBBox).hspan.lb - 1) ((CMBBox).vspan.lb + Int.ofNat i) + ⟨1, 0⟩)
local notation "GMLU" => @GMLU' _ _ _ ab0P cm0P abcm0P
local notation "GMLD" => @GMLD' _ _ _ ab0P cm0P abcm0P
local notation "GMLR" => @GMLR' _ _ _ ab0P cm0P abcm0P
local notation "GMLL" => @GMLL' _ _ _ ab0P cm0P abcm0P
theorem lu_len : (GMLU).length = (CMBBox).width := by{simp[GMLU']}
theorem ld_len : (GMLD).length = (CMBBox).width := by{simp[GMLD']}
theorem lr_len : (GMLR).length = (CMBBox).height := by{simp[GMLR']}
theorem ll_len : (GMLL).length = (CMBBox).height := by{simp[GMLL']}
theorem lu_nodup : (GMLU).Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem ld_nodup : (GMLD).Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem lr_nodup : (GMLR).Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem ll_nodup : (GMLL).Nodup := by{
  apply List.Nodup.map
  · {
    intro a b
    simp[two_nsmul, ← two_mul]
  }
  · apply List.nodup_range
}
theorem mod2_of_lu {d : GDart} (hd : d ∈ GMLU) : d.mod2 = ⟨0, 0⟩ := by{
  rw[GMLU', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_ld {d : GDart} (hd : d ∈ GMLD) : d.mod2 = ⟨1, 1⟩ := by{
  rw[GMLD', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_lr {d : GDart} (hd : d ∈ GMLR) : d.mod2 = ⟨0, 1⟩ := by{
  rw[GMLR', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem mod2_of_ll {d : GDart} (hd : d ∈ GMLL) : d.mod2 = ⟨1, 0⟩ := by{
  rw[GMLL', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.mod2_add_double]
  rfl
}
theorem lu_disjoint_lr : (GMLU).Disjoint (GMLR) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_lr hb] at hab
  simp at hab
}
theorem lu_disjoint_ld : (GMLU).Disjoint (GMLD) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_ld hb] at hab
  contradiction
}
theorem lu_disjoint_ll : (GMLU).Disjoint (GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lu ha, mod2_of_ll hb] at hab
  contradiction
}
theorem lr_disjoint_ld : (GMLR).Disjoint (GMLD) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lr ha, mod2_of_ld hb] at hab
  contradiction
}
theorem lr_disjoint_ll : (GMLR).Disjoint (GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_lr ha, mod2_of_ll hb] at hab
  contradiction
}
theorem ld_disjoint_ll : (GMLD).Disjoint (GMLL) := by{
  rw[List.disjoint_iff_ne]
  intro a ha b hb hab
  apply congrArg GPoint.mod2 at hab
  rw[mod2_of_ld ha, mod2_of_ll hb] at hab
  contradiction
}
theorem ll_disjoint_ld : (GMLL).Disjoint (GMLD) := by{
  symm
  apply ld_disjoint_ll
}
theorem ll_disjoint_lr : (GMLL).Disjoint (GMLR) := by{
  symm
  apply lr_disjoint_ll
}
theorem ld_disjoint_lr : (GMLD).Disjoint (GMLR) := by{
  symm
  apply lr_disjoint_ld
}
theorem half_y_of_lu {d : GDart} (hd : d ∈ GMLU) : d.half.y = (CMBBox).vspan.ub := by{
  rw[GMLU', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.y_half]
}
theorem half_y_of_ld {d : GDart} (hd : d ∈ GMLD) : d.half.y = (CMBBox).vspan.lb - 1 := by{
  rw[GMLD', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.y_half]
}
theorem half_x_of_lr {d : GDart} (hd : d ∈ GMLR) : d.half.x = (CMBBox).hspan.ub := by{
  rw[GMLR', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.x_half]
}
theorem half_x_of_ll {d : GDart} (hd : d ∈ GMLL) : d.half.x = (CMBBox).hspan.lb - 1 := by{
  rw[GMLL', List.mem_map] at hd
  have ⟨_, _, hd'⟩ := hd
  rw[←hd', GPoint.half_add_double]
  simp[GPoint.x_half]
}
theorem half_x_of_lu {d : GDart} (hd : d ∈ GMLU)
: (CMBBox).hspan.lb ≤ d.half.x ∧ d.half.x < (CMBBox).hspan.ub := by{
  rw[GMLU', List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.x_half, Int.zero_ediv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.width_eq_sub_of_proper CMBBox_proper]
  simp[hi]
}
theorem half_x_of_ld {d : GDart} (hd : d ∈ GMLD)
: (CMBBox).hspan.lb ≤ d.half.x ∧ d.half.x < (CMBBox).hspan.ub := by{
  rw[GMLD', List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.x_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.width_eq_sub_of_proper CMBBox_proper]
  simp[hi]
}
theorem half_y_of_lr {d : GDart} (hd : d ∈ GMLR)
: (CMBBox).vspan.lb ≤ d.half.y ∧ d.half.y < (CMBBox).vspan.ub := by{
  rw[GMLR', List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.y_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.height_eq_sub_of_proper CMBBox_proper]
  simp[hi]
}
theorem half_y_of_ll {d : GDart} (hd : d ∈ GMLL)
: (CMBBox).vspan.lb ≤ d.half.y ∧ d.half.y < (CMBBox).vspan.ub := by{
  rw[GMLL', List.mem_map] at hd
  have ⟨i, hi, hd'⟩ := hd
  rw[List.mem_range] at hi
  rw[←hd', GPoint.half_add_double]
  simp only [Int.ofNat_eq_natCast, GPoint.add_def, GPoint.y_half, Int.reduceDiv, add_zero,
    le_add_iff_nonneg_right, Nat.cast_nonneg, true_and, gt_iff_lt]
  rw[← lt_sub_iff_add_lt', ← GRectangle.height_eq_sub_of_proper CMBBox_proper]
  simp[hi]
}
theorem lu_subset_GMGrid {d : GDart} (hd : d ∈ GMLU) : d ∈ GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_lu hd
  have hy := half_y_of_lu hd
  rw[edge_half, mod2_of_lu hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx, Int.le_sub_one_iff,
  GRectangle.vspan_lt_of_proper CMBBox_proper]
}
theorem ld_subset_GMGrid {d : GDart} (hd : d ∈ GMLD) : d ∈ GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_ld hd
  have hy := half_y_of_ld hd
  rw[edge_half, mod2_of_ld hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx,
  GRectangle.vspan_lt_of_proper CMBBox_proper]
}
theorem lr_subset_GMGrid {d : GDart} (hd : d ∈ GMLR) : d ∈ GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_lr hd
  have hy := half_y_of_lr hd
  rw[edge_half, mod2_of_lr hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx, Int.le_sub_one_iff,
  GRectangle.hspan_lt_of_proper CMBBox_proper]
}
theorem ll_subset_GMGrid {d : GDart} (hd : d ∈ GMLL) : d ∈ GMGrid := by{
  rw[mem_GMGrid_iff]
  right
  have hx := half_x_of_ll hd
  have hy := half_y_of_ll hd
  rw[edge_half, mod2_of_ll hd]
  simp[GRectangle.mem_iff, GInterval.mem_iff, GPoint.ccw, hy, hx,
  GRectangle.hspan_lt_of_proper CMBBox_proper]
}
theorem lu_disjoint_inner {d : GDart} (hd : d ∈ GMLU) : ⟨d, lu_subset_GMGrid hd⟩ ∉ GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_y_of_lu hd]
}
theorem ld_disjoint_inner {d : GDart} (hd : d ∈ GMLD) : ⟨d, ld_subset_GMGrid hd⟩ ∉ GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_y_of_ld hd]
}
theorem lr_disjoint_inner {d : GDart} (hd : d ∈ GMLR) : ⟨d, lr_subset_GMGrid hd⟩ ∉ GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_x_of_lr hd]
}
theorem ll_disjoint_inner {d : GDart} (hd : d ∈ GMLL) : ⟨d, ll_subset_GMGrid hd⟩ ∉ GMInner := by{
  rw[mem_GMInner_iff]
  simp[GRectangle.mem_iff, GInterval.mem_iff, half_x_of_ll hd]
}
noncomputable def GMOuter' := GMLU ++ GMLL ++ GMLD ++ GMLR
local notation "GMOuter" => @GMOuter' _ _ _ ab0P cm0P abcm0P
theorem outer_nodup : (GMOuter).Nodup := by{
  unfold GMOuter'
  simp only [List.nodup_append', List.disjoint_append_left]
  simp only [ll_nodup, lr_nodup, lu_nodup, ld_nodup, true_and]
  simp[lu_disjoint_lr, lu_disjoint_ld, lu_disjoint_ll,
    ll_disjoint_ld, ll_disjoint_lr, ld_disjoint_lr]
}
theorem outer_length : (GMOuter).length = ((CMBBox).width + (CMBBox).height) * 2 := by{
  unfold GMOuter'
  simp[lu_len, lr_len, ld_len, ll_len]
  ring
}
theorem outer_subset_GMGrid {d : GDart} (hd : d ∈ GMOuter) : d ∈ GMGrid := by{
  simp only [GMOuter', List.mem_append] at hd
  rcases hd with ((hd | hd) | hd) | hd
  · exact lu_subset_GMGrid hd
  · exact ll_subset_GMGrid hd
  · exact ld_subset_GMGrid hd
  · exact lr_subset_GMGrid hd
}
theorem outer_disjoint_GMInner {d : GDart} (hd : d ∈ GMOuter)
  : ⟨d, outer_subset_GMGrid hd⟩ ∉ GMInner := by{
    simp only [GMOuter', List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact lu_disjoint_inner hd
    · exact ll_disjoint_inner hd
    · exact ld_disjoint_inner hd
    · exact lr_disjoint_inner hd
  }
theorem not_inner_in_outer {u : GMDart} (hu : u ∉ GMInner) : u.val ∈ GMOuter := by{
  match u with | ⟨d, hd⟩ => {
    rw[mem_GMGrid_iff] at hd
    rw[mem_GMInner_iff] at hu
    simp only at hu
    apply (Or.resolve_left · hu) at hd
    simp only
    simp only [GMOuter', List.mem_append]
    simp only [GRectangle.mem_iff, GInterval.mem_iff, edge_half] at hd hu
    simp only [not_and, not_lt, and_imp] at hu
    rw[← GPoint.double_half_add_mod2 (d:=d)]
    rcases GPoint.mod2_cases (p:=d) with hdm | hdm | hdm | hdm
    · {
      left; left; left
      simp only [GPoint.ccw, hdm, sub_zero, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right, Int.le_sub_one_iff, Int.sub_one_lt_iff] at hd
      simp only [hd, le_of_lt, forall_const] at hu
      rw[GMLU', List.mem_map]
      have hu' := le_antisymm (by{simp[hd]}) hu
      use (d.half.x - (CMBBox).hspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.left.left)]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.left.left), hdm, hu']
      simp[GRectangle.width_eq_sub_of_proper CMBBox_proper, hd]
    }
    · {
      left; left; right
      simp only [GPoint.ccw, hdm, sub_zero, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right] at hd
      have hd' := lt_trans (a:=d.half.x) (by{simp}) hd.left.right
      simp only [hd, not_le_of_gt hd.right.right, imp_false, not_true_eq_false, not_lt,
        not_le_of_gt hd', not_le] at hu
      rw[GMLL', List.mem_map]
      have hu' : d.half.x = (CMBBox').hspan.lb - 1 := by{
        rw[Int.le_add_one_iff] at hd
        simp only [not_le_of_gt hu, false_or] at hd
        rw[hd.left.left]
        ring
      }
      use (d.half.y - (CMBBox).vspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.right.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.right.left)]
      simp[GRectangle.height_eq_sub_of_proper CMBBox_proper, hd]
    }
    · {
      left; right
      simp only [GPoint.ccw, hdm, sub_self, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right] at hd
      have hd' := lt_trans (a:=d.half.y) (by{simp}) hd.right.right
      simp only [hd, not_le_of_gt hd', imp_false, not_le, forall_const] at hu
      rw[GMLD', List.mem_map]
      have hu' : d.half.y = (CMBBox').vspan.lb - 1 := by{
        rw[Int.le_add_one_iff] at hd
        simp only [not_le_of_gt hu, false_or] at hd
        rw[hd.right.left]
        ring
      }
      use (d.half.x - (CMBBox).hspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.left.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.left.left)]
      simp[GRectangle.width_eq_sub_of_proper CMBBox_proper, hd]
    }
    · {
      right
      simp only [GPoint.ccw, hdm, sub_self, GPoint.add_def, add_zero, GPoint.sub_def,
        add_sub_cancel_right, Int.le_sub_one_iff, Int.sub_one_lt_iff] at hd
      simp only [hd, le_of_lt, not_le_of_gt hd.right.right, imp_false, not_true_eq_false, not_lt,
        forall_const] at hu
      rw[GMLR', List.mem_map]
      have hu' := le_antisymm (by{simp[hd]}) hu
      use (d.half.y - (CMBBox).vspan.lb).toNat
      simp[two_nsmul, GPoint.ext_iff, hu', hdm]
      simp[max_eq_left (Int.sub_nonneg_of_le hd.right.left)]
      simp[Int.toNat_lt (Int.sub_nonneg_of_le hd.right.left)]
      simp[GRectangle.height_eq_sub_of_proper CMBBox_proper, hd]
    }
  }
}

theorem GMOuterDart_card : Fintype.card GMOuterDart = ((CMBBox).width + (CMBBox).height) * 2 := by{
  rw[← outer_length, ← List.Subtype.fintype_card_eq_length_of_nodup outer_nodup]
  apply Fintype.card_congr
  let f : GMOuterDart → { x // x ∈ GMOuter' } := fun ⟨⟨d, hd⟩, hu⟩ =>
    ⟨d, not_inner_in_outer hu⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro u1 u2 hu12
    match u1, u2 with | ⟨⟨d1, hd1⟩, hu1⟩, ⟨⟨d2, hd2⟩, hu2⟩ => {
      simp[f] at hu12
      simp[hu12]
    }
  }
  · {
    intro ⟨d, hd⟩
    use ⟨_, outer_disjoint_GMInner hd⟩
  }
}

theorem GMDart_card : Fintype.card GMDart
  = (CMBBox).area * 4 + ((CMBBox).width + (CMBBox).height) * 2
:= by{
  rw[← Fintype.ofEquiv_card GMDart_equiv_GMInnerDart_sum_GMOuterDart]
  have h:=@Fintype.card_sum GMInnerDart GMOuterDart
    _ _
  rw[GMInnerDart_card, GMOuterDart_card] at h
  rw[← h]
  apply congrArg
  apply Subsingleton.elim
}

section nodecard

noncomputable def GMInnerDartNode' : GMInnerDart → GMInnerDart :=
  fun ⟨u, hu⟩ => ⟨GMnode u, GMnode_inner_closed hu⟩
local notation "GMInnerDartNode" => @GMInnerDartNode' _ _ _ ab0P cm0P abcm0P
theorem GMInnerDartNode_injective : Injective GMInnerDartNode := by{
  intro ⟨u0, hu0⟩ ⟨u1, hu1⟩ hu01
  rw[GMInnerDartNode', GMInnerDartNode', Subtype.ext_iff] at hu01
  change (GMDartHypermap).node u0 = (GMDartHypermap).node u1 at hu01
  simp only[(GMDartHypermap).node_inj] at hu01
  simp[hu01]
}
noncomputable def GMInnerDartCNodeEquivalence' :=
  Finite.funReflTransGen_injective_equivalence
  (@GMInnerDartNode_injective _ _ _ ab0P cm0P abcm0P)
local notation "GMInnerDartCNodeEquivalence" => @GMInnerDartCNodeEquivalence' _ _ _ ab0P cm0P abcm0P
def GMInnerDartNsetoid' : Setoid GMInnerDart :=
  ⟨_, GMInnerDartCNodeEquivalence⟩
local notation "GMInnerDartNsetoid" => @GMInnerDartNsetoid' _ _ _ ab0P cm0P abcm0P
@[inline] noncomputable instance instDecidableGMInnerDartNsetoid
: DecidableRel GMInnerDartNsetoid := by{
  apply Fintype.injective_setoid.decidable
  apply GMInnerDartNode_injective
}
theorem GMInnerDartNode_val_val_eq_en {u : GMInnerDart} :
  (GMInnerDartNode u).val.val = edge (node u.val.val) := by{
    rw[← GMnode_val_of_mem_GMInner u.prop, ← Subtype.ext_iff]
    rw[GMInnerDartNode']
  }
theorem GMInnerDartNsetoid_iff_half_eq {u0 u1 : GMInnerDart} :
funReflTransGen GMInnerDartNode u0 u1 ↔ u0.val.val.half = u1.val.val.half := by{
  constructor
  · {
    intro h
    induction h with
    | refl => rfl
    | tail hh ht ih => {
      rw[ih]
      rw[fromFun, Subtype.ext_iff, Subtype.ext_iff, GMInnerDartNode_val_val_eq_en] at ht
      rw[← face_inj, fen_cancel] at ht
      rw[ht, face_half]
    }
  }
  · {
    intro h
    rw[half_eq_cases_face] at h
    rcases h with h | h | h | h
    · {
      rw[Subtype.ext (Subtype.ext h)]
      apply funReflTransGen.refl
    }
    · {
      nth_rw 1 [← fen_cancel ↑↑u0, face_inj, ← GMnode_val_of_mem_GMInner u0.prop,
      ← Subtype.ext_iff] at h
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, GMInnerDartNode']
      exact h
    }
    · {
      apply ReflTransGen.head (b:=GMInnerDartNode u0)
      · rfl
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, Subtype.ext_iff, GMInnerDartNode_val_val_eq_en,
      ← face_inj, fen_cancel, GMInnerDartNode_val_val_eq_en, ← face_inj, fen_cancel, h]
    }
    · {
      rw[face_3, ← GMnode_val_of_mem_GMInner u1.prop, ← Subtype.ext_iff] at h
      apply (GMInnerDartCNodeEquivalence).symm
      apply ReflTransGen.single
      rw[fromFun, Subtype.ext_iff, GMInnerDartNode', h]
    }
  }
}
theorem GMDartHypermapNsetoid_iff_half_eq_of_inner {u0 u1 : GMDart} (hu0 : u0 ∈ GMInner)
  (hu1 : u1 ∈ GMInner) : funReflTransGen GMnode u0 u1 ↔ u0.val.half = u1.val.half := by{
    have ih := GMInnerDartNsetoid_iff_half_eq (u0:=⟨u0, hu0⟩) (u1:=⟨u1, hu1⟩)
    rw[←ih]
    clear ih
    constructor
    · {
      intro h
      induction h with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        have hb : b ∈ GMInner := by{
          apply funReflTransGen_GMnode_inner_closed hh hu0
        }
        apply ReflTransGen.tail (b:=⟨b, hb⟩)
        · exact ih hb
        rw[fromFun] at ht
        simp only [fromFun, GMInnerDartNode', ht]
      }
    }
    · {
      intro h
      generalize hu0' : (⟨u0, hu0⟩ : GMInnerDart) = u0'
      generalize hu1' : (⟨u1, hu1⟩ : GMInnerDart) = u1'
      have hu0'v : u0'.val = u0 := by{simp[← hu0']}
      have hu1'v : u1'.val = u1 := by{simp[← hu1']}
      rw[← hu0'v, ← hu1'v]
      rw[hu0', hu1'] at h
      clear! u0 u1
      induction h with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        apply ih.tail
        rw[fromFun, Subtype.ext_iff, GMInnerDartNode'] at ht
        exact ht
      }
    }
  }
theorem GMDartHypermap_inner_ncomp : Fintype.nComp GMInnerDartNsetoid = (CMBBox).area := by{
  rw[← GRectangle.enum_length, ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
  apply Fintype.card_congr
  let f : Quotient GMInnerDartNsetoid → { x // x ∈ (CMBBox).enum } :=
    fun q => ⟨q.out.val.val.half, by{
      have hq := q.out.prop
      rw[mem_GMInner_iff] at hq
      rw[GRectangle.mem_enum_iff]
      exact hq
    }⟩
  apply Equiv.ofBijective f
  constructor
  · {
    intro q1 q2 hq12
    unfold f at hq12
    rw[Subtype.ext_iff] at hq12
    simp only at hq12
    rw[← GMInnerDartNsetoid_iff_half_eq] at hq12
    rw[← Quotient.out_equiv_out]
    exact hq12
  }
  · {
    intro ⟨p, hp⟩
    rw[GRectangle.mem_enum_iff] at hp
    use ⟦⟨⟨2 • p, by{simp[mem_GMGrid_iff, GPoint.half_double, hp]}⟩,
      by{simp[mem_GMInner_iff, GPoint.half_double, hp]}⟩⟧
    unfold f
    rw[Subtype.ext_iff]
    simp only
    have hp' : funReflTransGen _ _ _ := Quotient.mk_out (s:=GMInnerDartNsetoid)
      ⟨⟨2 • p, by{simp[mem_GMGrid_iff, GPoint.half_double, hp]}⟩,
      by{simp[mem_GMInner_iff, GPoint.half_double, hp]}⟩
    rw[GMInnerDartNsetoid_iff_half_eq] at hp'
    rw[hp']
    simp[GPoint.half_double]
  }
}

theorem GMDartHypermap_ncomp_ge
  : (GMDartHypermap).ncomp ≥ (CMBBox).area := by{
    rw[← GMDartHypermap_inner_ncomp]
    rw[Hypermap.ncomp, Fintype.nComp, Fintype.nComp, ge_iff_le]
    let f : Quotient GMInnerDartNsetoid → Quotient (GMDartHypermap).nsetoid :=
      fun q => ⟦q.out.val⟧
    apply Fintype.card_le_of_injective f
    intro q1 q2 hq12
    unfold f at hq12
    rw[Quotient.eq] at hq12
    rw[← Quotient.out_equiv_out]
    change funReflTransGen _ _ _
    change funReflTransGen GMnode _ _ at hq12
    match hq1 : q1.out, hq2 : q2.out with
    | ⟨u1, hu1⟩, ⟨u2, hu2⟩ => {
      simp only [hq1, hq2] at hq12
      clear! q1 q2
      induction hq12 with
      | refl => apply funReflTransGen.refl
      | @tail b c hh ht ih => {
        have hb : b ∈ GMInner' := funReflTransGen_GMnode_inner_closed hh hu1
        specialize ih hb
        apply ReflTransGen.tail ih
        rw[fromFun] at ht
        rw[fromFun, Subtype.ext_iff, GMInnerDartNode']
        exact ht
      }
    }
  }
end nodecard

section facecard

theorem GMDartHypermap_fsetoid_n3_iterate {u : GMDart} {m : ℕ}
  (hn3u : (node ∘ node ∘ node)^[m] u ∈ GMGrid) :
  funReflTransGen GMface u ⟨_, hn3u⟩ := by{
    match u with | ⟨d, hd⟩ => {
      induction m using Nat.strongRec generalizing d with
      | ind m ih => {
        have node_lemma : node (node (node d)) ∈ GMGrid ∨ (node (node d)) ∈ GMGrid
          ∨ node d ∈ GMGrid := by{
            apply of_not_not
            intro node_lemma
            simp only [not_or] at node_lemma
            have hn := hd
            rw[mem_GMGrid_iff] at hn
            simp only [mem_GMGrid_iff, not_or, node_3, face_half] at node_lemma
            have h0 := node_lemma.left.left
            have h1 := node_lemma.right.right.right
            rw[← face_half, fen_cancel] at h1
            exact hn.elim h1 h0
          }
        simp only at hn3u
        rcases em (∃m' < m, m' > 0 ∧ (node ∘ node ∘ node)^[m'] d ∈ GMGrid)
            with ⟨m', hm'm, hm'0, hm'⟩ | hall
        · {
          have ih' := ih (m - m') (Nat.sub_lt (Nat.zero_lt_of_lt hm'm) hm'0) _ hm'
            (by{rw[← iterate_add_apply, Nat.sub_add_cancel (le_of_lt hm'm)]; exact hn3u})
          simp only[← iterate_add_apply, Nat.sub_add_cancel (le_of_lt hm'm)] at ih'
          have ih'' := ih m' hm'm d hd hm'
          exact ReflTransGen.trans ih'' ih'
        }
        simp only [gt_iff_lt, not_exists, not_and] at hall
        have hm4 : m < 4 := by{
          apply lt_of_not_ge
          intro h
          have hall1 := hall 1 (by{omega}) (by{simp})
          have hall2 := hall 2 (by{omega}) (by{simp})
          have hall3 := hall 3 (by{omega}) (by{simp})
          simp only [iterate_zero, comp_apply, iterate_succ, node_4, id] at hall1 hall2 hall3
          simp[hall1, hall2, hall3] at node_lemma
        }
        match m with
        | 0 => simp[funReflTransGen.refl]
        | 1 => {
          simp only [iterate_one, comp_apply] at hn3u
          apply ReflTransGen.single
          simp only [fromFun, iterate_one, comp_apply, Subtype.ext_iff, GMface']
          rw[List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
        }
        | 2 => {
          have hall1 := hall 1 (by{simp}) (by{simp})
          simp only [iterate_succ, iterate_zero_apply, comp_apply, node_4] at hn3u hall1
          apply ReflTransGen.single
          simp only [fromFun, iterate_succ, iterate_zero_apply, comp_apply,
            Subtype.ext_iff, GMface', node_4]
          rw[List.find?_cons_of_neg, List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
          · simp[hall1]
        }
        | 3 => {
          have hall1 := hall 1 (by{simp}) (by{simp})
          have hall2 := hall 2 (by{simp}) (by{simp})
          simp only [iterate_succ, iterate_zero_apply, comp_apply, node_4] at hn3u hall1 hall2
          apply ReflTransGen.single
          simp only [fromFun, iterate_succ, iterate_zero_apply, comp_apply,
            Subtype.ext_iff, GMface', node_4]
          rw[List.find?_cons_of_neg, List.find?_cons_of_neg,
            List.find?_cons_of_pos, Option.getD_some]
          · simp[hn3u]
          · simp[hall2]
          · simp[hall1]
        }
      }
    }
  }

theorem GMDartHypermap_fsetoid_iff_end0 {u0 u1 : GMDart} :
  funReflTransGen GMface u0 u1 ↔ end0 u0 = end0 u1 := by{
    constructor
    · {
      intro h
      induction h with
      | refl => rfl
      | tail hh ht ih => {
        rw[fromFun] at ht
        rw[ih, ← ht, GMface_end0]
      }
    }
    · {
      intro h
      rw[end0_eq_exists_iterate_3] at h
      have ⟨m, hm⟩:=h
      clear h
      match u0, u1 with | ⟨d0, hd0⟩, ⟨d1, hd1⟩ => {
        simp only at hm
        induction m using Nat.strongRec generalizing d0 with
        | ind m ih => {
          simp only [← hm]
          apply GMDartHypermap_fsetoid_n3_iterate
        }
      }
    }
  }

theorem GMDartHypermap_fcomp
  : (GMDartHypermap).fcomp = ((CMBBox).width + 1) * ((CMBBox).height + 1) := by{
    let CMGridBox : GRectangle := ⟨
      ⟨(CMBBox).hspan.lb, (CMBBox).hspan.ub + 1⟩,
      ⟨(CMBBox).vspan.lb, (CMBBox).vspan.ub + 1⟩
    ⟩
    have CMGridBox_area : CMGridBox.area = ((CMBBox).width + 1) * ((CMBBox).height + 1) := by{
      simp only [GRectangle.area, GRectangle.width, GRectangle.height, GInterval.width,
      CMGridBox, add_sub_right_comm]
      congr
      · {
        rw[Int.toNat_add]
        · rfl
        · apply le_of_lt (Int.sub_pos_of_lt (GRectangle.hspan_lt_of_proper CMBBox_proper))
        · simp
      }
      · {
        rw[Int.toNat_add]
        · rfl
        · apply le_of_lt (Int.sub_pos_of_lt (GRectangle.vspan_lt_of_proper CMBBox_proper))
        · simp
      }
    }
    rw[← CMGridBox_area, ← GRectangle.enum_length,
      ← List.Subtype.fintype_card_eq_length_of_nodup GRectangle.enum_nodup]
    rw[Hypermap.fcomp]
    apply Fintype.card_congr
    have mem_lemma {u : GMDart} : end0 u ∈ CMGridBox.enum := by{
      rw[GRectangle.mem_enum_iff]
      match u with | ⟨d, hd⟩ => {
        simp only
        simp only [mem_GMGrid_iff] at hd
        simp only [edge_half, GRectangle.mem_iff, GInterval.mem_iff] at hd
        simp only [end0, GRectangle.mem_iff, CMGridBox, GInterval.mem_iff]
        simp only [Int.lt_add_one_iff]
        simp only [GPoint.add_def]
        simp only [GPoint.add_def, GPoint.sub_def] at hd
        rcases GPoint.mod2_cases (p:=d) with h | h | h | h
        all_goals
        simp only [GPoint.ccw, h, sub_zero, add_zero, add_sub_cancel_right, Int.le_sub_one_iff,
          Int.sub_one_lt_iff, sub_self, add_zero] at hd
        simp[h]
        omega
      }
    }
    have exists_GMGrid {p : GPixel} (hp : p ∈ CMGridBox) : ∃d, end0 d = p ∧ d ∈ GMGrid := by{
      match p with | ⟨px, py⟩ => {
        simp only [GRectangle.mem_iff, GInterval.mem_iff, CMGridBox, Int.lt_add_one_iff] at hp
        have hh := GRectangle.hspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)
        have hv := GRectangle.vspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)
        rcases lt_or_eq_of_le hp.left.right with hplr | hplr
        · {
          rcases lt_or_eq_of_le hp.right.right with hprr | hprr
          · {
            use 2 • ⟨px, py⟩
            rw[end0, GPoint.half_double, GPoint.mod2_double, mem_GMGrid_iff, add_zero]
            apply And.intro rfl
            left
            rw[GPoint.half_double]
            simp only [GRectangle.mem_iff, GInterval.mem_iff]
            omega
          }
          · {
            use 2 • ⟨px, py⟩ + ⟨0, -1⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
        }
        · {
          rcases lt_or_eq_of_le hp.right.right with hprr | hprr
          · {
            use 2 • ⟨px, py⟩ + ⟨-1, 0⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
          · {
            use 2 • ⟨px, py⟩ + ⟨-1, -1⟩
            simp only [end0, GPoint.half_add_double, GPoint.mod2_add_double, mem_GMGrid_iff]
            constructor
            · simp[GPoint.half, GPoint.mod2]
            · {
              left
              simp[GPoint.half, GRectangle.mem_iff, GInterval.mem_iff, hprr]
              omega
            }
          }
        }
      }
    }
    let f : Quotient (GMDartHypermap).fsetoid → { x // x ∈ CMGridBox.enum } :=
      fun q => ⟨end0 q.out, mem_lemma⟩
    apply Equiv.ofBijective f
    constructor
    · {
      intro q1 q2 hq12
      unfold f at hq12
      rw[Subtype.ext_iff] at hq12
      simp only at hq12
      rw[← GMDartHypermap_fsetoid_iff_end0] at hq12
      rw[← Quotient.out_equiv_out]
      exact hq12
    }
    · {
      intro ⟨p, hp⟩
      rw[GRectangle.mem_enum_iff] at hp
      have ⟨d, hd0, hd⟩:=exists_GMGrid hp
      use ⟦⟨d, hd⟩⟧
      unfold f
      have hout := Quotient.mk_out (s:=(GMDartHypermap).fsetoid) ⟨d, hd⟩
      change funReflTransGen GMface _ _ at hout
      rw[GMDartHypermap_fsetoid_iff_end0] at hout
      simp only [hout, hd0]
    }
  }
end facecard

section edgecard
theorem GMDartHypermap_ecomp
  : (GMDartHypermap).ecomp = (CMBBox).area * 2 + ((CMBBox).width + (CMBBox).height)
  := by{
    have ih := @GMDart_card n ab0 cm0 ab0P cm0P abcm0P
    rw[Hypermap.plain.ecomp_double GMDartHypermap_plain] at ih
    change _ = _ * (2 * 2) + _ at ih
    rw[← mul_assoc, ← add_mul] at ih
    simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at ih
    exact ih
  }
end edgecard

end card

section connected

noncomputable def C0' : GDart := 2 • ⟨(CMBBox).hspan.lb, (CMBBox).vspan.lb⟩
local notation "C0" => @C0' _ _ _ ab0P cm0P abcm0P
theorem C0_mem_GMGrid : C0 ∈ GMGrid := by{
  rw[mem_GMGrid_iff]
  left
  simp[C0', GPoint.half_double, GRectangle.mem_iff, GInterval.mem_iff,
  GRectangle.hspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P),
  GRectangle.vspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)]
}
theorem C0_mem_GInner : ⟨C0, C0_mem_GMGrid⟩ ∈ GMInner := by{
  rw[mem_GMInner_iff]
  simp[C0', GPoint.half_double, GRectangle.mem_iff, GInterval.mem_iff,
  GRectangle.hspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P),
  GRectangle.vspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)]
}
theorem GMDartHypermap_gsetoid_of_gsetoid_c0
: (∀x, (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x) → (∀x y, (GMDartHypermap).gsetoid x y) := by{
    intro h x y
    have hx := h x
    have hy := h y
    symm at hx
    exact (GMDartHypermap).gsetoid.iseqv.trans hx hy
  }
theorem GMDartHypermap_gsetoid_of_gsetoid_c0_inner
: (∀x ∈ GMInner, (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x)
→ (∀x y, (GMDartHypermap).gsetoid x y)
:= by{
    intro IH
    apply GMDartHypermap_gsetoid_of_gsetoid_c0
    intro x
    have hx := x.prop
    rw[mem_GMGrid_iff] at hx
    rcases em (x ∈ GMInner) with hx' | hx'
    · exact IH _ hx'
    rw[mem_GMInner_iff] at hx'
    apply (Or.resolve_left · hx') at hx
    have IH' := IH ⟨edge x, by{simp[mem_GMGrid_iff, hx]}⟩ (by{simp[mem_GMInner_iff, hx]})
    apply (GMDartHypermap).gsetoid.iseqv.trans IH'
    apply (GMDartHypermap).gsetoid.iseqv.symm
    apply Hypermap.cglink_of_cedge
    apply funReflTransGen.single
  }

theorem GMDartHypermap_gsetoid_half_eq : ∀x ∈ GMInner, ∀y ∈ GMInner, x.val.half = y.val.half
    → ((GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x ↔
    (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ y)
    := by{
      intro x hx y hy hxy
      rw[← GMDartHypermapNsetoid_iff_half_eq_of_inner hx hy] at hxy
      change (GMDartHypermap).cnode _ _ at hxy
      have hxy' : (GMDartHypermap).gsetoid _ _ := Hypermap.cglink_of_cnode hxy
      constructor
      · intro h; exact h.trans hxy'
      · symm at hxy'; intro h; exact h.trans hxy'
    }
theorem GMDartHypermap_gsetoid_end0_eq : ∀x y : GMDart, end0 x = end0 y
    → ((GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x ↔
    (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ y)
    := by{
      intro x y hxy
      rw[← GMDartHypermap_fsetoid_iff_end0] at hxy
      change (GMDartHypermap).cface _ _ at hxy
      have hxy' : (GMDartHypermap).gsetoid _ _ := Hypermap.cglink_of_cface hxy
      constructor
      · intro h; exact h.trans hxy'
      · symm at hxy'; intro h; exact h.trans hxy'
    }

section
theorem GMDartHypermap_gsetoid_x
  (IH : ∀ x ∈ GMInner, x.val.x = (C0).x → (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x) :
  ∀ x ∈ GMInner, (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x := by{
  intro x hx
  have hc0x : (C0).x = CMBBox'.hspan.lb * 2 := by{
    simp[C0', two_nsmul, ← mul_two]; rfl
  }
  have hx_mem := hx
  rw[mem_GMInner_iff', GRectangle.zoom] at hx
  have h := Nat.recAux (motive := fun m =>
    ∀x ∈ GMInner, m = (x.val.x - (CMBBox).hspan.lb * 2).toNat
    → GMDartHypermap'.gsetoid ⟨C0, C0_mem_GMGrid⟩ x)
  apply h ?_ ?_ ((x.val.x - (CMBBox).hspan.lb * 2).toNat) x hx_mem rfl
  · {
    clear! x
    intro x hx_mem hx0
    have hx:=hx_mem
    simp only [mem_GMInner_iff', GRectangle.mem_iff, GInterval.mem_iff, GRectangle.zoom] at hx
    symm at hx0
    rw[Int.toNat_eq_zero, sub_le_iff_le_add, zero_add] at hx0
    have hx':=le_antisymm hx0 hx.left.left
    apply IH _ hx_mem
    simp[C0', hx', two_nsmul, ←mul_two]
  }
  · {
    clear! x
    clear h
    intro k hk x hx hkx
    have hkx' : x.val.x > CMBBox'.hspan.lb * 2 := by{
      rw[gt_iff_lt, ← Int.sub_pos, Int.pos_iff_toNat_pos, ← hkx]
      simp
    }
    let x' : GMDart := ⟨⟨x.val.x - 1, x.val.y⟩, by{
      rw[mem_GMGrid_iff]
      left
      rw[← GRectangle.mem_zoom, GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }⟩
    have hx'_mem : x' ∈ GMInner := by{
      rw[mem_GMInner_iff', GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, x', Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }
    have hx'_eta : ⟨x'.val.x, x'.val.y⟩ = x'.val := rfl
    have hx'x : ⟨x'.val.x + 1, x'.val.y⟩ = x.val := by{simp[x']}
    have term_lemma' : (x'.val.x - CMBBox'.1.lb * 2).toNat + 1 =
      (x.val.x - CMBBox'.1.lb * 2).toNat
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

theorem GMDartHypermap_gsetoid_C0_y :
  ∀ x ∈ GMInner, x.val.x = (C0).x → (GMDartHypermap).gsetoid ⟨C0, C0_mem_GMGrid⟩ x := by{
  intro x hx hxc0
  have hc0x : (C0).y = CMBBox'.vspan.lb * 2 := by{
    simp[C0', two_nsmul, ← mul_two]; rfl
  }
  have hx_mem := hx
  rw[mem_GMInner_iff', GRectangle.zoom] at hx
  have h := Nat.recAux (motive := fun m =>
    ∀x ∈ GMInner, x.val.x = (C0).x → m = (x.val.y - (CMBBox).vspan.lb * 2).toNat
    → GMDartHypermap'.gsetoid ⟨C0, C0_mem_GMGrid⟩ x)
  apply h ?_ ?_ ((x.val.y - (CMBBox).vspan.lb * 2).toNat) x hx_mem hxc0 rfl
  · {
    clear! x
    intro x hx_mem hxc0 hx0
    have hx:=hx_mem
    simp only [mem_GMInner_iff', GRectangle.mem_iff, GInterval.mem_iff, GRectangle.zoom] at hx
    symm at hx0
    rw[Int.toNat_eq_zero, sub_le_iff_le_add, zero_add] at hx0
    have hx':=le_antisymm hx0 hx.right.left
    have h' : x = ⟨C0, C0_mem_GMGrid⟩ := by{
      simp[Subtype.ext_iff, GPoint.ext_iff, hxc0, hx', C0', two_nsmul, ← mul_two]
    }
    rw[h']
  }
  · {
    clear! x
    clear h
    intro k hk x hx hxc0 hkx
    have hkx' : x.val.y > CMBBox'.vspan.lb * 2 := by{
      rw[gt_iff_lt, ← Int.sub_pos, Int.pos_iff_toNat_pos, ← hkx]
      simp
    }
    let x' : GMDart := ⟨⟨x.val.x, x.val.y - 1⟩, by{
      rw[mem_GMGrid_iff]
      left
      rw[← GRectangle.mem_zoom, GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }⟩
    have hx'_mem : x' ∈ GMInner := by{
      rw[mem_GMInner_iff', GRectangle.zoom]
      simp only [GRectangle.mem_iff, GInterval.mem_iff, x', Int.le_sub_one_iff, Int.sub_one_lt_iff]
      simp only [mem_GMInner_iff', GRectangle.zoom, GRectangle.mem_iff, GInterval.mem_iff] at hx
      simp only [hx, and_self, le_of_lt, hkx']
    }
    have hx'_eta : ⟨x'.val.x, x'.val.y⟩ = x'.val := rfl
    have hx'x : ⟨x'.val.x, x'.val.y + 1⟩ = x.val := by{simp[x']}
    have term_lemma' : (x'.val.y - CMBBox'.2.lb * 2).toNat + 1 =
      (x.val.y - CMBBox'.2.lb * 2).toNat
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

theorem GMDartHypermap_connected : (GMDartHypermap).connected := by{
  unfold Hypermap.connected
  unfold Hypermap.gcomp
  rw[Fintype.nComp_eq_one_iff_nonempty_all]
  apply And.intro GMDart_nonempty
  have hh := GRectangle.hspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)
  have hv := GRectangle.vspan_lt_of_proper (@CMBBox_proper n ab0 cm0 ab0P cm0P abcm0P)
  apply GMDartHypermap_gsetoid_of_gsetoid_c0_inner
  apply GMDartHypermap_gsetoid_x
  apply GMDartHypermap_gsetoid_C0_y
}
end connected

theorem GMDartHypermap_planar : (GMDartHypermap).planar := by{
  rw[Hypermap.planar, Hypermap.genus, Hypermap.euler_rhs, Hypermap.euler_lhs]
  have hg : (GMDartHypermap).gcomp = 1 := GMDartHypermap_connected
  rw[hg, Hypermap.plain.ecomp_double GMDartHypermap_plain]
  simp only [one_mul, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, gt_iff_lt]
  rw[mul_two, ← add_assoc, ← Nat.sub_sub, Nat.add_sub_cancel]
  rw[add_comm (Hypermap.ncomp _), ← Nat.sub_sub]
  apply Nat.lt_of_le_of_lt (Nat.sub_le_sub_left GMDartHypermap_ncomp_ge _)
  rw[GMDartHypermap_ecomp, mul_two, add_right_comm, ← add_assoc, Nat.sub_right_comm]
  rw[Nat.add_sub_cancel, GMDartHypermap_fcomp, GRectangle.area]
  ring_nf
  omega
}

theorem GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner {u : GMDart} (hu : u ∈ GMInner)
  : ((GMDartHypermap).nodeinv u).val = face u.val := by{
    nth_rw 2 [← Hypermap.nodeinv_rightinv (H:=GMDartHypermap) u]
    change _ = face (GMnode _)
    have hu' : (GMDartHypermap).nodeinv u ∈ GMInner := by{
      apply funReflTransGen_GMnode_inner_closed ?_ hu
      apply (GMDartHypermap).cnode_equivalence.symm
      apply ReflTransGen.single
      rw[fromFun, (GMDartHypermap).nodeinv_rightinv]
    }
    rw[GMnode_val_of_mem_GMInner hu', fen_cancel]
  }
theorem GMDartHypermap_node_val_eq_en_of_mem_GMInner {u : GMDart} (hu : u ∈ GMInner)
  : ((GMDartHypermap).node u).val = edge (node u.val) := by{
    change (GMnode _).val = _
    rw[GMnode_val_of_mem_GMInner hu]
  }
theorem GMDartHypermap_edge_val_eq {u : GMDart}
  : ((GMDartHypermap).edge u).val = edge u.val := by{
    change (GMedge _).val = _
    rw[GMedge']
  }
theorem GMDartHypermap_faceinv_val_eq_node_of_mem_GMInner {u : GMDart} (hu : u ∈ GMInner)
  : ((GMDartHypermap).faceinv u).val = node u.val := by{
    rw[Hypermap.faceinv_eq, comp_apply, GMDartHypermap_edge_val_eq,
    GMDartHypermap_node_val_eq_en_of_mem_GMInner hu, edge_2]
  }

noncomputable def GMring' (i : Fin n) : List GMDart :=
  (CM i).ring.filterMap (fun d =>
    if hd : d ∈ GMGrid then some ⟨d, hd⟩ else none
  )
local notation "GMring" => @GMring' _ _ _ ab0P cm0P abcm0P
theorem GMring_map_val {i : Fin n} : (GMring i).map Subtype.val = (CM i).ring := by{
  unfold GMring'
  rw[List.map_filterMap]
  simp only [apply_dite, Option.map_none, Option.map_some]
  nth_rw 2 [← List.filterMap_some (l:=(CM i).ring)]
  apply List.filterMap_congr
  intro x hx
  rw[dite_eq_left_iff]
  simp only [reduceCtorEq, imp_false, Decidable.not_not]
  rw[Matte.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at hx
  rw[mem_GMGrid_iff]
  left
  exact CM_subset_CMBBox hx.left
}
theorem GMring_length {i : Fin n} : (GMring i).length = (CM i).ring.length := by{
  rw[← GMring_map_val, List.length_map]
}
theorem mem_GMring_iff_val_mem_ring {i : Fin n} {u : GMDart}
  : u ∈ GMring i ↔ u.val ∈ (CM i).ring := by{
    rw[GMring', List.mem_filterMap]
    constructor
    · {
      intro ⟨a, h0, h1⟩
      simp only [Option.dite_none_right_eq_some, Option.some.injEq, exists_subtype_mk_eq_iff] at h1
      exact h1 ▸ h0
    }
    · {
      intro h
      refine ⟨_, h, ?_⟩
      simp only [Subtype.coe_eta, dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false,
        Decidable.not_not]
      rw[Matte.mem_ring_iff_mem_disk_border, border, Set.mem_setOf] at h
      rw[mem_GMGrid_iff]
      left
      exact CM_subset_CMBBox h.left
    }
  }
theorem GMring_ne_nil {i : Fin n} : GMring i ≠ [] := by{
  intro h
  have ih := @GMring_map_val _ _ _ ab0P cm0P abcm0P i
  rw[h] at ih
  have ih' := (CM i).ring_ne_nil
  simp at ih
  simp[ih] at ih'
}
theorem GMring_subset_GMInner {i : Fin n} {u : GMDart} (hu : u ∈ GMring i)
  : u ∈ GMInner := by{
    rw[mem_GMInner_iff]
    rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border] at hu
    exact CM_subset_CMBBox hu.left
  }
theorem GMring_simpleCycle {i : Fin n} : (GMDartHypermap).simpleCycle
  (GMDartHypermap).rlink (GMring i)
  := by{
    unfold Hypermap.simpleCycle Hypermap.rlink List.IsCycleChain
    simp only [GMring_ne_nil, ↓ reduceDIte]
    change (_ ∧ funReflTransGen GMface _ _) ∧ _
    rw[GMDartHypermap_fsetoid_iff_end0, GMDartHypermap_edge_val_eq, edge_end0]
    rw[← List.getLast_map (l:=GMring i) (f := Subtype.val) (by{
      rw[List.ne_nil_iff_length_pos]
      simp[List.length_pos_iff_ne_nil, GMring_ne_nil]
    }), ← List.head_map (l:=GMring i) (f := Subtype.val) (by{
      rw[List.ne_nil_iff_length_pos]
      simp[List.length_pos_iff_ne_nil, GMring_ne_nil]
    })]
    have hc := (CM i).ring_cycle
    unfold List.IsCycleChain at hc
    simp only [(CM i).ring_ne_nil, ↓ reduceDIte, mrlink] at hc
    simp only [GMring_map_val, hc.right, and_true]
    constructor
    · {
      nth_rw 1 [← GMring_map_val, List.isChain_map] at hc
      apply (Eq.mp · hc.left)
      congr
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw[mrlink]
      change _ ↔ funReflTransGen GMface _ _
      rw[GMDartHypermap_fsetoid_iff_end0, GMDartHypermap_edge_val_eq, edge_end0]
    }
    · {
      have hs := (CM i).ring_simple
      rw[Hypermap.simpleList]
      rw[List.nodup_iff_getElem_ne_getElem] at hs
      rw[List.nodup_iff_getElem_ne_getElem]
      intro i j hij hjl
      simp only [List.length_map, GMring_length] at hjl
      specialize hs i j hij (by{simp[hjl]})
      simp only [List.getElem_map, ne_eq]
      simp only [List.getElem_map, ne_eq] at hs
      rw[Quotient.eq_iff_equiv]
      change ¬funReflTransGen GMface _ _
      simp only [← GMring_map_val, List.getElem_map] at hs
      rw[GMDartHypermap_fsetoid_iff_end0]
      exact hs
    }
  }

noncomputable def GMdisk' (i : Fin n) : Set GMDart :=
  (GMDartHypermap).diskN (GMring i)
local notation "GMdisk" => @GMdisk' _ _ _ ab0P cm0P abcm0P
theorem GMRing_subset_GMDisk {i : Fin n} {d : GMDart} (hd : d ∈ GMring i) : d ∈ GMdisk i := by{
  apply Hypermap.subset_diskN
  exact hd
}
theorem GMdisk_def {i : Fin n} : GMdisk i ⊆ {d | d.val.half ∈ CM i} := by{
  intro u ⟨nv, ri_nv, h⟩
  rw[Set.mem_setOf]
  rw[Hypermap.dconnect, ReflTransGen_iff_isChain_option] at h
  have ⟨s', vDs, shh, shl⟩:=h
  clear h
  match s' with
  | [] => simp at shh
  | v::s => {
    clear s'
    simp only [List.head?_cons, Option.some.injEq] at shh
    rw[List.getLast?_eq_some_getLast (by{simp}), Option.some_inj] at shl
    rw[← shl]
    clear! u
    have mi_u : v.val.half ∈ CM i := by{
      rw[shh, GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner (by{
        exact GMring_subset_GMInner ri_nv
      }), face_half]
      rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border] at ri_nv
      exact ri_nv.left
    }
    clear! nv
    generalize hvu : v = u
    simp only[hvu] at *
    clear hvu v
    revert vDs; intro uDs
    induction s generalizing u with
    | nil => simp[mi_u]
    | cons v s IHs => {
      rw[List.getLast_cons_cons]
      rw[List.isChain_cons_cons] at uDs
      have ⟨⟨r'u, uCv⟩, vDs⟩:=uDs
      clear uDs
      apply IHs
      · {
        clear IHs
        unfold Hypermap.clink at uCv
        simp only [union_iff, fromFun] at uCv
        rcases uCv with Du | Du
        · {
          rw[← Du, GMDartHypermap_nodeinv_val_eq_face_of_mem_GMInner, face_half]
          · exact mi_u
          rw[mem_GMInner_iff]
          apply CM_subset_CMBBox mi_u
        }
        rw[← Du]
        clear Du
        rw[mem_GMring_iff_val_mem_ring, Matte.mem_ring_iff_mem_disk_border, border,
        Set.mem_setOf, not_and, not_not] at r'u
        specialize r'u mi_u
        rw[← fen_cancel (Subtype.val _), face_half,
          ← GMDartHypermap_node_val_eq_en_of_mem_GMInner]
        · {
          rw[← comp_apply (f:= (GMDartHypermap).node), ← Hypermap.edgeinv_eq,
          Hypermap.plain.edgeinv_eq_edge GMDartHypermap_plain, GMDartHypermap_edge_val_eq]
          exact r'u
        }
        · {
          rw[
            funReflTransGen_GMnode_inner_closed_iff
              (funReflTransGen.single GMnode ((GMDartHypermap).face u))
          ]
          change (GMDartHypermap).node _ ∈ _
          rw[← comp_apply (f:=(GMDartHypermap).node), ← Hypermap.edgeinv_eq,
          Hypermap.plain.edgeinv_eq_edge GMDartHypermap_plain, mem_GMInner_iff,
          GMDartHypermap_edge_val_eq]
          exact CM_subset_CMBBox r'u
        }
      }
      · exact vDs
    }
  }
}
theorem GMdisk_disjoint {i j : Fin n} (hij : i ≠ j) : Disjoint (GMdisk i) (GMdisk j) := by{
  rw[Set.disjoint_iff_forall_ne]
  intro x hxi y hxj hxy
  rw[hxy.symm] at hxj
  clear! y
  have hxi' := GMdisk_def hxi
  have hxj' := GMdisk_def hxj
  rw[Set.mem_setOf] at hxi' hxj'
  have h := @CMP _ _ _ ab0P cm0P abcm0P i j ⟨x.val.half, hxi', hxj'⟩
  exact hij h
}

structure GMcutout' (E : Fin n → Prop) {α : Type _} [Fintype α] [DecidableEq α]
  (G : Hypermap α) (h : α → GMDart) (r : Fin n → List α) : Prop where
  map_planar : G.planar
  enc_injective : Injective h
  enc_morph_edge : ∀x, h (G.edge x) = (GMDartHypermap).edge (h x)
  enc_morph_cface : ∀x y, G.cface x y ↔ (GMDartHypermap).cface (h x) (h y)
  enc_morph_node : ∀x, (∀i, E i → x ∉ r i) → h (G.node x) = (GMDartHypermap).node (h x)
  ring_def : ∀i, ((r i).map h).reverse = GMring i
  ring_proper : ∀i, E i → List.IsCycleChain (fromFun G.node) (r i) ∧ (r i).Nodup

end

end GridPlane
