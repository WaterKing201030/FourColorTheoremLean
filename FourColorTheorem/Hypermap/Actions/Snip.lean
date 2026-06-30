import FourColorTheorem.Hypermap.Actions.Walkup

open Relation
open Function

namespace Hypermap

section

variable {α : Type _} [Fintype α] [DecidableEq α]
variable (H : Hypermap α)
variable (r : List α)

def dlink (x y : α) := x ∉ r ∧ H.clink x y
def dconnect (x y : α) := ReflTransGen (H.dlink r) (H.nodeinv y) x
def diskN := {x | ∃y ∈ r, H.dconnect r x y}
def diskE := {x | x ∈ H.diskN r ∧ x ∉ r}
def diskF := H.diskN r \ H.fband r
def diskFC := (H.diskN r)ᶜ \ H.fband r

end

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {H : Hypermap α} (HP : H.planar)
variable {r : List α} (scycRr : H.simpleCycle H.rlink r)

theorem diskN_nodeinv_close : ∀x ∈ H.diskN r, H.nodeinv x ∈ H.diskN r := by{
  intro x ⟨y, hyr, hdxy⟩
  rcases em' (x ∈ r) with hxr | hxr
  · {
    refine ⟨y, hyr, ?_⟩
    unfold dconnect at *
    apply hdxy.tail
    unfold dlink clink
    rw[union_iff, fromFun]
    simp[hxr]
  }
  refine ⟨x, hxr, ?_⟩
  apply ReflTransGen.refl
}
theorem diskN_cnode_close : ∀x ∈ H.diskN r, ∀y, H.cnode x y → y ∈ H.diskN r := by{
  intro x hx y hxy
  rw[cnode, ← funReflTransGen_bijInv_iff H.node_bijective, funReflTransGen_iff_iterate] at hxy
  change ∃_, H.nodeinv^[_] _ = _ at hxy
  have ⟨n, hn⟩:=hxy
  clear hxy
  induction n generalizing x with
  | zero => simp at hn; simp[hn ▸ hx]
  | succ n' ih => {
    exact ih (H.nodeinv x) (diskN_nodeinv_close _ hx) (by{rw[← iterate_succ_apply, hn]})
  }
}
theorem diskN_node_close : ∀x ∈ H.diskN r, node x ∈ H.diskN r := by{
  intro x hx
  apply diskN_cnode_close x hx
  apply funReflTransGen.single
}
theorem diskN_cnode_close_iff {x y : α} (hxy : H.cnode x y) : x ∈ H.diskN r ↔ y ∈ H.diskN r := by{
  constructor
  · intro h; exact diskN_cnode_close _ h _ hxy
  · {
    intro h
    apply H.cnode_Symm.symm at hxy
    exact diskN_cnode_close _ h _ hxy
  }
}
theorem subset_diskN {x : α} (hx : x ∈ r) : x ∈ H.diskN r := by{
  have h' : H.nodeinv x ∈ H.diskN r := by{
    refine ⟨x, hx, ?_⟩
    unfold dconnect
    apply ReflTransGen.refl
  }
  apply diskN_cnode_close _ h'
  apply ReflTransGen.single
  rw[fromFun, nodeinv_rightinv]
}

theorem mem_diskN_iff {x : α} : x ∈ H.diskN r ↔ x ∈ r ∨ x ∈ H.diskE r := by{
  unfold diskE
  rw[Set.mem_setOf]
  constructor
  · intro h; simp only [h, true_and]; apply em
  · intro h; apply h.elim subset_diskN And.left
}
-- theorem diskF_cface_close : ∀x ∈ H.diskF r, ∀y, H.cface x y → y ∈ H.diskF r := by{

-- }
-- theorem diskF_cface_close_iff {x y : α} (hxy : H.cface x y)
-- : x ∈ H.diskF r ↔ y ∈ H.diskF r := by{
--   constructor
--   · intro h; exact diskF_cface_close _ h _ hxy
--   · {
--     intro h
--     apply H.cface_Symm.symm at hxy
--     exact diskF_cface_close _ h _ hxy
--   }
-- }
-- theorem diskFC_cface_close : ∀x ∈ H.diskFC r, ∀y, H.cface x y → y ∈ H.diskFC r := by{

-- }
-- theorem diskFC_cface_close_iff {x y : α} (hxy : H.cface x y)
-- : x ∈ H.diskFC r ↔ y ∈ H.diskFC r := by{
--   constructor
--   · intro h; exact diskFC_cface_close _ h _ hxy
--   · {
--     intro h
--     apply H.cface_Symm.symm at hxy
--     exact diskFC_cface_close _ h _ hxy
--   }
-- }
-- theorem diskE_cedge_close : ∀x ∈ H.diskE r, ∀y, H.cedge x y → y ∈ H.diskE r := by{

-- }
-- theorem diskE_cedge_close_iff {x y : α} (hxy : H.cedge x y)
-- : x ∈ H.diskE r ↔ y ∈ H.diskE r := by{
--   constructor
--   · intro h; exact diskE_cedge_close _ h _ hxy
--   · {
--     intro h
--     apply H.cedge_Symm.symm at hxy
--     exact diskE_cedge_close _ h _ hxy
--   }
-- }

end Hypermap
