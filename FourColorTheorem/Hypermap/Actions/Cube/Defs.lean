import FourColorTheorem.Hypermap.Basic
import Mathlib.Tactic.DeriveFintype

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Function
open Relation

inductive CubeTag where
| CTn | CTen | CTf | CTnf | CTe | CTfe
deriving DecidableEq, Fintype
open CubeTag

abbrev CubeDart (_ : Hypermap α) := CubeTag × α
@[inline] instance cubeDart.instFintype : Fintype H.CubeDart :=
  inferInstance

def CubeDart.edge : H.CubeDart → H.CubeDart
| (CTen, x) => (CTnf, H.edge x)
| (CTf, x) => (CTe, node (face x))
| (CTnf, x) => (CTen, node (face x))
| (CTe, x) => (CTf, H.edge x)
| (CTfe, x) => (CTn, x)
| (CTn, x) => (CTfe, x)
def CubeDart.node : H.CubeDart → H.CubeDart
| (CTen, x) => (CTfe, x)
| (CTf, x) => (CTnf, H.edge x)
| (CTnf, x) => (CTe, H.node (face x))
| (CTe, x) => (CTf, x)
| (CTfe, x) => (CTn, face (H.edge x))
| (CTn, x) => (CTen, H.node x)
def CubeDart.face : H.CubeDart → H.CubeDart
| (CTen, x) => (CTf, x)
| (CTf, x) => (CTnf, x)
| (CTnf, x) => (CTn, H.face x)
| (CTe, x) => (CTe, H.edge x)
| (CTfe, x) => (CTfe, H.node x)
| (CTn, x) => (CTen, x)

lemma CubeDart.enf_cancel : ∀ x : H.CubeDart, x.face.node.edge = x := by{
  intro ⟨t, x⟩
  match t with | CTn | CTen | CTf | CTnf | CTe | CTfe => {
    simp[face, node, edge, H.nfe_cancel, H.enf_cancel, H.fen_cancel]
  }
}
@[reducible] def cube (H : Hypermap α) : Hypermap H.CubeDart :=
  ⟨CubeDart.edge, CubeDart.node, CubeDart.face, CubeDart.enf_cancel⟩
@[simp] theorem cube_edge : H.cube.edge = CubeDart.edge := rfl
@[simp] theorem cube_node : H.cube.node = CubeDart.node := rfl
@[simp] theorem cube_face : H.cube.face = CubeDart.face := rfl

end Hypermap
