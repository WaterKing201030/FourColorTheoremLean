import FourColorTheorem.Hypermap.Coloring.Basic
import FourColorTheorem.Hypermap.Actions.ConcatEdge

open Relation
open Function

namespace Hypermap

variable {α : Type _}
variable [Fintype α]
variable [DecidableEq α]
variable {H : Hypermap α}

open Relation
open Function
open CubeTag

theorem fourColorable_of_cube_fourColorable (Hc' : H.cube.fourColorable) : H.fourColorable := by{
  rcases Hc' with ⟨k', hk'e, hk'f⟩
  let k : α → FourColor := fun x => k' (CTnf, x)
  have hk'f' := isColoring.cface_invariant' hk'f
  use k
  constructor
  · {
    intro x
    unfold k
    have hk'e' := hk'e (CTen, x)
    simp only [edge, CubeDart.edge] at hk'e'
    have hk'f' : k' (CTen, x) = k' (CTnf, x) := by{
      apply hk'f'
      apply H.cube_cface_self
      · trivial
      · trivial
    }
    rwa[← hk'f']
  }
  · {
    unfold k
    intro x
    apply hk'f'
    rw[H.cube_cface_iff_cface (by trivial) (by trivial)]
    rw[H.cface_face]
    apply ReflTransGen.refl
  }
}

end Hypermap
