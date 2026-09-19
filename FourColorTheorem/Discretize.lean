import FourColorTheorem.Hypermap.Coloring
import FourColorTheorem.Hypermap.Properties.Composition
import FourColorTheorem.RealPlane.Coloring
import FourColorTheorem.Discretize.GridMap.Construction
import FourColorTheorem.Discretize.GridMap.UniverseLift

namespace RealPlane

/-- Discretize a finite simple real map by approximating its regions with
disjoint mattes, snipping their interiors from a framed grid, and taking
the dual. A four-coloring of this finite hypermap colors the original map. -/
theorem exists_discretize {m0 : Map} [IsFiniteSimpleMap m0]
  : ∃α : Type _, ∃_ : DecidableEq α, ∃_ : Fintype α, ∃G : Hypermap α,
  ∃_ : G.PlanarBridgeless, G.fourColorable → m0.colorable_with 4
  := by
  obtain ⟨n, r, ⟨G⟩⟩ := Discretize.exists_framed_region_grid m0
  obtain ⟨C⟩ := Discretize.exists_complete_grid_cutout G
  refine ⟨ULift C.Dart, inferInstance, inferInstance, C.hypermap.dual.liftDarts,
    C.hypermap.dual.liftDarts_planarBridgeless C.dual_planarBridgeless, ?_⟩
  intro hc
  exact C.coloring_of_complete (C.hypermap.dual.fourColorable_of_liftDarts hc)

end RealPlane
