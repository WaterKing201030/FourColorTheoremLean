import FourColorTheorem.Compactness.Limitcoloring

open RealPlane

theorem compactness {nc : ℕ}
  (fin_colorable : finColorable nc) : ∀m : Map, IsSimpleMap m → m.colorable_with nc := by{
    intro m hm
    use limitColoring m nc
    apply And.intro (limitColoring_isColoring m fin_colorable)
    apply size_limitColoring m fin_colorable
  }

