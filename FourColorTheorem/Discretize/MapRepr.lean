import FourColorTheorem.RealPlane.Defs.Composition

namespace RealPlane

structure MapRepr (m0 : Map) (n : ℕ) where
  mr : Fin n → Point
  mr_covered : ∀i, m0.cover (mr i)
  mr_injOn : ∀i j, m0 (mr i) (mr j) → i = j

def MapRepr.cover {m0 : Map} {n : ℕ} (MR : MapRepr m0 n)
  : Region := {z | ∃i, m0 (MR.mr i) z}

theorem IsFiniteSimpleMap.exists_mapRepr {m0 : Map}
  [IsFiniteSimpleMap m0] :
  ∃n, ∃MR : MapRepr m0 n, m0.cover ⊆ MR.cover
:= by{
  sorry
}

end RealPlane
