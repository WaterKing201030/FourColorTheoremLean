import FourColorTheorem.Discretize.GridHypermap.GMDisk

namespace GridPlane
namespace GridMapProper
open Relation
open Function
variable {n : ℕ} {ab0 : AdjBox n} {cm0 : CMatte n}

structure GMcutout (hgp : GridMapProper ab0 cm0) (E : Fin n → Prop)
  {α : Type _} [Fintype α] [DecidableEq α]
  (G : Hypermap α) (h : α → hgp.GMDart) (r : Fin n → List α) : Prop where
  map_planar : G.Planar
  enc_injective : Injective h
  enc_morph_edge : ∀x, h (G.edge x) = hgp.GMDartHypermap.edge (h x)
  enc_morph_cface : ∀x y, G.cface x y ↔ hgp.GMDartHypermap.cface (h x) (h y)
  enc_morph_node : ∀x, (∀i, E i → x ∉ r i) → h (G.node x) = hgp.GMDartHypermap.node (h x)
  ring_def : ∀i, ((r i).map h).reverse = hgp.GMring i
  ring_proper : ∀i, E i → List.IsCycleChain (fromFun G.node) (r i) ∧ (r i).Nodup

end GridMapProper
end GridPlane
