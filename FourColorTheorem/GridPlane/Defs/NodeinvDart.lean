import FourColorTheorem.GridPlane.Defs.Darts

/-! 一个函数，在Matte扩展中有用 -/

open Function
open Relation

namespace GridPlane

namespace GPoint
def nodeinvDart (q : GPixel) : GDart := 2 • q + q.mod2.ccw.ccw.ccw
theorem nodeinvDart_half {q : GPixel} : q.nodeinvDart.half = q := by{
  rw[nodeinvDart, GPoint.half_add_double]
  repeat rw[GPoint.mod2_ccw]
  rw[GPoint.half_mod2, add_zero]
}
theorem nodeinvDart_mod2 {q : GPixel} : q.nodeinvDart.mod2 = q.mod2.ccw.ccw.ccw := by{
  rw[nodeinvDart, GPoint.mod2_add_double]
  repeat rw[GPoint.mod2_ccw]
  rw[GPoint.mod2_mod2]
}

end GPoint

end GridPlane
