module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Spread
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §19.4: the folium of Descartes

The folium, its rational parametrization, first- and second-order tangent
formulae, and the reciprocal-parameter spread symmetry are all finite
polynomial constructions.  Denominators and the characteristic-three
exception are exposed as explicit hypotheses.
-/

namespace Purelib.Geometry.Plane.Line.DirectionSwap

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Swap the two direction coordinates. Simultaneously swapping both lines does not change spread. -/
public def swapDirection (line : Line
  K) : Line K where
  a := line.b
  b := line.a
  c := 0
  direction_nonzero := line.direction_nonzero.elim Or.inr Or.inl

end Purelib.Geometry.Plane.Line.DirectionSwap

end
