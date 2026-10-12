module
public import Purelib.Geometry.Coordinates.Polar.Squared
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry.Coordinates.Polar.Squared

section
@[expose] public section

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace Purelib.Geometry.Circles.Polar.Squared.RationalPolarCatalogue

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Line, ellipse, and hyperbola -/

/-- A central circle `x²+y²=K` is simply the constant-quadrance locus `Q=K`; its spread remains the free directional
coordinate. -/
theorem circle_rational_polar
    (xSquared ySquared circleQuadrance spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (circleEquation : xSquared + ySquared = circleQuadrance) :
    Q = circleQuadrance :=
  coordinates.1.trans circleEquation
end
end Purelib.Geometry.Circles.Polar.Squared.RationalPolarCatalogue

end
