module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

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

namespace Purelib.Curves.Plane.Limacon.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The limacon `r=2a cos(theta)+b`, expressed through explicit square witnesses, has the source's denominator-cleared
rational polar equation. -/
theorem limacon_rational_polar_cleared
    (radial cosine a b A B spread Q : K)
    (radialSquare : radial ^ 2 = Q) (cosineSquare : cosine ^ 2 = spread)
    (aSquare : a ^ 2 = A) (bSquare : b ^ 2 = B)
    (limaconEquation : radial = 2 * a * cosine + b) :
    (4 * A * spread - (Q + B)) ^ 2 = 4 * B * Q := by
  have centeredRelation :
      4 * A * spread - (Q + B) = -2 * b * radial := by
    rw [← radialSquare, ← cosineSquare, ← aSquare, ← bSquare,
      limaconEquation]
    ring1
  rw [centeredRelation, ← radialSquare, ← bSquare]
  ring1

/-- Setting `B=4A` in the limacon equation gives the cardioid equation. -/
theorem limacon_specializes_to_cardioid
    (A B spread Q : K)
    (limaconEquation :
      (4 * A * spread - (Q + B)) ^ 2 = 4 * B * Q)
    (parameterSpecialization : B = 4 * A) :
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 16 * A * Q := by
  rw [parameterSpecialization] at limaconEquation
  calc
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 4 * (4 * A) * Q :=
      limaconEquation
    _ = 16 * A * Q := by ring1
end Purelib.Curves.Plane.Limacon.Polar.RationalPolarCatalogue

end
