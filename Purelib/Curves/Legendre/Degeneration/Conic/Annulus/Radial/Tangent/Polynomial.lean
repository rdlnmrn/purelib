module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
public import Purelib.Curves.Legendre.Degeneration.Conic.Derivative
import Purelib.Tactic.Ring

/-!
# The original cubic spatial product rule along the retained radial chart

The independent cubic polynomial derivative consumes the exact original
conic ordinate and abscissa. The separately constructed original base and
ordinate velocities give its finite pointwise product-rule identity.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Polynomial.Dense.Gaussian

/-- The original radial point abscissa is the same cached half-gap ellipse expression read by its base coordinate. -/
theorem point_abscissa (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time : Fraction.Rational) :
    (point site parameter scale (Waist.direction quarter time) positive).abscissa =
      halfGap site parameter * baseDirection scale (Waist.direction quarter time).value := by
  have readback := congrArg (fun base : Canonical => base - center site parameter)
    (point_base site parameter scale (Waist.direction quarter time) positive)
  change center site parameter + (point site parameter scale (Waist.direction quarter time) positive).abscissa -
      center site parameter = center site parameter +
      halfGap site parameter * baseDirection scale (Waist.direction quarter time).value - center site parameter
    at readback
  exact (show (point site parameter scale (Waist.direction quarter time) positive).abscissa =
    center site parameter + (point site parameter scale (Waist.direction quarter time) positive).abscissa -
      center site parameter by ring1).trans
    (readback.trans (by ring1))

namespace Tangent

/-- The original independent cubic derivative times the true base velocity satisfies its exact conic product rule.

The original point and both separately constructed velocities remain
unchanged. The affine cofactor's spatial derivative is one; the normalized
ordinate and abscissa identities derive this curve law internally.
-/
theorem curveVelocity_eq (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (time : Fraction.Rational) :
    (GCD.derivative (Paths.polynomial parameter)).eval
        (point site parameter scale (Waist.direction quarter time) positive).base *
      baseVelocity site parameter scale quarter time =
    baseVelocity site parameter scale quarter time *
        ((point site parameter scale (Waist.direction quarter time) positive).ordinate *
          (point site parameter scale (Waist.direction quarter time) positive).ordinate) +
      2 * (unitPolynomial site).eval (point site parameter scale (Waist.direction quarter time) positive).base *
        (point site parameter scale (Waist.direction quarter time) positive).ordinate *
          ordinateVelocity site parameter scale quarter time := by
  rewrite [(point site parameter scale (Waist.direction quarter time) positive).polynomialDerivative_eq,
    baseVelocity_eq_ordinate_mul site parameter scale quarter positive time,
    ordinateVelocity_eq_abscissa_mul site parameter scale quarter time,
    point_abscissa site parameter scale quarter positive time]
  ring1

end Tangent

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

end
