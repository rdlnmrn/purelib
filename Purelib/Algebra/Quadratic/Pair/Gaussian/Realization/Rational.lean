module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization
public import Purelib.Data.Gaussian.Cast.Real
public import Purelib.Data.Rat.Fraction.Square.Check
public import Purelib.Data.Rat.Fraction.Field

/-!
# Rational-coordinate realization from retained nonsquareness inspection

The original real-axis coefficient map is injective. A finite canonical-square
exclusion and the supplied operational generator equation therefore realize
the same original pair ring, retaining its negative-parameter convention.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- Realize the original rational pair ring from the actual generator and complete finite square exclusion. -/
@[expose] def rational (parameter : Rational) (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate parameter))
    (inspection : Square.Inspection parameter) (missing : inspection.root? = none) : Realization Rational where
  parameter := -parameter
  coefficient := Cast.CoordinateTaylor.ofCoordinate
  zero_eq := Cast.ofCoordinate_zero
  one_eq := Cast.ofCoordinate_one
  injective := Cast.ofCoordinate_injective
  add_eq := Cast.ofCoordinate_add
  mul_eq := Cast.ofCoordinate_mul
  sub_eq := Cast.ofCoordinate_sub
  generator := generator
  identity := by
    rewrite [Cast.ofCoordinate_neg, _root_.neg_neg]
    exact identity
  nonsquare := by
    intro candidate same
    rewrite [_root_.neg_neg] at same
    exact inspection.not_square_of_missing missing candidate same

/-- The retained parameter is exactly the negative of the original rational generator square. -/
theorem rational_parameter (parameter : Rational) (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate parameter))
    (inspection : Square.Inspection parameter) (missing : inspection.root? = none) :
    (rational parameter generator identity inspection missing).parameter = -parameter := rfl

/-- Rational realization preserves the entire original coherent generator. -/
theorem rational_generator (parameter : Rational) (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate parameter))
    (inspection : Square.Inspection parameter) (missing : inspection.root? = none) :
    (rational parameter generator identity inspection missing).generator = generator := rfl

end Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

end
