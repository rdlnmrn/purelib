module
public import Purelib.Data.Rat.Distance.Basic
public import Purelib.Geometry.Projective.Line.Basic

public import Purelib.CCL.Measure.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Pointwise algebra of rational projective probes
-/

namespace Purelib.Data.Function.Rat

open Purelib.Data.Rat

open Purelib.CCL.Measure

public section

/-- Negate a rational-valued function on projective points. -/
@[expose] def negProbe
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) : Geometry.Projective.Line.GaussianLine → Coordinate :=
  fun point => -probe point

/-- Negating a rational probe preserves separation between its values.

For two projective inputs, the maximum of the two directed rational differences is
unchanged when both probe values are negated. -/
theorem rationalSeparation_negProbe (probe : Geometry.Projective.Line.GaussianLine → Coordinate)
    (left right : Geometry.Projective.Line.GaussianLine) :
    Distance.rationalSeparation
        (negProbe probe left) (negProbe probe right) =
      Distance.rationalSeparation (probe left) (probe right) := by
  unfold negProbe Distance.rationalSeparation
  rw [Fraction.Order.Basic.max_comm]
  congr 1 <;> ring1

/-- Square each value of a rational probe on projective points. -/
@[expose] def squareProbe
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) : Geometry.Projective.Line.GaussianLine → Coordinate :=
  fun point => probe point ^ 2

/-- Add two rational-valued functions pointwise on their common domain. -/
@[expose] def addProbe
    (left right : Geometry.Projective.Line.GaussianLine → Coordinate) : Geometry.Projective.Line.GaussianLine →
      Coordinate :=
  fun point => left point + right point

end

end Purelib.Data.Function.Rat
