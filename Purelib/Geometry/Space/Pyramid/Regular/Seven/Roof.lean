module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Space.Face.Altitude.Gram
import Purelib.Geometry.Space.Metric.DirectionSpread.Residual
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Cubic
import Init.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Space

open Purelib.Geometry.Space.Face.Altitude

open Purelib.LinearAlgebra

open Purelib.Polynomial.Recurrence.Spread.Roots.Seven

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.Pyramid.Regular.Seven.Roof

section

variable {K : Type*} [ExplicitField K]

/-- The radial quadrance recovered by the Spread law from base-side quadrance `2`, central spread `s`, and equal
base-sector spread `r`. -/
def pagodaRadialQuadrance (centralSpread baseSectorSpread : K)
  : K :=
  2 * baseSectorSpread / centralSpread

/-- The roof-edge quadrance is the radial quadrance plus the unit height quadrance. -/
def pagodaSlopingQuadrance (centralSpread baseSectorSpread : K)
  : K :=
  pagodaRadialQuadrance centralSpread baseSectorSpread + 1

/-- The equal base-sector spread in one triangular roof face. -/
def pagodaFaceBaseSpread (centralSpread baseSectorSpread : K) :
  K :=
  1 - 1 / (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)

/-- The vertex spread of one triangular roof face. -/
def pagodaFaceVertexSpread (centralSpread baseSectorSpread : K)
  : K :=
  4 * pagodaFaceBaseSpread centralSpread baseSectorSpread *
    (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread)

/-- Problem 13's exact finite calculation. The chosen roots `s` and `r` remain explicit data, just as a square-root
witness does elsewhere in the formalization. -/
theorem problem_13
    (centralSpread baseSectorSpread : K)
    (centralSpreadNonzero : centralSpread ≠ 0)
    (slopingQuadranceNonzero :
      pagodaSlopingQuadrance centralSpread baseSectorSpread ≠ 0)
    (seventhFactor : Cubic.seventhSpreadFactor centralSpread = 0)
    (baseIsosceles :
      centralSpread = 4 * baseSectorSpread * (1 - baseSectorSpread)) :
    Cubic.seventhSpreadValue centralSpread = 0 ∧
      (2 * baseSectorSpread - 1) ^ 2 = 1 - centralSpread ∧
      pagodaRadialQuadrance centralSpread baseSectorSpread * centralSpread =
        2 * baseSectorSpread ∧
      pagodaSlopingQuadrance centralSpread baseSectorSpread =
        pagodaRadialQuadrance centralSpread baseSectorSpread + 1 ∧
      4 * pagodaSlopingQuadrance centralSpread baseSectorSpread *
          (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread) = 2 ∧
      pagodaFaceVertexSpread centralSpread baseSectorSpread =
        4 * pagodaFaceBaseSpread centralSpread baseSectorSpread *
          (1 - pagodaFaceBaseSpread centralSpread baseSectorSpread) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    have fourZero : (4 : K) = 0 := by rw [show (4 : K) = 2 * 2 by ring1, twoZero]; ring1
    have baseZero : centralSpread = 0 := by
      calc
        centralSpread = 4 * baseSectorSpread * (1 - baseSectorSpread) :=
          baseIsosceles
        _ = 0 := by rw [fourZero]; ring1
    exact centralSpreadNonzero baseZero
  have denominatorNonzero :
      2 * pagodaSlopingQuadrance centralSpread baseSectorSpread ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero slopingQuadranceNonzero
  have denominatorCancel :=
    ExplicitField.div_mul_cancel (1 : K) denominatorNonzero
  constructor
  · unfold Cubic.seventhSpreadValue
    rw [seventhFactor]
    ring1
  constructor
  · rw [baseIsosceles]
    ring1
  constructor
  · unfold pagodaRadialQuadrance
    exact ExplicitField.div_mul_cancel
      (2 * baseSectorSpread) centralSpreadNonzero
  constructor
  · rfl
  constructor
  · unfold pagodaFaceBaseSpread
    calc
      4 * pagodaSlopingQuadrance centralSpread baseSectorSpread *
          (1 - (1 - 1 /
            (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread))) =
          2 * ((1 /
            (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)) *
              (2 * pagodaSlopingQuadrance centralSpread baseSectorSpread)) :=
                by
                ring1
      _ = 2 := by rw [denominatorCancel]; ring1
  · rfl

/-- The exact adjacent-roof-plane spread as a finite Gram quotient. -/
def pagodaAdjacentPlaneSpread (radius baseSectorSpread : K) : K
  :=
  let L := radius + 1
  let gram := L ^ 2 - radius ^ 2
  let mixed := (radius + 1 - 4 * baseSectorSpread) * L - radius ^ 2
  ((L * gram) ^ 2 - (L * mixed) ^ 2) / (L * gram) ^ 2

/-- Exercise 22.4 before decimal evaluation. The three vectors point from the apex to three consecutive base vertices.
The hypotheses are their exact Gram data; the scaled altitudes are perpendicular to the common roof edge, so their
direction spread is the spread between the adjacent planes. -/
theorem exercise_22_4_exact
    (shared first second : Coordinates3.Vector K) (radius baseSectorSpread : K)
    (slopingNonzero : radius + 1 ≠ 0)
    (gramNonzero : (radius + 1) ^ 2 - radius ^ 2 ≠ 0)
    (sharedQuadrance : Coordinates3.Vector.quadrance shared = radius + 1)
    (firstQuadrance : Coordinates3.Vector.quadrance first = radius + 1)
    (secondQuadrance : Coordinates3.Vector.quadrance second = radius + 1)
    (sharedFirst : Coordinates3.Vector.dot shared first = radius)
    (sharedSecond : Coordinates3.Vector.dot shared second = radius)
    (firstSecond :
      Coordinates3.Vector.dot first second = radius + 1 - 4 * baseSectorSpread) :
    Coordinates3.Vector.spread
        (Gram.scaledFaceAltitude shared first (radius + 1) radius)
        (Gram.scaledFaceAltitude shared second (radius + 1) radius)
        (by
          rw [(Gram.scaledFaceAltitude_metrics shared first second
            (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
            sharedQuadrance firstQuadrance secondQuadrance sharedFirst
            sharedSecond firstSecond).1]
          exact ExplicitField.mul_ne_zero slopingNonzero gramNonzero)
        (by
          rw [(Gram.scaledFaceAltitude_metrics shared first second
            (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
            sharedQuadrance firstQuadrance secondQuadrance sharedFirst
            sharedSecond firstSecond).2.1]
          exact ExplicitField.mul_ne_zero slopingNonzero gramNonzero) =
      pagodaAdjacentPlaneSpread radius baseSectorSpread := by
  let metrics := Gram.scaledFaceAltitude_metrics shared first second
    (radius + 1) radius (radius + 1 - 4 * baseSectorSpread)
    sharedQuadrance firstQuadrance secondQuadrance sharedFirst sharedSecond
    firstSecond
  have metricNonzero :
      (radius + 1) * ((radius + 1) ^ 2 - radius ^ 2) ≠ 0 :=
    ExplicitField.mul_ne_zero slopingNonzero gramNonzero
  have formula := Metric.DirectionSpread.Residual.directionSpread_metric_formula
    (Gram.scaledFaceAltitude shared first (radius + 1) radius)
    (Gram.scaledFaceAltitude shared second (radius + 1) radius)
    ((radius + 1) * ((radius + 1) ^ 2 - radius ^ 2))
    ((radius + 1) *
      ((radius + 1 - 4 * baseSectorSpread) * (radius + 1) - radius ^ 2))
    metricNonzero metrics.1 metrics.2.1 metrics.2.2
  exact formula

/-- Common-denominator numerator and denominator for the adjacent-plane spread computed from rational labels `qNum/qDen`
and `rNum/rDen`. -/
def pagodaPlaneSpreadIntegerPair
    (qNumerator qDenominator rNumerator rDenominator : Int) : Int × Int :=
  let gramNumerator := (2 * qNumerator + qDenominator) * rDenominator
  let mixedNumerator :=
    gramNumerator - 4 * rNumerator * (qNumerator + qDenominator)
  (gramNumerator ^ 2 - mixedNumerator ^ 2, gramNumerator ^ 2)
end
end Purelib.Geometry.Space.Pyramid.Regular.Seven.Roof

end
