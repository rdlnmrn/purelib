module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Point
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Exclusion
public import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

public section

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Excluding a displayed clear point from a winding-one track

A fixed rational point at which the polynomial is nonzero cannot remain in
an arbitrarily small nonzero-winding box.  The proof uses the existing finite
constant-dominance homotopy: if the point were inside, its nonzero value and
the box's coefficient-computed variation bound would force winding zero.

This is the terminal-point part of the persistent CCL equality handler.  A
local CCL terminal is either an exact polynomial root, or one explicit track
refinement excludes that displayed rational point.
-/

namespace Purelib.RootIsolation.Track.Exclusion.Point

/-- One coefficient-computed track refinement that excludes a displayed
nonroot while retaining the same winding-one track. -/
@[expose] def refinePastPoint
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Canonical) (nonroot : p.eval point ≠ 0) :
    WindingOneState p ambient :=
  track.refine current (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius p ambient point)
    (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius_pos p ambient point nonroot)

/-- Refining to exclude a displayed nonroot preserves containment in the original box. -/
theorem refinePastPoint_refines
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Canonical) (nonroot : p.eval point ≠ 0) :
    (refinePastPoint track current point nonroot).box.Refines current.box :=
  track.nested current (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius p ambient point)
    (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius_pos p ambient point nonroot)

/-- The coefficient-computed refinement excludes the original displayed nonroot from its retained box. -/
theorem refinePastPoint_excludes
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Canonical) (nonroot : p.eval point ≠ 0) :
    ¬(refinePastPoint track current point nonroot).box.Contains point := open Purelib.Data.Rat in
      by
  apply State.WindingOne.Exclusion.not_contains_of_margin degreePositive
  have accurate := track.accurate current
    (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius p ambient point)
    (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusionRadius_pos p ambient point nonroot)
  have coefficientNonnegative := (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient_pos p ambient).le
  exact
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      (Dense.Gaussian.Bounds.Box.Exclusion.Point.exclusion_margin p ambient point nonroot)

end Purelib.RootIsolation.Track.Exclusion.Point

end
