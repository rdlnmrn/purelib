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

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion

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

/-- Refine the original track using one retained exact nonzero polynomial value.

The executable radius consumes the supplied value rather than evaluating
the polynomial again. The equality certificate retains its original point.
-/
@[expose] def refinePastValue
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point value : Canonical) (_valueEq : p.eval point = value) (nonzero : value ≠ 0) :
    WindingOneState p ambient :=
  track.refine current
    (Uniform.uniformExclusionRadius p ambient
      (Gaussian.Norm.Basic.normSq value))
    (Uniform.uniformExclusionRadius_pos p ambient
      (Gaussian.Norm.Basic.normSq_pos nonzero))

/-- One coefficient-computed track refinement that excludes a displayed
nonroot while retaining the same winding-one track. -/
@[expose] def refinePastPoint
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Canonical) (nonroot : p.eval point ≠ 0) :
    WindingOneState p ambient :=
  track.refine current (Point.exclusionRadius p ambient point)
    (Point.exclusionRadius_pos p ambient point nonroot)

/-- A retained exact evaluation gives the same original point-exclusion refinement. -/
theorem refinePastValue_eq
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point value : Canonical) (valueEq : p.eval point = value) (nonzero : value ≠ 0) :
    refinePastValue track current point value valueEq nonzero =
      refinePastPoint track current point (fun zero => nonzero (valueEq.symm.trans zero)) := by
  cases valueEq
  rfl

/-- Refining to exclude a displayed nonroot preserves containment in the original box. -/
theorem refinePastPoint_refines
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Canonical) (nonroot : p.eval point ≠ 0) :
    (refinePastPoint track current point nonroot).box.Refines current.box :=
  track.nested current (Point.exclusionRadius p ambient point)
    (Point.exclusionRadius_pos p ambient point nonroot)

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
    (Point.exclusionRadius p ambient point)
    (Point.exclusionRadius_pos p ambient point nonroot)
  have coefficientNonnegative := (Uniform.exclusionCoefficient_pos p ambient).le
  exact
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      (Point.exclusion_margin p ambient point nonroot)

end Purelib.RootIsolation.Track.Exclusion.Point

end
