module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Exclusion
public import Purelib.RootIsolation.Track.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Uniform residual-based finite track refinement

A positive supplied polynomial residual lower bound determines one finite
refinement of the retained winding-one track. The refinement keeps the
original polynomial, ambient box and current state, and returns a state
whose box refines the original box. Every displayed point whose polynomial
residual meets the supplied bound is excluded from the refined box.
-/

namespace Purelib.RootIsolation.Track.Exclusion.Uniform

/-- One track refinement small enough to exclude every point whose displayed
polynomial residual is at least `lower`. -/
@[expose] def refinePastUniformMargin
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) :
    State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current (Uniform.uniformExclusionRadius p ambient lower)
    (Uniform.uniformExclusionRadius_pos p ambient positive)

/-- Uniform residual exclusion refines the original winding-one box. -/
theorem refinePastUniformMargin_refines
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) :
    (refinePastUniformMargin track current lower positive).box.Refines
      current.box :=
  track.nested current (Uniform.uniformExclusionRadius p ambient lower)
    (Uniform.uniformExclusionRadius_pos p ambient positive)

/-- The refined box excludes every displayed point whose residual meets the original positive lower bound. -/
theorem refinePastUniformMargin_excludes
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) (point : Gaussian.Basic.Canonical)
    (pointLower : lower ≤ Gaussian.Norm.Basic.normSq (p.eval point)) :
    ¬(refinePastUniformMargin track current lower positive).box.Contains
      point := by
  apply State.WindingOne.Exclusion.not_contains_of_margin degreePositive
  have accurate := track.accurate current
    (Uniform.uniformExclusionRadius p ambient lower)
    (Uniform.uniformExclusionRadius_pos p ambient positive)
  have coefficientNonnegative := (Uniform.exclusionCoefficient_pos p ambient).le
  exact
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      ((Uniform.uniform_exclusion_margin p ambient positive).trans_le pointLower)

/-- Uniform residual exclusion separates the complete clear box from the refined root box.

The retained overlap point would belong to both closed boxes if no strict
coordinate gap existed. Its genuine uniform polynomial lower bound is
excluded by the same original refinement request, so positive separation
follows without point sampling or another track refinement.
-/
theorem refinePastUniformMargin_separated
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) (region : Box)
    (regionLower : ∀ point, region.Contains point → lower ≤ Gaussian.Norm.Basic.normSq (p.eval point)) :
    (refinePastUniformMargin track current lower positive).box.Separated region := by
  if separated : (refinePastUniformMargin track current lower positive).box.Separated region then
    exact separated
  else
    let point := Box.overlapPoint (refinePastUniformMargin track current lower positive).box region
    have inside := Box.contains_overlapPoint_of_not_separated separated
    exact False.elim (refinePastUniformMargin_excludes degreePositive track current lower positive
      point (regionLower point inside.2) inside.1)

end Purelib.RootIsolation.Track.Exclusion.Uniform

end
