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
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

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
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) :
    State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius p ambient lower)
    (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos p ambient positive)

/-- Uniform residual exclusion refines the original winding-one box. -/
theorem refinePastUniformMargin_refines
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) :
    (refinePastUniformMargin track current lower positive).box.Refines
      current.box :=
  track.nested current (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius p ambient lower)
    (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos p ambient positive)

/-- The refined box excludes every displayed point whose residual meets the original positive lower bound. -/
theorem refinePastUniformMargin_excludes
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (lower : Fraction.Rational) (positive : 0 < lower) (point : Gaussian.Basic.Canonical)
    (pointLower : lower ≤ Data.Gaussian.Norm.Basic.normSq (p.eval point)) :
    ¬(refinePastUniformMargin track current lower positive).box.Contains
      point := by
  apply State.WindingOne.Exclusion.not_contains_of_margin degreePositive
  have accurate := track.accurate current
    (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius p ambient lower)
    (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos p ambient positive)
  have coefficientNonnegative := (Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient_pos p ambient).le
  exact
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      ((Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniform_exclusion_margin p ambient positive).trans_le pointLower)
end Purelib.RootIsolation.Track.Exclusion.Uniform

end
