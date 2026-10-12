module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Refinement of polynomial box bounds

The original inner and outer boxes supply their retained refinement
comparisons. Folding the same coefficients decreases both computed Horner
components and their positive maximum majorants.
-/

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity

open Purelib.Data.Gaussian

/-- Refining a rational box decreases both computed polynomial value and slope bounds.

The retained refinement witness decreases the original squared-radius
bound. Both computations fold the same coefficient list from zero
initial bounds, so their final value and slope bounds decrease together. -/
public theorem denseHornerNormBounds_le_of_refines (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {inner outer : Box} (refines : inner.Refines outer) :
    Dense.Gaussian.Bounds.Box.denseEvalNormBound polynomial inner ≤ Dense.Gaussian.Bounds.Box.denseEvalNormBound
      polynomial outer ∧
      Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound polynomial inner ≤
        Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound polynomial outer :=
  Purelib.Polynomial.Dense.Gaussian.Bounds.Horner.fold_bounds_mono polynomial.coeffs inner.normSqBound_nonneg
    (Box.normSqBound_le_of_refines refines)
    ⟨0, 0⟩ ⟨0, 0⟩ (by decide) (by decide) le_rfl le_rfl

/-- The positive value majorant cannot increase when the box is refined.

Refinement decreases the original folded value bound. Taking its
maximum with the same scalar floor one preserves that comparison. -/
public theorem denseEvalNormMajorant_le_of_refines (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {inner outer : Box} (refines : inner.Refines outer) :
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant polynomial inner ≤ Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
      polynomial outer :=
  Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
    (Data.Rat.Fraction.Order.Basic.le_trans _ _ _
      (denseHornerNormBounds_le_of_refines polynomial refines).1
      (Fraction.Order.Basic.le_max_right _ _))

/-- The positive Lipschitz multiplier cannot increase when the box is refined.

Refinement decreases the original folded slope bound. Taking its
maximum with the same scalar floor one preserves that comparison. -/
public theorem denseLipschitzBound_le_of_refines (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {inner outer : Box} (refines : inner.Refines outer) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial inner ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound
      polynomial outer :=
  Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
    (Data.Rat.Fraction.Order.Basic.le_trans _ _ _
      (denseHornerNormBounds_le_of_refines polynomial refines).2
      (Fraction.Order.Basic.le_max_right _ _))

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
