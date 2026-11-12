module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Monotonicity
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
    denseEvalNormBound polynomial inner ≤ denseEvalNormBound
      polynomial outer ∧
      denseEvalNormLipschitzBound polynomial inner ≤
        denseEvalNormLipschitzBound polynomial outer :=
  Horner.fold_bounds_mono polynomial.coeffs inner.normSqBound_nonneg
    (Box.normSqBound_le_of_refines refines)
    ⟨0, 0⟩ ⟨0, 0⟩ (by decide) (by decide) le_rfl le_rfl

/-- The positive value majorant cannot increase when the box is refined.

Refinement decreases the original folded value bound. Taking its
maximum with the same scalar floor one preserves that comparison. -/
public theorem denseEvalNormMajorant_le_of_refines (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {inner outer : Box} (refines : inner.Refines outer) :
    denseEvalNormMajorant polynomial inner ≤ denseEvalNormMajorant
      polynomial outer :=
  Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
    (Fraction.Order.Basic.le_trans _ _ _
      (denseHornerNormBounds_le_of_refines polynomial refines).1
      (Fraction.Order.Basic.le_max_right _ _))

/-- The positive Lipschitz multiplier cannot increase when the box is refined.

Refinement decreases the original folded slope bound. Taking its
maximum with the same scalar floor one preserves that comparison. -/
public theorem denseLipschitzBound_le_of_refines (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {inner outer : Box} (refines : inner.Refines outer) :
    denseLipschitzBound polynomial inner ≤ denseLipschitzBound
      polynomial outer :=
  Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
    (Fraction.Order.Basic.le_trans _ _ _
      (denseHornerNormBounds_le_of_refines polynomial refines).2
      (Fraction.Order.Basic.le_max_right _ _))

/-- Refining the original box decreases all three original Taylor Horner components on the same coefficient list. -/
public theorem denseHornerTaylorNormBounds_le_of_refines
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) {inner outer : Box}
    (refines : inner.Refines outer) :
    (Taylor.denseHornerTaylorNormBounds polynomial inner).value ≤
        (Taylor.denseHornerTaylorNormBounds polynomial outer).value ∧
      (Taylor.denseHornerTaylorNormBounds polynomial inner).slope ≤
        (Taylor.denseHornerTaylorNormBounds polynomial outer).slope ∧
      Taylor.denseEvalTaylorRemainderBound polynomial inner ≤ Taylor.denseEvalTaylorRemainderBound polynomial outer :=
  Bounds.Taylor.HornerTaylorNormBounds.fold_le polynomial.coeffs inner.normSqBound_nonneg
    (Box.normSqBound_le_of_refines refines) ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Fraction.Order.Basic.le_refl _) (Fraction.Order.Basic.le_refl _) (Fraction.Order.Basic.le_refl _)

/-- Refining a rational box decreases the exact original finite Taylor remainder coefficient. -/
public theorem denseEvalTaylorRemainderBound_le_of_refines
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) {inner outer : Box}
    (refines : inner.Refines outer) :
    Taylor.denseEvalTaylorRemainderBound polynomial inner ≤ Taylor.denseEvalTaylorRemainderBound polynomial outer :=
  (denseHornerTaylorNormBounds_le_of_refines polynomial refines).2.2

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
