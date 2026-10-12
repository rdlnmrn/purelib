module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.List.NormBounds
import Purelib.Data.Gaussian.List.Proximity
public import Purelib.Data.Gaussian.List.Proximity.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor.Uniform
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform
import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.Uniform
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.Data.Gaussian

public section
namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

/-- Coefficient quadrance bound shared by every reading admitted at
`target`.  It depends only on the displayed reference reading and the
requested allowance, not on the later process states. -/
@[expose] def admittedExtractionCoefficientBound
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) :
      Fraction.Rational :=
  Gaussian.List.Proximity.Bounds.admittedCoefficientBound (1 :: reference.values) target

/-- Positive derivative-evaluation majorant known from the reference
reading. -/
@[expose] def admittedExtractionDerivative
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    Fraction.Rational :=
  max 1
    (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds (reference.degree + 1)
      (reference.admittedExtractionCoefficientBound target)
      box.normSqBound).slope

/-- The reference-computed derivative-evaluation majorant is strictly positive. -/
theorem admittedExtractionDerivative_pos
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    0 < reference.admittedExtractionDerivative target box :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- Uniform Horner/Taylor scan for every monic reading admitted at
`target`. -/
@[expose] def admittedExtractionTaylorBounds
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds :=
  Dense.Gaussian.Bounds.Taylor.Uniform.uniformTaylorBounds (reference.degree + 1)
    (reference.admittedExtractionCoefficientBound target) box.normSqBound

/-- Positive Lipschitz majorant known from the reference reading. -/
@[expose] def admittedExtractionLipschitz
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    Fraction.Rational :=
  max 1 (reference.admittedExtractionTaylorBounds target box).slope

/-- The reference-computed Lipschitz majorant is strictly positive. -/
theorem admittedExtractionLipschitz_pos
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    0 < reference.admittedExtractionLipschitz target box :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- Positive Taylor-remainder majorant known from the reference reading. -/
@[expose] def admittedExtractionTaylor
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    Fraction.Rational :=
  max 1 (reference.admittedExtractionTaylorBounds target box).remainder

/-- The reference-computed Taylor-remainder majorant is strictly positive. -/
theorem admittedExtractionTaylor_pos
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational) (box :
      Box) :
    0 < reference.admittedExtractionTaylor target box :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- Package the precomputed bounds as the exact majorant resource consumed
by separated Newton extraction after the later reading has been obtained. -/
@[expose] def admittedExtractionMajorants
    (reference reading : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target)
    (same : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.SameChannels reference.entries
      reading.entries)
    (referenceSmall : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt reference.entries
      target)
    (readingSmall : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt reading.entries target)
    (box : Box) :
    Dense.Gaussian.Newton.Box.Majorants.ExtractionMajorants reading.polynomial box := by
  have close := Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.values_close_of_sameChannels same
    referenceSmall readingSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le
  have monicClose := Gaussian.List.Proximity.monicCoefficientsClose coefficientNonnegative close
  have bounded : Gaussian.List.NormBounds.CoefficientsNormLe (1 :: reading.values)
      (reference.admittedExtractionCoefficientBound target) := by
    exact Gaussian.List.Proximity.Bounds.coefficientsNormLe_of_close monicClose positive.le
  have coefficientBoundPositive :
      0 < reference.admittedExtractionCoefficientBound target := by
    exact Gaussian.List.Proximity.Bounds.admittedCoefficientBound_pos (1 :: reference.values) positive
  have degreeEqual : reading.degree = reference.degree :=
    (Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.degree_eq_of_sameChannels same).symm
  have coefficientsLength : reading.polynomial.coeffs.length =
      reference.degree + 1 := by
    change (1 :: reading.values).length = reference.degree + 1
    simp only [List.length_cons, reading.values_length, degreeEqual, -eq_self, -iff_self]
    rfl
  have taylorBounds := Dense.Gaussian.Bounds.Box.Taylor.Uniform.denseHornerTaylor_le_uniform reading.polynomial box
    bounded coefficientBoundPositive.le
  rw [coefficientsLength] at taylorBounds
  have derivativeBound : ∀ {point : Gaussian.Basic.Canonical}, box.Contains point →
      Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.GCD.derivative reading.polynomial).eval point) ≤
        (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds (reference.degree + 1)
          (reference.admittedExtractionCoefficientBound target)
          box.normSqBound).slope := by
    intro point inside
    have automatic := Dense.Gaussian.Bounds.Derivative.Uniform.normSq_evalDerivativeCoeffs_le_uniform
      (1 :: reading.values) point
      (reference.admittedExtractionCoefficientBound target) box.normSqBound
      bounded (box.normSq_le_normSqBound inside)
      coefficientBoundPositive.le box.normSqBound_nonneg
    simp only [Dense.Gaussian.GCD.derivative]
    rw [Dense.Derivative.eval_derivative]
    change Data.Gaussian.Norm.Basic.normSq
        (Dense.Derivative.evalDerivativeCoeffs point
          (1 :: reading.values)).2 ≤ _
    simpa only [List.length_cons, reading.values_length, degreeEqual, -eq_self, -iff_self] using
      automatic
  exact
    { lipschitz := reference.admittedExtractionLipschitz target box
      lipschitz_pos := reference.admittedExtractionLipschitz_pos target box
      lipschitz_upper := by
        unfold Dense.Gaussian.Bounds.Box.denseLipschitzBound
          Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound
          Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.admittedExtractionLipschitz
        rw [Dense.Gaussian.Bounds.Box.Taylor.Uniform.denseHornerNormTaylor_slope]
        apply Fraction.Order.Basic.max_le
        · exact Fraction.Order.Basic.le_max_left _ _
        · apply Data.Rat.Fraction.Order.Basic.le_trans _ _ _ ?_ (Fraction.Order.Basic.le_max_right _ _)
          simpa only [Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.admittedExtractionTaylorBounds,
            -eq_self, -iff_self] using taylorBounds.2.1
      taylor := reference.admittedExtractionTaylor target box
      taylor_pos := reference.admittedExtractionTaylor_pos target box
      taylor_upper := by
        unfold Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound
          Dense.Gaussian.Bounds.Box.Taylor.denseEvalTaylorRemainderBound
          Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.admittedExtractionTaylor
        apply Fraction.Order.Basic.max_le
        · exact Fraction.Order.Basic.le_max_left _ _
        · apply Data.Rat.Fraction.Order.Basic.le_trans _ _ _ ?_ (Fraction.Order.Basic.le_max_right _ _)
          simpa only [Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.admittedExtractionTaylorBounds,
            -eq_self, -iff_self] using taylorBounds.2.2
      derivative := reference.admittedExtractionDerivative target box
      derivative_pos := reference.admittedExtractionDerivative_pos target box
      derivative_upper := by
        intro point inside
        exact (derivativeBound inside).trans (Fraction.Order.Basic.le_max_right _ _) }

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
