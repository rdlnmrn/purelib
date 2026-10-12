module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.GetD
import Purelib.Data.Nat.Order
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Certificate.Raw
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Certificate.Raw
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Path.Affine.SmallCoefficients
public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic.Eight

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier
public import Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Geometry.Rational.Box.Certificate
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Polynomial.Dense.SmallCoefficients
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Cached eight-step same-box preparation

This module threads eight prepared square-root owners on a depth-three
parameter mesh and retains their same-box invariants. Callers supply the
kernel-checked step theorem for every edge. The parametric reset and segment
operations are also used by the reusable root-replay constructions; they do
not depend on fixed quartic sample tables.
-/

namespace Purelib.Examples.Riemann.PreparedEightStepSameBox

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
open Purelib.Geometry
open Purelib.RootIsolation.SquareRoot.Clearance
open Purelib.RootIsolation
open Purelib.Riemann.Paths

open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic

open Purelib.Data.Rat.Certificate.Raw (RationalData)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration (workingRootDiameter workingRootDiameter_positive)

/-- The original Gaussian rational scalar carrier. -/
private abbrev Gaussian := Basic.Canonical

/-- The original exact rational box-coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The original exact rational scalar carrier. -/
private abbrev Q := Fraction.Rational

open Purelib.Riemann.Periods.PeriodCurves
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision
open Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier

/-- The original square-root continuation owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The exact five-coefficient cache for the affine pullback of the quartic minus one.

Retains the original origin and direction with their binomial coefficients in descending degree order. -/
@[expose] def affineQuarticCache (origin direction : Basic.Canonical) :
    CoefficientPolynomial :=
  ⟨[direction ^ 4,
    4 * origin * direction ^ 3,
    6 * origin ^ 2 * direction ^ 2,
    4 * origin ^ 3 * direction,
    origin ^ 4 - 1]⟩

/-- The affine Horner cache through degree zero.

The retained origin and direction multiply the zero polynomial before adding
the constant term. This starts the descending coefficient cache. -/
@[expose] def affineQuarticStage1 (origin direction : Purelib.Data.Gaussian.Basic.Canonical) :=
  Substitution.Affine.mulLine origin direction 0 + Dense.Basic.DensePolynomial.constant 1

/-- The affine Horner cache through degree one.

The retained origin and direction feed the preceding cached stage, followed
by the displayed constant term in the descending coefficient representation. -/
@[expose] def affineQuarticStage2 (origin direction : Purelib.Data.Gaussian.Basic.Canonical) :=
  Substitution.Affine.mulLine origin direction
    (affineQuarticStage1 origin direction) + Dense.Basic.DensePolynomial.constant 0

/-- The affine Horner cache through degree two.

The retained origin and direction feed the preceding cached stage, followed
by the displayed constant term in the descending coefficient representation. -/
@[expose] def affineQuarticStage3 (origin direction : Purelib.Data.Gaussian.Basic.Canonical) :=
  Substitution.Affine.mulLine origin direction
    (affineQuarticStage2 origin direction) + Dense.Basic.DensePolynomial.constant 0

/-- The affine Horner cache through degree three.

The retained origin and direction feed the preceding cached stage, followed
by the displayed constant term in the descending coefficient representation. -/
@[expose] def affineQuarticStage4 (origin direction : Purelib.Data.Gaussian.Basic.Canonical) :=
  Substitution.Affine.mulLine origin direction
    (affineQuarticStage3 origin direction) + Dense.Basic.DensePolynomial.constant 0

/-- The degree-zero affine Horner cache has its exact retained binomial coefficients. -/
theorem affineQuarticStage1_eq (origin direction : Purelib.Data.Gaussian.Basic.Canonical) :
    affineQuarticStage1 origin direction = ⟨[1]⟩ := by
  apply Dense.Basic.DensePolynomial.ext
  with_unfolding_all rfl

/-- The degree-one affine Horner cache has its exact binomial coefficients.

Nonzero origin and direction preserve the retained normalized coefficient
spine. Scalar identities identify its entries in descending degree order. -/
theorem affineQuarticStage2_eq (origin direction : Purelib.Data.Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    affineQuarticStage2 origin direction = ⟨[direction, origin]⟩ := by
  unfold affineQuarticStage2
  rw [affineQuarticStage1_eq, Dense.Basic.DensePolynomial.add_constant_zero,
    Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply Dense.Basic.DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_one_coeff origin direction 1 originNonzero directionNonzero
    (by decide) ⟨[1]⟩ rfl]
  rw [Basic.mul_one direction, Basic.mul_one origin]

/-- The degree-two affine Horner cache has its exact binomial coefficients.

Nonzero origin and direction preserve the retained normalized coefficient
spine. Scalar identities identify its entries in descending degree order. -/
theorem affineQuarticStage3_eq (origin direction : Purelib.Data.Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    affineQuarticStage3 origin direction =
      ⟨[direction ^ 2, 2 * origin * direction, origin ^ 2]⟩ := by
  unfold affineQuarticStage3
  rw [affineQuarticStage2_eq origin direction originNonzero directionNonzero,
    Dense.Basic.DensePolynomial.add_constant_zero, Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply Dense.Basic.DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_two_coeffs origin direction direction origin originNonzero
    directionNonzero directionNonzero ⟨[direction, origin]⟩ rfl]
  apply congrArg₂ List.cons
  · ring1
  · apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · rfl

/-- The degree-three affine Horner cache has its exact binomial coefficients.

Nonzero origin and direction preserve the retained normalized coefficient
spine. Scalar identities identify its entries in descending degree order. -/
theorem affineQuarticStage4_eq (origin direction : Purelib.Data.Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    affineQuarticStage4 origin direction =
      ⟨[direction ^ 3, 3 * origin * direction ^ 2,
        3 * origin ^ 2 * direction, origin ^ 3]⟩ := by
  unfold affineQuarticStage4
  rw [affineQuarticStage3_eq origin direction originNonzero directionNonzero,
    Dense.Basic.DensePolynomial.add_constant_zero, Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply Dense.Basic.DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_three_coeffs origin direction (direction ^ 2)
    (2 * origin * direction) (origin ^ 2) originNonzero directionNonzero
    (Power.pow_ne_zero_direct direction
      directionNonzero 2)
    ⟨[direction ^ 2, 2 * origin * direction, origin ^ 2]⟩ rfl]
  apply congrArg₂ List.cons
  · ring1
  · apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · apply congrArg₂ List.cons
        · ring1
        · rfl
/-- The original affine composition equals its exact five-coefficient quartic cache.

Requires nonzero origin and direction, preserving the original dense polynomial and coefficient order. -/
theorem affineQuarticCache_eq (origin direction : Basic.Canonical)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    Substitution.Affine.composeLine quarticPolynomial origin direction =
      affineQuarticCache origin direction := by
  unfold Substitution.Affine.composeLine
    Substitution.Affine.composeLineCoeffs
  rw [show quarticPolynomial.coeffs =
    [(1 : Basic.Canonical), 0, 0, 0, -1] by with_unfolding_all rfl]
  change Substitution.Affine.mulLine origin direction
      (affineQuarticStage4 origin direction) + Dense.Basic.DensePolynomial.constant (-1) = _
  rw [affineQuarticStage4_eq origin direction originNonzero directionNonzero]
  have mulEq :
      Substitution.Affine.mulLine origin direction
          ⟨[direction ^ 3, 3 * origin * direction ^ 2,
            3 * origin ^ 2 * direction, origin ^ 3]⟩ =
        ⟨[direction ^ 4, 4 * origin * direction ^ 3,
          6 * origin ^ 2 * direction ^ 2,
          4 * origin ^ 3 * direction, origin ^ 4]⟩ := by
    apply Dense.Basic.DensePolynomial.ext
    rw [Path.Affine.SmallCoefficients.mulLine_four_coeffs origin direction (direction ^ 3)
      (3 * origin * direction ^ 2) (3 * origin ^ 2 * direction)
      (origin ^ 3) originNonzero directionNonzero
      (Power.pow_ne_zero_direct direction
        directionNonzero 3)
      ⟨[direction ^ 3, 3 * origin * direction ^ 2,
        3 * origin ^ 2 * direction, origin ^ 3]⟩ rfl]
    apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · apply congrArg₂ List.cons
        · ring1
        · apply congrArg₂ List.cons
          · ring1
          · apply congrArg₂ List.cons
            · ring1
            · rfl
  rw [mulEq, Polynomial.Dense.SmallCoefficients.quartic_add_constant _ _ _ _ _
    (Power.pow_ne_zero_direct direction
      directionNonzero 4)]
  unfold affineQuarticCache
  apply Dense.Basic.DensePolynomial.ext
  rfl

/-- Checked exact norm bounds give dense Lipschitz constant one for the affine quartic cache.

Uses the supplied origin/direction norm identities and retained arithmetic certificate for the unit slope ceiling. -/
theorem affineQuarticCache_denseLipschitz_eq_one
    (origin direction : Basic.Canonical) (originNormData directionNormData : Certificate.Raw.RationalData)
    (originNormEq : Norm.Basic.normSq origin =
      originNormData.toRational)
    (directionNormEq : Norm.Basic.normSq direction =
      directionNormData.toRational)
    (checked : Certificate.Raw.RationalData.Le
      (affineQuarticSlopeData originNormData directionNormData)
        (naturalData 1)) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache origin direction)
        ClearSheetContinuation.parameterAmbient = (1 : Fraction.Rational) := by
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  apply Fraction.Order.Basic.max_eq_left
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [originNormEq, directionNormEq, fourNorm, sixNorm]
  have promoted := Certificate.Raw.RationalData.le_sound checked
  rw [affineQuarticSlopeData_toRational, naturalData_toRational] at promoted
  exact promoted

/-- The affine quartic cache has the checked exact slope when that slope is at least one.

Retains the supplied norm identities and separate exact slope and unit-floor comparisons. -/
theorem affineQuarticCache_denseLipschitz_eq_slope
    (origin direction : Basic.Canonical)
    (originNormData directionNormData slopeData : Certificate.Raw.RationalData)
    (originNormEq : Norm.Basic.normSq origin =
      originNormData.toRational)
    (directionNormEq : Norm.Basic.normSq direction =
      directionNormData.toRational)
    (slopeEq : Certificate.Raw.RationalData.Eq
      (affineQuarticSlopeData originNormData directionNormData) slopeData)
    (oneLeSlope : Certificate.Raw.RationalData.Le (naturalData 1) slopeData) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache origin direction)
        ClearSheetContinuation.parameterAmbient =
      slopeData.toRational := by
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  have promotedSlope := Certificate.Raw.RationalData.eq_sound slopeEq
  rw [affineQuarticSlopeData_toRational] at promotedSlope
  have promotedFloor := Certificate.Raw.RationalData.le_sound oneLeSlope
  rw [naturalData_toRational] at promotedFloor
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [originNormEq, directionNormEq, fourNorm, sixNorm, promotedSlope]
  exact Fraction.Order.Basic.max_eq_right promotedFloor

/-- The parametric same-box arithmetic certificate gives the exact affine quartic Lipschitz value.

Promotes its retained origin/direction norm and maximum identities to the original symbolic coefficient formula. -/
theorem affineQuarticCache_denseLipschitz_eq_generated_parametric
    (data : PreparedParametricSameBoxCellBoundsData) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache data.affineOrigin.toGaussian
          data.affineDirection.toGaussian)
        ClearSheetContinuation.parameterAmbient =
      data.affineDenseLipschitz.toRational := by
  have originNorm : Norm.Basic.normSq
      data.affineOrigin.toGaussian = data.affineOriginNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineOriginNormSqExact
  have directionNorm : Norm.Basic.normSq
      data.affineDirection.toGaussian =
        data.affineDirectionNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineDirectionNormSqExact
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  have dense := Certificate.Raw.RationalData.eq_sound data.affineDenseLipschitzExact
  rw [maxData_toRational, naturalData_toRational,
    affineQuarticSlopeData_toRational,
    show ((1 : Nat) : Fraction.Rational) = (1 : Fraction.Rational) by rfl] at dense
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [originNorm, directionNorm, fourNorm, sixNorm]
  exact dense

/-- The retained reset-cell arithmetic certificate gives the exact affine quartic Lipschitz value. -/
theorem affineQuarticCache_denseLipschitz_eq_generated_reset
    (data : PreparedParametricResetCellBoundsData) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache data.affineOrigin.toGaussian
          data.affineDirection.toGaussian)
        ClearSheetContinuation.parameterAmbient =
      data.affineDenseLipschitz.toRational := by
  have originNorm : Norm.Basic.normSq
      data.affineOrigin.toGaussian = data.affineOriginNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineOriginNormSqExact
  have directionNorm : Norm.Basic.normSq
      data.affineDirection.toGaussian =
        data.affineDirectionNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineDirectionNormSqExact
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  have dense := Certificate.Raw.RationalData.eq_sound data.affineDenseLipschitzExact
  rw [maxData_toRational, naturalData_toRational,
    affineQuarticSlopeData_toRational,
    show ((1 : Nat) : Fraction.Rational) = (1 : Fraction.Rational) by rfl] at dense
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [originNorm, directionNorm, fourNorm, sixNorm]
  exact dense

/-- The retained double-reset arithmetic certificate gives the exact affine quartic Lipschitz value. -/
theorem affineQuarticCache_denseLipschitz_eq_generated_double_reset
    (data : PreparedParametricDoubleResetCellBoundsData) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache data.affineOrigin.toGaussian
          data.affineDirection.toGaussian)
        ClearSheetContinuation.parameterAmbient =
      data.affineDenseLipschitz.toRational := by
  have originNorm : Norm.Basic.normSq
      data.affineOrigin.toGaussian = data.affineOriginNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineOriginNormSqExact
  have directionNorm : Norm.Basic.normSq
      data.affineDirection.toGaussian =
        data.affineDirectionNormSq.toRational := by
    rw [← Certificate.Raw.GaussianData.normSq_toRational]
    exact Certificate.Raw.RationalData.eq_sound data.affineDirectionNormSqExact
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  have dense := Certificate.Raw.RationalData.eq_sound data.affineDenseLipschitzExact
  rw [maxData_toRational, naturalData_toRational,
    affineQuarticSlopeData_toRational,
    show ((1 : Nat) : Fraction.Rational) = (1 : Fraction.Rational) by rfl] at dense
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [originNorm, directionNorm, fourNorm, sixNorm]
  exact dense

/-- The fixed-eighth same-box certificate gives the original exact affine quartic Lipschitz value. -/
theorem affineQuarticCache_denseLipschitz_eq_generated
    (data : PreparedSameBoxCellBoundsData) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache data.affineOrigin.toGaussian
          data.affineDirection.toGaussian)
        ClearSheetContinuation.parameterAmbient =
      data.affineDenseLipschitz.toRational :=
  affineQuarticCache_denseLipschitz_eq_generated_parametric
    data.toPreparedParametricSameBoxCellBoundsData

/-- The retained parametric Lipschitz value times one sixty-fourth equals the exact displayed variation. -/
theorem generatedAffineQuarticVariation_parametric
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.affineDenseLipschitz.toRational * (1 / 64 : Fraction.Rational) =
      data.variationUpper.toRational := by
  have promoted := Certificate.Raw.RationalData.eq_sound data.affineVariationExact
  rw [Certificate.Raw.RationalData.mul_toRational, oneSixtyFourthData_toRational] at promoted
  exact promoted

/-- The fixed-eighth Lipschitz value times one sixty-fourth equals the exact displayed variation. -/
theorem generatedAffineQuarticVariation
    (data : PreparedSameBoxCellBoundsData) :
    data.affineDenseLipschitz.toRational * (1 / 64 : Fraction.Rational) =
      data.variationUpper.toRational :=
  generatedAffineQuarticVariation_parametric
    data.toPreparedParametricSameBoxCellBoundsData

/-- The affine quartic Lipschitz constant is one under the specified origin and direction norm bounds.

Requires origin squared norm at most 5/16 and direction squared norm exactly 1/64. -/
theorem affineQuarticCache_denseLipschitz_eq_one_of_norm_le
    (origin direction : Basic.Canonical)
    (originNormLe : Norm.Basic.normSq origin ≤
      (5 / 16 : Fraction.Rational))
    (directionNormEq : Norm.Basic.normSq direction =
      (1 / 64 : Fraction.Rational)) :
    Bounds.Box.denseLipschitzBound
        (affineQuarticCache origin direction)
        ClearSheetContinuation.parameterAmbient = (1 : Fraction.Rational) := by
  let originNormData : RationalData :=
    { numerator := 5, denominator := 16, denominatorPositive := by decide }
  let directionNormData : RationalData :=
    { numerator := 1, denominator := 64, denominatorPositive := by decide }
  have checked : Certificate.Raw.RationalData.Le
      (affineQuarticSlopeData originNormData directionNormData)
      (naturalData 1) := by decide
  have upperBound := Certificate.Raw.RationalData.le_sound checked
  rw [affineQuarticSlopeData_toRational, naturalData_toRational] at upperBound
  have originDataEq : originNormData.toRational = (5 / 16 : Fraction.Rational) := by rfl
  have directionDataEq : directionNormData.toRational = (1 / 64 : Fraction.Rational) := by rfl
  rw [originDataEq, directionDataEq] at upperBound
  have fourNorm : Norm.Basic.normSq
      (4 : Basic.Canonical) = (16 : Fraction.Rational) := by
    with_unfolding_all decide
  have sixNorm : Norm.Basic.normSq
      (6 : Basic.Canonical) = (36 : Fraction.Rational) := by
    with_unfolding_all decide
  let x := Norm.Basic.normSq origin
  let d := Norm.Basic.normSq direction
  have dNonnegative : (0 : Fraction.Rational) ≤ d :=
    Norm.Basic.normSq_nonneg direction
  have xNonnegative : (0 : Fraction.Rational) ≤ x :=
    Norm.Basic.normSq_nonneg origin
  have xSquareLe : x ^ 2 ≤ (5 / 16 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct xNonnegative originNormLe 2
  have xCubeLe : x ^ 3 ≤ (5 / 16 : Fraction.Rational) ^ 3 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct xNonnegative originNormLe 3
  have dCubeNonnegative : (0 : Fraction.Rational) ≤ d ^ 3 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct dNonnegative 3
  have dSquareNonnegative : (0 : Fraction.Rational) ≤ d ^ 2 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct dNonnegative 2
  have coefficientBNonnegative : (0 : Fraction.Rational) ≤ 192 * 16 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 192) (by omega)).le
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 16) (by omega)).le
  have coefficientCNonnegative : (0 : Fraction.Rational) ≤ 32 * 36 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 32) (by omega)).le
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 36) (by omega)).le
  have coefficientDNonnegative : (0 : Fraction.Rational) ≤ 4 * 16 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4) (by omega)).le
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 16) (by omega)).le
  have bLe : 192 * (16 * x * d ^ 3) ≤
      192 * (16 * (5 / 16 : Fraction.Rational) * d ^ 3) := by
    rw [show 192 * (16 * x * d ^ 3) = (192 * 16 * d ^ 3) * x by ring1,
      show 192 * (16 * (5 / 16 : Fraction.Rational) * d ^ 3) =
        (192 * 16 * d ^ 3) * (5 / 16) by ring1]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      originNormLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct coefficientBNonnegative
        dCubeNonnegative)
  have cLe : 32 * (36 * x ^ 2 * d ^ 2) ≤
      32 * (36 * (5 / 16 : Fraction.Rational) ^ 2 * d ^ 2) := by
    rw [show 32 * (36 * x ^ 2 * d ^ 2) =
        (32 * 36 * d ^ 2) * x ^ 2 by ring1,
      show 32 * (36 * (5 / 16 : Fraction.Rational) ^ 2 * d ^ 2) =
        (32 * 36 * d ^ 2) * (5 / 16 : Fraction.Rational) ^ 2 by ring1]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      xSquareLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct coefficientCNonnegative
        dSquareNonnegative)
  have dLe : 4 * (16 * x ^ 3 * d) ≤
      4 * (16 * (5 / 16 : Fraction.Rational) ^ 3 * d) := by
    rw [show 4 * (16 * x ^ 3 * d) = (4 * 16 * d) * x ^ 3 by ring1,
      show 4 * (16 * (5 / 16 : Fraction.Rational) ^ 3 * d) =
        (4 * 16 * d) * (5 / 16 : Fraction.Rational) ^ 3 by ring1]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      xCubeLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct coefficientDNonnegative
        dNonnegative)
  unfold affineQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  apply Fraction.Order.Basic.max_eq_left
  simp only [Norm.Basic.normSq_mul,
    Power.normSq_pow]
  rw [fourNorm, sixNorm]
  change 1024 * d ^ 4 + 192 * (16 * x * d ^ 3) +
      32 * (36 * x ^ 2 * d ^ 2) + 4 * (16 * x ^ 3 * d) ≤ 1
  have dEq : d = (1 / 64 : Fraction.Rational) := directionNormEq
  rw [dEq] at bLe cLe dLe ⊢
  exact (add_le_add (add_le_add (add_le_add le_rfl bLe) cLe) dLe).trans
    upperBound

/-- A point with real part minus one quarter and imaginary square at most one quarter has norm square at most 5/16. -/
theorem normSq_point_negQuarter_le_fiveSixteenths (imaginary : Fraction.Rational)
    (imaginarySqLe : imaginary ^ 2 ≤ (1 / 4 : Fraction.Rational)) :
    Norm.Basic.normSq
        (point (-1 / 4) imaginary) ≤ (5 / 16 : Fraction.Rational) := by
  unfold point Norm.Basic.normSq
  have quarterSquare : (-1 / 4 : Fraction.Rational) ^ 2 = 1 / 16 := by
    rw [pow_two, Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4) (by omega)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4) (by omega)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 16) (by omega)).ne'
    ring1
  rw [quarterSquare]
  calc
    (1 / 16 : Fraction.Rational) + imaginary ^ 2 ≤ 1 / 16 + 1 / 4 :=
      add_le_add le_rfl imaginarySqLe
    _ = 5 / 16 := by with_unfolding_all decide

/-- Checked exact rational square data gives the squared norm of its displayed Gaussian point. -/
theorem normSq_point_eq_of_data
    (real imaginary norm : Certificate.Raw.RationalData)
    (checked : Certificate.Raw.RationalData.Eq
      (Certificate.Raw.RationalData.add (squareData real) (squareData imaginary)) norm) :
    Norm.Basic.normSq
        (point real.toRational imaginary.toRational) = norm.toRational := by
  have promoted := Certificate.Raw.RationalData.eq_sound checked
  rw [Certificate.Raw.RationalData.add_toRational, squareData_toRational,
    squareData_toRational] at promoted
  exact promoted

open Purelib.Approximation.Rational in
/-- An exact one-sixteenth derivative margin bounds the original preparation radius by one sixty-fourth. -/
theorem preparationRadius_le_oneSixtyFourth_of_margin_eq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (rootDiameter : Fraction.Rational)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 16 : Fraction.Rational)) :
    UniformSquareRootPreparation.preparationRadius segment
        rootDiameter ≤ (1 / 64 : Fraction.Rational) := by
  unfold UniformSquareRootPreparation.preparationRadius
  rw [marginEq]
  have targetPositive : (0 : Fraction.Rational) < (1 / 16 : Fraction.Rational) / (72 * 8) :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
        (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by omega)))
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by omega))
        (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by omega)))
  have squareLt := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive
  have targetEq : (1 / 16 : Fraction.Rational) / (72 * 8) = 1 / 9216 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct, one_mul]
    rw [← Fraction.Field.inv_mul_direct]
    rw [show (16 : Fraction.Rational) * (72 * 8) = 9216 by ring1]
  have squareEq : (1 / 64 : Fraction.Rational) ^ 2 = 1 / 4096 := by
    rw [pow_two, Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by omega)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by omega)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4096) (by omega)).ne'
    ring1
  have targetLt : (1 / 16 : Fraction.Rational) / (72 * 8) < (1 / 64 : Fraction.Rational) ^ 2 := by
    rw [targetEq, squareEq]
    have productPositive : (0 : Fraction.Rational) < (4096 : Fraction.Rational) * 9216 :=
      Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 4096) (by omega))
        (Fraction.Cast.Order.natCast_pos_direct (n := 9216) (by omega))
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := (4096 : Fraction.Rational) * 9216) _ productPositive
    have cancelNineThousand : (1 / (9216 : Fraction.Rational) : Fraction.Rational) * 9216 = 1 :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 9216) (by omega)).ne'
    have cancelFourThousand : (1 / (4096 : Fraction.Rational) : Fraction.Rational) * 4096 = 1 :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4096) (by omega)).ne'
    calc
      (1 / (9216 : Fraction.Rational) : Fraction.Rational) * ((4096 : Fraction.Rational) * 9216) =
          ((1 / (9216 : Fraction.Rational) : Fraction.Rational) * 9216) * 4096 := by ring1
      _ = 4096 := by
        rw [cancelNineThousand]
        ring1
      _ < 9216 := Fraction.Cast.Order.natCast_lt_direct
        (m := 4096) (n := 9216) (by omega)
      _ = ((1 / (4096 : Fraction.Rational) : Fraction.Rational) * 4096) * 9216 := by
        rw [cancelFourThousand]
        ring1
      _ = (1 / (4096 : Fraction.Rational) : Fraction.Rational) * ((4096 : Fraction.Rational) * 9216) := by ring1
  have dyadicLt :
      SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
          ((1 / 16 : Fraction.Rational) / (72 * 8)) < (1 / 64 : Fraction.Rational) :=
    Bounds.Square.lt_of_sq_lt_sq_of_nonneg
      (Fraction.Order.Field.div_nonneg_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by omega)).le
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by omega)).le)
      (squareLt.trans targetLt)
  exact (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_left _ _).trans dyadicLt.le)

/-- The stated derivative-margin and radius bounds put predicted clearance below the original one-eighth transport
floor.

Requires a positive root-diameter request, margin at most 1/16, radius at most 1/64 and derivative majorant at least
two. -/
theorem predictedClearance_le_eighthTransportFloor_of_sixteenthMargin
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 16 : Fraction.Rational))
    (radiusLe :
      UniformSquareRootPreparation.preparationRadius segment
        rootDiameter ≤ (1 / 64 : Fraction.Rational))
    (derivativeLower : (2 : Fraction.Rational) ≤
      UniformSquareRootPreparation.rootSampleDerivativeMajorant
        segment) :
    UniformSquareRootPreparation.predictedClearance segment
        rootDiameter ≤
      (1 / 8 : Fraction.Rational) ^ 2 / (4 * 65536) := by
  let radius :=
    UniformSquareRootPreparation.preparationRadius segment
      rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  let derivative :=
    UniformSquareRootPreparation.rootSampleDerivativeMajorant
      segment
  let floor : Fraction.Rational := (1 / 8) ^ 2 / (4 * 65536)
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * (2 * derivative * radius ^ 2)) ≤ floor
  have radiusPositive : 0 < radius :=
    UniformSquareRootPreparation.preparationRadius_positive
      segment rootDiameterPositive
  have radiusSqNonnegative : 0 ≤ radius ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct radius
  have marginNonnegative : 0 ≤ margin :=
    (ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Fraction.Rational) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by omega))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (Fraction.Order.Field.le_div_iff_pos
      taylorDenominatorPositive).mp
      (UniformSquareRootPreparation.preparationRadius_sq_lt_taylorRatio
        segment rootDiameterPositive).le
  have correctionCoefficientNonnegative : (0 : Fraction.Rational) ≤ 36 * 8 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 36) (by omega)).le
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by omega)).le
  have correctionNonnegative :
      0 ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      correctionCoefficientNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    have doubledCorrection :
        2 * ((36 * 8) * radius ^ 2) ≤ margin := by
      calc
        2 * ((36 * 8) * radius ^ 2) = radius ^ 2 * (72 * 8) := by ring1
        _ ≤ margin := scaledTaylor
    have singleCorrection : (36 * 8) * radius ^ 2 ≤ margin :=
      (calc
        (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
        _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) (Fraction.Order.Arithmetic.mul_nonneg_direct
              correctionCoefficientNonnegative radiusSqNonnegative)
        _ ≤ margin := doubledCorrection)
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          singleCorrection radiusSqNonnegative
  have differenceNonnegative :
      0 ≤ margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct
          correctionNonnegative _
      _ = margin * radius ^ 2 := by ring1
  have marginSquareLe : margin ^ 2 ≤ (1 / 256 : Fraction.Rational) := by
    calc
      margin ^ 2 ≤ (1 / 16 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct marginNonnegative
          marginLe 2
      _ = (1 / 256 : Fraction.Rational) := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        apply Fraction.Field.div_eq_div_of_cross_mul
          (Fraction.Field.mul_ne_zero_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 16) (by omega)).ne'
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 16) (by omega)).ne')
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 256) (by omega)).ne'
        ring1
  have radiusSquareLe : radius ^ 2 ≤ (1 / 4096 : Fraction.Rational) := by
    calc
      radius ^ 2 ≤ (1 / 64 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
          radiusLe 2
      _ = (1 / 4096 : Fraction.Rational) := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        apply Fraction.Field.div_eq_div_of_cross_mul
          (Fraction.Field.mul_ne_zero_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 64) (by omega)).ne'
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 64) (by omega)).ne')
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4096) (by omega)).ne'
        ring1
  have radiusFourthLe : (radius ^ 2) ^ 2 ≤
      (1 / 4096 : Fraction.Rational) * radius ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusSquareLe radiusSqNonnegative
  have coefficientEq :
      (1 / 256 : Fraction.Rational) * (1 / 4096) = 1 / 1048576 := by
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 256) (by omega)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4096) (by omega)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 1048576) (by omega)).ne'
    ring1
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (1 / 1048576 : Fraction.Rational) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct differenceNonnegative
          differenceLeFirst 2
      _ = margin ^ 2 * (radius ^ 2) ^ 2 := by ring1
      _ ≤ (1 / 256 : Fraction.Rational) * (radius ^ 2) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          marginSquareLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
      _ ≤ (1 / 256 : Fraction.Rational) *
          ((1 / 4096 : Fraction.Rational) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusFourthLe
          (Fraction.Order.Field.div_nonneg_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 1) (by omega)).le
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 256) (by omega)).le)
      _ = (1 / 1048576 : Fraction.Rational) * radius ^ 2 := by
        rw [← mul_assoc, coefficientEq]
  have floorNonnegative : 0 ≤ floor :=
    Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 8))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4) (by omega)).le
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 65536) (by omega)).le)
  have coefficientLe : (1 / 1048576 : Fraction.Rational) ≤ floor * 16 := by
    apply le_of_eq
    apply Fraction.Field.mul_right_cancel_of_ne
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 1048576) (by omega)).ne'
    have leftCancel :
        (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1048576) (by omega)).ne'
    have floorCancel : floor * 16777216 = 1 := by
      dsimp only [floor]
      have largeDenominatorNonzero : (4 * 65536 : Fraction.Rational) ≠ 0 :=
        (Fraction.Order.Arithmetic.mul_pos_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by omega))
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by omega))).ne'
      have eighthCancel : (1 / 8 : Fraction.Rational) * 8 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 8) (by omega)).ne'
      rw [show (16777216 : Fraction.Rational) = (4 * 65536) * 64 by ring1]
      rw [show (((1 / 8 : Fraction.Rational) ^ 2 / (4 * 65536)) *
          ((4 * 65536) * 64)) =
        (((1 / 8 : Fraction.Rational) ^ 2 / (4 * 65536)) *
          (4 * 65536)) * 64 by ring1,
        Fraction.Field.div_mul_cancel_of_ne _ _
          largeDenominatorNonzero]
      rw [show (1 / 8 : Fraction.Rational) ^ 2 * 64 =
          ((1 / 8 : Fraction.Rational) * 8) ^ 2 by ring1,
        eighthCancel, one_pow]
    calc
      (1 / 1048576 : Fraction.Rational) * 1048576 = 1 := leftCancel
      _ = (floor * 16) * 1048576 := by
        rw [show (floor * 16) * (1048576 : Fraction.Rational) =
          floor * 16777216 by ring1, floorCancel]
  have denominatorLower : 16 * radius ^ 2 ≤
      4 * (2 * derivative * radius ^ 2) := by
    calc
      16 * radius ^ 2 = (4 * (2 * 2)) * radius ^ 2 := by ring1
      _ ≤ (4 * (2 * derivative)) * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              derivativeLower (by decide)) (by decide))
          radiusSqNonnegative
      _ = 4 * (2 * derivative * radius ^ 2) := by ring1
  have numeratorLeFloorDenominator :
      (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 ≤
        floor * (4 * (2 * derivative * radius ^ 2)) := by
    calc
      (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 ≤
          (1 / 1048576 : Fraction.Rational) * radius ^ 2 := numeratorLe
      _ ≤ (floor * 16) * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          coefficientLe radiusSqNonnegative
      _ = floor * (16 * radius ^ 2) := by ring1
      _ ≤ floor * (4 * (2 * derivative * radius ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          denominatorLower floorNonnegative
  have denominatorPositive :
      (0 : Fraction.Rational) < 4 * (2 * derivative * radius ^ 2) := by
    change (0 : Fraction.Rational) < 4 *
      UniformSquareRootPreparation.linearizationMajorant
        segment rootDiameter
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (UniformSquareRootPreparation.linearizationMajorant_positive
        segment rootDiameterPositive)
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    numeratorLeFloorDenominator

/-- An exact one-sixteenth derivative margin puts the original predicted clearance below the one-eighth transport floor.
-/
theorem predictedClearance_le_eighthTransportFloor_of_margin_eq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 16 : Fraction.Rational)) :
    UniformSquareRootPreparation.predictedClearance segment
        rootDiameter ≤
      (1 / 8 : Fraction.Rational) ^ 2 / (4 * 65536) :=
  predictedClearance_le_eighthTransportFloor_of_sixteenthMargin
    segment rootDiameter rootDiameterPositive marginEq.le
      (preparationRadius_le_oneSixtyFourth_of_margin_eq
        segment rootDiameter marginEq)
      ((by decide : (2 : Fraction.Rational) ≤ 10).trans
        (UniformSquareRootPreparation.ten_le_rootSampleDerivativeMajorant
          segment))

/-- An exact quarter derivative margin gives preparation radius one sixty-fourth at the original working request. -/
theorem preparationRadius_eq_oneSixtyFourth_of_quarter_margin
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 4 : Fraction.Rational)) :
    UniformSquareRootPreparation.preparationRadius segment
        workingRootDiameter = (1 / 64 : Fraction.Rational) := by
  rw [UniformSquareRootPreparation.preparationRadius]
  rw [marginEq]
  unfold workingRootDiameter
  decide +kernel

/-- The original finite radicand majorant bounds twice a starting squared-norm lower bound plus one.

Uses the exact leftmost scan leaf and supplied lower bound without replacing the finite scan. -/
theorem twice_startNormSqLower_add_one_le_radicandNormBound
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (sourceNormSqLower : Fraction.Rational)
    (sourceNormLower : sourceNormSqLower ≤
      Norm.Basic.normSq
        (polynomial.eval (segment.pointAt 0))) :
    2 * sourceNormSqLower + 1 ≤
      UniformSquareRootPreparation.radicandNormBound segment := by
  let leafDirection :=
    UniformSquareRootPreparation.dyadicLeftmostDirection
      (finish - start) 4
  let leafPolynomial :=
    Substitution.Affine.composeLine polynomial start leafDirection
  have sourceNormLower' : sourceNormSqLower ≤
      Norm.Basic.normSq (polynomial.eval start) := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using
      sourceNormLower
  have constantLower : 2 * sourceNormSqLower ≤
      2 * Norm.Basic.normSq
        (polynomial.eval start) := by
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      sourceNormLower' (by decide)
  have leafMajorant :=
    Bounds.Box.twice_normSq_eval_zero_le_denseEvalNormMajorant
      leafPolynomial ClearSheetContinuation.parameterAmbient
  have leafEvaluation : leafPolynomial.eval 0 = polynomial.eval start := by
    dsimp only [leafPolynomial]
    rw [Substitution.Affine.eval_composeLineGaussian]
    rw [zero_mul, add_zero]
  rw [leafEvaluation] at leafMajorant
  have leafLower : 2 * sourceNormSqLower ≤
      UniformSquareRootPreparation.dyadicLineNormMajorant
        polynomial start leafDirection 0 :=
    constantLower.trans leafMajorant
  have scannedLower :=
    UniformSquareRootPreparation.dyadicLineNormMajorant_leftmost_le
      polynomial start (finish - start) 4
  unfold UniformSquareRootPreparation.radicandNormBound
    UniformSquareRootPreparation.radicandScanDepth
  calc
    2 * sourceNormSqLower + 1 ≤
        UniformSquareRootPreparation.dyadicLineNormMajorant
          polynomial start leafDirection 0 + 1 :=
      Fraction.Order.Arithmetic.add_le_add_right_direct leafLower 1
    _ ≤ UniformSquareRootPreparation.dyadicLineNormMajorant
          polynomial start (finish - start) 4 + 1 :=
      Fraction.Order.Arithmetic.add_le_add_right_direct scannedLower 1

/-- Starting squared norm at least one gives original finite radicand majorant at least three. -/
theorem three_le_radicandNormBound_of_one_le_start_normSq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (sourceNormLower : (1 : Fraction.Rational) ≤
      Norm.Basic.normSq
        (polynomial.eval (segment.pointAt 0))) :
    (3 : Fraction.Rational) ≤
      UniformSquareRootPreparation.radicandNormBound segment := by
  have generated :=
    twice_startNormSqLower_add_one_le_radicandNormBound segment 1
      sourceNormLower
  simpa only [show (2 : Fraction.Rational) * 1 + 1 = 3 by ring1] using generated

/-- The retained numerical comparison bounds original quarter-margin predicted clearance by its specified transport
floor.

Requires the exact radius, positive transport margin, source-norm lower bound, matching derivative floor and original
scalar budget inequality. -/
theorem predictedClearance_le_transportFloor_of_quarter_margin
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (transportMargin sourceNormSqLower derivativeLower : Fraction.Rational)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 4 : Fraction.Rational))
    (radiusEq :
      UniformSquareRootPreparation.preparationRadius segment
        workingRootDiameter = (1 / 64 : Fraction.Rational))
    (transportMarginPositive : 0 < transportMargin)
    (sourceNormLower : sourceNormSqLower ≤
      Norm.Basic.normSq
        (polynomial.eval (segment.pointAt 0)))
    (derivativeLowerEq : derivativeLower =
      4 * (2 * ((1 / 4 : Fraction.Rational) +
        (2 * sourceNormSqLower + 1))))
    (numerical :
      ((1 / 4 : Fraction.Rational) * (1 / 64) ^ 2 -
          36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
            transportMargin *
          (4 * (2 * derivativeLower * (1 / 64 : Fraction.Rational) ^ 2))) :
    UniformSquareRootPreparation.predictedClearance segment
        workingRootDiameter ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        transportMargin := by
  have radicandLower :=
    twice_startNormSqLower_add_one_le_radicandNormBound segment
      sourceNormSqLower sourceNormLower
  have derivativeLowerBound : derivativeLower ≤
      UniformSquareRootPreparation.rootSampleDerivativeMajorant
        segment := by
    rw [derivativeLowerEq]
    unfold UniformSquareRootPreparation.rootSampleDerivativeMajorant
      UniformSquareRootPreparation.rootSampleNormSqMajorant
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · exact add_le_add le_rfl radicandLower
      · decide
    · decide
  have radiusPositive : (0 : Fraction.Rational) < (1 / 64 : Fraction.Rational) :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega))
  have denominatorPositive : (0 : Fraction.Rational) <
      4 * (2 *
        UniformSquareRootPreparation.rootSampleDerivativeMajorant
          segment * (1 / 64 : Fraction.Rational) ^ 2) :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (UniformSquareRootPreparation.rootSampleDerivativeMajorant_positive
            segment))
        (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2))
  have denominatorLower :
      4 * (2 * derivativeLower * (1 / 64 : Fraction.Rational) ^ 2) ≤
        4 * (2 *
          UniformSquareRootPreparation.rootSampleDerivativeMajorant
            segment * (1 / 64 : Fraction.Rational) ^ 2) := by
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          derivativeLowerBound (by decide)
      · exact Fraction.Order.Arithmetic.sq_nonneg_direct _
    · decide
  unfold UniformSquareRootPreparation.predictedClearance
    UniformSquareRootPreparation.linearizationMajorant
  rw [marginEq, radiusEq]
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  exact numerical.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      denominatorLower
      (ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt_pos
        transportMargin transportMarginPositive).le)

/-- The retained parametric certificate bounds quarter-margin predicted clearance by its own transport floor. -/
theorem predictedClearance_le_generatedTransportFloor_of_quarter_margin
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (data : PreparedParametricSameBoxCellBoundsData)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 4 : Fraction.Rational))
    (sourceNormLower : data.sourceNormSqLower.toRational ≤
      Norm.Basic.normSq
        (polynomial.eval (segment.pointAt 0))) :
    UniformSquareRootPreparation.predictedClearance segment
        workingRootDiameter ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.transportMargin.toRational := by
  exact predictedClearance_le_transportFloor_of_quarter_margin segment
    data.transportMargin.toRational data.sourceNormSqLower.toRational
      data.predictedDerivativeLower.toRational marginEq
        (preparationRadius_eq_oneSixtyFourth_of_quarter_margin segment marginEq)
          data.transportMargin_positive sourceNormLower
            data.predictedDerivativeLower_eq
              data.predictedClearanceFitsTransport_sound

/-- A quarter derivative margin and starting norm-square floor one bound predicted clearance by the one-eighth transport
floor. -/
theorem predictedClearance_le_eighthTransportFloor_of_quarter_margin
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 4 : Fraction.Rational))
    (sourceNormLower : (1 : Fraction.Rational) ≤
      Norm.Basic.normSq
        (polynomial.eval (segment.pointAt 0))) :
    UniformSquareRootPreparation.predictedClearance segment
        workingRootDiameter ≤
      (1 / 8 : Fraction.Rational) ^ 2 / (4 * 65536) := by
  have radicandLower :=
    three_le_radicandNormBound_of_one_le_start_normSq segment sourceNormLower
  have derivativeLower : (26 : Fraction.Rational) ≤
      UniformSquareRootPreparation.rootSampleDerivativeMajorant
        segment := by
    unfold UniformSquareRootPreparation.rootSampleDerivativeMajorant
      UniformSquareRootPreparation.rootSampleNormSqMajorant
    calc
      (26 : Fraction.Rational) = 4 * (2 * ((1 / 4 : Fraction.Rational) + 3)) := by
        with_unfolding_all decide
      _ ≤ 4 * (2 * ((1 / 4 : Fraction.Rational) +
          UniformSquareRootPreparation.radicandNormBound
            segment)) := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          · exact add_le_add le_rfl radicandLower
          · decide
        · decide
  exact
    UniformSquareRootPreparation.predictedClearance_le_eighthTransportFloor_of_exactRadius
      segment workingRootDiameter marginEq
        (preparationRadius_eq_oneSixtyFourth_of_quarter_margin segment marginEq)
          derivativeLower

/-- Exact input-owner transport preserves the original subdivision terminal owner heterogeneously. -/
private theorem eightStepCastOwner_terminalOwner_heq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    HEq (subdivision.castOwner equal).terminalOwner
      subdivision.terminalOwner := by
  cases equal
  rfl

/-- Prepending an original cached step preserves the retained tail's exact terminal owner heterogeneously. -/
theorem eightStepNextCached_terminalOwner_heq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      ClearSheetContinuation.variationBound segment
          left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    HEq (Subdivision.nextCached segment within left owner request cached
      ordered cachedSmall canonicalSmall remaining).terminalOwner
        remaining.terminalOwner := by
  unfold Subdivision.nextCached
  exact eightStepCastOwner_terminalOwner_heq _ _

/-- Exact radicand transport preserves the original owner's ambient-clearance dominance. -/
theorem castSameBoxOwner_dominance
    {source target : Basic.Canonical} (equal : source = target)
    (owner : Owner source)
    (dominance :
      ExactQuadraticOwnerClearance.AmbientClearanceDominance
        owner) :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner) := by
  cases equal
  exact dominance

/-- Exact radicand transport preserves the original owner's quadratic ambient budget. -/
theorem castSameBoxOwner_budget
    {source target : Basic.Canonical} (equal : source = target)
    (owner : Owner source)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      owner) :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner) := by
  cases equal
  exact budget

/-- Exact radicand transport preserves a bound on the original ambient-left clearance. -/
theorem castSameBoxOwner_ambientLeftLe
    {source target : Basic.Canonical} (equal : source = target)
    (owner : Owner source) (upper : Fraction.Rational)
    (bound : owner.track.initial.ambientLeftClearance.bound ≤ upper) :
    (SquareRoot.Owner.Transport.castOwnerParameter equal owner).track.initial.ambientLeftClearance.bound ≤
      upper := by
  cases equal
  exact bound

/-- Exact radicand transport preserves the original ambient-left clearance value. -/
@[simp] theorem castSameBoxOwner_ambientLeftBound
    {source target : Basic.Canonical} (equal : source = target)
    (owner : Owner source) :
    (SquareRoot.Owner.Transport.castOwnerParameter equal owner).track.initial.ambientLeftClearance.bound =
      owner.track.initial.ambientLeftClearance.bound := by
  cases equal
  rfl

/-- Transport a retained same-box state across an exact equality of endpoint radicands.

Preserves the original owner, box, clearance floor, dominance, budget and ambient cap/refinement certificates. -/
theorem reindexSameBoxState
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {sourceStart sourceFinish targetStart targetFinish : Basic.Canonical}
    (sourceSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      sourceStart sourceFinish)
    (targetSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      targetStart targetFinish)
    (sourceLeft targetLeft : Endpoint)
    (owner : Owner
      (polynomial.eval (sourceSegment.pointAt sourceLeft.parameter)))
    (equal : polynomial.eval (sourceSegment.pointAt sourceLeft.parameter) =
      polynomial.eval (targetSegment.pointAt targetLeft.parameter))
    (box : Rational.Box) (preparedUpper marginFloor : Fraction.Rational)
    (state : ParametricSameBoxState sourceSegment sourceLeft owner box
      preparedUpper marginFloor) :
    ParametricSameBoxState targetSegment targetLeft
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner) box preparedUpper
        marginFloor where
  boxEq := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
    exact state.boxEq
  clearanceFloor := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_clearance_bound]
    exact state.clearanceFloor
  dominance := castSameBoxOwner_dominance equal owner state.dominance
  budget := castSameBoxOwner_budget equal owner state.budget
  ambientLeftLe := castSameBoxOwner_ambientLeftLe equal owner preparedUpper
    state.ambientLeftLe
  ambientRefines := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_ambient]
    exact state.ambientRefines

/-- Transport a retained same-box state while supplying a new exact ambient-left cap.

Keeps the original owner, box and floor; requires the new cap on the actual source owner's ambient-left clearance. -/
theorem reindexRecapSameBoxState
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {sourceStart sourceFinish targetStart targetFinish : Basic.Canonical}
    (sourceSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      sourceStart sourceFinish)
    (targetSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      targetStart targetFinish)
    (sourceLeft targetLeft : Endpoint)
    (owner : Owner
      (polynomial.eval (sourceSegment.pointAt sourceLeft.parameter)))
    (equal : polynomial.eval (sourceSegment.pointAt sourceLeft.parameter) =
      polynomial.eval (targetSegment.pointAt targetLeft.parameter))
    (box : Rational.Box) (oldUpper newUpper marginFloor : Fraction.Rational)
    (state : ParametricSameBoxState sourceSegment sourceLeft owner box
      oldUpper marginFloor)
    (ambientLeftLe : owner.track.initial.ambientLeftClearance.bound ≤ newUpper) :
    ParametricSameBoxState targetSegment targetLeft
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner) box newUpper
        marginFloor where
  boxEq := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
    exact state.boxEq
  clearanceFloor := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_clearance_bound]
    exact state.clearanceFloor
  dominance := castSameBoxOwner_dominance equal owner state.dominance
  budget := castSameBoxOwner_budget equal owner state.budget
  ambientLeftLe := castSameBoxOwner_ambientLeftLe equal owner newUpper
    ambientLeftLe
  ambientRefines := by
    rw [SquareRoot.Owner.Transport.castOwnerParameter_ambient]
    exact state.ambientRefines

/-- Weaken a retained same-box state's ambient-left cap along a supplied scalar inequality. -/
theorem widenSameBoxState
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (left : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (box : Rational.Box) (oldUpper newUpper marginFloor : Fraction.Rational)
    (state : ParametricSameBoxState segment left owner box oldUpper marginFloor)
    (upperLe : oldUpper ≤ newUpper) :
    ParametricSameBoxState segment left owner box newUpper marginFloor where
  boxEq := state.boxEq
  clearanceFloor := state.clearanceFloor
  dominance := state.dominance
  budget := state.budget
  ambientLeftLe := state.ambientLeftLe.trans upperLe
  ambientRefines := state.ambientRefines

/-- Replace a retained same-box state's cap using a bound on its actual owner's ambient-left clearance. -/
theorem recapSameBoxState
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (left : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (box : Rational.Box) (oldUpper newUpper marginFloor : Fraction.Rational)
    (state : ParametricSameBoxState segment left owner box oldUpper marginFloor)
    (ambientLeftLe : owner.track.initial.ambientLeftClearance.bound ≤ newUpper) :
    ParametricSameBoxState segment left owner box newUpper marginFloor where
  boxEq := state.boxEq
  clearanceFloor := state.clearanceFloor
  dominance := state.dominance
  budget := state.budget
  ambientLeftLe := ambientLeftLe
  ambientRefines := state.ambientRefines

/-- The original cached reset edge and its retained successor same-box state.

Keeps canonical carry success, the selected new box, the actual advanced owner and separate quarter-square upper bounds
for ambient-left clearance and clearance. -/
structure ParametricResetStep
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (newBox : Rational.Box)
    (preparedUpper marginFloor : Fraction.Rational) : Prop where
  /-- The original canonical prepared owner carries the retained edge variation. -/ canonicalSmall :
    ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound
  /-- The original canonical prepared source box equals the selected reset box. -/ preparedBox :
    (CachedSource.canonical segment left owner request).preparedOwner.track.initial.box =
      newBox
  /-- The actual cached successor owner retains the stated new-box same-box invariant. -/ nextState :
    ParametricSameBoxState segment request.endpoint
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request) canonicalSmall)
        newBox preparedUpper marginFloor
  /-- The actual successor ambient-left clearance is at most one quarter of the retained cap squared. -/
    nextAmbientLeftLeQuarter :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.ambientLeftClearance.bound ≤
      preparedUpper ^ 2 / 4
  /-- The actual successor clearance is at most one quarter of the retained cap squared. -/ nextClearanceLeQuarter :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.clearance.bound ≤
      preparedUpper ^ 2 / 4

namespace ParametricResetStep

/-- The exact successor owner computed by the original cached reset edge. -/
@[expose] def nextOwner
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    {request : StepRequest} {newBox : Rational.Box}
    {preparedUpper marginFloor : Fraction.Rational}
    (step : ParametricResetStep segment within left owner request newBox
      preparedUpper marginFloor) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  advanceCached segment within left owner request
    (CachedSource.canonical segment left owner request) step.canonicalSmall

end ParametricResetStep

/-- The retained direct bounds and original clearance ceiling also bound the strengthened owner's clearance. -/
theorem strengthenQuadraticOwner_clearance_le_upper_of_directBounds
    {parameter : Basic.Canonical} (owner : Owner parameter)
    (lower upper : Fraction.Rational)
    (bounds :
      ExactQuadraticOwnerClearance.DirectBoundaryBounds parameter
        owner.track.initial.box lower upper)
    (clearanceLe : owner.track.initial.clearance.bound ≤ upper) :
    (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      owner).track.initial.clearance.bound ≤ upper := by
  rw [ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    owner bounds.leftNonzero bounds.rightNonzero bounds.bottomNonzero
      bounds.topNonzero]
  exact Fraction.Order.Basic.max_le clearanceLe bounds.le_upper

/-- Build a reset-step certificate from the exact selected prepared owner and its retained bounds.

Requires the original selection identity, small variation, exact box/ambient, positive residual floor, transport
prediction, dominance, budget and target norm ceiling. -/
theorem parametricResetStepOfPreparedOwner
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (newBox : Rational.Box)
    (preparedUpper marginFloor : Fraction.Rational)
    (selectedOwner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (preparedEq : prepared segment left owner request = selectedOwner)
    (selectedSmall :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        selectedOwner.track.initial.clearance.bound)
    (selectedInitialBox : selectedOwner.track.initial.box = newBox)
    (selectedAmbientBox : selectedOwner.ambient = newBox)
    (selectedDominance :
      ExactQuadraticOwnerClearance.AmbientClearanceDominance
        selectedOwner)
    (selectedBudget :
      ExactQuadraticOwnerClearance.QuadraticAmbientBudget
        selectedOwner)
    (selectedAmbientLeftLe :
      selectedOwner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (preparedContracts : preparedUpper ^ 2 / 4 ≤ preparedUpper)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (marginFloorPositive : 0 < marginFloor)
    (predictedLeFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        marginFloor)
    (selectedMargin : marginFloor ≤
      selectedOwner.track.initial.clearance.bound -
        Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (targetNormSqLe : Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricResetStep segment within left owner request newBox preparedUpper
      marginFloor := by
  let cached := CachedSource.canonical segment left owner request
  have cachedSmall :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedSmall
  have cachedInitialBox : cached.preparedOwner.track.initial.box = newBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedInitialBox
  have cachedAmbientBox : cached.preparedOwner.ambient = newBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedAmbientBox
  have cachedDominance :
      ExactQuadraticOwnerClearance.AmbientClearanceDominance
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedDominance
  have cachedBudget :
      ExactQuadraticOwnerClearance.QuadraticAmbientBudget
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedBudget
  have cachedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedAmbientLeftLe
  have cachedMargin : marginFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedMargin
  let advanceCache := parametricQuadraticAdvanceCache segment within left owner
    request cached cachedSmall different marginFloor marginFloorPositive
      predictedLeFloor cachedDominance cachedMargin cachedBudget targetNormSqLe
  have cachedQuarterLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
        (4 : Fraction.Rational)⁻¹ ≤ preparedUpper ^ 2 * (4 : Fraction.Rational)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
          cachedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Fraction.Rational) < 4)).le
  refine
    { canonicalSmall := ?_
      preparedBox := cachedInitialBox
      nextState :=
        { boxEq := advanceCache.initialBox.trans cachedInitialBox
          clearanceFloor := advanceCache.clearanceFloor
          dominance := advanceCache.dominance
          budget := advanceCache.budget
          ambientLeftLe := (advanceCache.ambientLeftQuarterSq.trans
            cachedQuarterLe).trans preparedContracts
          ambientRefines := ?_ }
      nextAmbientLeftLeQuarter :=
        advanceCache.ambientLeftQuarterSq.trans cachedQuarterLe
      nextClearanceLeQuarter :=
        advanceCache.clearanceQuarterSq.trans cachedQuarterLe }
  · rw [preparedEq]
    exact selectedSmall
  · rw [advanceCache.ambientBox, cachedAmbientBox]
    exact Rational.Box.refines_refl _

/-- Build a reset-step certificate with separate retained transport and residual floors.

Keeps the exact selected owner and side majorants, using the supplied residual-square tradeoff to establish the
independent retained successor floor. -/
theorem retainedParametricResetStepOfPreparedOwner
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (newBox : Rational.Box)
    (preparedUpper retainedFloor residualFloor sideUpper : Fraction.Rational)
    (selectedOwner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (preparedEq : prepared segment left owner request = selectedOwner)
    (selectedSmall :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        selectedOwner.track.initial.clearance.bound)
    (selectedInitialBox : selectedOwner.track.initial.box = newBox)
    (selectedAmbientBox : selectedOwner.ambient = newBox)
    (selectedDominance :
      ExactQuadraticOwnerClearance.AmbientClearanceDominance
        selectedOwner)
    (selectedBudget :
      ExactQuadraticOwnerClearance.QuadraticAmbientBudget
        selectedOwner)
    (selectedAmbientLeftLe :
      selectedOwner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (preparedContracts : preparedUpper ^ 2 / 4 ≤ preparedUpper)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (predictedLeFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        retainedFloor)
    (selectedResidualPositive : 0 < residualFloor)
    (selectedResidual : residualFloor ≤
      selectedOwner.track.initial.clearance.bound -
        Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (selectedSideBounds :
      ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
        selectedOwner sideUpper)
    (tradeoff :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          retainedFloor ≤ residualFloor ^ 2 / (4 * sideUpper))
    (targetNormSqLe : Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricResetStep segment within left owner request newBox preparedUpper
      retainedFloor := by
  let cached := CachedSource.canonical segment left owner request
  have cachedSmall :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedSmall
  have cachedInitialBox : cached.preparedOwner.track.initial.box = newBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedInitialBox
  have cachedAmbientBox : cached.preparedOwner.ambient = newBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedAmbientBox
  have cachedDominance :
      ExactQuadraticOwnerClearance.AmbientClearanceDominance
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedDominance
  have cachedBudget :
      ExactQuadraticOwnerClearance.QuadraticAmbientBudget
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedBudget
  have cachedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedAmbientLeftLe
  have cachedResidual : residualFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedResidual
  have cachedSideBounds :
      ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
        cached.preparedOwner sideUpper := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEq]
    exact selectedSideBounds
  let advanceCache := retainedFloorQuadraticAdvanceCache segment within left
    owner request cached cachedSmall different retainedFloor residualFloor
      sideUpper predictedLeFloor cachedDominance selectedResidualPositive
        cachedResidual cachedSideBounds tradeoff cachedBudget targetNormSqLe
  have cachedQuarterLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
        (4 : Fraction.Rational)⁻¹ ≤ preparedUpper ^ 2 * (4 : Fraction.Rational)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
          cachedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Fraction.Rational) < 4)).le
  refine
    { canonicalSmall := ?_
      preparedBox := cachedInitialBox
      nextState :=
        { boxEq := advanceCache.initialBox.trans cachedInitialBox
          clearanceFloor := advanceCache.clearanceFloor
          dominance := advanceCache.dominance
          budget := advanceCache.budget
          ambientLeftLe := (advanceCache.ambientLeftQuarterSq.trans
            cachedQuarterLe).trans preparedContracts
          ambientRefines := ?_ }
      nextAmbientLeftLeQuarter :=
        advanceCache.ambientLeftQuarterSq.trans cachedQuarterLe
      nextClearanceLeQuarter :=
        advanceCache.clearanceQuarterSq.trans cachedQuarterLe }
  · rw [preparedEq]
    exact selectedSmall
  · rw [advanceCache.ambientBox, cachedAmbientBox]
    exact Rational.Box.refines_refl _

/-! ## Generated same-box certificate bridge -/

/-- A semantic bridge from retained fixed-eighth arithmetic data to eligible original mesh edges.

Keeps source/target identities, exact variation, distinct radicands, the nominal box, cap, diameter/refinement and
one-eighth prediction certificates. -/
structure GeneratedSameBoxCellCertificate
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (data : PreparedSameBoxCellBoundsData)
    (box : Rational.Box) (preparedUpper : Fraction.Rational)
    (eligible : Fin 8 → Prop) : Prop where
  /-- Each eligible original source evaluation equals the retained arithmetic source parameter. -/ sourceParameter : ∀
    edge, eligible edge →
    polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter) =
      (data.sourceParameter edge).toGaussian
  /-- Each eligible original target evaluation equals the retained arithmetic target parameter. -/ targetParameter : ∀
    edge, eligible edge →
    polynomial.eval
        (segment.pointAt (Eight.secondEdgeRequest edge).endpoint.parameter) =
      (data.targetParameter edge).toGaussian
  /-- Each eligible original edge has exactly the retained arithmetic variation. -/ variation : ∀ edge, eligible edge →
    ClearSheetContinuation.variationBound segment
        (Eight.secondMeshEndpoint (Eight.secondEdgeSource
          edge)).parameter
        (Eight.secondEdgeRequest edge).endpoint.parameter =
      data.variationUpper.toRational
  /-- Every eligible edge has distinct original source and target radicands. -/ different : ∀ edge, eligible edge →
    polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter) ≠
      polynomial.eval
        (segment.pointAt (Eight.secondEdgeRequest edge).endpoint.parameter)
  /-- The retained arithmetic box equals the original nominal box. -/ boxEq : data.box.toBox = box
  /-- The retained arithmetic direct upper bound is below the supplied cap. -/ directUpperLe :
    data.directUpper.toRational ≤ preparedUpper
  /-- The original box meets every retained edge's diameter request. -/ boxSmall : ∀ edge, box.diagonalSq <
    (Eight.secondEdgeRequest edge).rootDiameter
  /-- The original box refines the segment's preparation ambient box. -/ boxRefines : box.Refines
    (UniformSquareRootPreparation.rootAmbient segment)
  /-- The original preparation prediction is below the specified retained transport floor. -/ predictedLeFloor :
    preparedClearanceLower segment (Eight.secondMeshEndpoint 0)
      (Eight.secondEdgeRequest 0) ≤
    ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      (1 / 8 : Fraction.Rational)

namespace GeneratedSameBoxCellCertificate

/-- Turn an eligible original edge and retained arithmetic certificate into its exact same-box advance.

Preserves the actual input owner and one-eighth successor floor, with separate residual margin, side majorant and
direct-cap certificates. -/
theorem step
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {data : PreparedSameBoxCellBoundsData}
    {box : Rational.Box} {preparedUpper : Fraction.Rational}
    {eligible : Fin 8 → Prop}
    (certificate : GeneratedSameBoxCellCertificate segment within data box
      preparedUpper eligible)
    (edge : Fin 8) (edgeEligible : eligible edge)
    (owner : Owner
      (polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter)))
    (state : ParametricSameBoxState segment
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)) owner box preparedUpper
        (1 / 8 : Fraction.Rational)) :
    ParametricSameBoxStep segment within
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)) owner
        (Eight.secondEdgeRequest edge) box data.directLower.toRational preparedUpper
          (1 / 8 : Fraction.Rational) := by
  apply retainedFloorSameBoxStepOfGeneratedBoundsFromState segment within
    (Eight.secondMeshEndpoint (Eight.secondEdgeSource edge))
      owner
      (Eight.secondEdgeRequest edge) box preparedUpper (1 / 8 : Fraction.Rational) state
        (certificate.boxSmall edge) certificate.boxRefines
          certificate.predictedLeFloor data.directLower.toRational
            (residualFloor := data.residualMarginFloor.toRational)
            (sideUpper := data.sideMajorantUpper.toRational)
  · have bounds := data.directBoundaryBounds edge
    rw [certificate.sourceParameter edge edgeEligible, ← certificate.boxEq]
    exact
      { leftNonzero := bounds.leftNonzero
        rightNonzero := bounds.rightNonzero
        bottomNonzero := bounds.bottomNonzero
        topNonzero := bounds.topNonzero
        lower_le := bounds.lower_le
        le_upper := bounds.le_upper.trans certificate.directUpperLe }
  · rw [certificate.variation edge edgeEligible]
    exact data.variationUpper_lt_directLower
  · exact certificate.different edge edgeEligible
  · exact data.residualMarginFloor_positive
  · rw [certificate.variation edge edgeEligible,
      certificate.sourceParameter edge edgeEligible,
      certificate.targetParameter edge edgeEligible]
    exact data.residualMargin_le edge
  · rw [certificate.sourceParameter edge edgeEligible, ← certificate.boxEq]
    exact data.quadraticBoxSideMajorantBounds edge
      data.sideMajorantUpper.toRational data.one_le_sideMajorantUpper le_rfl
  · exact data.retainedEighthTradeoff_sound
  · rw [certificate.targetParameter edge edgeEligible]
    exact (data.targetNormSq_le edge).trans
      data.targetNormSqUpper_le_twoHundredFiftySix

end GeneratedSameBoxCellCertificate

/-- A semantic bridge from retained parametric arithmetic data to eligible original mesh edges.

Keeps the generator-selected transport margin separate from residual and side budgets, with exact endpoint/variation
identities and per-edge direct caps. -/
structure GeneratedParametricSameBoxCellCertificate
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (data : PreparedParametricSameBoxCellBoundsData)
    (box : Rational.Box) (preparedUpper : Fraction.Rational)
    (eligible : Fin 8 → Prop) : Prop where
  /-- Each eligible original source evaluation equals the retained arithmetic source parameter. -/ sourceParameter : ∀
    edge, eligible edge →
    polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter) =
      (data.sourceParameter edge).toGaussian
  /-- Each eligible original target evaluation equals the retained arithmetic target parameter. -/ targetParameter : ∀
    edge, eligible edge →
    polynomial.eval
        (segment.pointAt (Eight.secondEdgeRequest edge).endpoint.parameter) =
      (data.targetParameter edge).toGaussian
  /-- Each eligible original edge has exactly the retained arithmetic variation. -/ variation : ∀ edge, eligible edge →
    ClearSheetContinuation.variationBound segment
        (Eight.secondMeshEndpoint (Eight.secondEdgeSource
          edge)).parameter
        (Eight.secondEdgeRequest edge).endpoint.parameter =
      data.variationUpper.toRational
  /-- Every eligible edge has distinct original source and target radicands. -/ different : ∀ edge, eligible edge →
    polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter) ≠
      polynomial.eval
        (segment.pointAt (Eight.secondEdgeRequest edge).endpoint.parameter)
  /-- The retained arithmetic box equals the original nominal box. -/ boxEq : data.box.toBox = box
  /-- Each eligible edge's retained direct upper bound is below the supplied cap. -/ directUpperAtLe : ∀ edge, eligible
    edge →
    (data.directUpperAt edge).toRational ≤ preparedUpper
  /-- The original box meets every retained edge's diameter request. -/ boxSmall : ∀ edge, box.diagonalSq <
    (Eight.secondEdgeRequest edge).rootDiameter
  /-- The original box refines the segment's preparation ambient box. -/ boxRefines : box.Refines
    (UniformSquareRootPreparation.rootAmbient segment)
  /-- The original preparation prediction is below the specified retained transport floor. -/ predictedLeFloor :
    preparedClearanceLower segment (Eight.secondMeshEndpoint 0)
      (Eight.secondEdgeRequest 0) ≤
    ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.transportMargin.toRational

namespace GeneratedParametricSameBoxCellCertificate

/-- Turn an eligible original edge and retained arithmetic certificate into its exact same-box advance.

Preserves the actual input owner and retained parametric successor floor, with separate residual margin, side majorant
and direct-cap certificates. -/
theorem step
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {data : PreparedParametricSameBoxCellBoundsData}
    {box : Rational.Box} {preparedUpper : Fraction.Rational}
    {eligible : Fin 8 → Prop}
    (certificate : GeneratedParametricSameBoxCellCertificate segment within
      data box preparedUpper eligible)
    (edge : Fin 8) (edgeEligible : eligible edge)
    (owner : Owner
      (polynomial.eval
        (segment.pointAt
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)).parameter)))
    (state : ParametricSameBoxState segment
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)) owner box preparedUpper
        data.transportMargin.toRational) :
    ParametricSameBoxStep segment within
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)) owner
        (Eight.secondEdgeRequest edge) box data.directLower.toRational preparedUpper
          data.transportMargin.toRational := by
  apply retainedFloorSameBoxStepOfGeneratedBoundsFromState segment within
    (Eight.secondMeshEndpoint (Eight.secondEdgeSource edge))
      owner
      (Eight.secondEdgeRequest edge) box preparedUpper
        data.transportMargin.toRational state
          (certificate.boxSmall edge) certificate.boxRefines
            certificate.predictedLeFloor data.directLower.toRational
              (residualFloor := data.residualMarginFloor.toRational)
              (sideUpper := data.sideMajorantUpper.toRational)
  · have bounds := data.directBoundaryBoundsAt edge
    rw [certificate.sourceParameter edge edgeEligible, ← certificate.boxEq]
    exact
      { leftNonzero := bounds.leftNonzero
        rightNonzero := bounds.rightNonzero
        bottomNonzero := bounds.bottomNonzero
        topNonzero := bounds.topNonzero
        lower_le := bounds.lower_le
        le_upper := bounds.le_upper.trans
          (certificate.directUpperAtLe edge edgeEligible) }
  · rw [certificate.variation edge edgeEligible]
    exact data.variationUpper_lt_directLower
  · exact certificate.different edge edgeEligible
  · exact data.residualMarginFloor_positive
  · rw [certificate.variation edge edgeEligible,
      certificate.sourceParameter edge edgeEligible,
      certificate.targetParameter edge edgeEligible]
    exact data.residualMargin_le edge
  · rw [certificate.sourceParameter edge edgeEligible, ← certificate.boxEq]
    exact data.quadraticBoxSideMajorantBounds edge
      data.sideMajorantUpper.toRational data.one_le_sideMajorantUpper le_rfl
  · exact data.retainedFloorTradeoff_sound
  · rw [certificate.targetParameter edge edgeEligible]
    exact (data.targetNormSq_le edge).trans
      data.targetNormSqUpper_le_twoHundredFiftySix

end GeneratedParametricSameBoxCellCertificate

set_option genInjectivity false in
/-- The original eight-step subdivision with its exact terminal owner and cached readbacks.

Retains all prepared source boxes, endpoint, ordered dyadic edges and requests, plus terminal state and separate
quarter-square clearance bounds. -/
structure EightStepSameBoxResult
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter)))
    (box : Rational.Box) (preparedUpper marginFloor : Fraction.Rational) where
  /-- The actual original terminal owner at mesh point eight. -/ ownerEight : Owner
    (polynomial.eval (segment.pointAt (Eight.secondMeshEndpoint 8).parameter))
  /-- The retained same-box state of the original terminal owner. -/ terminalState : ParametricSameBoxState segment
    (Eight.secondMeshEndpoint 8)
    ownerEight box preparedUpper marginFloor
  /-- The terminal ambient-left clearance is at most one quarter of the retained cap squared. -/
    terminalAmbientLeftLeQuarter :
    ownerEight.track.initial.ambientLeftClearance.bound ≤
      preparedUpper ^ 2 / 4
  /-- The terminal clearance is at most one quarter of the retained cap squared. -/ terminalClearanceLeQuarter :
    ownerEight.track.initial.clearance.bound ≤ preparedUpper ^ 2 / 4
  /-- The actual retained prepared source-owner box for each original edge. -/ preparedBox : Fin 8 →
    Rational.Box
  /-- The original cached dependent subdivision indexed by its exact input owner. -/ subdivision : Subdivision segment
    within (Eight.secondMeshEndpoint 0) ownerZero
  /-- The original subdivision's prepared source boxes equal the ordered eight-entry cached list. -/ preparedBoxes_eq :
    subdivision.preparedBoxes =
    [preparedBox 0, preparedBox 1, preparedBox 2, preparedBox 3,
      preparedBox 4, preparedBox 5, preparedBox 6, preparedBox 7]
  /-- The original subdivision terminal owner equals the cached terminal owner heterogeneously. -/ terminalOwner_heq :
    HEq subdivision.terminalOwner ownerEight
  /-- The retained original subdivision ends at parameter one. -/ endpoint_eq : subdivision.endpoint.parameter = 1
  /-- The retained original subdivision has the exact depth-three dyadic edge list. -/ parameterEdges_eq :
    subdivision.parameterEdges =
    ClearSheetContinuation.Subdivision.dyadicEdges 3
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
  /-- The retained original subdivision has the exact depth-three working-diameter request list. -/ requests_eq :
    subdivision.requests = Subdivision.dyadicRequests 3
    PreparedClearPathModels.zeroEndpoint
      PreparedClearPathModels.oneEndpoint workingRootDiameter
        workingRootDiameter_positive

constructive_injectivity EightStepSameBoxResult

namespace EightStepSameBoxResult

/-- Transport the original cached parameter-zero owner to the displayed segment start. -/
@[expose] def inputOwner
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (_result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) : Owner (polynomial.eval start) := by
  simpa only [Eight.secondMeshEndpoint,
    PreparedClearPathModels.zeroEndpoint,
    Geometry.ClearPath.ClearSegment.pointAt_zero] using ownerZero

/-- The displayed input owner retains the original cached parameter-zero owner heterogeneously. -/
theorem inputOwner_heq_ownerZero
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) : HEq result.inputOwner ownerZero := by
  unfold inputOwner
  exact cast_heq _ _

/-- Returning the displayed input owner to parameter zero recovers the exact original owner. -/
theorem startOwnerEq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    PreparedClearPathModels.ownerAtStart segment
      result.inputOwner = ownerZero := by
  apply eq_of_heq
  have input_heq : HEq
      (PreparedClearPathModels.ownerAtStart segment
        result.inputOwner) result.inputOwner := by
    unfold PreparedClearPathModels.ownerAtStart
    exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _
  exact input_heq.trans result.inputOwner_heq_ownerZero

/-- View the retained eight-step subdivision as a complete displayed segment.

Preserves the original subdivision through its exact input-owner transport and retained endpoint certificate. -/
@[expose] def completeSegment
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    PreparedClearPathModels.CompleteSegment segment within
      result.inputOwner where
  subdivision := Subdivision.castOwner result.startOwnerEq.symm
    result.subdivision
  endpoint_eq := by
    rw [Subdivision.castOwner_endpoint]
    exact result.endpoint_eq

/-- The completed segment retains the original exact depth-three dyadic edge list. -/
theorem completeSegment_parameterEdges
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    result.completeSegment.subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges 3
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint := by
  change (Subdivision.castOwner result.startOwnerEq.symm
    result.subdivision).parameterEdges = _
  rw [Subdivision.castOwner_parameterEdges]
  exact result.parameterEdges_eq

/-- The completed segment retains the original exact working-diameter request list. -/
theorem completeSegment_requests
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    result.completeSegment.subdivision.requests =
      Subdivision.dyadicRequests 3
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint workingRootDiameter
            workingRootDiameter_positive := by
  change (Subdivision.castOwner result.startOwnerEq.symm
    result.subdivision).requests = _
  rw [Subdivision.castOwner_requests]
  exact result.requests_eq

/-- The completed segment retains the original ordered list of eight prepared source boxes. -/
theorem completeSegment_preparedBoxes
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    result.completeSegment.subdivision.preparedBoxes =
      [result.preparedBox 0, result.preparedBox 1,
        result.preparedBox 2, result.preparedBox 3,
        result.preparedBox 4, result.preparedBox 5,
        result.preparedBox 6, result.preparedBox 7] := by
  change (Subdivision.castOwner result.startOwnerEq.symm
    result.subdivision).preparedBoxes = _
  rw [Subdivision.castOwner_preparedBoxes]
  exact result.preparedBoxes_eq

/-- The completed segment retains the exact cached terminal owner heterogeneously. -/
theorem completeSegment_finishOwner_heq
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    HEq result.completeSegment.finishOwner result.ownerEight :=
  (PreparedClearPathModels.CompleteSegment.finishOwner_heq_terminalOwner
    result.completeSegment).trans
      ((eightStepCastOwner_terminalOwner_heq result.startOwnerEq.symm
        result.subdivision).trans result.terminalOwner_heq)

/-- Adjacent completed cached cells have equal handoff owners when their retained endpoint owners agree heterogeneously.
-/
theorem completeSegment_finishOwner_eq_inputOwner
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start middle finish : Basic.Canonical}
    {leftSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      start middle}
    {leftWithin : leftSegment.WithinAmbient}
    {leftOwnerZero : Owner
      (polynomial.eval
        (leftSegment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {leftBox : Rational.Box} {leftPreparedUpper leftMarginFloor : Fraction.Rational}
    (leftResult : EightStepSameBoxResult leftSegment leftWithin leftOwnerZero
      leftBox leftPreparedUpper leftMarginFloor)
    {rightSegment : Geometry.ClearPath.ClearSegment polynomial ambient
      middle finish}
    {rightWithin : rightSegment.WithinAmbient}
    {rightOwnerZero : Owner
      (polynomial.eval
        (rightSegment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {rightBox : Rational.Box} {rightPreparedUpper rightMarginFloor : Fraction.Rational}
    (rightResult : EightStepSameBoxResult rightSegment rightWithin
      rightOwnerZero rightBox rightPreparedUpper rightMarginFloor)
    (rightOwnerZero_heq_leftOwnerEight :
      HEq rightOwnerZero leftResult.ownerEight) :
    leftResult.completeSegment.finishOwner = rightResult.inputOwner := by
  apply eq_of_heq
  exact leftResult.completeSegment_finishOwner_heq.trans
    (rightOwnerZero_heq_leftOwnerEight.symm.trans
      rightResult.inputOwner_heq_ownerZero.symm)

/-- The original centered-edge list of a cached depth-three result has exactly eight entries. -/
theorem centeredEdges_length_eight
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    (result.completeSegment.centeredEdges curve differential sheet).length =
      8 := by
  calc
    _ = result.completeSegment.subdivision.stepCount :=
      PreparedClearPathModels.CompleteSegment.centeredEdges_length
        curve differential sheet result.completeSegment
    _ = result.completeSegment.subdivision.parameterEdges.length :=
      (PreparedSheetContinuation.Subdivision.parameterEdges_length
        result.completeSegment.subdivision).symm
    _ = 8 := by
      rw [result.completeSegment_parameterEdges]
      rfl

/-- Select an original centered integration edge using its exact retained eight-entry length certificate. -/
@[expose] def centeredEdge
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    PreparedSubdivisionModelCore.CenteredEdge curve differential :=
  (result.completeSegment.centeredEdges curve differential sheet).get
    (Fin.cast (result.centeredEdges_length_eight curve differential sheet).symm
      edge)

/-- Transporting the finite index size preserves the original list constructed by a finite function. -/
private theorem ofFn_cast_size {Alpha : Type} {left right : Nat}
    (equal : left = right) (values : Fin left → Alpha) :
    List.ofFn values =
      List.ofFn (fun index : Fin right => values (Fin.cast equal.symm index)) := by
  cases equal
  rfl

open Purelib.Data.List in
/-- Enumerating a list's original entries in order reconstructs that exact list. -/
private theorem ofFn_getElem_constructive {Alpha : Type} :
    (values : List Alpha) →
      List.ofFn (fun index : Fin values.length => values[index.val]) = values
  | [] => rfl
  | head :: tail => by
      rw [OfFn.Basic.ofFn_succ]
      congr
      exact ofFn_getElem_constructive tail

/-- The original centered-edge list equals the finite list of its eight retained edge projections. -/
theorem centeredEdges_eq_ofFn_centeredEdge
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    result.completeSegment.centeredEdges curve differential sheet =
      List.ofFn (result.centeredEdge curve differential sheet) := by
  let edges := result.completeSegment.centeredEdges curve differential sheet
  have length : edges.length = 8 :=
    result.centeredEdges_length_eight curve differential sheet
  calc
    edges = List.ofFn (fun index : Fin edges.length =>
        edges[index.val]) := (ofFn_getElem_constructive edges).symm
    _ = List.ofFn (fun edge : Fin 8 =>
        edges[(Fin.cast length.symm edge).val]) :=
      ofFn_cast_size length (fun index : Fin edges.length => edges[index.val])
    _ = List.ofFn (result.centeredEdge curve differential sheet) := rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The completed segment's original tail integral sample equals the finite sum of its eight retained edge samples. -/
theorem completeSegment_integralSample_eq_sumFin_centeredEdge
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor) :
    Basic.PathModel.tailMappedIntegralSample
        (result.completeSegment.centeredEdges curve differential sheet)
        PreparedSubdivisionModelCore.CenteredEdge.model =
      FiniteSum.Fin.sumFin (fun edge : Fin 8 =>
        (result.centeredEdge curve differential sheet edge).model.integralSample) := by
  rw [result.centeredEdges_eq_ofFn_centeredEdge]
  rfl

/-- Each retained centered edge refers heterogeneously to the original displayed segment. -/
theorem centeredEdge_segment_heq
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    HEq (result.centeredEdge curve differential sheet edge).edge.segment
      segment := by
  apply PreparedSubdivisionModelCore.centeredEdges_segment_heq
    curve differential sheet result.completeSegment.subdivision
      (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
        differential sheet result.completeSegment.subdivision)
  unfold centeredEdge
  unfold PreparedClearPathModels.CompleteSegment.centeredEdges
  dsimp only
  exact List.get_mem _ _

/-- An original eight-entry edge index is one of its eight explicit values. -/
private theorem centeredEdgeFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- The selected centered edge retains its exact original depth-three mesh interval. -/
theorem centeredEdge_parameterEdge
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    (result.centeredEdge curve differential sheet edge).parameterEdge =
      { left := Eight.secondMeshEndpoint
          (Eight.secondEdgeSource edge)
        right := (Eight.secondEdgeRequest edge).endpoint } := by
  have mapped := result.completeSegment.centeredEdges_parameterEdges
    curve differential sheet
  rw [result.completeSegment_parameterEdges] at mapped
  have indexed := congrArg (fun entries => Purelib.Data.List.getElem? entries edge.val) mapped
  simp only [Purelib.Data.List.getElem?_map] at indexed
  have source :
      Purelib.Data.List.getElem? (result.completeSegment.centeredEdges curve differential sheet) edge.val =
        some (result.centeredEdge curve differential sheet edge) := by
    rw [Purelib.Data.List.getElem?_eq_getElem _ _ (by
      rw [result.centeredEdges_length_eight curve differential sheet]
      exact edge.isLt)]
    rfl
  rw [source] at indexed
  simp only [Option.map_some] at indexed
  have target :
      Purelib.Data.List.getElem? (ClearSheetContinuation.Subdivision.dyadicEdges 3
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint) edge.val =
        some
          { left := Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)
            right := (Eight.secondEdgeRequest edge).endpoint } := by
    rcases centeredEdgeFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals with_unfolding_all rfl
  rw [target] at indexed
  exact Option.some.inj indexed

/-- The selected centered edge starts at its original dyadic source point. -/
theorem centeredEdge_point_zero
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    (result.centeredEdge curve differential sheet edge).edge.point 0 =
      segment.pointAt
        (Eight.secondMeshEndpoint (Eight.secondEdgeSource
          edge)).parameter := by
  have membership :
      result.centeredEdge curve differential sheet edge ∈
        result.completeSegment.centeredEdges curve differential sheet := by
    unfold centeredEdge
    unfold PreparedClearPathModels.CompleteSegment.centeredEdges
    dsimp only
    exact List.get_mem _ _
  have pointEqual :=
    PreparedSubdivisionModelCore.centeredEdges_point_zero
      curve differential sheet result.completeSegment.subdivision
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet result.completeSegment.subdivision)
        (result.centeredEdge curve differential sheet edge) membership
  rw [result.centeredEdge_parameterEdge curve differential sheet edge] at pointEqual
  exact pointEqual

/-- The selected centered edge ends at its original dyadic request point. -/
theorem centeredEdge_point_one
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    (result.centeredEdge curve differential sheet edge).edge.point 1 =
      segment.pointAt (Eight.secondEdgeRequest edge).endpoint.parameter := by
  have membership :
      result.centeredEdge curve differential sheet edge ∈
        result.completeSegment.centeredEdges curve differential sheet := by
    unfold centeredEdge
    unfold PreparedClearPathModels.CompleteSegment.centeredEdges
    dsimp only
    exact List.get_mem _ _
  have pointEqual :=
    PreparedSubdivisionModelCore.centeredEdges_point_one
      curve differential sheet result.completeSegment.subdivision
        (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
          differential sheet result.completeSegment.subdivision)
        (result.centeredEdge curve differential sheet edge) membership
  rw [result.centeredEdge_parameterEdge curve differential sheet edge] at pointEqual
  exact pointEqual

/-- The selected centered edge retains the original canonical center state. -/
theorem centeredEdge_center
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    (result.centeredEdge curve differential sheet edge).center =
      PreparedConstantModels.PreparedEdge.CenterState.canonical
        (result.centeredEdge curve differential sheet edge).edge := by
  apply PreparedSubdivisionAutomaticModels.centeredEdges_canonical_center
    curve differential sheet result.completeSegment.subdivision
  unfold centeredEdge
  unfold PreparedClearPathModels.CompleteSegment.centeredEdges
  dsimp only
  exact List.get_mem _ _

/-- The selected centered edge retains its exact cached prepared source-owner box. -/
theorem centeredEdge_preparedBox
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {ownerZero : Owner
      (curve.polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter))}
    {box : Rational.Box} {preparedUpper marginFloor : Fraction.Rational}
    (sheet : Fin 2)
    (result : EightStepSameBoxResult segment within ownerZero box
      preparedUpper marginFloor)
    (edge : Fin 8) :
    (result.centeredEdge curve differential sheet edge).edge.cached.preparedOwner.track.initial.box =
      result.preparedBox edge := by
  have mapped := result.completeSegment.centeredEdges_preparedBoxes
    curve differential sheet
  rw [result.completeSegment_preparedBoxes] at mapped
  have indexed := congrArg (fun entries => Purelib.Data.List.getElem? entries edge.val) mapped
  simp only [Purelib.Data.List.getElem?_map] at indexed
  have source :
      Purelib.Data.List.getElem? (result.completeSegment.centeredEdges curve differential sheet) edge.val =
        some (result.centeredEdge curve differential sheet edge) := by
    rw [Purelib.Data.List.getElem?_eq_getElem _ _ (by
      rw [result.centeredEdges_length_eight curve differential sheet]
      exact edge.isLt)]
    rfl
  rw [source] at indexed
  simp only [Option.map_some] at indexed
  have target :
      Purelib.Data.List.getElem? [result.preparedBox 0, result.preparedBox 1,
        result.preparedBox 2, result.preparedBox 3,
        result.preparedBox 4, result.preparedBox 5,
        result.preparedBox 6, result.preparedBox 7] edge.val =
          some (result.preparedBox edge) := by
    rcases centeredEdgeFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals rfl
  rw [target] at indexed
  exact Option.some.inj indexed

end EightStepSameBoxResult

/-- Thread eight original same-box advances through the retained depth-three mesh.

Consumes the supplied ordered edge-step certificates, caches each actual owner/state once and retains the exact final
subdivision, requests, boxes and terminal owner. -/
@[expose] def eightStepSameBox
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter)))
    (box : Rational.Box) (directLower preparedUpper marginFloor : Fraction.Rational)
    (initialState : ParametricSameBoxState segment (Eight.secondMeshEndpoint 0)
      ownerZero box preparedUpper marginFloor)
    (preparedContracts : preparedUpper ^ 2 / 4 ≤ preparedUpper)
    (ordered : ∀ edge : Fin 8,
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)).parameter ≤
        (Eight.secondEdgeRequest edge).endpoint.parameter)
    (step : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner box
            preparedUpper marginFloor ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) box directLower preparedUpper
              marginFloor) :
    EightStepSameBoxResult segment within ownerZero box preparedUpper
      marginFloor := by
  let stepZero := step 0 ownerZero initialState
  let ownerOne := stepZero.nextOwner
  let stateOne := stepZero.nextState initialState preparedContracts
  let stepOne := step 1 ownerOne stateOne
  let ownerTwo := stepOne.nextOwner
  let stateTwo := stepOne.nextState stateOne preparedContracts
  let stepTwo := step 2 ownerTwo stateTwo
  let ownerThree := stepTwo.nextOwner
  let stateThree := stepTwo.nextState stateTwo preparedContracts
  let stepThree := step 3 ownerThree stateThree
  let ownerFour := stepThree.nextOwner
  let stateFour := stepThree.nextState stateThree preparedContracts
  let stepFour := step 4 ownerFour stateFour
  let ownerFive := stepFour.nextOwner
  let stateFive := stepFour.nextState stateFour preparedContracts
  let stepFive := step 5 ownerFive stateFive
  let ownerSix := stepFive.nextOwner
  let stateSix := stepFive.nextState stateFive preparedContracts
  let stepSix := step 6 ownerSix stateSix
  let ownerSeven := stepSix.nextOwner
  let stateSeven := stepSix.nextState stateSix preparedContracts
  let stepSeven := step 7 ownerSeven stateSeven
  let ownerEight := stepSeven.nextOwner
  let stateEight := stepSeven.nextState stateSeven preparedContracts
  let tailEight : Subdivision segment within (Eight.secondMeshEndpoint 8)
      ownerEight := .stop _ _
  let tailSeven : Subdivision segment within (Eight.secondMeshEndpoint 7)
      ownerSeven :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 7) ownerSeven
      (Eight.secondEdgeRequest 7)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
          (Eight.secondEdgeRequest 7)) (ordered 7) stepSeven.canonicalSmall
            stepSeven.canonicalSmall tailEight
  let tailSix : Subdivision segment within (Eight.secondMeshEndpoint 6) ownerSix :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 6) ownerSix
      (Eight.secondEdgeRequest 6)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 6) ownerSix
          (Eight.secondEdgeRequest 6)) (ordered 6) stepSix.canonicalSmall
            stepSix.canonicalSmall tailSeven
  let tailFive : Subdivision segment within (Eight.secondMeshEndpoint 5) ownerFive :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 5) ownerFive
      (Eight.secondEdgeRequest 5)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 5) ownerFive
          (Eight.secondEdgeRequest 5)) (ordered 5) stepFive.canonicalSmall
            stepFive.canonicalSmall tailSix
  let tailFour : Subdivision segment within (Eight.secondMeshEndpoint 4) ownerFour :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 4) ownerFour
      (Eight.secondEdgeRequest 4)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 4) ownerFour
          (Eight.secondEdgeRequest 4)) (ordered 4) stepFour.canonicalSmall
            stepFour.canonicalSmall tailFive
  let tailThree : Subdivision segment within (Eight.secondMeshEndpoint 3)
      ownerThree :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 3) ownerThree
      (Eight.secondEdgeRequest 3)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
          (Eight.secondEdgeRequest 3)) (ordered 3) stepThree.canonicalSmall
            stepThree.canonicalSmall tailFour
  let tailTwo : Subdivision segment within (Eight.secondMeshEndpoint 2) ownerTwo :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 2) ownerTwo
      (Eight.secondEdgeRequest 2)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 2) ownerTwo
          (Eight.secondEdgeRequest 2)) (ordered 2) stepTwo.canonicalSmall
            stepTwo.canonicalSmall tailThree
  let tailOne : Subdivision segment within (Eight.secondMeshEndpoint 1) ownerOne :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 1) ownerOne
      (Eight.secondEdgeRequest 1)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 1) ownerOne
          (Eight.secondEdgeRequest 1)) (ordered 1) stepOne.canonicalSmall
            stepOne.canonicalSmall tailTwo
  let subdivision : Subdivision segment within (Eight.secondMeshEndpoint 0)
      ownerZero :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 0) ownerZero
      (Eight.secondEdgeRequest 0)
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 0) ownerZero
          (Eight.secondEdgeRequest 0)) (ordered 0) stepZero.canonicalSmall
            stepZero.canonicalSmall tailOne
  have preparedBoxZero :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 0) ownerZero
        (Eight.secondEdgeRequest 0)).preparedOwner.track.initial.box = box :=
    stepZero.advanceCache.initialBox.symm.trans stepZero.nextOwnerBox
  have preparedBoxOne :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 1) ownerOne
        (Eight.secondEdgeRequest 1)).preparedOwner.track.initial.box = box :=
    stepOne.advanceCache.initialBox.symm.trans stepOne.nextOwnerBox
  have preparedBoxTwo :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 2) ownerTwo
        (Eight.secondEdgeRequest 2)).preparedOwner.track.initial.box = box :=
    stepTwo.advanceCache.initialBox.symm.trans stepTwo.nextOwnerBox
  have preparedBoxThree :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
        (Eight.secondEdgeRequest 3)).preparedOwner.track.initial.box = box :=
    stepThree.advanceCache.initialBox.symm.trans stepThree.nextOwnerBox
  have preparedBoxFour :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 4) ownerFour
        (Eight.secondEdgeRequest 4)).preparedOwner.track.initial.box = box :=
    stepFour.advanceCache.initialBox.symm.trans stepFour.nextOwnerBox
  have preparedBoxFive :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 5) ownerFive
        (Eight.secondEdgeRequest 5)).preparedOwner.track.initial.box = box :=
    stepFive.advanceCache.initialBox.symm.trans stepFive.nextOwnerBox
  have preparedBoxSix :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 6) ownerSix
        (Eight.secondEdgeRequest 6)).preparedOwner.track.initial.box = box :=
    stepSix.advanceCache.initialBox.symm.trans stepSix.nextOwnerBox
  have preparedBoxSeven :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
        (Eight.secondEdgeRequest 7)).preparedOwner.track.initial.box = box :=
    stepSeven.advanceCache.initialBox.symm.trans stepSeven.nextOwnerBox
  have tailEightPreparedBoxes : tailEight.preparedBoxes = [] := by
    rfl
  have tailSevenPreparedBoxes : tailSeven.preparedBoxes = [box] := by
    simp only [tailSeven, Subdivision.nextCached_preparedBoxes,
      preparedBoxSeven]
    exact congrArg (fun boxes => box :: boxes) tailEightPreparedBoxes
  have tailSixPreparedBoxes : tailSix.preparedBoxes = [box, box] := by
    simp only [tailSix, Subdivision.nextCached_preparedBoxes,
      preparedBoxSix]
    exact congrArg (fun boxes => box :: boxes) tailSevenPreparedBoxes
  have tailFivePreparedBoxes : tailFive.preparedBoxes = [box, box, box] := by
    simp only [tailFive, Subdivision.nextCached_preparedBoxes,
      preparedBoxFive]
    exact congrArg (fun boxes => box :: boxes) tailSixPreparedBoxes
  have tailFourPreparedBoxes : tailFour.preparedBoxes =
      [box, box, box, box] := by
    simp only [tailFour, Subdivision.nextCached_preparedBoxes,
      preparedBoxFour]
    exact congrArg (fun boxes => box :: boxes) tailFivePreparedBoxes
  have tailThreePreparedBoxes : tailThree.preparedBoxes =
      [box, box, box, box, box] := by
    simp only [tailThree, Subdivision.nextCached_preparedBoxes,
      preparedBoxThree]
    exact congrArg (fun boxes => box :: boxes) tailFourPreparedBoxes
  have tailTwoPreparedBoxes : tailTwo.preparedBoxes =
      [box, box, box, box, box, box] := by
    simp only [tailTwo, Subdivision.nextCached_preparedBoxes,
      preparedBoxTwo]
    exact congrArg (fun boxes => box :: boxes) tailThreePreparedBoxes
  have tailOnePreparedBoxes : tailOne.preparedBoxes =
      [box, box, box, box, box, box, box] := by
    simp only [tailOne, Subdivision.nextCached_preparedBoxes,
      preparedBoxOne]
    exact congrArg (fun boxes => box :: boxes) tailTwoPreparedBoxes
  have subdivisionPreparedBoxes : subdivision.preparedBoxes =
      [box, box, box, box, box, box, box, box] := by
    simp only [subdivision, Subdivision.nextCached_preparedBoxes,
      preparedBoxZero]
    exact congrArg (fun boxes => box :: boxes) tailOnePreparedBoxes
  exact
    { ownerEight := ownerEight
      terminalState := stateEight
      terminalAmbientLeftLeQuarter := stepSeven.nextAmbientLeftLeQuarter
      terminalClearanceLeQuarter := by
        apply stepSeven.advanceCache.clearanceQuarterSq.trans
        change
          (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
              (Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
              (4 : Fraction.Rational)⁻¹ ≤
            preparedUpper ^ 2 * (4 : Fraction.Rational)⁻¹
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact Fraction.Order.Arithmetic.pow_le_pow_direct
            (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
              (Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.positive.le
                stepSeven.preparedAmbientLeftLe 2
        · exact (Fraction.Order.Field.inv_pos_direct
            (by decide : (0 : Fraction.Rational) < 4)).le
      preparedBox := fun _ => box
      subdivision := subdivision
      preparedBoxes_eq := subdivisionPreparedBoxes
      terminalOwner_heq := by
        change HEq subdivision.terminalOwner ownerEight
        exact
          (eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
            ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
              ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                  ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                    ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                      ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                        ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                          (by rfl))))))))
      endpoint_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight,
          Subdivision.nextCached_endpoint]
        rfl
      requests_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight]
        exact Eight.ExplicitQuarticPreparedSecondCellCertificate.secondDyadicRequests.symm
      parameterEdges_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight,
          Subdivision.nextCached_parameterEdges]
        change
          [{ left := Eight.secondMeshEndpoint 0,
              right := (Eight.secondEdgeRequest 0).endpoint },
            { left := Eight.secondMeshEndpoint 1,
              right := (Eight.secondEdgeRequest 1).endpoint },
            { left := Eight.secondMeshEndpoint 2,
              right := (Eight.secondEdgeRequest 2).endpoint },
            { left := Eight.secondMeshEndpoint 3,
              right := (Eight.secondEdgeRequest 3).endpoint },
            { left := Eight.secondMeshEndpoint 4,
              right := (Eight.secondEdgeRequest 4).endpoint },
            { left := Eight.secondMeshEndpoint 5,
              right := (Eight.secondEdgeRequest 5).endpoint },
            { left := Eight.secondMeshEndpoint 6,
              right := (Eight.secondEdgeRequest 6).endpoint },
            { left := Eight.secondMeshEndpoint 7,
              right := (Eight.secondEdgeRequest 7).endpoint }] =
            ClearSheetContinuation.Subdivision.dyadicEdges 3
              PreparedClearPathModels.zeroEndpoint
                PreparedClearPathModels.oneEndpoint
        with_unfolding_all rfl }

/-- Every original uniform eight-step prepared source box equals the retained common box. -/
theorem eightStepSameBox_preparedBox
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter)))
    (box : Rational.Box) (directLower preparedUpper marginFloor : Fraction.Rational)
    (initialState : ParametricSameBoxState segment (Eight.secondMeshEndpoint 0)
      ownerZero box preparedUpper marginFloor)
    (preparedContracts : preparedUpper ^ 2 / 4 ≤ preparedUpper)
    (ordered : ∀ edge : Fin 8,
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)).parameter ≤
        (Eight.secondEdgeRequest edge).endpoint.parameter)
    (step : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner box
            preparedUpper marginFloor ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) box directLower preparedUpper
              marginFloor)
    (edge : Fin 8) :
    (eightStepSameBox segment within ownerZero box directLower preparedUpper
      marginFloor initialState preparedContracts ordered step).preparedBox
        edge = box := by
  rfl

/-- Thread four original same-box edges, one midpoint reset and three successor-box edges.

Keeps the actual reset at edge four, separate before/after caps and direct bounds, original dependent owner chain and
exact ordered box/readback lists. -/
@[expose] def eightStepResetAtFour
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter)))
    (oldBox newBox : Rational.Box)
    (beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor :
      Fraction.Rational)
    (initialState : ParametricSameBoxState segment (Eight.secondMeshEndpoint 0)
      ownerZero oldBox beforeUpper marginFloor)
    (beforeContracts : beforeUpper ^ 2 / 4 ≤ beforeUpper)
    (afterContracts : afterUpper ^ 2 / 4 ≤ afterUpper)
    (ordered : ∀ edge : Fin 8,
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)).parameter ≤
        (Eight.secondEdgeRequest edge).endpoint.parameter)
    (beforeStep : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner oldBox
            beforeUpper marginFloor -> edge.val < 4 ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) oldBox beforeDirectLower beforeUpper
              marginFloor)
    (resetStep : ∀
      (owner : Owner
        (polynomial.eval
          (segment.pointAt (Eight.secondMeshEndpoint 4).parameter))),
      ParametricSameBoxState segment (Eight.secondMeshEndpoint 4) owner oldBox
          beforeUpper marginFloor ->
      owner.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 ->
        ParametricResetStep segment within (Eight.secondMeshEndpoint 4) owner
          (Eight.secondEdgeRequest 4) newBox afterUpper marginFloor)
    (afterStep : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner newBox
            afterUpper marginFloor -> 5 ≤ edge.val ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) newBox afterDirectLower afterUpper
              marginFloor) :
    EightStepSameBoxResult segment within ownerZero newBox afterUpper
      marginFloor := by
  let stepZero := beforeStep 0 ownerZero initialState (by decide)
  let ownerOne := stepZero.nextOwner
  let stateOne := stepZero.nextState initialState beforeContracts
  let stepOne := beforeStep 1 ownerOne stateOne (by decide)
  let ownerTwo := stepOne.nextOwner
  let stateTwo := stepOne.nextState stateOne beforeContracts
  let stepTwo := beforeStep 2 ownerTwo stateTwo (by decide)
  let ownerThree := stepTwo.nextOwner
  let stateThree := stepTwo.nextState stateTwo beforeContracts
  let stepThree := beforeStep 3 ownerThree stateThree (by decide)
  let ownerFour := stepThree.nextOwner
  let stateFour := stepThree.nextState stateThree beforeContracts
  have ownerFourClearanceLe :
      ownerFour.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 := by
    apply stepThree.advanceCache.clearanceQuarterSq.trans
    change
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
          (Eight.secondEdgeRequest
            3)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Fraction.Rational)⁻¹ ≤
        beforeUpper ^ 2 * (4 : Fraction.Rational)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
          (Eight.secondEdgeRequest
            3)).preparedOwner.track.initial.ambientLeftClearance.positive.le
            stepThree.preparedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Fraction.Rational) < 4)).le
  let resetFour := resetStep ownerFour stateFour ownerFourClearanceLe
  let ownerFive := resetFour.nextOwner
  let stateFive := resetFour.nextState
  let stepFive := afterStep 5 ownerFive stateFive (by decide)
  let ownerSix := stepFive.nextOwner
  let stateSix := stepFive.nextState stateFive afterContracts
  let stepSix := afterStep 6 ownerSix stateSix (by decide)
  let ownerSeven := stepSix.nextOwner
  let stateSeven := stepSix.nextState stateSix afterContracts
  let stepSeven := afterStep 7 ownerSeven stateSeven (by decide)
  let ownerEight := stepSeven.nextOwner
  let stateEight := stepSeven.nextState stateSeven afterContracts
  let tailEight : Subdivision segment within (Eight.secondMeshEndpoint 8)
      ownerEight := .stop _ _
  let tailSeven : Subdivision segment within (Eight.secondMeshEndpoint 7)
      ownerSeven :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 7) ownerSeven
      (Eight.secondEdgeRequest 7)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
          (Eight.secondEdgeRequest 7)) (ordered 7) stepSeven.canonicalSmall
            stepSeven.canonicalSmall tailEight
  let tailSix : Subdivision segment within (Eight.secondMeshEndpoint 6) ownerSix :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 6) ownerSix
      (Eight.secondEdgeRequest 6)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 6) ownerSix
          (Eight.secondEdgeRequest 6)) (ordered 6) stepSix.canonicalSmall
            stepSix.canonicalSmall tailSeven
  let tailFive : Subdivision segment within (Eight.secondMeshEndpoint 5) ownerFive :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 5) ownerFive
      (Eight.secondEdgeRequest 5)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 5) ownerFive
          (Eight.secondEdgeRequest 5)) (ordered 5) stepFive.canonicalSmall
            stepFive.canonicalSmall tailSix
  let tailFour : Subdivision segment within (Eight.secondMeshEndpoint 4) ownerFour :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 4) ownerFour
      (Eight.secondEdgeRequest 4)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 4) ownerFour
          (Eight.secondEdgeRequest 4)) (ordered 4) resetFour.canonicalSmall
            resetFour.canonicalSmall tailFive
  let tailThree : Subdivision segment within (Eight.secondMeshEndpoint 3)
      ownerThree :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 3) ownerThree
      (Eight.secondEdgeRequest 3)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
          (Eight.secondEdgeRequest 3)) (ordered 3) stepThree.canonicalSmall
            stepThree.canonicalSmall tailFour
  let tailTwo : Subdivision segment within (Eight.secondMeshEndpoint 2) ownerTwo :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 2) ownerTwo
      (Eight.secondEdgeRequest 2)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 2) ownerTwo
          (Eight.secondEdgeRequest 2)) (ordered 2) stepTwo.canonicalSmall
            stepTwo.canonicalSmall tailThree
  let tailOne : Subdivision segment within (Eight.secondMeshEndpoint 1) ownerOne :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 1) ownerOne
      (Eight.secondEdgeRequest 1)
        (CachedSource.canonical segment (Eight.secondMeshEndpoint 1) ownerOne
          (Eight.secondEdgeRequest 1)) (ordered 1) stepOne.canonicalSmall
            stepOne.canonicalSmall tailTwo
  let subdivision : Subdivision segment within (Eight.secondMeshEndpoint 0)
      ownerZero :=
    Subdivision.nextCached segment within (Eight.secondMeshEndpoint 0) ownerZero
      (Eight.secondEdgeRequest 0)
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 0) ownerZero
          (Eight.secondEdgeRequest 0)) (ordered 0) stepZero.canonicalSmall
            stepZero.canonicalSmall tailOne
  have preparedBoxZero :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 0) ownerZero
        (Eight.secondEdgeRequest 0)).preparedOwner.track.initial.box = oldBox :=
    stepZero.advanceCache.initialBox.symm.trans stepZero.nextOwnerBox
  have preparedBoxOne :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 1) ownerOne
        (Eight.secondEdgeRequest 1)).preparedOwner.track.initial.box = oldBox :=
    stepOne.advanceCache.initialBox.symm.trans stepOne.nextOwnerBox
  have preparedBoxTwo :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 2) ownerTwo
        (Eight.secondEdgeRequest 2)).preparedOwner.track.initial.box = oldBox :=
    stepTwo.advanceCache.initialBox.symm.trans stepTwo.nextOwnerBox
  have preparedBoxThree :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 3) ownerThree
        (Eight.secondEdgeRequest 3)).preparedOwner.track.initial.box = oldBox :=
    stepThree.advanceCache.initialBox.symm.trans stepThree.nextOwnerBox
  have preparedBoxFour :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 4) ownerFour
        (Eight.secondEdgeRequest 4)).preparedOwner.track.initial.box = newBox :=
    resetFour.preparedBox
  have preparedBoxFive :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 5) ownerFive
        (Eight.secondEdgeRequest 5)).preparedOwner.track.initial.box = newBox :=
    stepFive.advanceCache.initialBox.symm.trans stepFive.nextOwnerBox
  have preparedBoxSix :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 6) ownerSix
        (Eight.secondEdgeRequest 6)).preparedOwner.track.initial.box = newBox :=
    stepSix.advanceCache.initialBox.symm.trans stepSix.nextOwnerBox
  have preparedBoxSeven :
      (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
        (Eight.secondEdgeRequest 7)).preparedOwner.track.initial.box = newBox :=
    stepSeven.advanceCache.initialBox.symm.trans stepSeven.nextOwnerBox
  have tailEightPreparedBoxes : tailEight.preparedBoxes = [] := by
    rfl
  have tailSevenPreparedBoxes : tailSeven.preparedBoxes = [newBox] := by
    simp only [tailSeven, Subdivision.nextCached_preparedBoxes,
      preparedBoxSeven]
    exact congrArg (fun boxes => newBox :: boxes) tailEightPreparedBoxes
  have tailSixPreparedBoxes : tailSix.preparedBoxes = [newBox, newBox] := by
    simp only [tailSix, Subdivision.nextCached_preparedBoxes,
      preparedBoxSix]
    exact congrArg (fun boxes => newBox :: boxes) tailSevenPreparedBoxes
  have tailFivePreparedBoxes : tailFive.preparedBoxes =
      [newBox, newBox, newBox] := by
    simp only [tailFive, Subdivision.nextCached_preparedBoxes,
      preparedBoxFive]
    exact congrArg (fun boxes => newBox :: boxes) tailSixPreparedBoxes
  have tailFourPreparedBoxes : tailFour.preparedBoxes =
      [newBox, newBox, newBox, newBox] := by
    simp only [tailFour, Subdivision.nextCached_preparedBoxes,
      preparedBoxFour]
    exact congrArg (fun boxes => newBox :: boxes) tailFivePreparedBoxes
  have tailThreePreparedBoxes : tailThree.preparedBoxes =
      [oldBox, newBox, newBox, newBox, newBox] := by
    simp only [tailThree, Subdivision.nextCached_preparedBoxes,
      preparedBoxThree]
    exact congrArg (fun boxes => oldBox :: boxes) tailFourPreparedBoxes
  have tailTwoPreparedBoxes : tailTwo.preparedBoxes =
      [oldBox, oldBox, newBox, newBox, newBox, newBox] := by
    simp only [tailTwo, Subdivision.nextCached_preparedBoxes,
      preparedBoxTwo]
    exact congrArg (fun boxes => oldBox :: boxes) tailThreePreparedBoxes
  have tailOnePreparedBoxes : tailOne.preparedBoxes =
      [oldBox, oldBox, oldBox, newBox, newBox, newBox, newBox] := by
    simp only [tailOne, Subdivision.nextCached_preparedBoxes,
      preparedBoxOne]
    exact congrArg (fun boxes => oldBox :: boxes) tailTwoPreparedBoxes
  have subdivisionPreparedBoxes : subdivision.preparedBoxes =
      [oldBox, oldBox, oldBox, oldBox, newBox, newBox, newBox, newBox] := by
    simp only [subdivision, Subdivision.nextCached_preparedBoxes,
      preparedBoxZero]
    exact congrArg (fun boxes => oldBox :: boxes) tailOnePreparedBoxes
  exact
    { ownerEight := ownerEight
      terminalState := stateEight
      terminalAmbientLeftLeQuarter := stepSeven.nextAmbientLeftLeQuarter
      terminalClearanceLeQuarter := by
        apply stepSeven.advanceCache.clearanceQuarterSq.trans
        change
          (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
              (Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
              (4 : Fraction.Rational)⁻¹ ≤
            afterUpper ^ 2 * (4 : Fraction.Rational)⁻¹
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact Fraction.Order.Arithmetic.pow_le_pow_direct
            (CachedSource.canonical segment (Eight.secondMeshEndpoint 7) ownerSeven
              (Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.positive.le
                stepSeven.preparedAmbientLeftLe 2
        · exact (Fraction.Order.Field.inv_pos_direct
            (by decide : (0 : Fraction.Rational) < 4)).le
      preparedBox := fun edge => if edge.val < 4 then oldBox else newBox
      subdivision := subdivision
      preparedBoxes_eq := by
        change subdivision.preparedBoxes =
          [oldBox, oldBox, oldBox, oldBox,
            newBox, newBox, newBox, newBox]
        exact subdivisionPreparedBoxes
      terminalOwner_heq := by
        change HEq subdivision.terminalOwner ownerEight
        exact
          (eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
            ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
              ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                  ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                    ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                      ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                        ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                          (by rfl))))))))
      endpoint_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight,
          Subdivision.nextCached_endpoint]
        rfl
      requests_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight]
        exact Eight.ExplicitQuarticPreparedSecondCellCertificate.secondDyadicRequests.symm
      parameterEdges_eq := by
        simp only [subdivision, tailOne, tailTwo, tailThree, tailFour,
          tailFive, tailSix, tailSeven, tailEight,
          Subdivision.nextCached_parameterEdges]
        change
          [{ left := Eight.secondMeshEndpoint 0,
              right := (Eight.secondEdgeRequest 0).endpoint },
            { left := Eight.secondMeshEndpoint 1,
              right := (Eight.secondEdgeRequest 1).endpoint },
            { left := Eight.secondMeshEndpoint 2,
              right := (Eight.secondEdgeRequest 2).endpoint },
            { left := Eight.secondMeshEndpoint 3,
              right := (Eight.secondEdgeRequest 3).endpoint },
            { left := Eight.secondMeshEndpoint 4,
              right := (Eight.secondEdgeRequest 4).endpoint },
            { left := Eight.secondMeshEndpoint 5,
              right := (Eight.secondEdgeRequest 5).endpoint },
            { left := Eight.secondMeshEndpoint 6,
              right := (Eight.secondEdgeRequest 6).endpoint },
            { left := Eight.secondMeshEndpoint 7,
              right := (Eight.secondEdgeRequest 7).endpoint }] =
            ClearSheetContinuation.Subdivision.dyadicEdges 3
              PreparedClearPathModels.zeroEndpoint
                PreparedClearPathModels.oneEndpoint
        with_unfolding_all rfl }

/-- The original midpoint-reset cache retains the old box on edges zero through three and the new box thereafter. -/
theorem eightStepResetAtFour_preparedBox
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Owner
      (polynomial.eval
        (segment.pointAt (Eight.secondMeshEndpoint 0).parameter)))
    (oldBox newBox : Rational.Box)
    (beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor :
      Fraction.Rational)
    (initialState : ParametricSameBoxState segment (Eight.secondMeshEndpoint 0)
      ownerZero oldBox beforeUpper marginFloor)
    (beforeContracts : beforeUpper ^ 2 / 4 ≤ beforeUpper)
    (afterContracts : afterUpper ^ 2 / 4 ≤ afterUpper)
    (ordered : ∀ edge : Fin 8,
      (Eight.secondMeshEndpoint (Eight.secondEdgeSource
        edge)).parameter ≤
        (Eight.secondEdgeRequest edge).endpoint.parameter)
    (beforeStep : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner oldBox
            beforeUpper marginFloor -> edge.val < 4 ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) oldBox beforeDirectLower beforeUpper
              marginFloor)
    (resetStep : ∀
      (owner : Owner
        (polynomial.eval
          (segment.pointAt (Eight.secondMeshEndpoint 4).parameter))),
      ParametricSameBoxState segment (Eight.secondMeshEndpoint 4) owner oldBox
          beforeUpper marginFloor ->
      owner.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 ->
        ParametricResetStep segment within (Eight.secondMeshEndpoint 4) owner
          (Eight.secondEdgeRequest 4) newBox afterUpper marginFloor)
    (afterStep : ∀ (edge : Fin 8)
      (owner : Owner
        (polynomial.eval
          (segment.pointAt
            (Eight.secondMeshEndpoint
              (Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner newBox
            afterUpper marginFloor -> 5 ≤ edge.val ->
        ParametricSameBoxStep segment within
          (Eight.secondMeshEndpoint (Eight.secondEdgeSource
            edge)) owner
            (Eight.secondEdgeRequest edge) newBox afterDirectLower afterUpper
              marginFloor)
    (edge : Fin 8) :
    (eightStepResetAtFour segment within ownerZero oldBox newBox
      beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor
      initialState beforeContracts afterContracts ordered beforeStep resetStep
        afterStep).preparedBox edge =
      if edge.val < 4 then oldBox else newBox := by
  rfl

end Purelib.Examples.Riemann.PreparedEightStepSameBox
