module
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Encoding
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Approximation.Gaussian.Grid.Resource
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource
import Purelib.Data.Gaussian.Resource
import Purelib.Data.Rat.Fraction.Resource.Width
public import Purelib.Polynomial.Approximation.Resource.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Resource
import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Grid.Basic
import Purelib.Approximation.Rational.QuadraticTarget.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Fraction.Canonical
import Purelib.Data.GaussianInt.Fraction.Canonical.Height
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.RootIsolation
import Purelib.NumberTheory.Approximation.Best.Search
import Purelib.NumberTheory.Approximation.Best.Successor.Exhaustive
public import Purelib.NumberTheory.Approximation.Best.Successor.Local
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.History
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.Block
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.Chain
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
public import Purelib.NumberTheory.Approximation.Hurwitz.Geometry
import Purelib.NumberTheory.Approximation.Hurwitz.Lakein
public import Purelib.Polynomial.Approximation.BestResidual
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator
public import Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator.Intrinsic
public import Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator
public import Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator.Sharp
import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RationalFunctions.Approximation.Height.Basic
import Purelib.RationalFunctions.Approximation.Height.Budget
import Purelib.RationalFunctions.Approximation.Height.Build
public import Purelib.RationalFunctions.Approximation.Height.Target
import Purelib.RationalFunctions.Height.Residual
import Purelib.RootIsolation.Approximation.Denominator
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Divisibility.Basic

import Purelib.Data.ComplexContinuedFraction.Hurwitz.Trace
import Purelib.Polynomial.Dense.Derivative
import Purelib.Tactic.QuotientFreeOmega
public import papers.RFAP.Chapters.Paper
import Purelib.NumberTheory.Approximation.Best.Successor.Dynamics
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Trace
import Batteries.Data.List.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RationalFunctions.Residual.Local.Prepare
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Raw

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

open Purelib.Papers.RFAP

open Purelib.Polynomial

@[expose] public section

/-!
# RFAP denominator-height companion API

This facade contains the denominator-height calibration, finite best-residual
search, finite Hurwitz--Lakein comparison, and explicit finite
Dirichlet-window sharpness witnesses developed in the second RFAP paper.  It
deliberately imports the first paper's finite box and residual interface, then
adds only explicitly bounded approximation constructions.
-/

namespace Purelib.Papers.RFAP.Approximation

open Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds

/-- The canonical rational coordinate type retained from the first RFAP paper. -/
abbrev Coordinate := Paper.Coordinate
/-- The canonical Gaussian rational carrier retained from the first RFAP paper. -/
abbrev Gaussian := Paper.Gaussian
/-- Dense Gaussian polynomials with the first paper's original coefficient representation. -/
abbrev GaussianPolynomial := Paper.GaussianPolynomial
/-- A Gaussian rational fraction with an explicit positive natural common denominator. -/
abbrev GaussianFraction := Data.Gaussian.Basic.Canonical.Fraction.NaturalDenominator
/-- A rational rectangular box with its original geometric bounds. -/
abbrev Box := Geometry.Rational.Box
/-- A retained box state certified to have winding number one. -/
abbrev WindingOneState := RootIsolation.State.WindingOne.Basic.WindingOneState
/-- A finite root-approximation track on winding-one states. -/
abbrev WindingOneTrack := RootIsolation.Track.Basic.WindingOneTrack
/-- The first paper's squarefree polynomial certificate. -/
abbrev SquarefreeCertificate := Paper.SquarefreeCertificate
/-- A protected local quotient context retaining its source and opposite polynomials. -/
abbrev LocalQuotientContext := Paper.LocalQuotientContext
/-- A displayed Gaussian-integer numerator and nonzero Gaussian-integer denominator. -/
abbrev HurwitzFraction := Data.GaussianInt.Fraction
/-- A Gaussian fraction in the deterministic reduced canonical form. -/
abbrev ReducedHurwitzFraction :=
  Data.GaussianInt.Fraction.Canonical.CanonicalFraction
/-- One finite stage of the Hurwitz expansion of a displayed Gaussian fraction. -/
abbrev HurwitzStage := Data.ComplexContinuedFraction.Hurwitz.Trace.Stage
/-- The generation certificate linking a Hurwitz stage to its original source. -/
abbrev HurwitzGenerated := Hurwitz.Geometry.Generated
/-- A numerator–denominator pair of Gaussian integers in the Hurwitz continuant calculation. -/
abbrev HurwitzConvergentPair := Data.GaussianInt.Pair.Basic.ConvergentPair
/-- The project-owned Gaussian integer coefficient type. -/
abbrev GaussianInt := Data.GaussianInt
/-- A normalized Gaussian working record before erasing its representation data. -/
abbrev WorkingGaussian := Data.Gaussian.Basic.Number
/-- The retained inputs to the second-stage arithmetic resource certificate. -/
abbrev StageTwoInput := Approximation.Resource.Certificate.StageTwoInput

/-- The positive integer scale obtained by clearing the finitely many
Gaussian-rational coefficients of a displayed polynomial. -/
def denominatorCoefficientScale (p : GaussianPolynomial) : Nat :=
  Polynomial.Dense.Gaussian.Denominator.Clearing.coefficientScale p

/-- Necessary denominator-height inequality for every displayed sample with
nonzero residual. -/
theorem one_le_scaled_height_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          Data.Gaussian.Norm.Basic.normSq
            (p.eval fraction.value) :=
  Dense.Gaussian.Residual.NaturalDenominator.one_le_scaled_height_mul_residual
    p nonzero fraction residualNonzero

/-- Exact integral identity behind the common-denominator lower bound. -/
theorem scaledHeightResidual_eq_integralNorm
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) :
    (denominatorCoefficientScale p : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ p.natDegree *
        Data.Gaussian.Norm.Basic.normSq
          (p.eval fraction.value) =
      (Data.GaussianInt.normNat
        (Dense.Gaussian.Residual.NaturalDenominator.residualNumerator p fraction) : Coordinate) :=
  Dense.Gaussian.Residual.NaturalDenominator.scaled_height_mul_residual_eq_normNat
    p nonzero fraction

/-- Necessary denominator-height inequality for a displayed
Gaussian-integer numerator/denominator sample. -/
theorem one_le_scaled_gaussianHeight_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          Data.Gaussian.Norm.Basic.normSq
            (p.eval fraction.value) :=
  Dense.Gaussian.Residual.GaussianDenominator.one_le_scaled_height_mul_residual
    p nonzero fraction residualNonzero

/-- Execute Gaussian Euclidean reduction and deterministic unit
canonicalisation on a displayed Gaussian fraction. -/
def canonicalReducedGaussianFraction (fraction : HurwitzFraction) :
    ReducedHurwitzFraction :=
  Data.GaussianInt.Fraction.Canonical.Height.canonicalReduction fraction

/-- Canonical Gaussian reduction preserves the value of the displayed fraction. -/
theorem canonicalReducedGaussianFraction_value (fraction : HurwitzFraction) :
    (canonicalReducedGaussianFraction fraction).value = fraction.value :=
  Data.GaussianInt.Fraction.Canonical.Height.canonicalReduction_value fraction

/-- Presentation-independent denominator quadrance obtained by canonical
Gaussian Euclidean reduction. -/
def intrinsicGaussianDenominatorHeight (fraction : HurwitzFraction) : Nat :=
  Data.GaussianInt.Fraction.Canonical.Height.intrinsicHeight fraction

/-- The intrinsic reduced Gaussian denominator height is strictly positive. -/
theorem intrinsicGaussianDenominatorHeight_pos (fraction : HurwitzFraction) :
    0 < intrinsicGaussianDenominatorHeight fraction :=
  Data.GaussianInt.Fraction.Canonical.Height.intrinsicHeight_pos fraction

/-- The intrinsic reduced height is at most the height of the displayed denominator. -/
theorem intrinsicGaussianDenominatorHeight_le_displayed
    (fraction : HurwitzFraction) :
    intrinsicGaussianDenominatorHeight fraction ≤ fraction.height :=
  Data.GaussianInt.Fraction.Canonical.Height.intrinsicHeight_le_height fraction

/-- Equal-valued Gaussian fractions have the same intrinsic reduced denominator height. -/
theorem intrinsicGaussianDenominatorHeight_eq_of_value_eq
    (left right : HurwitzFraction) (valueEqual : left.value = right.value) :
    intrinsicGaussianDenominatorHeight left =
      intrinsicGaussianDenominatorHeight right :=
  Data.GaussianInt.Fraction.Canonical.Height.intrinsicHeight_eq_of_value_eq
    left right valueEqual

/-- Exact integral identity behind the intrinsic reduced Gaussian-height
obstruction. -/
theorem scaledIntrinsicGaussianHeightResidual_eq_integralNorm
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction) :
    (denominatorCoefficientScale p : Coordinate) ^ 2 *
          (intrinsicGaussianDenominatorHeight fraction : Coordinate) ^
            p.natDegree *
        Data.Gaussian.Norm.Basic.normSq
          (p.eval fraction.value) =
      (Data.GaussianInt.normNat
        (Dense.Gaussian.Residual.GaussianDenominator.Intrinsic.intrinsicResidualNumerator p
          fraction) : Coordinate) :=
  Dense.Gaussian.Residual.GaussianDenominator.Intrinsic.scaled_intrinsicHeight_mul_residual_eq_normNat
    p nonzero fraction

/-- Necessary residual inequality using presentation-independent canonical
reduced Gaussian-denominator height. -/
theorem one_le_scaled_intrinsicGaussianHeight_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (intrinsicGaussianDenominatorHeight fraction : Coordinate) ^
            p.natDegree *
          Data.Gaussian.Norm.Basic.normSq
            (p.eval fraction.value) :=
  Dense.Gaussian.Residual.GaussianDenominator.Intrinsic.one_le_scaled_intrinsicHeight_mul_residual
    p nonzero fraction residualNonzero

/-- Explicit equality family showing joint sharpness of the unit constant,
coefficient-scale square, and degree-th power of displayed height. -/
theorem denominatorHeightBound_isSharp
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (denominatorCoefficientScale
        (Dense.Gaussian.Residual.NaturalDenominator.Sharp.sharpPolynomial degree scale
          scalePositive) : Coordinate) ^ 2 *
          ((Dense.Gaussian.Residual.NaturalDenominator.Sharp.sharpFraction denominator
            denominatorPositive).height : Coordinate) ^
            (Dense.Gaussian.Residual.NaturalDenominator.Sharp.sharpPolynomial degree scale
              scalePositive).natDegree *
        Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.Residual.NaturalDenominator.Sharp.sharpPolynomial degree scale
            scalePositive).eval
              (Dense.Gaussian.Residual.NaturalDenominator.Sharp.sharpFraction denominator
                denominatorPositive).value) = 1 :=
  Dense.Gaussian.Residual.NaturalDenominator.Sharp.scaled_height_mul_residual_eq_one
    degree scale denominator scalePositive denominatorPositive

/-- Execute Newton-band extraction and return an interior Gaussian-rational
sample with its exact common-denominator height and residual bound. -/
def approximateWithHeight
    {p : GaussianPolynomial} {ambient : Geometry.Rational.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    RootIsolation.Approximation.Denominator.Output degreeAtLeastTwo squarefree elimination
      current epsilon :=
  RootIsolation.Approximation.Denominator.approximate degreeAtLeastTwo squarefree elimination
    current epsilonPositive

/-- Execute Newton-band extraction with the square-root-scaled request for a
displayed positive residual target. -/
def approximateWithTarget
    {p : GaussianPolynomial} {ambient : Geometry.Rational.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient)
    (target : Coordinate) :
    RootIsolation.Approximation.Denominator.Output degreeAtLeastTwo squarefree elimination
      current
        (Approximation.Rational.QuadraticTarget.Basic.targetEpsilon
          (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) target) :=
  RootIsolation.Approximation.Denominator.approximateTarget degreeAtLeastTwo squarefree
    elimination current target

/-- The target-based polynomial approximation has residual quadrance at most its positive requested target. -/
theorem approximateWithTarget_residual_le
    {p : GaussianPolynomial} {ambient : Geometry.Rational.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RootIsolation.State.Raw.RawWindingState p ambient)
    {target : Coordinate} (targetPositive : 0 < target) :
    Data.Gaussian.Norm.Basic.normSq
      (p.eval (approximateWithTarget degreeAtLeastTwo squarefree elimination
        current target).fraction.value) ≤ target := by
  let retained := approximateWithTarget degreeAtLeastTwo squarefree elimination current target
  have bound : Data.Gaussian.Basic.Canonical.normSq
      (p.eval retained.fraction.value) ≤ target :=
    RootIsolation.Approximation.Denominator.approximateTarget_residual_le degreeAtLeastTwo
      squarefree elimination current targetPositive
  exact (Data.Gaussian.Norm.Basic.normSq_eq_canonical
    (p.eval retained.fraction.value)).trans_le bound

/-- Exact finite minimization of residual over all displayed
common-denominator Gaussian fractions in the supplied numerator and
denominator window. -/
def bestResidualSample (p : GaussianPolynomial)
    (numeratorBound denominatorBound : Nat) : Option GaussianFraction :=
  Approximation.BestResidual.best p numeratorBound denominatorBound

/-- A positive denominator bound makes the finite residual search return a sample. -/
theorem bestResidualSample_exists (p : GaussianPolynomial)
    (numeratorBound : Nat) {denominatorBound : Nat}
    (positive : 0 < denominatorBound) :
    ∃ selected,
      bestResidualSample p numeratorBound denominatorBound = some selected :=
  Approximation.BestResidual.best_exists p numeratorBound positive

/-- The selected sample minimizes residual quadrance among fractions inside the supplied numerator and denominator
window. -/
theorem bestResidualSample_is_optimal
    {p : GaussianPolynomial} {numeratorBound denominatorBound : Nat}
    {selected candidate : GaussianFraction}
    (selection : bestResidualSample p numeratorBound denominatorBound =
      some selected)
    (realBound : candidate.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : candidate.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : candidate.denominator ≤ denominatorBound) :
    Approximation.BestResidual.score p selected ≤ Approximation.BestResidual.score p candidate :=
  Approximation.BestResidual.best_is_optimal selection realBound imaginaryBound
    denominatorBounded

/-- Construct the denominator-controlled residual sample for a protected
rational-function site.  Swapping source and opposite gives the pole result
for the reciprocal residual. -/
def approximateQuotientWithHeight
    {source opposite : GaussianPolynomial} {ambient : Geometry.Rational.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    RationalFunctions.Approximation.Height.Basic.Output context degreeAtLeastTwo squarefree
      elimination epsilon :=
  RationalFunctions.Approximation.Height.Build.approximate context degreeAtLeastTwo
    squarefree elimination epsilonPositive

/-- Protected quotient approximation with the corresponding square-root
target request. -/
def approximateQuotientWithTarget
    {source opposite : GaussianPolynomial} {ambient : Geometry.Rational.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    (target : Coordinate) :
    RationalFunctions.Approximation.Height.Basic.Output context degreeAtLeastTwo squarefree
      elimination
        (Approximation.Rational.QuadraticTarget.Basic.targetEpsilon
          (RationalFunctions.Approximation.Height.Budget.targetCoefficient context) target) :=
  RationalFunctions.Approximation.Height.Target.approximateTarget context degreeAtLeastTwo
    squarefree elimination target

/-- The protected quotient approximation has residual quadrance at most its positive requested target. -/
theorem approximateQuotientWithTarget_residual_le
    {source opposite : GaussianPolynomial} {ambient : Geometry.Rational.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    {target : Coordinate} (targetPositive : 0 < target) :
    Paper.quotientResidualSq source opposite
        (approximateQuotientWithTarget context degreeAtLeastTwo squarefree
          elimination target).polynomial.fraction.value ≤ target :=
  RationalFunctions.Approximation.Height.Target.approximateTarget_quotientResidual_le
    context degreeAtLeastTwo squarefree elimination targetPositive

/-- Necessary height inequality for a protected nonzero quotient residual.
At a pole, source and opposite are exchanged, so this is the reciprocal
residual inequality. -/
theorem one_le_scaled_height_mul_quotientResidual
    {source opposite : GaussianPolynomial} {ambient : Geometry.Rational.Box}
    (context : LocalQuotientContext source opposite ambient)
    {state : RootIsolation.State.WindingOne.Basic.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (fraction : GaussianFraction) (inside : state.box.Contains fraction.value)
    (sourceNonzero : source.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale source : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ source.natDegree *
          context.oppositeMajorant *
            Paper.quotientResidualSq source opposite fraction.value :=
  RationalFunctions.Height.Residual.one_le_scaled_height_mul_quotientResidual
    context refinesProtected fraction inside sourceNonzero

/-- Finite Lakein comparison for every displayed stage of the executable
Hurwitz expansion.  Any Gaussian-rational competitor with nonzero and
strictly smaller denominator has at least the current convergent's
division-free residual quadrance. -/
theorem hurwitzConvergent_atLeastAsGoodAs
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage)
    (competitor : HurwitzConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      Data.GaussianInt.normNat
          competitor.denominator <
        Data.GaussianInt.normNat
          stage.current.denominator) :
    Best.Error.AtLeastAsGoodAs
      source.value stage.current competitor :=
  Hurwitz.Lakein.Stage.atLeastAsGoodAs_of_generated stage generated
    competitor competitorDenominatorNonzero denominatorSmaller

/-- The stronger unconditional description of the existing Lakein result:
every generated continuant is weakly best against all strictly smaller
denominators. -/
theorem hurwitzConvergent_isWeakLowerBest
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage) :
    Best.Basic.IsWeakLowerBest source.value stage.current :=
  Hurwitz.Lakein.Stage.isWeakLowerBest_of_generated stage generated

/-- At the terminal stage the exact Hurwitz continuant satisfies the full
strict/equal-height best-approximation predicate. -/
theorem terminalHurwitzConvergent_isBest
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage)
    (terminal : Data.GaussianInt.Division.Nearest.remainder stage.quotient = 0) :
    Best.Basic.IsBest source.value stage.current :=
  Hurwitz.Lakein.Stage.isBest_of_generated_of_terminal
    stage generated terminal

/-- Execute the proved finite search for all best Gaussian-rational
approximations to a displayed rational source. -/
def allBestGaussianApproximations (source : HurwitzFraction) :
    List HurwitzConvergentPair :=
  Best.Search.allBest source

/-- The finite selector is both sound and complete for the full two-tier
best-approximation predicate. -/
theorem mem_allBestGaussianApproximations_iff
    (source : HurwitzFraction) (pair : HurwitzConvergentPair) :
    pair ∈ allBestGaussianApproximations source ↔
      Best.Basic.IsBest source.value pair :=
  Best.Search.mem_allBest_iff_isBest source pair

/-- The all-best calculation always returns at least one pair; the terminal
Hurwitz continuant is an explicit witness. -/
theorem allBestGaussianApproximations_nonempty (source : HurwitzFraction) :
    allBestGaussianApproximations source ≠ [] :=
  Hurwitz.Lakein.allBest_nonempty source

/-- Execute the finite all-best calculation on the certified rational sample
returned by one RAT response. -/
def ratResponseBestApproximations (sample : GaussianFraction) :
    List HurwitzConvergentPair :=
  Best.RootIsolation.bestApproximations sample

/-- The RAT-response calculation emits all and only full best approximants
to its displayed finite response point. -/
theorem mem_ratResponseBestApproximations_iff
    (sample : GaussianFraction) (pair : HurwitzConvergentPair) :
    pair ∈ ratResponseBestApproximations sample ↔
      Best.Basic.IsBest sample.value pair :=
  Best.RootIsolation.mem_bestApproximations_iff sample pair

/-- A finite RAT response always computes at least one full best
approximant. -/
theorem ratResponseBestApproximations_nonempty (sample : GaussianFraction) :
    ratResponseBestApproximations sample ≠ [] :=
  Best.RootIsolation.bestApproximations_nonempty sample

/-- Deterministically select one representative of the next occupied best
level above a certified best RAT-response approximant. -/
def nextRATResponseBestApproximation?
    (sample : GaussianFraction) (lower : HurwitzConvergentPair) :
    Option HurwitzConvergentPair :=
  Best.RootIsolation.nextBestApproximation? sample lower

/-- Every pair emitted by the RAT-response step is genuinely consecutive
best; the algorithm cannot emit a merely provisional approximant. -/
theorem nextRATResponseBestApproximation?_sound
    {sample : GaussianFraction} {lower next : HurwitzConvergentPair}
    (selected :
      nextRATResponseBestApproximation? sample lower = some next) :
    Best.Consecutive.Basic.AreConsecutiveBest
      sample.value lower next :=
  Best.RootIsolation.nextBestApproximation?_sound selected

/-- Total finite RAT-response step: produce the next consecutive best pair,
or certify that the current pair represents the response exactly. -/
theorem nextRATResponseBestApproximation_or_exactTerminal
    {sample : GaussianFraction} {lower : HurwitzConvergentPair}
    (lowerBest : Best.Basic.IsBest sample.value lower) :
    (∃ next : HurwitzConvergentPair,
      nextRATResponseBestApproximation? sample lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest
          sample.value lower next) ∨
      Best.Error.errorQuadrance sample.value lower = 0 :=
  Best.RootIsolation.nextBestApproximation_or_exactTerminal lowerBest

/-- Complete RFAP-II arithmetic response attached directly to one finite call
of any RFAP-I root-approximation track.  It retains the refined box, canonical
rational anchor, residual bound, all-and-only-best table, and total
next-best-or-terminal step. -/
def respondToRAT
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    Best.RootIsolation.TrackBestResponse
      degreePositive track current epsilon epsilonPositive :=
  Best.RootIsolation.respondToTrack degreePositive track current epsilon
    epsilonPositive

/-- Every member emitted by the combined RFAP-I/RFAP-II response is a full
best approximant to that response's displayed rational anchor. -/
theorem mem_respondToRAT_approximants_iff
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (pair : HurwitzConvergentPair) :
    pair ∈ (respondToRAT degreePositive track current epsilon
        epsilonPositive).approximants ↔
      Best.Basic.IsBest
        (respondToRAT degreePositive track current epsilon
          epsilonPositive).sample.value pair :=
  (respondToRAT degreePositive track current epsilon
    epsilonPositive).memApproximantsIff pair

/-- Every best member of a combined RFAP-I/RFAP-II response has a computed
consecutive successor or an exact zero-error terminal certificate. -/
theorem respondToRAT_next_or_exactTerminal
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (lower : HurwitzConvergentPair)
    (lowerBest : Best.Basic.IsBest
      (respondToRAT degreePositive track current epsilon
        epsilonPositive).sample.value lower) :
    (∃ next : HurwitzConvergentPair,
      (respondToRAT degreePositive track current epsilon
        epsilonPositive).next? lower = some next ∧
        Best.Consecutive.Basic.AreConsecutiveBest
          (respondToRAT degreePositive track current epsilon
            epsilonPositive).sample.value lower next) ∨
      Best.Error.errorQuadrance
        (respondToRAT degreePositive track current epsilon
          epsilonPositive).sample.value lower = 0 :=
  (respondToRAT degreePositive track current epsilon
    epsilonPositive).nextOrTerminal lowerBest

/-- RFAP-II arithmetic capability carried by every branch of the positive
degree RFAP-I finite FTA.  A linear result has an exact-point response;
a higher result supports a complete best response at every finite call of
each returned degree-indexed RAT. -/
def FTAApproximationCapability
    {p : GaussianPolynomial} : RootIsolation.FTA.Positive.Basic.PositiveResult p → Type
  | .linear root _ => Best.RootIsolation.PointBestResponse root.point
  | .higher boxes degree =>
      ∀ (index : Fin p.natDegree)
        (current : WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
        (epsilon : Coordinate) (epsilonPositive : 0 < epsilon),
        Best.RootIsolation.TrackBestResponse
          (by omega : 0 < p.natDegree)
          (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Construct the RFAP-II best-approximation capability for an arbitrary
positive-degree RFAP-I FTA result, branch by branch and without changing the
Paper-I facade. -/
def strengthenFTAResult
    {p : GaussianPolynomial} (result : RootIsolation.FTA.Positive.Basic.PositiveResult p) :
    FTAApproximationCapability result := by
  cases result with
  | linear root degree =>
      exact Best.RootIsolation.respondToPoint root.point
  | higher boxes degree =>
      intro index current epsilon epsilonPositive
      exact Best.RootIsolation.respondToTrack (by omega)
        (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- RFAP-II arithmetic capability carried by one signed polynomial-factor
observation in the RFAP-I rational-function action principle.  Exact linear
sites use their displayed point; every higher site supports a best response
at each finite call of each returned RAT. -/
def RationalSiteApproximationCapability
    {source opposite : GaussianPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries} :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context → Type
  | .exact root _ _ =>
      Best.RootIsolation.PointBestResponse root.point
  | .higher boxes degree =>
      ∀ (index : Fin context.focus.part.polynomial.natDegree)
        (current : WindingOneState context.focus.part.polynomial
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox context.focus.part.polynomial))
        (epsilon : Coordinate) (epsilonPositive : 0 < epsilon),
        Best.RootIsolation.TrackBestResponse
          (by omega : 0 < context.focus.part.polynomial.natDegree)
          (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Construct the RFAP-II best-approximation capability for every exact or
higher-degree signed site returned by RFAP-I. -/
def strengthenRationalSite
    {source opposite : GaussianPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
    RationalSiteApproximationCapability observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      exact Best.RootIsolation.respondToPoint root.point
  | higher boxes degree =>
      intro index current epsilon epsilonPositive
      exact Best.RootIsolation.respondToTrack (by omega)
        (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Execute the finite successor calculation returning every best pair at the
next occupied denominator level above `lower`. -/
def consecutiveBestSuccessors
    (source : HurwitzFraction) (lower : HurwitzConvergentPair) :
    List HurwitzConvergentPair :=
  Best.Successor.Exhaustive.consecutiveSuccessors source lower

/-- Exact specification of the finite consecutive-minimal-vector successor
calculation. -/
theorem mem_consecutiveBestSuccessors_iff
    (source : HurwitzFraction) (lower candidate : HurwitzConvergentPair) :
    candidate ∈ consecutiveBestSuccessors source lower ↔
      Best.Consecutive.Basic.AreConsecutiveBest
        source.value lower candidate :=
  Best.Successor.Exhaustive.mem_consecutiveSuccessors_iff
    source lower candidate

/-- Source/state-computed trailing-coefficient bound used by the local
successor generator. -/
def localSuccessorCoefficientBound
    (source : HurwitzFraction) (previous : HurwitzConvergentPair) : Nat :=
  Best.Successor.Local.trailingCoefficientBound source previous

/-- Execute the proved coefficient-local successor search from one supplied
adjacent best pair. -/
def localConsecutiveBestSuccessors
    (source : HurwitzFraction)
    (previous current : HurwitzConvergentPair) :
    List HurwitzConvergentPair :=
  Best.Successor.Local.successors source previous current

/-- The exact coefficient-local validation predicate used by the successor
calculation. -/
def passesLocalSuccessorTest
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair) : Prop :=
  Best.Successor.Local.PassesLocalSuccessorTest
    source previous current candidate

/-- The coefficient-local validation predicate is equivalent to occupying
the next best level, provided the supplied state is adjacent. -/
theorem passesLocalSuccessorTest_iff
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value previous current) :
    passesLocalSuccessorTest source previous current candidate ↔
      Best.Consecutive.Basic.AreConsecutiveBest
        source.value current candidate :=
  Best.Successor.Local.passesLocalSuccessorTest_iff first

/-- The coefficient-local successor calculation returns exactly the next
occupied best level and skips none, provided its input state is adjacent. -/
theorem mem_localConsecutiveBestSuccessors_iff
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value previous current) :
    candidate ∈ localConsecutiveBestSuccessors source previous current ↔
      Best.Consecutive.Basic.AreConsecutiveBest
        source.value current candidate :=
  Best.Successor.Local.mem_successors_iff first candidate

/-- Explicit size bound for the coefficient-local candidate list underlying
the successor calculation. -/
theorem localSuccessorCandidates_length_le
    (source : HurwitzFraction)
    (previous current : HurwitzConvergentPair) :
    (Best.Successor.Local.candidates source previous current).length ≤
      64 * (localSuccessorCoefficientBound source previous + 1) ^ 2 :=
  Best.Successor.Local.candidates_length_le source previous current

/-- Constructive local characterization of consecutive best levels by the
absence of a nonzero pair in their mixed open cylinder. -/
theorem consecutiveBest_iff_mixedCylinderEmpty
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) :
    Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper ↔
      Best.Basic.IsBest source.value lower ∧
        Best.Basic.IsBest source.value upper ∧
        Best.Error.denominatorQuadrance lower <
          Best.Error.denominatorQuadrance upper ∧
        Best.Consecutive.Basic.MixedCylinderEmpty
          source.value lower upper :=
  Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty
    source lower upper

/-- A bounded small-error pair descends by an executable finite minimization
to a genuine best pair of no greater height or error. -/
theorem exists_bestBelow_of_small
    (source : HurwitzFraction) (candidate : HurwitzConvergentPair)
    (candidateNonzero : candidate.denominator ≠ 0)
    (denominatorBounded :
      Best.Error.denominatorQuadrance candidate ≤
        Data.GaussianInt.normNat
          source.denominator)
    (smallError :
      Best.Error.errorQuadrance source.value candidate ≤ 1 / 2) :
    ∃ selected : HurwitzConvergentPair,
      Best.Basic.IsBest source.value selected ∧
        Best.Error.denominatorQuadrance selected ≤
          Best.Error.denominatorQuadrance candidate ∧
        Best.Error.errorQuadrance source.value selected ≤
          Best.Error.errorQuadrance source.value candidate :=
  Best.Search.exists_best_below_of_small candidateNonzero
    denominatorBounded smallError

/-- Determinant quadrance of the coefficient sublattice spanned by two
displayed approximation pairs. -/
def coefficientIndexQuadrance
    (left right : HurwitzConvergentPair) : Nat :=
  Data.GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance left right

/-- Consecutive best levels are represented by coefficientwise independent
pairs, so their displayed determinant quadrance is positive. -/
theorem consecutiveBest_coefficientIndexQuadrance_pos
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    0 < coefficientIndexQuadrance lower upper :=
  (Best.Consecutive.Basic.AreConsecutiveBest.coefficientIndexQuadrance_pos consecutive)

/-- Sharp constructive determinant classification for consecutive best
pairs over a displayed rational source. -/
theorem consecutiveBest_coefficientIndexQuadrance_eq_one_or_two
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    coefficientIndexQuadrance lower upper = 1 ∨
      coefficientIndexQuadrance lower upper = 2 :=
  (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive)

/-- Complete finite coefficient-coset classification of every ambient pair
relative to two consecutive best levels. -/
theorem consecutiveBest_coefficientSpan_or_centeredCoset
    (source : HurwitzFraction) (lower upper candidate : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    Data.GaussianInt.Pair.LinearCombination.InCoefficientSpan lower upper candidate ∨
      Data.GaussianInt.Pair.LinearCombination.InCenteredCoefficientCoset
        lower upper candidate :=
  (Best.Consecutive.Index.AreConsecutiveBest.coefficientSpan_or_centeredCoset consecutive) candidate

/-- In the index-two case any two nondivisible cleared coefficients construct
an ambient pair in the centered coset. -/
theorem consecutiveBest_exists_centeredCoefficientPair
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient :
      Data.GaussianInt)
    (leftNotDivisible :
      ¬ Data.GaussianInt.Divisibility.Basic.Divides
        (Data.GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)
          leftCoefficient)
    (rightNotDivisible :
      ¬ Data.GaussianInt.Divisibility.Basic.Divides
        (Data.GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)
          rightCoefficient) :
    ∃ candidate : HurwitzConvergentPair,
      Data.GaussianInt.Pair.LinearCombination.scalePair
          (Data.GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)
          candidate =
        Data.GaussianInt.Pair.LinearCombination.linearCombination lower upper
          leftCoefficient rightCoefficient :=
  (Best.Consecutive.Index.AreConsecutiveBest.exists_centeredCoefficientPair consecutive) indexTwo
    leftCoefficient rightCoefficient leftNotDivisible rightNotDivisible

/-- Coefficient normal form for two consecutive index-two transitions. -/
theorem consecutiveBest_indexTwoTransition
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient :
        Data.GaussianInt,
      Data.GaussianInt.normNat
          lowerCoefficient = 1 ∧
      Data.GaussianInt.Divisibility.Basic.Divides
        (Data.GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle)
          middleCoefficient ∧
      upper = Data.GaussianInt.Pair.LinearCombination.linearCombination lower middle
        lowerCoefficient middleCoefficient :=
  (Best.Consecutive.NormalForm.AreConsecutiveBest.integralTransition_with_divisible_middleCoefficient first) second
    leftIndexTwo rightIndexTwo

/-- Uniform square-root-free error-ratio bound for an index-two consecutive
best pair. -/
theorem consecutiveBest_indexTwoErrorRatio
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    Best.Error.errorQuadrance source.value lower <
      4 * Best.Error.errorQuadrance source.value upper :=
  (Best.Consecutive.NormalForm.AreConsecutiveBest.errorQuadrance_lower_lt_four_mul_upper_of_index_two consecutive)
    indexTwo

/-- Fully finite repeated-index normal form.  The Gaussian step is one of the
twelve nonzero integral values having quadrance one, two, or four. -/
theorem consecutiveBest_indexTwoEnumeratedTransition
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : Data.GaussianInt,
      Data.GaussianInt.normNat lowerUnit = 1 ∧
      (Data.GaussianInt.normNat step = 1 ∨
        Data.GaussianInt.normNat step = 2 ∨
        Data.GaussianInt.normNat step = 4) ∧
      upper = Data.GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerUnit
        (Data.GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle * step) :=
  (Best.Consecutive.NormalForm.AreConsecutiveBest.repeatedIndexTwo_enumeratedNormalForm first) second leftIndexTwo
    rightIndexTwo

/-- Two successive consecutive best transitions cannot both have
coefficient-index quadrance two. -/
theorem consecutiveBest_repeatedIndexTwo_impossible
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) : False :=
  Best.Consecutive.RepeatedIndex.repeatedIndexTwo_impossible first second leftIndexTwo
    rightIndexTwo

/-- An index-two consecutive best transition is necessarily followed by an
index-one transition. -/
theorem consecutiveBest_nextIndex_eq_one_of_indexTwo
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2) :
    coefficientIndexQuadrance middle upper = 1 :=
  Best.Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two first
    second leftIndexTwo

/-- Source-computed finite bound for the determinant quadrance of consecutive
best pairs. -/
theorem consecutiveBest_coefficientIndexQuadrance_le_sourceBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    coefficientIndexQuadrance lower upper ≤
      4 * Best.Search.numeratorQuadranceBound source *
        Data.GaussianInt.normNat
          source.denominator :=
  (Best.Consecutive.NormalForm.AreConsecutiveBest.coefficientIndexQuadrance_le_sourceBound consecutive)

/-- Squared denominator--error product governing the finite request window
between two consecutive best levels. -/
def consecutiveDirichletWindowQuadrance
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) : Coordinate :=
  Dirichlet.Window.SourceBound.dirichletWindowQuadrance
    source.value lower upper

/-- One displayed coefficient-index quadrance for every adjacent pair in a
finite list of approximation records. -/
def consecutiveCoefficientIndexQuadrances
    (pairs : List HurwitzConvergentPair) : List Nat :=
  Dirichlet.Window.Chain.coefficientIndexQuadrances pairs

/-- One exact squared Dirichlet-window product for every adjacent pair in a
finite list of approximation records. -/
def consecutiveDirichletWindowQuadrances
    (source : HurwitzFraction)
    (pairs : List HurwitzConvergentPair) : List Coordinate :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances source.value pairs

/-- The adjacent-window list and coefficient-index list have the same length. -/
theorem consecutiveDirichletWindowQuadrances_length_eq_indexQuadrances_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair) :
    (consecutiveDirichletWindowQuadrances source pairs).length =
      (consecutiveCoefficientIndexQuadrances pairs).length :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
    source.value pairs

/-- The determinant index is strictly below four times the exact consecutive
window product. -/
theorem consecutiveBest_index_lt_four_mul_dirichletWindow
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (coefficientIndexQuadrance lower upper : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  (Dirichlet.Window.SourceBound.AreConsecutiveBest.coefficientIndexQuadrance_lt_four_mul_dirichletWindow consecutive)

/-- Every consecutive window product is strictly greater than one quarter,
in a division-free statement. -/
theorem one_lt_four_mul_consecutiveDirichletWindow
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (1 : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  (Dirichlet.Window.SourceBound.AreConsecutiveBest.one_lt_four_mul_dirichletWindow consecutive)

/-- An index-two consecutive window product is strictly greater than one
half, again stated without division. -/
theorem two_lt_four_mul_consecutiveDirichletWindow_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (2 : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  (Dirichlet.Window.SourceBound.AreConsecutiveBest.two_lt_four_mul_dirichletWindow_of_indexTwo consecutive) indexTwo

/-- Normalized determinant gap associated to two consecutive best levels. -/
def consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
    (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
      Dirichlet.Window.Basic.errorRatio source.value lower upper)

/-- Displayed refined normalized-gap threshold, exactly `35/408`. -/
def refinedNormalizedDeterminantGapThreshold : Coordinate :=
  Dirichlet.Window.Basic.refinedGapThreshold

/-- The refined normalized-gap threshold 35/408 is less than one half. -/
theorem refinedNormalizedDeterminantGapThreshold_lt_half :
    refinedNormalizedDeterminantGapThreshold < (1 / 2 : Coordinate) :=
  Dirichlet.Window.Basic.refinedGapThreshold_lt_half

/-- The refined threshold satisfies the nonnegative quadratic boundary test. -/
theorem refinedNormalizedDeterminantGapThreshold_quadratic_nonnegative :
    0 ≤ refinedNormalizedDeterminantGapThreshold ^ 2 -
      3 * refinedNormalizedDeterminantGapThreshold + 1 / 4 :=
  Dirichlet.Window.Basic.refinedGapThreshold_quadratic_nonnegative

/-- Clearing the refined gap threshold's denominator yields thirty-five. -/
theorem refinedNormalizedDeterminantGapThreshold_mul_denominator :
    refinedNormalizedDeterminantGapThreshold * 408 = 35 :=
  Dirichlet.Window.Basic.refinedGapThreshold_mul_denominator

/-- Displayed refined universal squared-window bound, exactly `816/35`. -/
def refinedUniversalDirichletWindowBound : Coordinate :=
  Dirichlet.Window.Basic.refinedUniversalWindowBound

/-- Displayed factor `408/35` multiplying one coefficient index in the
refined squared-window bound. -/
def refinedIndexDirichletWindowFactor : Coordinate :=
  Dirichlet.Window.Basic.refinedIndexFactor

/-- Clearing the refined index factor's denominator yields 408. -/
theorem refinedIndexDirichletWindowFactor_mul_denominator :
    refinedIndexDirichletWindowFactor * 35 = 408 :=
  Dirichlet.Window.Basic.refinedIndexFactor_mul_denominator

/-- Clearing the refined universal window bound's denominator yields 816. -/
theorem refinedUniversalDirichletWindowBound_mul_denominator :
    refinedUniversalDirichletWindowBound * 35 = 816 :=
  Dirichlet.Window.Basic.refinedUniversalWindowBound_mul_denominator

/-- Displayed quadratic-boundary threshold, exactly `102/1189`. -/
def quadraticNormalizedDeterminantGapThreshold : Coordinate :=
  Dirichlet.Window.Basic.quadraticGapThreshold

/-- Exact reciprocal factor `1189/102` for the quadratic-boundary threshold. -/
def quadraticIndexDirichletWindowFactor : Coordinate :=
  Dirichlet.Window.Basic.quadraticIndexFactor

/-- Index-aware universal squared-window bound, exactly `1189/102`. -/
def indexAwareUniversalDirichletWindowBound : Coordinate :=
  Dirichlet.Window.Basic.quadraticIndexFactor

/-- Centered index-two normalized determinant-gap bound, exactly `71/56`. -/
def centeredIndexTwoNormalizedDeterminantGap : Coordinate :=
  Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold

/-- Clearing the centered index-two gap denominator yields seventy-one. -/
theorem centeredIndexTwoNormalizedDeterminantGap_mul_denominator :
    centeredIndexTwoNormalizedDeterminantGap * 56 = 71 :=
  Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold_mul_denominator

/-- Centered index-two squared-window bound, exactly `112/71`. -/
def centeredIndexTwoDirichletWindowBound : Coordinate :=
  Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound

/-- Clearing the centered index-two window-bound denominator yields 112. -/
theorem centeredIndexTwoDirichletWindowBound_mul_denominator :
    centeredIndexTwoDirichletWindowBound * 71 = 112 :=
  Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound_mul_denominator

/-- Finite-octant universal squared-window bound, exactly `112/71`. -/
def octantUniversalDirichletWindowBound : Coordinate :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound

/-- Clearing the finite-octant universal window-bound denominator yields 112. -/
theorem octantUniversalDirichletWindowBound_mul_denominator :
    octantUniversalDirichletWindowBound * 71 = 112 :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_mul_denominator

/-- Improved finite-octant normalized-gap certificate, exactly `71/112`. -/
def octantNormalizedDeterminantGap : Coordinate :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold

/-- Clearing the finite-octant normalized-gap denominator yields seventy-one. -/
theorem octantNormalizedDeterminantGap_mul_denominator :
    octantNormalizedDeterminantGap * 112 = 71 :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneGapThreshold_mul_denominator

/-- Improved determinant-index-one squared-window bound, exactly `112/71`. -/
def octantIndexOneDirichletWindowBound : Coordinate :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound

/-- Clearing the finite-octant index-one window-bound denominator yields 112. -/
theorem octantIndexOneDirichletWindowBound_mul_denominator :
    octantIndexOneDirichletWindowBound * 71 = 112 :=
  Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound_mul_denominator

/-- Near-optimal dyadic base gap, exactly `205/256`. -/
def dyadicNormalizedDeterminantGap : Coordinate :=
  Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound

/-- The dyadic gap multiplied by 256 is 205. -/
theorem dyadicNormalizedDeterminantGap_mul_denominator :
    dyadicNormalizedDeterminantGap * (2 : Coordinate) ^ 8 =
      13 * 16 - 3 :=
  Dirichlet.Window.IndexOne.Bounds.sharpIndexOneGapBound_mul_denominator

/-- Matching determinant-index-two gap, exactly `205/128`. -/
def dyadicCenteredIndexTwoNormalizedDeterminantGap : Coordinate :=
  Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold

/-- Near-optimal dyadic universal squared-window bound, exactly `256/205`. -/
def dyadicUniversalDirichletWindowBound : Coordinate :=
  Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound

/-- The dyadic universal window bound multiplied by 205 is 256. -/
theorem dyadicUniversalDirichletWindowBound_mul_denominator :
    dyadicUniversalDirichletWindowBound * (13 * 16 - 3 : Coordinate) =
      (2 : Coordinate) ^ 8 :=
  Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound_mul_denominator

/-- Universal squared-window bound obtained from the quadratic gap alone,
exactly `1189/51`. -/
def quadraticUniversalDirichletWindowBound : Coordinate :=
  Dirichlet.Window.Basic.quadraticUniversalWindowBound

/-- The quadratic normalized-gap threshold 102/1189 is less than one half. -/
theorem quadraticNormalizedDeterminantGapThreshold_lt_half :
    quadraticNormalizedDeterminantGapThreshold < (1 / 2 : Coordinate) :=
  Dirichlet.Window.Basic.quadraticGapThreshold_lt_half

/-- The quadratic normalized-gap threshold satisfies the nonnegative boundary test. -/
theorem quadraticNormalizedDeterminantGapThreshold_quadratic_nonnegative :
    0 ≤ quadraticNormalizedDeterminantGapThreshold ^ 2 -
      3 * quadraticNormalizedDeterminantGapThreshold + 1 / 4 :=
  Dirichlet.Window.Basic.quadraticGapThreshold_quadratic_nonnegative

/-- The cleared integer boundary certificate 4·102² − 12·102·1189 + 1189² equals one. -/
theorem quadraticNormalizedDeterminantGapThreshold_integerCertificate :
    (4 * 102 ^ 2 - 12 * 102 * 1189 + 1189 ^ 2 : Int) = 1 :=
  Dirichlet.Window.Basic.quadraticGapThreshold_integerCertificate

/-- Clearing the quadratic universal window-bound denominator yields 1189. -/
theorem quadraticUniversalDirichletWindowBound_mul_denominator :
    quadraticUniversalDirichletWindowBound * 51 = 1189 :=
  Dirichlet.Window.Basic.quadraticUniversalWindowBound_mul_denominator

/-- Clearing the index-aware universal window-bound denominator yields 1189. -/
theorem indexAwareUniversalDirichletWindowBound_mul_denominator :
    indexAwareUniversalDirichletWindowBound * 102 = 1189 :=
  Dirichlet.Window.IndexTwo.Bounds.quadraticIndexFactor_mul_denominator

/-- The quadratic universal window bound is smaller than the refined universal bound. -/
theorem quadraticUniversalDirichletWindowBound_lt_refined :
    quadraticUniversalDirichletWindowBound <
      refinedUniversalDirichletWindowBound :=
  Dirichlet.Window.Basic.quadraticUniversalWindowBound_lt_refinedUniversalWindowBound

/-- Displayed refined bound `1224/35` for the sum of two successive squared
Dirichlet-window products. -/
def refinedTwoWindowDirichletSumBound : Coordinate :=
  Dirichlet.Window.Block.refinedTwoWindowSumBound

/-- Clearing the refined two-window sum-bound denominator yields 1224. -/
theorem refinedTwoWindowDirichletSumBound_mul_denominator :
    refinedTwoWindowDirichletSumBound * 35 = 1224 :=
  Dirichlet.Window.Block.refinedTwoWindowSumBound_mul_denominator

/-- Sharper displayed bound `1189/34` for the sum of two successive squared
Dirichlet-window products. -/
def quadraticTwoWindowDirichletSumBound : Coordinate :=
  Dirichlet.Window.Block.quadraticTwoWindowSumBound

/-- Clearing the quadratic two-window sum-bound denominator yields 1189. -/
theorem quadraticTwoWindowDirichletSumBound_mul_denominator :
    quadraticTwoWindowDirichletSumBound * 34 = 1189 :=
  Dirichlet.Window.Block.quadraticTwoWindowSumBound_mul_denominator

/-- Improved finite-octant bound `224/71` for the sum of two successive
squared Dirichlet-window products. -/
def octantTwoWindowDirichletSumBound : Coordinate :=
  Dirichlet.Window.Block.octantTwoWindowSumBound

/-- Clearing the finite-octant two-window sum-bound denominator yields 224. -/
theorem octantTwoWindowDirichletSumBound_mul_denominator :
    octantTwoWindowDirichletSumBound * 71 = 224 :=
  Dirichlet.Window.Block.octantTwoWindowSumBound_mul_denominator

/-- Near-optimal dyadic bound `512/205` for the sum of two successive
squared Dirichlet-window products. -/
def dyadicTwoWindowDirichletSumBound : Coordinate :=
  Dirichlet.Window.Block.dyadicTwoWindowSumBound

/-- Clearing the dyadic two-window sum-bound denominator yields 512. -/
theorem dyadicTwoWindowDirichletSumBound_mul_denominator :
    dyadicTwoWindowDirichletSumBound * 205 = 512 :=
  Dirichlet.Window.Block.dyadicTwoWindowSumBound_mul_denominator

/-- The normalized determinant gap of consecutive best levels is at least
`1/12`. -/
theorem one_twelfth_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (1 / 12 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.Basic.AreConsecutiveBest.one_twelfth_le_normalizedDeterminantGap
    consecutive

/-- The three neighbouring coefficients in the finite octant containing the
normalized error ratio force a determinant gap of at least one half. -/
theorem half_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.half_le_normalizedDeterminantGap
    consecutive

/-- The exact finite chamber calculation with the norm-two leading
coefficient strengthens the normalized gap to the displayed rational
`71/112`. -/
theorem octantGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    octantNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
    consecutive

/-- The five-obstruction chamber forces every consecutive normalized gap
above the near-optimal dyadic base value `205/256`. -/
theorem dyadicGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    dyadicNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
    consecutive

/-- In determinant index two, the oriented centered chamber forces the
matching dyadic gap `205/128`. -/
theorem dyadicCenteredIndexTwoGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    dyadicCenteredIndexTwoNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- Exact root-free index-two gap family.  Every displayed rational `gap`
between `3/4` and the smaller quadratic boundary gives the lower bound
`2 * gap`, without constructing the boundary as a completed value. -/
theorem twice_gapThreshold_le_consecutiveNormalizedDeterminantGap_of_indexTwo
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    2 * gap ≤ consecutiveNormalizedDeterminantGap source lower upper := by
  exact
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold Dirichlet.Window.IndexOne.Optimal.gapPolynomial
        exact quadraticNonnegative⟩ consecutive indexTwo

/-- The explicit `12,5` weighted certificate sharpens the normalized gap to
the displayed rational `35/408`. -/
theorem refinedThreshold_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    refinedNormalizedDeterminantGapThreshold ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.Basic.AreConsecutiveBest.refinedGap_le_normalizedDeterminantGap
    consecutive

/-- The rational boundary certificate `102/1189` is a sharper lower bound
for the normalized determinant gap. -/
theorem quadraticThreshold_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    quadraticNormalizedDeterminantGapThreshold ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.Basic.AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    consecutive quadraticNormalizedDeterminantGapThreshold
      quadraticNormalizedDeterminantGapThreshold_lt_half
      quadraticNormalizedDeterminantGapThreshold_quadratic_nonnegative

/-- Root-free exact boundary for the normalized consecutive determinant gap:
it is at least one half, or it satisfies the displayed rational quadratic
inequality. -/
theorem consecutiveNormalizedDeterminantGap_boundary
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Coordinate) ≤
        consecutiveNormalizedDeterminantGap source lower upper ∨
      consecutiveNormalizedDeterminantGap source lower upper ^ 2 -
          3 * consecutiveNormalizedDeterminantGap source lower upper +
        1 / 4 < 0 :=
  Dirichlet.Window.Basic.AreConsecutiveBest.normalizedDeterminantGap_boundary
    consecutive

/-- Certify any displayed rational normalized-gap threshold below one half by
checking that its boundary polynomial is nonnegative. -/
theorem threshold_le_consecutiveNormalizedDeterminantGap_of_quadratic
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold ≤ consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.Basic.AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Direct division-free window bound furnished by any displayed rational
threshold passing the quadratic test. -/
theorem quadraticThreshold_mul_consecutiveDirichletWindow_le_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower upper ≤
      (coefficientIndexQuadrance lower upper : Coordinate) :=
  Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Universal division-free form of the quadratic-threshold window bound. -/
theorem quadraticThreshold_mul_consecutiveDirichletWindow_le_two
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_two
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- The exact window product times its normalized determinant gap equals the
coefficient-index quadrance. -/
theorem consecutiveDirichletWindow_mul_normalizedGap_eq_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper *
        consecutiveNormalizedDeterminantGap source lower upper =
      (coefficientIndexQuadrance lower upper : Coordinate) :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
    consecutive

/-- A consecutive squared Dirichlet-window product is at most twelve times
its coefficient-index quadrance. -/
theorem consecutiveBest_dirichletWindow_le_twelve_mul_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      12 * (coefficientIndexQuadrance lower upper : Coordinate) :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_twelve_mul_index
    consecutive

/-- Every consecutive squared Dirichlet-window product is at most `24`,
independently of the displayed source. -/
theorem consecutiveBest_dirichletWindow_le_twentyFour
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 24 :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyFour
    consecutive

/-- Every consecutive squared Dirichlet-window product is at most the
displayed rational `816/35`, independently of the source. -/
theorem consecutiveBest_dirichletWindow_le_refinedUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      refinedUniversalDirichletWindowBound :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedUniversalBound
    consecutive

/-- The quadratic-boundary certificate bounds a consecutive squared window
by `1189/102` times its coefficient-index quadrance. -/
theorem consecutiveBest_dirichletWindow_le_quadraticIndexFactor
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticIndexDirichletWindowFactor *
        (coefficientIndexQuadrance lower upper : Coordinate) :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
    consecutive

/-- In determinant index two, the centered coefficient coset forces the
normalized determinant gap to be at least `71/56`. -/
theorem centeredIndexTwoNormalizedDeterminantGap_le_consecutive
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    centeredIndexTwoNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- Compatibility form of the strengthened centered index-two gap. -/
theorem one_le_consecutiveNormalizedDeterminantGap_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (1 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.one_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- A determinant-index-two consecutive squared window is at most
`112/71`. -/
theorem consecutiveBest_dirichletWindow_le_centeredIndexTwoBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      centeredIndexTwoDirichletWindowBound :=

    AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
    consecutive indexTwo

/-- Compatibility form of the strengthened index-two window bound. -/
theorem consecutiveBest_dirichletWindow_le_two_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexTwo
    consecutive indexTwo

/-- A determinant-index-one consecutive squared window is at most `2`. -/
theorem consecutiveBest_dirichletWindow_le_two_of_indexOne
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne : coefficientIndexQuadrance lower upper = 1) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexOne
    consecutive indexOne

/-- A determinant-index-one consecutive squared window is at most the
displayed rational `112/71`. -/
theorem consecutiveBest_dirichletWindow_le_octantIndexOneBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper)
    (indexOne : coefficientIndexQuadrance lower upper = 1) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      octantIndexOneDirichletWindowBound :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
    consecutive indexOne

/-- Finite-octant source-independent squared-window bound `112/71`. -/
theorem consecutiveBest_dirichletWindow_le_octantUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      octantUniversalDirichletWindowBound :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
    consecutive

/-- Near-optimal dyadic source-independent squared-window bound `256/205`. -/
theorem consecutiveBest_dirichletWindow_le_dyadicUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      dyadicUniversalDirichletWindowBound :=
  Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
    consecutive

/-- Exact root-free universal Dirichlet-window family.  Every displayed
rational `gap` satisfying the three finite inequalities gives
`gap * window <= 1`; such cuts approach the optimal quadratic boundary from
inside the displayed rational arithmetic. -/
theorem gapThreshold_mul_consecutiveDirichletWindow_le_one
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    gap * consecutiveDirichletWindowQuadrance source lower upper ≤ 1 := by
  exact Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
    gap ⟨threeFourthsLe, gapLtOne, by
      unfold Dirichlet.Window.IndexOne.Optimal.gapPolynomial
      exact quadraticNonnegative⟩ consecutive

/-! ## Finite sharpness beyond every requested scale -/

/-- Executable Pell stage selected for a proposed sharper rational threshold
and a requested finite scale. -/
def sharpnessStage (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  Dirichlet.Critical.Sharpness.sharpnessStage threshold requestedScale

/-- Displayed rational source computed at the selected sharpness stage. -/
def sharpnessSource (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzFraction :=
  Dirichlet.Critical.Pair.criticalSource
    (sharpnessStage threshold requestedScale)

/-- Lower endpoint of the selected consecutive-best window. -/
def sharpnessLowerPair (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzConvergentPair :=
  Dirichlet.Critical.Pair.criticalLowerPair
    (sharpnessStage threshold requestedScale)

/-- Upper endpoint of the selected consecutive-best window. -/
def sharpnessUpperPair (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzConvergentPair :=
  Dirichlet.Critical.Pair.criticalUpperPair
    (sharpnessStage threshold requestedScale)

/-- Actual upper-pair denominator quadrance of the explicit critical window. -/
def sharpnessDenominatorScale
    (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  Best.Error.denominatorQuadrance
    (sharpnessUpperPair threshold requestedScale)

/-- Finite constructive sharpness of the rational-cut window theorem.  If a
displayed threshold is on the sharper side of the omitted quadratic boundary,
then beyond every requested finite scale the executable Pell construction
returns a displayed rational source and consecutive best pair for which that
threshold would make the universal window inequality false.  The source is
allowed to depend on the requested scale. -/
theorem sharperGapThreshold_has_counterexample
    (threshold : Coordinate)
    (threeFourthsLe : (3 / 4 : Coordinate) ≤ threshold)
    (thresholdLtOne : threshold < 1)
    (quadraticNegative : threshold ^ 2 - 12 * threshold + 9 < 0)
    (requestedScale : Nat) :
    requestedScale <
        sharpnessDenominatorScale threshold requestedScale ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (sharpnessSource threshold requestedScale).value
        (sharpnessLowerPair threshold requestedScale)
        (sharpnessUpperPair threshold requestedScale) ∧
      1 < threshold *
        consecutiveDirichletWindowQuadrance
          (sharpnessSource threshold requestedScale)
          (sharpnessLowerPair threshold requestedScale)
          (sharpnessUpperPair threshold requestedScale) := by
  have certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold := by
    exact ⟨threeFourthsLe, thresholdLtOne, by
      unfold Dirichlet.Critical.Sharpness.windowBoundaryPolynomial
      exact quadraticNegative⟩
  simpa only [sharpnessStage, sharpnessSource,
    sharpnessLowerPair, sharpnessUpperPair,
    sharpnessDenominatorScale, consecutiveDirichletWindowQuadrance] using
      Dirichlet.Critical.Sharpness.criticalWindowSharpness
        certificate requestedScale

/-- Public result type for an arbitrary finite same-source sharpness run and
one rational box on which every selected window remains valid. -/
abbrev RobustSharpnessRun
    (threshold : Coordinate) (requestedScale count : Nat) :=
  Dirichlet.Critical.Robust.Run.FullyRobustRun
    threshold requestedScale count

/-- Compute exactly the requested finite number of strictly scale-increasing
bad windows at one displayed source, together with one proper rational box
on which their consecutive-best and strict-violation certificates hold
uniformly. -/
def robustSharpnessRun
    {threshold : Coordinate}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    RobustSharpnessRun threshold requestedScale count :=
  Dirichlet.Critical.Robust.Run.criticalFullyRobustRun
    certificate requestedScale count

/-- Index-aware source-independent squared-window bound `1189/102`. -/
theorem consecutiveBest_dirichletWindow_le_indexAwareUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      indexAwareUniversalDirichletWindowBound :=
  Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
    consecutive

/-- Quadratic-gap-only source-independent squared-window bound `1189/51`. -/
theorem consecutiveBest_dirichletWindow_le_quadraticUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticUniversalDirichletWindowBound :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticUniversalBound
    consecutive

/-- The coefficient-index quadrances of two successive consecutive best
transitions have sum at most three. -/
theorem successiveBest_coefficientIndexQuadrance_add_le_three
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    coefficientIndexQuadrance lower middle +
        coefficientIndexQuadrance middle upper ≤ 3 :=
  Dirichlet.Window.Block.coefficientIndexQuadrance_add_le_three first second

/-- For every displayed rational threshold passing the quadratic test, one
of two successive windows satisfies the scaled index-one bound. -/
theorem quadraticThreshold_mul_one_successiveDirichletWindow_le_one
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower middle ≤ 1 ∨
      threshold * consecutiveDirichletWindowQuadrance source middle upper ≤ 1 :=
  Dirichlet.Window.Block.quadraticThreshold_mul_one_dirichletWindow_le_one
    first second threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Parameterized two-window certificate: every rational threshold passing
the quadratic test times the sum of two successive windows is at most three. -/
theorem quadraticThreshold_mul_successiveDirichletWindowSum_le_three
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold *
        (consecutiveDirichletWindowQuadrance source lower middle +
          consecutiveDirichletWindowQuadrance source middle upper) ≤ 3 :=
  Dirichlet.Window.Block.quadraticThreshold_mul_dirichletWindowSum_le_three
    first second threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Exact root-free two-window family: every displayed rational passing the
optimal quadratic test scales two successive windows by at most two. -/
theorem gapThreshold_mul_successiveDirichletWindowSum_le_two
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    gap * (consecutiveDirichletWindowQuadrance source lower middle +
      consecutiveDirichletWindowQuadrance source middle upper) ≤ 2 := by
  exact
    Dirichlet.Window.Block.gapThreshold_mul_dirichletWindowQuadrance_add_le_two
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold Dirichlet.Window.IndexOne.Optimal.gapPolynomial
        exact quadraticNonnegative⟩ first second

/-- Among two successive consecutive best transitions, at least one squared
window satisfies the index-one bound `408/35`. -/
theorem successiveBest_one_dirichletWindow_le_refinedIndexFactor
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle ≤
        refinedIndexDirichletWindowFactor ∨
      consecutiveDirichletWindowQuadrance source middle upper ≤
        refinedIndexDirichletWindowFactor :=
  Dirichlet.Window.Block.one_dirichletWindowQuadrance_le_refinedIndexFactor
    first second

/-- Two successive squared Dirichlet-window products have sum at most the
displayed rational `1224/35`. -/
theorem successiveBest_dirichletWindow_add_le_refinedTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      refinedTwoWindowDirichletSumBound :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_refinedTwoWindowSumBound
    first second

/-- Among two successive transitions, one squared window satisfies the
sharper index-one bound `1189/102`. -/
theorem successiveBest_one_dirichletWindow_le_quadraticIndexFactor
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle ≤
        quadraticIndexDirichletWindowFactor ∨
      consecutiveDirichletWindowQuadrance source middle upper ≤
        quadraticIndexDirichletWindowFactor :=
  Dirichlet.Window.Block.one_dirichletWindowQuadrance_le_quadraticIndexFactor
    first second

/-- Sharper two-window sum bound `1189/34`. -/
theorem successiveBest_dirichletWindow_add_le_quadraticTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      quadraticTwoWindowDirichletSumBound :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_quadraticTwoWindowSumBound
    first second

/-- Index-aware two-window sum bound `1189/51`. -/
theorem successiveBest_dirichletWindow_add_le_indexAwareTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      quadraticUniversalDirichletWindowBound :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_quadraticUniversalWindowBound
    first second

/-- Improved finite-octant two-window sum bound `224/71`. -/
theorem successiveBest_dirichletWindow_add_le_octantTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      octantTwoWindowDirichletSumBound :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_octantTwoWindowSumBound
    first second

/-- Near-optimal dyadic two-window sum bound `512/205`. -/
theorem successiveBest_dirichletWindow_add_le_dyadicTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      dyadicTwoWindowDirichletSumBound :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_dyadicTwoWindowSumBound
    first second

/-- Finite-octant two-window sum bound `4`. -/
theorem successiveBest_dirichletWindow_add_le_four
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤ 4 :=
  Dirichlet.Window.Block.dirichletWindowQuadrance_add_le_four first second

/-- Exact parity-sensitive form of the alternating index-two pattern along a
finite displayed chain. -/
theorem bestChain_two_mul_coefficientIndexQuadrances_sum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (consecutiveCoefficientIndexQuadrances pairs).sum ≤
      3 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 :=
  Dirichlet.Window.Chain.two_mul_coefficientIndexQuadrances_sum_le_with_parity
    pairs chain

/-- Parity-free consequence of the finite-chain index bound. -/
theorem bestChain_two_mul_coefficientIndexQuadrances_sum_le
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (consecutiveCoefficientIndexQuadrances pairs).sum ≤
      3 * (consecutiveCoefficientIndexQuadrances pairs).length + 1 :=
  Dirichlet.Window.Chain.two_mul_coefficientIndexQuadrances_sum_le pairs chain

/-- The quadratic threshold times the total exact window cost of a finite
displayed chain is at most its computed coefficient-index sum. -/
theorem bestChain_quadraticThreshold_mul_windowSum_le_indexSum
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      ((consecutiveCoefficientIndexQuadrances pairs).sum : Coordinate) :=
  Dirichlet.Window.Chain.quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Uniform division-free finite-chain certificate obtained by combining the
quadratic threshold with exclusion of successive index two. -/
theorem bestChain_two_mul_quadraticThreshold_mul_windowSum_le
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold *
        (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (3 * (consecutiveCoefficientIndexQuadrances pairs).length + 1 : Nat) :=
  Dirichlet.Window.Chain.two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Exact parity-sensitive finite-chain window certificate. -/
theorem bestChain_two_mul_quadraticThreshold_mul_windowSum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold *
        (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  Dirichlet.Window.Chain.two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_with_parity
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Concrete sharp finite-chain bound obtained from the certified threshold
`35/408` and its exact reciprocal factor `408/35`. -/
theorem bestChain_two_mul_windowSum_le_refinedIndexFactor_mul_parityBound
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      refinedIndexDirichletWindowFactor *
        (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
          (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  Dirichlet.Window.Chain.two_mul_dirichletWindowQuadrances_sum_le_refinedIndexFactor_mul_parityBound
    pairs chain

/-- Sharper concrete finite-chain bound obtained from threshold `102/1189`
and reciprocal factor `1189/102`. -/
theorem bestChain_two_mul_windowSum_le_quadraticIndexFactor_mul_parityBound
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      quadraticIndexDirichletWindowFactor *
        (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
          (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  Dirichlet.Window.Chain.two_mul_dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_parityBound
    pairs chain

/-- Direct accumulated index-aware bound: each transition in the supplied
finite chain contributes at most `1189/102`. -/
theorem bestChain_windowSum_le_indexAwareUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      indexAwareUniversalDirichletWindowBound *
        ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
    pairs chain

/-- Direct accumulated finite-octant bound: each transition contributes at
most the universal rational `112/71`. -/
theorem bestChain_windowSum_le_octantUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      octantUniversalDirichletWindowBound *
        ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
    pairs chain

/-- The near-optimal dyadic bound accumulates along every supplied finite
chain of consecutive best pairs. -/
theorem bestChain_windowSum_le_dyadicUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (Dirichlet.Window.Chain.dirichletWindowQuadrances
        source.value pairs).sum ≤
      dyadicUniversalDirichletWindowBound *
        ((Dirichlet.Window.Chain.coefficientIndexQuadrances pairs).length :
          Coordinate) :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
    pairs chain

/-- Exact root-free finite-chain family: the displayed gap times the window
sum is at most the number of supplied transitions. -/
theorem gapThreshold_mul_bestChain_windowSum_le_length
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    gap * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) := by
  exact
    Dirichlet.Window.Chain.gapThreshold_mul_dirichletWindowQuadrances_sum_le_length
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold Dirichlet.Window.IndexOne.Optimal.gapPolynomial
        exact quadraticNonnegative⟩ pairs chain

/-- Compatibility theorem for the earlier `28/15` finite-octant chain bound:
clearing its denominator gives `28n` for `n` transitions. -/
theorem bestChain_fifteen_mul_windowSum_le_twentyEight_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    15 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (28 * (consecutiveCoefficientIndexQuadrances pairs).length : Nat) :=
  Dirichlet.Window.Chain.fifteen_mul_dirichletWindowQuadrances_sum_le_twentyEight_mul_length
    pairs chain

/-- Compatibility with the earlier parity-sensitive finite-octant bound. -/
theorem bestChain_fifteen_mul_windowSum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    15 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (29 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  Dirichlet.Window.Chain.fifteen_mul_dirichletWindowQuadrances_sum_le_with_parity
    pairs chain

/-- Direct finite-octant chain bound: each transition contributes at most
two. -/
theorem bestChain_windowSum_le_two_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      2 * ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  Dirichlet.Window.Chain.dirichletWindowQuadrances_sum_le_two_mul_length
    pairs chain

/-- A successor returned by the executable selector supplies the approximation
for every natural quadrance request between the two endpoint levels. -/
theorem mem_consecutiveBestSuccessors_witnesses_dirichletWindow
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower)
    (request : Nat)
    (aboveLower :
      Best.Error.denominatorQuadrance lower < request)
    (noHigherThanUpper :
      request ≤ Best.Error.denominatorQuadrance upper) :
    lower.denominator ≠ 0 ∧
      Best.Error.denominatorQuadrance lower < request ∧
      (request : Coordinate) *
          Best.Error.errorQuadrance source.value lower ≤
        consecutiveDirichletWindowQuadrance source lower upper := by
  have consecutive :=
    (mem_consecutiveBestSuccessors_iff source lower upper).mp member
  exact (Dirichlet.Window.SourceBound.AreConsecutiveBest.lower_witnesses_dirichletWindow consecutive) request aboveLower
    noHigherThanUpper

/-- The displayed source denominator bounds every consecutive Dirichlet
window product. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_sourceBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      (Data.GaussianInt.normNat
        source.denominator : Coordinate) / 2 :=
  ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)
    |> Dirichlet.Window.SourceBound.AreConsecutiveBest.dirichletWindowQuadrance_le_sourceBound

/-- Every successor returned by the executable selector has squared
Dirichlet-window product at most `24`, independently of the source. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_twentyFour
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 24 :=
  consecutiveBest_dirichletWindow_le_twentyFour source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
refined source-independent squared-window bound `816/35`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_refinedUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      refinedUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_refinedUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the sharper
source-independent squared-window bound `1189/51`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_quadraticUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_quadraticUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
index-aware source-independent squared-window bound `1189/102`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_indexAwareUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      indexAwareUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_indexAwareUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the exact
finite-octant source-independent squared-window bound `112/71`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_octantUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      octantUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_octantUniversalBound
    source lower upper
      ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
near-optimal dyadic source-independent squared-window bound `256/205`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_dyadicUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      dyadicUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_dyadicUniversalBound
    source lower upper
      ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-! ## Explicit RFAP-II calculation envelopes -/

/-- Execute addition through canonical gcd-reduced coordinate records. -/
def normalizedCoordinateAdd (left right : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedAdd left right

/-- Normalized coordinate addition agrees with rational addition. -/
theorem normalizedCoordinateAdd_eq (left right : Coordinate) :
    normalizedCoordinateAdd left right = left + right :=
  Fraction.Arithmetic.normalizedAdd_eq left right

/-- Execute multiplication with cross-cancellation and a final canonical
gcd reduction. -/
def normalizedCoordinateMul (left right : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedMul left right

/-- Normalized coordinate multiplication agrees with rational multiplication. -/
theorem normalizedCoordinateMul_eq (left right : Coordinate) :
    normalizedCoordinateMul left right = left * right :=
  Fraction.Arithmetic.normalizedMul_eq left right

/-- Negate a coordinate through its normalized rational record. -/
def normalizedCoordinateNeg (source : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedNeg source

/-- Normalized coordinate negation agrees with rational negation. -/
theorem normalizedCoordinateNeg_eq (source : Coordinate) :
    normalizedCoordinateNeg source = -source :=
  Fraction.Arithmetic.normalizedNeg_eq source

/-- Subtract two coordinates through normalized rational records. -/
def normalizedCoordinateSub (left right : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedSub left right

/-- Normalized coordinate subtraction agrees with rational subtraction. -/
theorem normalizedCoordinateSub_eq (left right : Coordinate) :
    normalizedCoordinateSub left right = left - right :=
  Fraction.Arithmetic.normalizedSub_eq left right

/-- Invert a coordinate through its normalized rational record. -/
def normalizedCoordinateInv (source : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedInv source

/-- Normalized coordinate inversion agrees with the rational inverse. -/
theorem normalizedCoordinateInv_eq (source : Coordinate) :
    normalizedCoordinateInv source = source⁻¹ :=
  Fraction.Arithmetic.normalizedInv_eq source

/-- Divide two coordinates through normalized rational records. -/
def normalizedCoordinateDiv (left right : Coordinate) : Coordinate :=
  Fraction.Arithmetic.normalizedDiv left right

/-- Normalized coordinate division agrees with rational division. -/
theorem normalizedCoordinateDiv_eq (left right : Coordinate) :
    normalizedCoordinateDiv left right = left / right :=
  Fraction.Arithmetic.normalizedDiv_eq left right

/-- Bit width of the canonical numerator/denominator record for a coordinate. -/
def rationalRecordWidth (value : Coordinate) : Nat :=
  Fraction.Resource.Width.rationalRecordWidth value

/-- Source-only bit budget for normalized coordinate addition. -/
def normalizedAddBitBudget (left right : Coordinate) : Nat :=
  Fraction.Resource.Width.normalizedAddBitBudget left right

/-- The canonical record width after addition is bounded by the source-only addition budget. -/
theorem normalizedCoordinateAdd_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateAdd left right) ≤
      normalizedAddBitBudget left right :=
  Fraction.Resource.Width.normalizedAdd_width_le_budget left right

/-- Source-only bit budget for normalized coordinate multiplication. -/
def normalizedMulBitBudget (left right : Coordinate) : Nat :=
  Fraction.Resource.Width.normalizedMulBitBudget left right

/-- The canonical record width after multiplication is bounded by the source-only multiplication budget. -/
theorem normalizedCoordinateMul_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateMul left right) ≤
      normalizedMulBitBudget left right :=
  Fraction.Resource.Width.normalizedMul_width_le_budget left right

/-- The source-only bit budget for normalized coordinate subtraction. -/
def normalizedSubBitBudget (left right : Coordinate) : Nat :=
  Fraction.Resource.Width.normalizedSubBitBudget left right

/-- The canonical record width after subtraction is bounded by the source-only subtraction budget. -/
theorem normalizedCoordinateSub_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateSub left right) ≤
      normalizedSubBitBudget left right :=
  Fraction.Resource.Width.normalizedSub_width_le_budget left right

/-- The source-only bit budget for normalized coordinate division. -/
def normalizedDivBitBudget (left right : Coordinate) : Nat :=
  Fraction.Resource.Width.normalizedDivBitBudget left right

/-- The canonical record width after division is bounded by the source-only division budget. -/
theorem normalizedCoordinateDiv_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateDiv left right) ≤
      normalizedDivBitBudget left right :=
  Fraction.Resource.Width.normalizedDiv_width_le_budget left right

/-- Execute polynomial evaluation through normalized Gaussian working
records and erase the result. -/
def normalizedPolynomialEvaluation (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.Canonical :=
  Data.Gaussian.Basic.value
    (Dense.Basic.DensePolynomial.eval polynomial point)

/-- Erasing normalized Gaussian polynomial evaluation gives the polynomial's original evaluation. -/
theorem normalizedPolynomialEvaluation_eq (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) :
    normalizedPolynomialEvaluation polynomial point = polynomial.eval point :=
  Dense.Gaussian.Evaluation.Horner.value_eval polynomial point

/-- The source-only component-bit budget for normalized Gaussian polynomial evaluation. -/
def normalizedEvaluationBitBudget (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) : Nat :=
  Dense.Gaussian.Evaluation.Resource.normalizedEvaluationBitBudget polynomial point

/-- The source-only operation-step budget for normalized Gaussian polynomial evaluation. -/
def normalizedEvaluationStepBudget (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) : Nat :=
  Dense.Gaussian.Evaluation.Resource.normalizedEvaluationStepBudget polynomial point

/-- The normalized evaluation trace uses no more steps than its computed budget. -/
theorem normalizedEvaluation_steps_le_budget
    (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.Trace.steps point polynomial.coeffs ≤
      normalizedEvaluationStepBudget polynomial point :=
  Dense.Gaussian.Evaluation.Resource.normalizedEvaluation_steps_le_budget polynomial point

/-- Normalized polynomial and derivative evaluation followed by the Newton
division and subtraction. -/
def normalizedNewtonCenter (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) : WorkingGaussian :=
  Dense.Gaussian.Newton.Basic.newtonCenter polynomial point

/-- Erasing the normalized Newton center gives the original Newton quotient-and-subtraction expression. -/
theorem normalizedNewtonCenter_eq (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.value (normalizedNewtonCenter polynomial point) =
      point - polynomial.eval point /
        (Dense.Derivative.derivative polynomial).eval point :=
  Dense.Gaussian.Newton.Basic.value_newtonCenter polynomial point

/-- The source-only component-bit budget for normalized Newton arithmetic. -/
def normalizedNewtonBitBudget (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) : Nat :=
  Dense.Gaussian.Newton.Resource.normalizedNewtonBitBudget polynomial point

/-- The source-only operation-step budget for normalized Newton arithmetic. -/
def normalizedNewtonStepBudget (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) : Nat :=
  Dense.Gaussian.Newton.Resource.normalizedNewtonStepBudget polynomial point

/-- The normalized Newton working record fits its computed component-bit budget. -/
theorem normalizedNewtonCenter_width_le_budget
    (polynomial : GaussianPolynomial)
    (point : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Resource.workingGaussianWidth
        (normalizedNewtonCenter polynomial point) ≤
      normalizedNewtonBitBudget polynomial point :=
  Dense.Gaussian.Newton.Resource.normalizedNewtonCenter_width_le_budget polynomial point

/-- Component-bit budget for the numerator and denominator of the nearest
grid record returned from a displayed centre and radius. -/
def gridRecordBitBudget
    (center : Data.Gaussian.Basic.Canonical) (radius : Coordinate) : Nat :=
  Approximation.Gaussian.Grid.Resource.gridRecordBitBudget center radius

/-- The common-denominator grid fraction fits the bit budget computed from its center and radius. -/
theorem gridFraction_width_le_budget
    (center : Data.Gaussian.Basic.Canonical) (radius : Coordinate) :
    Data.Gaussian.Fraction.NaturalDenominator.Resource.commonFractionWidth
        (Approximation.Gaussian.Grid.Basic.gridFraction center radius) ≤
      gridRecordBitBudget center radius :=
  Approximation.Gaussian.Grid.Resource.gridFraction_width_le_budget center radius

/-- Natural quadrance recurrence bounding every intermediate suffix value of
homogeneous Gaussian-integer evaluation. -/
def homogeneousWorkingEnvelope (numerator denominator : GaussianInt)
    (coefficients : List GaussianInt) : Nat :=
  Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousWorkingEnvelope numerator denominator
    coefficients

/-- The homogeneous Gaussian-integer evaluation has norm bounded by the retained working envelope. -/
theorem homogeneousEvaluation_norm_le_envelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    Data.GaussianInt.normNat
        (Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval numerator denominator
          coefficients) ≤
      homogeneousWorkingEnvelope numerator denominator coefficients :=
  (Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource.homogeneousEval_norm_le_envelope
    numerator denominator coefficients).trans (by
      cases coefficients with
      | nil => rfl
      | cons coefficient remaining => exact Data.Nat.Order.le_max_left _ _)

/-- Binary-width bound on the number of clauses in the terminating Hurwitz
encoder. -/
def hurwitzStepBudget (fraction : HurwitzFraction) : Nat :=
  Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzStepBudget fraction

/-- The finite Hurwitz encoding length is bounded by its source-computed step budget. -/
theorem hurwitzEncoding_length_le_budget (fraction : HurwitzFraction) :
    (Data.ComplexContinuedFraction.Hurwitz.Encoding.encode fraction).length ≤
      hurwitzStepBudget fraction :=
  Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitz_length_le_stepBudget fraction

/-- Source-only quadrance budget for both members of the encoded continuant. -/
def hurwitzContinuantNormBudget (fraction : HurwitzFraction) : Nat :=
  Data.ComplexContinuedFraction.Hurwitz.Resource.hurwitzContinuantNormBudget fraction

/-- Both numerator and denominator of the encoded continuant satisfy the source-only norm budget. -/
theorem hurwitzContinuant_norm_le_budget (fraction : HurwitzFraction) :
    Data.GaussianInt.normNat
          (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
            (Data.ComplexContinuedFraction.Hurwitz.Encoding.encode fraction)).numerator ≤
        hurwitzContinuantNormBudget fraction ∧
      Data.GaussianInt.normNat
          (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
            (Data.ComplexContinuedFraction.Hurwitz.Encoding.encode fraction)).denominator ≤
        hurwitzContinuantNormBudget fraction :=
  Data.ComplexContinuedFraction.Hurwitz.Resource.encodedContinuant_norm_le_budget fraction

/-- Aggregate accounted-operation budget for the normalized Newton and
RFAP-II post-processing calculations. -/
def stageTwoStepBudget (input : StageTwoInput) : Nat :=
  Approximation.Resource.Certificate.stageTwoStepBudget input

/-- Aggregate component-bit budget for the same calculation family. -/
def stageTwoBitBudget (input : StageTwoInput) : Nat :=
  Approximation.Resource.Certificate.stageTwoBitBudget input

/-- A single constructive certificate for all normalized-Horner, Newton,
grid, homogeneous-evaluation, Hurwitz, and target-scan bounds named by the
RFAP-II resource interface. -/
theorem stageTwoResourceCertificate (input : StageTwoInput) :
    Approximation.Resource.Certificate.StageTwoResourcesWithin input
      (stageTwoStepBudget input) (stageTwoBitBudget input) :=
  Approximation.Resource.Certificate.stageTwo_resource_certificate input

end Purelib.Papers.RFAP.Approximation
