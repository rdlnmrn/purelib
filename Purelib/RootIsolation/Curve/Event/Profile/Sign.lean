module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Interval.Proper
import Purelib.Data.Rat.List.Minimum
public import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Residual
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Request
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.BoundaryFactorization (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Rational.Factorization (ConditionRelation)
open Purelib.RootIsolation.CCL.Boundary.Charts
  (SourcePersistentConditionProfilesProfileAnalysisAlias
   SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (ProfileEventLeaf)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile

open Purelib.Algebra
namespace Basic.ProfileEventLeaf

/-! ## Quantitative separation from an apart box edge -/

/-- Coefficient of the squarefree-factor contribution in one finite Bezout
identity. -/
@[expose] def apartResidualCoefficient
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Fraction.Rational :=
  2 * Dense.Rational.Bounds.Horner.evalSqBound apart.left
      chart.cell.interval * ProfileEventLeaf.factorResidualCoefficient analysis

/-- The original Bézout factor-term residual coefficient is nonnegative. -/
theorem apartResidualCoefficient_nonneg
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 ≤ apartResidualCoefficient analysis condition apart :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.left
        chart.cell.interval))
    (ProfileEventLeaf.factorResidualCoefficient_nonneg analysis)

/-- First width: the factor term in the Bezout identity is below `1/2`. -/
@[expose] def apartResidualWidth
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth
    (apartResidualCoefficient analysis condition apart) (1 / 2)

/-- The original coefficient-computed width making the factor contribution smaller than one half is positive. -/
theorem apartResidualWidth_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartResidualWidth analysis condition apart :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    (apartResidualCoefficient_nonneg analysis condition apart) (by decide)

/-- Uniform positive quadrance lower target for the apart condition value. -/
@[expose] def apartConditionLower
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Fraction.Rational :=
  (1 / 2) / (2 *
    (Dense.Rational.Bounds.Horner.evalSqBound apart.right
      chart.cell.interval + 1))

/-- The original Bézout and Horner data supply a positive squared-value lower target for the apart condition. -/
theorem apartConditionLower_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartConditionLower analysis condition apart :=
  Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.right
          chart.cell.interval) (by decide)))

/-- Final width: additionally make condition variation smaller than its
Bezout lower bound. -/
@[expose] def apartSignWidth
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Fraction.Rational :=
  min (apartResidualWidth analysis condition apart)
    (Data.Rat.SmallWidth.shrinkingWidth
      (Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
        chart.cell.interval)
      (apartConditionLower analysis condition apart))

/-- The original joint residual and variation width for an apart condition is positive. -/
theorem apartSignWidth_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartSignWidth analysis condition apart :=
  Fraction.Order.Basic.lt_min (apartResidualWidth_pos analysis condition
    apart)
    (Data.Rat.SmallWidth.shrinkingWidth_pos
      (by
        exact (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
          condition chart.cell.interval).2)
      (apartConditionLower_pos analysis condition apart))

/-- At any positive width no larger than the apart-sign width, the factor
term in the Bezout identity is strictly below `1/2` everywhere in the
requested event. -/
theorem apart_left_contribution_lt_half_of_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    2 * (apart.left.eval parameter *
      analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 := by
  let width := epsilon
  let residualWidth := apartResidualWidth analysis condition apart
  let coefficient := apartResidualCoefficient analysis condition apart
  let leftBound := Dense.Rational.Bounds.Horner.evalSqBound apart.left
    chart.cell.interval
  let residualCoefficient := ProfileEventLeaf.factorResidualCoefficient analysis
  have widthPositive : 0 < width := positive
  have residualWidthPositive : 0 < residualWidth :=
    apartResidualWidth_pos analysis condition apart
  have widthLe : width ≤ residualWidth :=
    epsilonLe.trans (Fraction.Order.Basic.min_le_left _ _)
  have widthSqLe : width ^ 2 ≤ residualWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct widthPositive.le widthLe 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [-eq_self, -iff_self, coefficient] using
      apartResidualCoefficient_nonneg analysis condition apart
  have coefficientWidthLe : coefficient * width ^ 2 ≤
      coefficient * residualWidth ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSqLe
      coefficientNonnegative
  have coefficientResidualSmall : coefficient * residualWidth ^ 2 <
      (1 / 2 : Fraction.Rational) := by
    simpa only [-eq_self, -iff_self, residualWidth, coefficient,
      apartResidualWidth] using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative (show (0 : Fraction.Rational) < 1 / 2 by decide)
  have refinesChart := leaf.request_refines_chart width
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have leftEvalBound : apart.left.eval parameter ^ 2 ≤ leftBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound apart.left
      chart.cell.interval parameterInsideChart
  have factorBound : analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      residualCoefficient * width ^ 2 := by
    simpa only [-eq_self, -iff_self, width, residualCoefficient] using
      leaf.factor_eval_sq_request_le width widthPositive parameter inside
  have productBound : apart.left.eval parameter ^ 2 *
        analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      leftBound * (residualCoefficient * width ^ 2) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct leftEvalBound factorBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (analysis.profile.factor.polynomial.eval parameter))
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.left
        chart.cell.interval)
  calc
    2 * (apart.left.eval parameter *
        analysis.profile.factor.polynomial.eval parameter) ^ 2 =
        2 * (apart.left.eval parameter ^ 2 *
          analysis.profile.factor.polynomial.eval parameter ^ 2) := by
      rw [Semiring.Normalization.product_pow]
    _ ≤ 2 * (leftBound * (residualCoefficient * width ^ 2)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ = coefficient * width ^ 2 := by
      dsimp only [coefficient, apartResidualCoefficient, leftBound,
        residualCoefficient]
      ring1
    _ ≤ coefficient * residualWidth ^ 2 := coefficientWidthLe
    _ < 1 / 2 := coefficientResidualSmall

/-- Specialization at the computed apart-sign width. -/
theorem apart_left_contribution_lt_half
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (parameter : Fraction.Rational)
    (inside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        parameter) :
    2 * (apart.left.eval parameter *
      analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 :=
  leaf.apart_left_contribution_lt_half_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl parameter inside

/-- The apart condition itself is uniformly separated from zero throughout
every request no wider than its computed apart-sign width. -/
theorem apartConditionLower_lt_eval_sq_of_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 := by
  let width := epsilon
  let factorValue := analysis.profile.factor.polynomial.eval parameter
  let conditionValue := condition.eval parameter
  let leftValue := apart.left.eval parameter
  let rightValue := apart.right.eval parameter
  let rightBound := Dense.Rational.Bounds.Horner.evalSqBound apart.right
    chart.cell.interval
  let denominator := 2 * (rightBound + 1)
  have leftSmall : 2 * (leftValue * factorValue) ^ 2 < 1 / 2 := by
    simpa only [-eq_self, -iff_self, width, factorValue, leftValue] using
      leaf.apart_left_contribution_lt_half_of_le condition apart epsilon
        positive epsilonLe parameter inside
  have identity : 1 = leftValue * factorValue +
      rightValue * conditionValue := by
    simpa only [-eq_self, -iff_self, leftValue, factorValue, rightValue, conditionValue] using
      apart.identity parameter
  have totalLower : (1 : Fraction.Rational) ≤
      2 * (leftValue * factorValue) ^ 2 +
        2 * (rightValue * conditionValue) ^ 2 := by
    calc
      (1 : Fraction.Rational) =
          (leftValue * factorValue + rightValue * conditionValue) ^ 2 := by
        rw [← identity]
        decide
      _ ≤ 2 * ((leftValue * factorValue) ^ 2 +
          (rightValue * conditionValue) ^ 2) :=
        Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
      _ = 2 * (leftValue * factorValue) ^ 2 +
          2 * (rightValue * conditionValue) ^ 2 := by ring1
  have rightStrict : (1 / 2 : Fraction.Rational) <
      2 * (rightValue * conditionValue) ^ 2 := by
    by_contra notStrict
    have rightLe : 2 * (rightValue * conditionValue) ^ 2 ≤ 1 / 2 :=
      le_of_not_gt notStrict
    have firstStep := Fraction.Order.Arithmetic.add_lt_add_right_direct
      leftSmall (2 * (rightValue * conditionValue) ^ 2)
    have secondStep := Fraction.Order.Arithmetic.add_le_add_right_direct
      rightLe (1 / 2 : Fraction.Rational)
    have sumStrict :
        2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 < 1 := by
      calc
        2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 <
            1 / 2 + 2 * (rightValue * conditionValue) ^ 2 := firstStep
        _ ≤ 1 / 2 + 1 / 2 := by
          simpa only [-eq_self, -iff_self, Fraction.Field.add_comm] using secondStep
        _ = 1 := by decide
    exact (not_lt_of_ge totalLower) sumStrict
  have refinesChart := leaf.request_refines_chart width
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have rightEvalBound : rightValue ^ 2 ≤ rightBound := by
    simpa only [-eq_self, -iff_self, rightValue, rightBound] using
      Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound apart.right
        chart.cell.interval parameterInsideChart
  have rightBoundLe : rightBound ≤ rightBound + 1 := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      (show (0 : Fraction.Rational) ≤ 1 by decide) rightBound
    simpa only [-eq_self, -iff_self, zero_add, Fraction.Field.add_comm] using shifted
  have conditionSquareNonnegative : 0 ≤ conditionValue ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct conditionValue
  have rightProductUpper :
      2 * (rightValue * conditionValue) ^ 2 ≤
        denominator * conditionValue ^ 2 := by
    rw [Semiring.Normalization.product_pow]
    have valueBound : rightValue ^ 2 * conditionValue ^ 2 ≤
        (rightBound + 1) * conditionValue ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (rightEvalBound.trans rightBoundLe) conditionSquareNonnegative
    calc
      2 * (rightValue ^ 2 * conditionValue ^ 2) ≤
          2 * ((rightBound + 1) * conditionValue ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct valueBound
          (by decide)
      _ = denominator * conditionValue ^ 2 := by
        dsimp only [denominator]
        ring1
  have denominatorPositive : 0 < denominator :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.right
          chart.cell.interval) (by decide))
  apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
  calc
    (1 / 2 : Fraction.Rational) <
        2 * (rightValue * conditionValue) ^ 2 := rightStrict
    _ ≤ denominator * conditionValue ^ 2 := rightProductUpper
    _ = conditionValue ^ 2 * denominator :=
      Fraction.Field.mul_comm _ _

/-- Specialization at the computed apart-sign width. -/
theorem apartConditionLower_lt_eval_sq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (parameter : Fraction.Rational)
    (inside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 :=
  leaf.apartConditionLower_lt_eval_sq_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl parameter inside

/-- At any positive width no larger than the apart-sign width, the variation
of the apart condition between any two event parameters is smaller than its
uniform quadrance lower bound. -/
theorem condition_eval_sub_sq_lt_lower_of_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    {left right : Fraction.Rational}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart := by
  let width := epsilon
  let requested := leaf.request width
  let chartLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
      chart.cell.interval
  let variationWidth :=
    Data.Rat.SmallWidth.shrinkingWidth
      chartLipschitz (apartConditionLower analysis condition apart)
  have widthPositive : 0 < width := positive
  have variationWidthPositive : 0 < variationWidth :=
    Data.Rat.SmallWidth.shrinkingWidth_pos
      (by
        simpa only [-eq_self, -iff_self, chartLipschitz] using
          (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
            condition chart.cell.interval).2)
      (apartConditionLower_pos analysis condition apart)
  have widthLeVariation : width ≤ variationWidth :=
    epsilonLe.trans (Fraction.Order.Basic.min_le_right _ _)
  have widthSqLeVariation : width ^ 2 ≤ variationWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct widthPositive.le
      widthLeVariation 2
  have chartLipschitzNonnegative : 0 ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
        condition chart.cell.interval).2
  have variationSmall : chartLipschitz * variationWidth ^ 2 <
      apartConditionLower analysis condition apart := by
    simpa only [-eq_self, -iff_self, variationWidth] using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        chartLipschitzNonnegative
        (apartConditionLower_pos analysis condition apart)
  have localVariation := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le
    condition requested.cell.interval leftInside rightInside
  have localLeChart :
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
          requested.cell.interval ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz, requested] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        condition (leaf.request_refines_chart width)
  have parameterDistance : (left - right) ^ 2 ≤
      (Bounds.width requested.cell.interval) ^ 2 :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have requestedWidth : (Bounds.width requested.cell.interval) ≤ width :=
    leaf.request_width_le width widthPositive
  have requestedWidthSq : (Bounds.width requested.cell.interval) ^ 2 ≤ width ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Bounds.width_nonneg requested.cell.interval) requestedWidth 2
  have distanceLeVariation : (left - right) ^ 2 ≤ variationWidth ^ 2 :=
    parameterDistance.trans (requestedWidthSq.trans widthSqLeVariation)
  have localNonnegative :
      0 ≤ Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
        requested.cell.interval :=
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg condition
      requested.cell.interval).2
  exact localVariation.trans_lt
    ((Fraction.Order.Arithmetic.mul_le_mul_direct localLeChart
      distanceLeVariation
      (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right))
      chartLipschitzNonnegative).trans_lt variationSmall)

/-- Specialization at the computed apart-sign width. -/
theorem condition_eval_sub_sq_lt_lower
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    {left right : Fraction.Rational}
    (leftInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        right) :
    (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart :=
  leaf.condition_eval_sub_sq_lt_lower_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl
        leftInside rightInside

/-- Every two values of an apart condition on any sufficiently narrow
requested event have positive product, hence one stable strict sign. -/
theorem condition_eval_mul_pos_of_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    {left right : Fraction.Rational}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right := by
  have variation := leaf.condition_eval_sub_sq_lt_lower_of_le condition apart
    epsilon positive epsilonLe leftInside rightInside
  have rightLower := leaf.apartConditionLower_lt_eval_sq_of_le condition apart
    epsilon positive epsilonLe right rightInside
  have differenceSmall :
      (condition.eval left - condition.eval right) ^ 2 <
        condition.eval right ^ 2 := variation.trans rightLower
  rcases lt_or_ge (0 : Fraction.Rational)
      (condition.eval left * condition.eval right) with positive | nonpositive
  · exact positive
  · have squareOrder := Purelib.Data.Rat.Bounds.Square.right_sq_le_sub_sq_of_mul_nonpos nonpositive
    exact (not_lt_of_ge squareOrder differenceSmall).elim

/-- Specialization at the computed apart-sign width. -/
theorem condition_eval_mul_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    {left right : Fraction.Rational}
    (leftInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        right) :
    0 < condition.eval left * condition.eval right :=
  leaf.condition_eval_mul_pos_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl
        leftInside rightInside

/-- Uniform separation and stable sign of an apart condition on any
explicitly bounded rational cell.  This is the request-path-independent form
used by complete finite refinement families: callers provide chart
containment, the requested width bound, and the already established
profile-factor residual. -/
theorem apartConditionControl_on_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (cell : Cell)
    (condition : CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : (Bounds.width cell.interval) ≤ epsilon)
    (factorBound : ∀ parameter : Fraction.Rational,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        ProfileEventLeaf.factorResidualCoefficient analysis * epsilon ^ 2)
    {left right : Fraction.Rational}
    (leftInside : cell.interval.Contains left)
    (rightInside : cell.interval.Contains right) :
    (∀ parameter : Fraction.Rational, cell.interval.Contains parameter →
      apartConditionLower analysis condition apart <
        condition.eval parameter ^ 2) ∧
      0 < condition.eval left * condition.eval right := by
  let residualWidth := apartResidualWidth analysis condition apart
  let residualCoefficient := ProfileEventLeaf.factorResidualCoefficient analysis
  let apartCoefficient := apartResidualCoefficient analysis condition apart
  let leftBound := Dense.Rational.Bounds.Horner.evalSqBound apart.left
    chart.cell.interval
  have widthLeResidual : epsilon ≤ residualWidth :=
    epsilonLe.trans (Fraction.Order.Basic.min_le_left _ _)
  have widthSqLeResidual : epsilon ^ 2 ≤ residualWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct positive.le
      widthLeResidual 2
  have apartCoefficientNonnegative : 0 ≤ apartCoefficient := by
    simpa only [-eq_self, -iff_self, apartCoefficient] using
      apartResidualCoefficient_nonneg analysis condition apart
  have apartCoefficientWidthLe :
      apartCoefficient * epsilon ^ 2 ≤
        apartCoefficient * residualWidth ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      widthSqLeResidual apartCoefficientNonnegative
  have apartCoefficientResidualSmall :
      apartCoefficient * residualWidth ^ 2 < (1 / 2 : Fraction.Rational) := by
    simpa only [-eq_self, -iff_self, apartCoefficient, residualWidth,
      apartResidualWidth] using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        apartCoefficientNonnegative (show (0 : Fraction.Rational) < 1 / 2 by decide)
  have factorContributionSmall : ∀ parameter : Fraction.Rational,
      cell.interval.Contains parameter →
      2 * (apart.left.eval parameter *
        analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 := by
    intro parameter parameterInside
    have parameterInsideChart : chart.cell.interval.Contains parameter :=
      ⟨refinesChart.1.trans parameterInside.1,
        parameterInside.2.trans refinesChart.2⟩
    have leftEvalBound : apart.left.eval parameter ^ 2 ≤ leftBound :=
      Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound apart.left
        chart.cell.interval parameterInsideChart
    have profileBound := factorBound parameter parameterInside
    have productBound : apart.left.eval parameter ^ 2 *
          analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        leftBound * (residualCoefficient * epsilon ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct leftEvalBound profileBound
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (analysis.profile.factor.polynomial.eval parameter))
        (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.left
          chart.cell.interval)
    calc
      2 * (apart.left.eval parameter *
          analysis.profile.factor.polynomial.eval parameter) ^ 2 =
          2 * (apart.left.eval parameter ^ 2 *
            analysis.profile.factor.polynomial.eval parameter ^ 2) := by
        rw [Semiring.Normalization.product_pow]
      _ ≤ 2 * (leftBound * (residualCoefficient * epsilon ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
          (by decide)
      _ = apartCoefficient * epsilon ^ 2 := by
        dsimp only [apartCoefficient, apartResidualCoefficient, leftBound,
          residualCoefficient]
        ring1
      _ ≤ apartCoefficient * residualWidth ^ 2 := apartCoefficientWidthLe
      _ < 1 / 2 := apartCoefficientResidualSmall
  have conditionLowerAt : ∀ parameter : Fraction.Rational,
      cell.interval.Contains parameter →
      apartConditionLower analysis condition apart <
        condition.eval parameter ^ 2 := by
    intro parameter parameterInside
    let factorValue := analysis.profile.factor.polynomial.eval parameter
    let conditionValue := condition.eval parameter
    let leftValue := apart.left.eval parameter
    let rightValue := apart.right.eval parameter
    let rightBound := Dense.Rational.Bounds.Horner.evalSqBound apart.right
      chart.cell.interval
    let denominator := 2 * (rightBound + 1)
    have leftSmall : 2 * (leftValue * factorValue) ^ 2 < 1 / 2 := by
      simpa only [-eq_self, -iff_self, leftValue, factorValue] using
        factorContributionSmall parameter parameterInside
    have identity : 1 = leftValue * factorValue +
        rightValue * conditionValue := by
      simpa only [-eq_self, -iff_self, leftValue, factorValue, rightValue, conditionValue] using
        apart.identity parameter
    have totalLower : (1 : Fraction.Rational) ≤
        2 * (leftValue * factorValue) ^ 2 +
          2 * (rightValue * conditionValue) ^ 2 := by
      calc
        (1 : Fraction.Rational) =
            (leftValue * factorValue + rightValue * conditionValue) ^ 2 := by
          rw [← identity]
          decide
        _ ≤ 2 * ((leftValue * factorValue) ^ 2 +
            (rightValue * conditionValue) ^ 2) :=
          Purelib.Data.Rat.Bounds.Square.add_sq_le_two _ _
        _ = 2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 := by ring1
    have rightStrict : (1 / 2 : Fraction.Rational) <
        2 * (rightValue * conditionValue) ^ 2 := by
      by_contra notStrict
      have rightLe : 2 * (rightValue * conditionValue) ^ 2 ≤ 1 / 2 :=
        le_of_not_gt notStrict
      have firstStep := Fraction.Order.Arithmetic.add_lt_add_right_direct
        leftSmall (2 * (rightValue * conditionValue) ^ 2)
      have secondStep := Fraction.Order.Arithmetic.add_le_add_right_direct
        rightLe (1 / 2 : Fraction.Rational)
      have sumStrict :
          2 * (leftValue * factorValue) ^ 2 +
              2 * (rightValue * conditionValue) ^ 2 < 1 := by
        calc
          2 * (leftValue * factorValue) ^ 2 +
              2 * (rightValue * conditionValue) ^ 2 <
              1 / 2 + 2 * (rightValue * conditionValue) ^ 2 := firstStep
          _ ≤ 1 / 2 + 1 / 2 := by
            simpa only [-eq_self, -iff_self, Fraction.Field.add_comm] using secondStep
          _ = 1 := by decide
      exact (not_lt_of_ge totalLower) sumStrict
    have parameterInsideChart : chart.cell.interval.Contains parameter :=
      ⟨refinesChart.1.trans parameterInside.1,
        parameterInside.2.trans refinesChart.2⟩
    have rightEvalBound : rightValue ^ 2 ≤ rightBound := by
      simpa only [-eq_self, -iff_self, rightValue, rightBound] using
        Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound apart.right
          chart.cell.interval parameterInsideChart
    have rightBoundLe : rightBound ≤ rightBound + 1 := by
      have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
        (show (0 : Fraction.Rational) ≤ 1 by decide) rightBound
      simpa only [-eq_self, -iff_self, zero_add, Fraction.Field.add_comm] using shifted
    have conditionSquareNonnegative : 0 ≤ conditionValue ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct conditionValue
    have rightProductUpper :
        2 * (rightValue * conditionValue) ^ 2 ≤
          denominator * conditionValue ^ 2 := by
      rw [Semiring.Normalization.product_pow]
      have valueBound : rightValue ^ 2 * conditionValue ^ 2 ≤
          (rightBound + 1) * conditionValue ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (rightEvalBound.trans rightBoundLe) conditionSquareNonnegative
      calc
        2 * (rightValue ^ 2 * conditionValue ^ 2) ≤
            2 * ((rightBound + 1) * conditionValue ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct valueBound
            (by decide)
        _ = denominator * conditionValue ^ 2 := by
          dsimp only [denominator]
          ring1
    have denominatorPositive : 0 < denominator :=
      Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
          (Dense.Rational.Bounds.Horner.evalSqBound_nonneg apart.right
            chart.cell.interval) (by decide))
    apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
    calc
      (1 / 2 : Fraction.Rational) <
          2 * (rightValue * conditionValue) ^ 2 := rightStrict
      _ ≤ denominator * conditionValue ^ 2 := rightProductUpper
      _ = conditionValue ^ 2 * denominator :=
        Fraction.Field.mul_comm _ _
  let chartLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
      chart.cell.interval
  let variationWidth :=
    Data.Rat.SmallWidth.shrinkingWidth
      chartLipschitz (apartConditionLower analysis condition apart)
  have widthLeVariation : epsilon ≤ variationWidth :=
    epsilonLe.trans (Fraction.Order.Basic.min_le_right _ _)
  have widthSqLeVariation : epsilon ^ 2 ≤ variationWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct positive.le
      widthLeVariation 2
  have chartLipschitzNonnegative : 0 ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
        condition chart.cell.interval).2
  have variationSmall : chartLipschitz * variationWidth ^ 2 <
      apartConditionLower analysis condition apart := by
    simpa only [-eq_self, -iff_self, variationWidth] using
      Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        chartLipschitzNonnegative
        (apartConditionLower_pos analysis condition apart)
  have localVariation := Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le
    condition cell.interval leftInside rightInside
  have localLeChart :
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound condition
          cell.interval ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        condition refinesChart
  have parameterDistance : (left - right) ^ 2 ≤ (Bounds.width cell.interval) ^ 2 :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      cell.interval leftInside rightInside
  have cellWidthSq : (Bounds.width cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct (Bounds.width_nonneg cell.interval)
      widthLe 2
  have distanceLeVariation : (left - right) ^ 2 ≤ variationWidth ^ 2 :=
    parameterDistance.trans (cellWidthSq.trans widthSqLeVariation)
  have variation : (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart :=
    localVariation.trans_lt
      ((Fraction.Order.Arithmetic.mul_le_mul_direct localLeChart
        distanceLeVariation
        (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right))
        chartLipschitzNonnegative).trans_lt variationSmall)
  have rightLower := conditionLowerAt right rightInside
  have differenceSmall :
      (condition.eval left - condition.eval right) ^ 2 <
        condition.eval right ^ 2 := variation.trans rightLower
  constructor
  · exact conditionLowerAt
  · rcases lt_or_ge (0 : Fraction.Rational)
        (condition.eval left * condition.eval right) with stable | nonpositive
    · exact stable
    · have squareOrder := Purelib.Data.Rat.Bounds.Square.right_sq_le_sub_sq_of_mul_nonpos nonpositive
      exact (not_lt_of_ge squareOrder differenceSmall).elim

/-- Uniform quadrance separation of an apart condition on an arbitrary
complete-refinement cell. -/
theorem apartConditionLower_lt_eval_sq_on_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (cell : Cell)
    (condition : CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : (Bounds.width cell.interval) ≤ epsilon)
    (factorBound : ∀ parameter : Fraction.Rational,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        ProfileEventLeaf.factorResidualCoefficient analysis * epsilon ^ 2)
    (parameter : Fraction.Rational)
    (inside : cell.interval.Contains parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 :=
  (apartConditionControl_on_cell cell condition apart epsilon positive
    epsilonLe refinesChart widthLe factorBound inside inside).1 parameter inside

/-- Stable sign projection of the complete apart-condition control. -/
theorem condition_eval_mul_pos_on_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (cell : Cell)
    (condition : CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : (Bounds.width cell.interval) ≤ epsilon)
    (factorBound : ∀ parameter : Fraction.Rational,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        ProfileEventLeaf.factorResidualCoefficient analysis * epsilon ^ 2)
    {left right : Fraction.Rational}
    (leftInside : cell.interval.Contains left)
    (rightInside : cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  (apartConditionControl_on_cell cell condition apart epsilon positive
    epsilonLe refinesChart widthLe factorBound leftInside rightInside).2

end Basic.ProfileEventLeaf

/-! ## One finite request width for all apart conditions in a profile -/

/-- Equality-owned conditions impose no shrinking requirement; an apart
condition contributes its coefficient-computed sign width. -/
@[expose] def Sign.relationSignWidth
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis)
    (entry : Sigma fun condition =>
      ConditionRelation condition
        analysis.profile.factor) : Fraction.Rational :=
  match entry.2 with
  | .equality _ _ => 1
  | .apart apart => Basic.ProfileEventLeaf.apartSignWidth analysis entry.1 apart

/-- Each original equality or apart relation contributes a positive sign-control width. -/
theorem Sign.relationSignWidth_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis)
    (entry : Sigma fun condition =>
      ConditionRelation condition
        analysis.profile.factor) :
    0 < Sign.relationSignWidth analysis entry := by
  rcases entry with ⟨condition, relation⟩
  cases relation with
  | equality _ _ =>
      simpa only [-eq_self, -iff_self, Sign.relationSignWidth] using
        (show (0 : Fraction.Rational) < 1 by decide)
  | apart apart =>
      simpa only [-eq_self, -iff_self, Sign.relationSignWidth] using
        Basic.ProfileEventLeaf.apartSignWidth_pos analysis condition apart

/-- Compute the ordered list of sign-control widths for the original profile's retained condition relations. -/
@[expose] def Sign.relationSignWidths
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) : List
      Fraction.Rational :=
  analysis.profile.relations.map (Sign.relationSignWidth analysis)

/-- One displayed positive rational width satisfying all apart-condition
requirements of the profile simultaneously. -/
@[expose] def Sign.profileSignWidth
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) :
      Fraction.Rational :=
  Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum
    (Sign.relationSignWidths analysis)

/-- The finite minimum of the original profile's positive condition widths is positive. -/
theorem Sign.profileSignWidth_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) :
    0 < Sign.profileSignWidth analysis := by
  apply Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum_pos
  intro width widthMember
  dsimp only [Sign.relationSignWidths] at widthMember
  have widthMember := Data.List.Map.mem_map.mp widthMember
  rcases widthMember with ⟨entry, _entryMember, rfl⟩
  exact Sign.relationSignWidth_pos analysis entry

/-- The original profile-wide sign width is no larger than any retained relation's computed width. -/
theorem Sign.profileSignWidth_le_relation
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis)
    (entry : Sigma fun condition =>
      ConditionRelation condition
        analysis.profile.factor)
    (member : entry ∈ analysis.profile.relations) :
    Sign.profileSignWidth analysis ≤ Sign.relationSignWidth analysis entry := by
  apply Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum_le_of_mem
  exact Data.List.Map.mem_map.mpr ⟨entry, member, rfl⟩

/-- The original profile-wide sign width meets the computed bound for every retained apart condition. -/
theorem Sign.profileSignWidth_le_apart
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis)
    (condition : CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (member : (⟨condition,
      ConditionRelation.apart apart⟩ :
        Sigma fun queried =>
          ConditionRelation queried
            analysis.profile.factor) ∈ analysis.profile.relations) :
    Sign.profileSignWidth analysis ≤
      Basic.ProfileEventLeaf.apartSignWidth analysis condition apart :=
  Sign.profileSignWidth_le_relation analysis _ member

namespace Basic.ProfileEventLeaf

/-- At the single profile-wide request width, every two evaluations of any
recorded apart condition have the same strict sign. -/
theorem profile_condition_eval_mul_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (condition : CoefficientPolynomial)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (member : (⟨condition,
      ConditionRelation.apart apart⟩ :
        Sigma fun queried =>
          ConditionRelation queried
            analysis.profile.factor) ∈ analysis.profile.relations)
    {left right : Fraction.Rational}
    (leftInside : (leaf.request
      (Curve.Event.Profile.Sign.profileSignWidth analysis)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (Curve.Event.Profile.Sign.profileSignWidth analysis)).cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  leaf.condition_eval_mul_pos_of_le condition apart
    (Curve.Event.Profile.Sign.profileSignWidth analysis) (Curve.Event.Profile.Sign.profileSignWidth_pos analysis)
      (Curve.Event.Profile.Sign.profileSignWidth_le_apart analysis condition apart member)
        leftInside rightInside

end Basic.ProfileEventLeaf
end Purelib.RootIsolation.Curve.Event.Profile

end
