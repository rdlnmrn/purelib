module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.Data.Rat.Interval.Width
public import Purelib.RootIsolation.Curve.Event.Profile.Request
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts
  (SourcePersistentConditionProfilesProfileAnalysisAlias
   SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Basic

open Purelib.Algebra
namespace ProfileEventLeaf

/-- Fixed chart-wide coefficient for the gcd-reduced profile residual. -/
@[expose] def reducedResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
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
  4 * Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
    (Dense.Rational.Pair.Reduction.reducedDenominator
      (Dense.Derivative.derivative analysis.profile.factor.polynomial)
      analysis.profile.factor.polynomial) chart.cell.interval

/-- The original chart-wide reduced profile residual coefficient is nonnegative. -/
theorem reducedResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
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
    0 ≤ reducedResidualCoefficient analysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval).2

/-- The reduced profile factor has squared residual bounded by the original chart coefficient times the positive
requested width squared.

The retained nonzero Sturm count supplies the local residual bound, and interval refinement transports its finite
Lipschitz majorant to the original chart. -/
theorem reduced_eval_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
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
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      reducedResidualCoefficient analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let requested := leaf.request epsilon
  let localLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      requested.cell.interval
  let chartLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (leaf.requestResolution epsilon).denominator_eval_sq_le
      requested.countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, localLipschitz, chartLipschitz, requested, reduced] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        reduced (leaf.request_refines_chart epsilon)
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Fraction.Rational) ≤ 4 by decide)
  have widthSqLe : (Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Bounds.width_nonneg requested.cell.interval)
      (leaf.request_width_le epsilon positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct coefficientLe widthSqLe
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (Bounds.width requested.cell.interval))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- Fixed coefficient for the final squarefree profile factor itself. -/
@[expose] def factorResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
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
  Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.GCD.gcd
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval *
    reducedResidualCoefficient analysis

/-- The original profile-factor residual coefficient, including its derivative gcd, is nonnegative. -/
theorem factorResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
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
    0 ≤ factorResidualCoefficient analysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg
      (Dense.GCD.gcd
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval)
    (reducedResidualCoefficient_nonneg analysis)

/-- The original profile factor has squared residual bounded by its retained coefficient times the positive requested
width squared.

The exact derivative-gcd factorization lifts the reduced residual using a finite Horner bound on the original chart. -/
theorem factor_eval_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
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
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      factorResidualCoefficient analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := Dense.GCD.gcd
    (Dense.Derivative.derivative event) event
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let commonBound := Dense.Rational.Bounds.Horner.evalSqBound common
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      reducedResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, event, reduced] using
      leaf.reduced_eval_sq_request_le epsilon positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (reducedResidualCoefficient analysis * epsilon ^ 2) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      reducedEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (reduced.eval parameter))
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg common
        chart.cell.interval)
  have identity : event.eval parameter =
      common.eval parameter * reduced.eval parameter := by
    simpa only [-eq_self, -iff_self, event, common, reduced,
      Dense.Rational.Pair.Reduction.reducedDenominator] using
      Dense.GCD.rightFactor_eval_identity
        (Dense.Derivative.derivative event) event parameter
  rw [identity, Semiring.Normalization.product_pow]
  change common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
    (commonBound * reducedResidualCoefficient analysis) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)
end ProfileEventLeaf
end Purelib.RootIsolation.Curve.Event.Profile.Basic

end
