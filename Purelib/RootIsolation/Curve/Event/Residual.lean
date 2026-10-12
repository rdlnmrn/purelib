module
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Polynomial.Dense.Rational.Squarefree.Product
import Purelib.RationalFunctions.Curve.Substitution
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Factor
import Purelib.Data.Rat.Interval.Width
public import Purelib.RootIsolation.Curve.Event.Request
public import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Decomposition
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent projective shrinking of nonzero CCL curve events

Every nonconstant curve analysis has already been split into squarefree
coordinate factors and an aligned finite partition.  This module extracts the
nonzero-count leaves as explicit finite event records.  Each record carries
the existing central-third Sturm transducer and, simultaneously, a homogeneous
projective image bound for its rational boundary chart.

The homogeneous estimate remains valid across an affine pole.  It is therefore
combined with each chart's positive homogeneous-weight lower bound to obtain
the genuine finite `chi^2` shrinking fact needed to couple a narrowing
parameter event to a narrowing winding box without choosing a completed
parameter or root.
-/

namespace Purelib.RootIsolation.Curve.Event.Basic
namespace EventLeaf

/-- Fixed finite coefficient for the gcd-reduced event residual. -/
def reducedEventResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Fraction.Rational :=
  4 * Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound
    (Dense.Rational.Pair.Reduction.reducedDenominator
      (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
      factorAnalysis.factor.polynomial) chart.cell.interval

/-- The original chart-wide reduced event residual coefficient is nonnegative. -/
theorem reducedEventResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :
    0 ≤ reducedEventResidualCoefficient factorAnalysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval).2

/-- Every rational parameter in a requested nonzero event has uniformly
small gcd-reduced factor residual.  The bound is quadratic in the requested
width and is obtained solely from finite endpoint signs and Horner bounds. -/
theorem reduced_eval_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial).eval parameter ^ 2 ≤
      reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let event := factorAnalysis.factor.polynomial
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
  have refinesChart := leaf.request_refines_chart epsilon
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [localLipschitz, chartLipschitz, requested, reduced] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        reduced refinesChart
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Fraction.Rational) ≤ 4 by decide)
  have widthLe := leaf.request_width_le epsilon positive
  have widthSqLe : (Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Bounds.width_nonneg requested.cell.interval) widthLe 2
  have widthSqNonnegative : 0 ≤ (Bounds.width requested.cell.interval) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct (Bounds.width requested.cell.interval)
  have chartCoefficientNonnegative : 0 ≤ 4 * chartLipschitz :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) chartNonnegative
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct coefficientLe widthSqLe
      widthSqNonnegative chartCoefficientNonnegative)

/-- Fixed coefficient for the residual of the selected squarefree factor,
including the finite derivative gcd that was divided out before Sturm
counting. -/
def factorEventResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Fraction.Rational :=
  Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.GCD.gcd
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval *
    reducedEventResidualCoefficient factorAnalysis

/-- The selected squarefree factor's original residual coefficient is nonnegative. -/
theorem factorEventResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :
    0 ≤ factorEventResidualCoefficient factorAnalysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg
      (Dense.GCD.gcd
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval)
    (reducedEventResidualCoefficient_nonneg factorAnalysis)

/-- The selected factor itself is uniformly small on the requested event.
The lift from the reduced Sturm denominator uses the displayed finite
derivative-gcd factor, bounded by a finite Horner scan on the original chart. -/
theorem factor_eval_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      factorEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let event := factorAnalysis.factor.polynomial
  let common := Dense.GCD.gcd
    (Dense.Derivative.derivative event) event
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let commonBound := Dense.Rational.Bounds.Horner.evalSqBound common
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound := by
    exact Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [event, reduced] using
      leaf.reduced_eval_sq_request_le epsilon positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      reducedEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (reduced.eval parameter))
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg common
        chart.cell.interval)
  have identity : event.eval parameter =
      common.eval parameter * reduced.eval parameter := by
    simpa only [event, common, reduced,
      Dense.Rational.Pair.Reduction.reducedDenominator] using
      Dense.GCD.rightFactor_eval_identity
        (Dense.Derivative.derivative event) event parameter
  rw [identity, Fraction.Field.mul_pow_direct]
  change common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
    (commonBound * reducedEventResidualCoefficient factorAnalysis) *
      epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- The explicitly computed product of all other squarefree occurrences in
the finite curve-gcd decomposition. -/
def curveGCDCofactor
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial :=
  Dense.Rational.Squarefree.factorCofactor
    factorAnalysis.factor.polynomial
    (Curve.Event.eventDecomposition data
      gcdDegreePositive).factors

/-- Fixed coefficient for the complete curve-gcd residual on a requested
event cell. -/
def gcdEventResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Fraction.Rational :=
  factorEventResidualCoefficient factorAnalysis *
    Dense.Rational.Bounds.Horner.evalSqBound
      (curveGCDCofactor factorAnalysis) chart.cell.interval

/-- The original full curve-gcd residual coefficient, including the retained cofactor, is nonnegative. -/
theorem gcdEventResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :
    0 ≤ gcdEventResidualCoefficient factorAnalysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (factorEventResidualCoefficient_nonneg factorAnalysis)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg
      (curveGCDCofactor factorAnalysis) chart.cell.interval)

/-- Every parameter in a requested nonzero squarefree event makes the full
curve gcd uniformly small.  Other factor occurrences are retained as an
explicit finite cofactor and bounded on the original chart. -/
theorem gcd_eval_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let decomposition := Curve.Event.eventDecomposition data
    gcdDegreePositive
  let cofactor := curveGCDCofactor factorAnalysis
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound cofactor
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have factorBound :=
    leaf.factor_eval_sq_request_le epsilon positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (factorEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
          cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct factorBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (factorEventResidualCoefficient_nonneg factorAnalysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon))
  have identity :
      (Curve.Substitution.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
        factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
    calc
      (Curve.Substitution.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
          (Dense.Rational.Squarefree.factorProduct
            decomposition.factors).eval parameter :=
        decomposition.evalIdentity parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          (Dense.Rational.Squarefree.factorCofactor
            factorAnalysis.factor.polynomial decomposition.factors).eval
              parameter :=
        Dense.Rational.Squarefree.factorProduct_eval_eq_factor_mul_cofactor
          factorAnalysis.factor decomposition.factors factorAnalysis.member
            parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
        rfl
  rw [identity, Fraction.Field.mul_pow_direct]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (factorEventResidualCoefficient factorAnalysis * cofactorBound) *
      epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- Finite chart-wide majorant for the two cofactors that lift the executable
curve gcd back to the real and imaginary denominator-cleared coordinates. -/
def curveGCDLiftCoefficient
    (p : CoefficientPolynomial) {form :
      HermitianForm}
    (chart : BoundedChart form) : Fraction.Rational :=
  Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.GCD.leftFactor
        (Curve.Substitution.realPolynomial p
          chart.parameterization.curve)
        (Curve.Substitution.imaginaryPolynomial p
          chart.parameterization.curve)) chart.cell.interval +
    Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.GCD.rightFactor
        (Curve.Substitution.realPolynomial p
          chart.parameterization.curve)
        (Curve.Substitution.imaginaryPolynomial p
          chart.parameterization.curve)) chart.cell.interval

/-- The finite sum of real and imaginary cofactor majorants is nonnegative. -/
theorem curveGCDLiftCoefficient_nonneg
    (p : CoefficientPolynomial) {form :
      HermitianForm}
    (chart : BoundedChart form) : 0 ≤
      curveGCDLiftCoefficient p chart :=
  add_nonneg
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)

/-- Fixed coefficient for the homogeneous denominator-cleared polynomial
residual on a requested nonzero event. -/
def clearedEventResidualCoefficient
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Fraction.Rational :=
  gcdEventResidualCoefficient factorAnalysis *
    curveGCDLiftCoefficient p chart

/-- The original denominator-cleared coordinate residual coefficient is nonnegative. -/
theorem clearedEventResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :
    0 ≤ clearedEventResidualCoefficient factorAnalysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (gcdEventResidualCoefficient_nonneg factorAnalysis)
    (curveGCDLiftCoefficient_nonneg p chart)

/-- Both denominator-cleared coordinate residuals are uniformly small on the
whole requested event cell.  This is the coefficient-computable event-wide
bridge from the squarefree Sturm transducer back to the original curve
substitution. -/
theorem cleared_coordinate_norm_sq_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Curve.Substitution.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (Curve.Substitution.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let real := Curve.Substitution.realPolynomial p
    chart.parameterization.curve
  let imaginary := Curve.Substitution.imaginaryPolynomial p
    chart.parameterization.curve
  let common := Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve
  let left := Dense.GCD.leftFactor real imaginary
  let right := Dense.GCD.rightFactor real imaginary
  let liftBound := curveGCDLiftCoefficient p chart
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [common] using
      leaf.gcd_eval_sq_request_le epsilon positive parameter inside
  have leftEvalBound : left.eval parameter ^ 2 ≤
      Dense.Rational.Bounds.Horner.evalSqBound left chart.cell.interval :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound left
      chart.cell.interval parameterInsideChart
  have rightEvalBound : right.eval parameter ^ 2 ≤
      Dense.Rational.Bounds.Horner.evalSqBound right chart.cell.interval :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound right
      chart.cell.interval parameterInsideChart
  have cofactorSumBound :
      left.eval parameter ^ 2 + right.eval parameter ^ 2 ≤ liftBound := by
    simpa only [left, right, real, imaginary, liftBound,
      curveGCDLiftCoefficient] using add_le_add leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
          liftBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct (left.eval parameter))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (right.eval parameter)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (gcdEventResidualCoefficient_nonneg factorAnalysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [real, imaginary, common, left,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [real, imaginary, common, right,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (gcdEventResidualCoefficient factorAnalysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, Fraction.Field.mul_pow_direct, Fraction.Field.mul_pow_direct]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
        liftBound := productBound
    _ = (gcdEventResidualCoefficient factorAnalysis * liftBound) *
        epsilon ^ 2 := by ring1

/-- Gaussian form of `cleared_coordinate_norm_sq_request_le`. -/
theorem normSq_clearedEval_request_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearedEval p
          chart.parameterization.curve).eval
            (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
      clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  simpa only [Curve.Substitution.realPolynomial,
    Curve.Substitution.imaginaryPolynomial,
    Curve.clearedReal,
    Curve.clearedImag,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Data.Gaussian.Norm.Basic.normSq] using
      leaf.cleared_coordinate_norm_sq_request_le epsilon positive parameter
        inside

/-- Fixed coefficient converting the homogeneous event residual into an
original-polynomial residual at affine chart points lying in `targetBox`. -/
def affineEventResidualCoefficient
    {p : CoefficientPolynomial} {box targetBox : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : Fraction.Rational :=
  clearedEventResidualCoefficient factorAnalysis /
    chart.affineDenominatorPowerNormSqLower p targetBox

/-- The original affine residual coefficient is nonnegative because its retained denominator-power lower bound is
positive. -/
theorem affineEventResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {box targetBox : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :
    0 ≤ affineEventResidualCoefficient
      (targetBox := targetBox) factorAnalysis :=
  Fraction.Order.Field.div_nonneg_direct
    (clearedEventResidualCoefficient_nonneg factorAnalysis)
    (chart.affineDenominatorPowerNormSqLower_pos p targetBox).le

/-- Every point where the requested event meets a displayed finite box has
small original-polynomial residual.  The coefficient is uniform over the
whole box and event cell; the chart denominator may approach zero elsewhere. -/
theorem normSq_eval_point_request_le_of_inside
    {p : CoefficientPolynomial} {box targetBox : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (parameterInside :
      (leaf.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      affineEventResidualCoefficient (targetBox := targetBox)
        factorAnalysis * epsilon ^ 2 := open Purelib.Algebra.Field in by
  let curve := chart.parameterization.curve
  let power :=
    (Curve.clearingState p curve).denominatorPower.eval
      (Gaussian.Cast.Path.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := Data.Gaussian.Norm.Basic.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      Data.Gaussian.Norm.Basic.normSq power := by
    simpa only [lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound :=
    leaf.normSq_clearedEval_request_le epsilon positive parameter
      parameterInside
  have semantics := Curve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      Data.Gaussian.Norm.Basic.normSq power * residual ≤
        clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [curve, power, residual, semantics,
      Gaussian.Norm.Basic.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      Data.Gaussian.Norm.Basic.normSq power * residual :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct powerLower
      (Gaussian.Norm.Basic.normSq_nonneg _)
  change residual ≤
    (clearedEventResidualCoefficient factorAnalysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2) /
          lower := by
      apply (Fraction.Order.Field.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          Fraction.Field.mul_comm _ _
        _ ≤ Data.Gaussian.Norm.Basic.normSq power * residual :=
          lowerProductBound
        _ ≤ clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 :=
          clearedProductBound
    _ = (clearedEventResidualCoefficient factorAnalysis / lower) *
        epsilon ^ 2 := by
      simp only [ExplicitField.div_eq_mul_inv]
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.mul_comm (epsilon ^ 2),
        ← Fraction.Field.mul_assoc]
end EventLeaf

end Purelib.RootIsolation.Curve.Event.Basic

end
