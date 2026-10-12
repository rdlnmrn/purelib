module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Polynomial.Dense.Rational.Squarefree.Product
import Purelib.RationalFunctions.Curve.Substitution
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Factor
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Residual
public import Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift
import Purelib.RootIsolation.Curve.Event.Residual
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Refinement
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Residual

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf

open Purelib.Algebra
section Profile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
  Geometry.Projective.Hermitian.HermitianForm}
variable {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
variable {data : Curve.Event.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box
  chart data
  gcdDegreePositive}
variable {analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}
section CompleteRequestLeaf

/-- The reduced profile polynomial remains uniformly small on every later
deterministic request from this retained child. -/
theorem request_reduced_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis * target ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let localLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      (entry.request target).cell.interval
  let chartLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (entry.requestResolution target).denominator_eval_sq_le
      (entry.request target).countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, localLipschitz, chartLipschitz, reduced] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        reduced (entry.request_refines_chart target)
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Fraction.Rational) ≤ 4 by decide)
  have widthSqLe : (Data.Rat.Interval.Bounds.width (entry.request target).cell.interval) ^ 2 ≤
      target ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Data.Rat.Interval.Bounds.width_nonneg (entry.request target).cell.interval)
        (entry.request_width_le target positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * target ^ 2
  exact localBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct coefficientLe widthSqLe
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (Data.Rat.Interval.Bounds.width (entry.request target).cell.interval))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- The profile factor itself stays uniformly small along the selected
descendant event branch. -/
theorem request_factor_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
        analysis * target ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := Dense.GCD.gcd
    (Dense.Derivative.derivative event) event
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let commonBound := Dense.Rational.Bounds.Horner.evalSqBound common
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis * target ^ 2 := by
    simpa only [-eq_self, -iff_self, event, reduced] using
      entry.request_reduced_eval_sq_le target positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
            analysis * target ^ 2) :=
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
    (commonBound *
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the selected descendant's residual through the exact profile
cofactor to the source squarefree curve factor. -/
theorem
  request_source_factor_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
        analysis * target ^ 2 := by
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have profileBound :=
    entry.request_factor_eval_sq_le target positive parameter inside
  have cofactorEvalBound : analysis.profile.cofactor.eval parameter ^ 2 ≤
      cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      analysis.profile.cofactor chart.cell.interval parameterInsideChart
  have productBound :
      analysis.profile.factor.polynomial.eval parameter ^ 2 *
          analysis.profile.cofactor.eval parameter ^ 2 ≤
        (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
            analysis * target ^ 2) * cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct profileBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (analysis.profile.cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct target))
  have identity : factorAnalysis.factor.polynomial.eval parameter =
      analysis.profile.factor.polynomial.eval parameter *
        analysis.profile.cofactor.eval parameter :=
    Dense.Rational.Factorization.eval_factorization
      analysis.profile.factorization parameter
  rw [identity, Semiring.Normalization.product_pow]
  change analysis.profile.factor.polynomial.eval parameter ^ 2 *
      analysis.profile.cofactor.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
        analysis * cofactorBound) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the selected descendant through the remaining finite curve-gcd
factors. -/
theorem request_gcd_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * target ^ 2 := by
  let decomposition := Curve.Event.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    Curve.Event.Basic.EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound cofactor
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have sourceBound :=
    entry.request_source_factor_eval_sq_le target positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
            analysis * target ^ 2) * cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct target))
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
          cofactor.eval parameter := by rfl
  rw [identity, Semiring.Normalization.product_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
      analysis * cofactorBound) * target ^ 2
  exact productBound.trans_eq (by ring1)

/-- Lift the descendant residual through both displayed cofactors of the
denominator-cleared rational curve. -/
theorem
  request_cleared_coordinate_norm_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    (Curve.Substitution.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (Curve.Substitution.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
        analysis * target ^ 2 := by
  let real := Curve.Substitution.realPolynomial p
    chart.parameterization.curve
  let imaginary := Curve.Substitution.imaginaryPolynomial p
    chart.parameterization.curve
  let common := Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve
  let left := Dense.GCD.leftFactor real imaginary
  let right := Dense.GCD.rightFactor real imaginary
  let liftBound :=
    Curve.Event.Basic.EventLeaf.curveGCDLiftCoefficient
      p chart
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * target ^ 2 := by
    simpa only [-eq_self, -iff_self, common] using
      entry.request_gcd_eval_sq_le target positive parameter inside
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
    simpa only [-eq_self, -iff_self, left, right, real, imaginary, liftBound,
      Curve.Event.Basic.EventLeaf.curveGCDLiftCoefficient] using
        Fraction.Order.Arithmetic.add_le_add_direct leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
            analysis * target ^ 2) * liftBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct (left.eval parameter))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (right.eval parameter)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct target))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [-eq_self, -iff_self, real, imaginary, common, left,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [-eq_self, -iff_self, real, imaginary, common, right,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
      analysis * liftBound) * target ^ 2
  rw [realIdentity, imaginaryIdentity, Semiring.Normalization.product_pow, Semiring.Normalization.product_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * target ^ 2) * liftBound := productBound
    _ = (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * liftBound) * target ^ 2 := by ring1

/-- Gaussian form of the descendant's cleared-coordinate residual. -/
theorem
  request_normSq_clearedEval_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearedEval p
          chart.parameterization.curve).eval
            (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
        analysis * target ^ 2 := by
  simpa only [-eq_self, -iff_self, Curve.Substitution.realPolynomial,
    Curve.Substitution.imaginaryPolynomial,
    Curve.clearedReal,
    Curve.clearedImag,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Data.Gaussian.Norm.Basic.normSq] using
      entry.request_cleared_coordinate_norm_sq_le target positive parameter
        inside

/-- Every affine point on the selected descendant branch that lies in a
displayed target box has original-polynomial residual of order `target²`. -/
theorem
  request_normSq_eval_point_le_of_inside
    {targetBox : Box} {leaf :
      Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis}
    {epsilon : Fraction.Rational} (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (target : Fraction.Rational) (positive : 0 < target) (parameter : Fraction.Rational)
    (parameterInside :
      (entry.request target).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient
          (targetBox := targetBox) analysis * target ^ 2 := open Purelib.Algebra.Field in by
  let curve := chart.parameterization.curve
  let power :=
    (Curve.clearingState p curve).denominatorPower.eval
      (Gaussian.Cast.Path.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := Data.Gaussian.Norm.Basic.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [-eq_self, -iff_self, lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      Data.Gaussian.Norm.Basic.normSq power := by
    simpa only [-eq_self, -iff_self, lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound := entry.request_normSq_clearedEval_le target positive
    parameter parameterInside
  have semantics := Curve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      Data.Gaussian.Norm.Basic.normSq power * residual ≤
        Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * target ^ 2 := by
    simpa only [-eq_self, -iff_self, curve, power, residual, semantics,
      Gaussian.Norm.Basic.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      Data.Gaussian.Norm.Basic.normSq power * residual :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct powerLower
      (Gaussian.Norm.Basic.normSq_nonneg _)
  change residual ≤
    (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
      analysis / lower) * target ^ 2
  calc
    residual ≤
        (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * target ^ 2) / lower := by
      apply (Fraction.Order.Field.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          Fraction.Field.mul_comm _ _
        _ ≤ Data.Gaussian.Norm.Basic.normSq power * residual :=
          lowerProductBound
        _ ≤ Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * target ^ 2 := clearedProductBound
    _ =
        (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis / lower) * target ^ 2 := by
      simp only [-eq_self, -iff_self, ExplicitField.div_eq_mul_inv]
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.mul_comm (target ^ 2),
        ← Fraction.Field.mul_assoc]

/-- The gcd-reduced profile polynomial is uniformly small throughout every
retained child, not only along the formerly selected request path. -/
theorem reduced_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let localLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      entry.cell.interval
  let chartLipschitz :=
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (Curve.Event.Profile.Complete.Basic.completeRequestResolution leaf epsilon entry.cell
      entry.member).denominator_eval_sq_le
      entry.countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, localLipschitz, chartLipschitz, reduced] using
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound_le_of_refines
        reduced entry.refines_chart
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [-eq_self, -iff_self, chartLipschitz] using
      (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Fraction.Rational) ≤ 4 by decide)
  have widthSqLe : (Data.Rat.Interval.Bounds.width entry.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Data.Rat.Interval.Bounds.width_nonneg entry.cell.interval) (entry.width_le positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct coefficientLe widthSqLe
      (Fraction.Order.Arithmetic.sq_nonneg_direct (Data.Rat.Interval.Bounds.width entry.cell.interval))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- The profile factor itself is uniformly small throughout every retained
child. -/
theorem factor_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
        analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := Dense.GCD.gcd
    (Dense.Derivative.derivative event) event
  let reduced := Dense.Rational.Pair.Reduction.reducedDenominator
    (Dense.Derivative.derivative event) event
  let commonBound := Dense.Rational.Bounds.Horner.evalSqBound common
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, event, reduced] using
      entry.reduced_eval_sq_le positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
            analysis * epsilon ^ 2) :=
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
    (commonBound *
      Curve.Event.Profile.Basic.ProfileEventLeaf.reducedResidualCoefficient
        analysis) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- The source squarefree factor containing the profile is uniformly small
throughout every retained child. -/
theorem source_factor_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
        analysis * epsilon ^ 2 := by
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have profileBound := entry.factor_eval_sq_le positive parameter inside
  have cofactorEvalBound : analysis.profile.cofactor.eval parameter ^ 2 ≤
      cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      analysis.profile.cofactor chart.cell.interval parameterInsideChart
  have productBound :
      analysis.profile.factor.polynomial.eval parameter ^ 2 *
          analysis.profile.cofactor.eval parameter ^ 2 ≤
        (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
            analysis * epsilon ^ 2) * cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct profileBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (analysis.profile.cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon))
  have identity : factorAnalysis.factor.polynomial.eval parameter =
      analysis.profile.factor.polynomial.eval parameter *
        analysis.profile.cofactor.eval parameter :=
    Dense.Rational.Factorization.eval_factorization
      analysis.profile.factorization parameter
  rw [identity, Semiring.Normalization.product_pow]
  change analysis.profile.factor.polynomial.eval parameter ^ 2 *
      analysis.profile.cofactor.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
        analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- The complete curve gcd is uniformly small throughout every retained
profile child. -/
theorem gcd_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * epsilon ^ 2 := by
  let decomposition := Curve.Event.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    Curve.Event.Basic.EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound cofactor
    chart.cell.interval
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have sourceBound := entry.source_factor_eval_sq_le positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
            analysis * epsilon ^ 2) * cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient_nonneg
          analysis)
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
          cofactor.eval parameter := by rfl
  rw [identity, Semiring.Normalization.product_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient
      analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- Both denominator-cleared coordinates of the original polynomial are
uniformly small throughout every retained profile child. -/
theorem
  cleared_coordinate_norm_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    (Curve.Substitution.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (Curve.Substitution.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
        analysis * epsilon ^ 2 := by
  let real := Curve.Substitution.realPolynomial p
    chart.parameterization.curve
  let imaginary := Curve.Substitution.imaginaryPolynomial p
    chart.parameterization.curve
  let common := Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve
  let left := Dense.GCD.leftFactor real imaginary
  let right := Dense.GCD.rightFactor real imaginary
  let liftBound :=
    Curve.Event.Basic.EventLeaf.curveGCDLiftCoefficient
      p chart
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, common] using entry.gcd_eval_sq_le positive parameter inside
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
    simpa only [-eq_self, -iff_self, left, right, real, imaginary, liftBound,
      Curve.Event.Basic.EventLeaf.curveGCDLiftCoefficient] using
        Fraction.Order.Arithmetic.add_le_add_direct leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
            analysis * epsilon ^ 2) * liftBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct (left.eval parameter))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (right.eval parameter)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [-eq_self, -iff_self, real, imaginary, common, left,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [-eq_self, -iff_self, real, imaginary, common, right,
      Curve.Substitution.gcdPolynomial] using
      Dense.GCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
      analysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, Semiring.Normalization.product_pow, Semiring.Normalization.product_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * epsilon ^ 2) * liftBound := productBound
    _ = (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient
        analysis * liftBound) * epsilon ^ 2 := by ring1

/-- Gaussian form of the retained child's cleared-coordinate residual. -/
theorem normSq_clearedEval_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearedEval p
          chart.parameterization.curve).eval
            (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
        analysis * epsilon ^ 2 := by
  simpa only [-eq_self, -iff_self, Curve.Substitution.realPolynomial,
    Curve.Substitution.imaginaryPolynomial,
    Curve.clearedReal,
    Curve.clearedImag,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Data.Gaussian.Norm.Basic.normSq] using
      entry.cleared_coordinate_norm_sq_le positive parameter inside

/-- Every affine point where a retained child meets a displayed box has a
uniformly small original-polynomial residual. -/
theorem
  normSq_eval_point_le_of_inside
    {targetBox : Box} {leaf :
      Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis}
    {epsilon : Fraction.Rational} (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (parameterInside : entry.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient
          (targetBox := targetBox) analysis * epsilon ^ 2 := open Purelib.Algebra.Field in by
  let curve := chart.parameterization.curve
  let power :=
    (Curve.clearingState p curve).denominatorPower.eval
      (Gaussian.Cast.Path.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := Data.Gaussian.Norm.Basic.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [-eq_self, -iff_self, lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      Data.Gaussian.Norm.Basic.normSq power := by
    simpa only [-eq_self, -iff_self, lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound := entry.normSq_clearedEval_le positive parameter
    parameterInside
  have semantics := Curve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      Data.Gaussian.Norm.Basic.normSq power * residual ≤
        Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, curve, power, residual, semantics,
      Gaussian.Norm.Basic.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      Data.Gaussian.Norm.Basic.normSq power * residual :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct powerLower
      (Gaussian.Norm.Basic.normSq_nonneg _)
  change residual ≤
    (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
      analysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2) / lower := by
      apply (Fraction.Order.Field.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          Fraction.Field.mul_comm _ _
        _ ≤ Data.Gaussian.Norm.Basic.normSq power * residual :=
          lowerProductBound
        _ ≤ Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis * epsilon ^ 2 := clearedProductBound
    _ =
        (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient
          analysis / lower) * epsilon ^ 2 := by
      simp only [-eq_self, -iff_self, ExplicitField.div_eq_mul_inv]
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.mul_comm (epsilon ^ 2),
        ← Fraction.Field.mul_assoc]

/-- Homogeneous chordal diameter bound for every retained child,
independently of affine poles. -/
theorem chordalSq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    {left right : Fraction.Rational}
    (leftInside : entry.cell.interval.Contains left)
    (rightInside : entry.cell.interval.Contains right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  have leftChart : chart.cell.interval.Contains left :=
    ⟨entry.refines_chart.1.trans leftInside.1,
      leftInside.2.trans entry.refines_chart.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨entry.refines_chart.1.trans rightInside.1,
      rightInside.2.trans entry.refines_chart.2⟩
  have parameterBound :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      entry.cell.interval leftInside rightInside
  have widthSquare : (Data.Rat.Interval.Bounds.width entry.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Data.Rat.Interval.Bounds.width_nonneg entry.cell.interval) (entry.width_le positive) 2
  exact (chart.chordalSq_le_uniform leftChart rightChart).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      chart.uniformChordalVariationCoefficient_nonneg)

end CompleteRequestLeaf

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf

end
