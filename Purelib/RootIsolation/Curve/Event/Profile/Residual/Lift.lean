module
import Purelib.Algebra.Semiring.Normalization
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
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Product
import Purelib.RationalFunctions.Curve.Substitution
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Factor
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Residual
public import Purelib.RootIsolation.Curve.Event.Residual
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
import Purelib.RootIsolation.Curve.Event.Profile.Request
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring

open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentProfileResidualProfileAnalysisAlias)
open Purelib.RootIsolation.Curve.Event.Basic (EventLeaf)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (SourcePersistentProfileResidualProfileEventLeafAlias)

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
# Original-polynomial residuals on condition-profile CCL events

A condition profile is a further finite factor of one squarefree curve-gcd
factor.  Its Sturm request directly bounds only that final profile factor.
This module multiplies through the displayed finite cofactors, then through
the two cleared curve coordinates, to recover a coefficient-computed bound
for the original Gaussian polynomial at every displayed affine point of the
requested profile cylinder.

All parameters and coefficients are constructive rationals.  The estimates
hold pointwise throughout a finite request interval and make no root
existence assertion.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift

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
variable {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileResidualSquarefreeFactorAnalysisAlias p box chart
  data
  gcdDegreePositive}

/-- Coefficient obtained by lifting the profile-factor residual through its
displayed cofactor in the source squarefree factor. -/
@[expose] def sourceFactorResidualCoefficient
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
      Fraction.Rational :=
  Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
      analysis *
    Dense.Rational.Bounds.Horner.evalSqBound analysis.profile.cofactor
      chart.cell.interval

/-- The original squarefree-factor residual coefficient, including the retained profile cofactor, is nonnegative. -/
theorem sourceFactorResidualCoefficient_nonneg
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
    0 ≤ sourceFactorResidualCoefficient analysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
      analysis)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg
      analysis.profile.cofactor chart.cell.interval)

namespace ProfileEventLeaf

/-- The original squarefree factor containing this profile is uniformly
small throughout the requested profile event. -/
theorem source_factor_eval_sq_request_le
    {analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis}
    (leaf : SourcePersistentProfileResidualProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient analysis * epsilon ^ 2 := by
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have profileBound := leaf.factor_eval_sq_request_le epsilon positive
    parameter inside
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

end ProfileEventLeaf

/-- Coefficient obtained after multiplying the source squarefree factor by
the explicitly computed product of all other curve-gcd factors. -/
@[expose] def profileGCDResidualCoefficient
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
      Fraction.Rational :=
  sourceFactorResidualCoefficient analysis *
    Dense.Rational.Bounds.Horner.evalSqBound
      (EventLeaf.curveGCDCofactor
        factorAnalysis) chart.cell.interval

/-- The original complete curve-gcd residual coefficient lifted from this profile is nonnegative. -/
theorem profileGCDResidualCoefficient_nonneg
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
    0 ≤ profileGCDResidualCoefficient analysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (sourceFactorResidualCoefficient_nonneg analysis)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg
      (EventLeaf.curveGCDCofactor
        factorAnalysis) chart.cell.interval)

namespace ProfileEventLeaf

/-- The complete real/imaginary curve gcd is uniformly small throughout the
requested profile event. -/
theorem gcd_eval_sq_request_le
    {analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis}
    (leaf : SourcePersistentProfileResidualProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * epsilon ^ 2 := by
  let decomposition := Curve.Event.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := Dense.Rational.Bounds.Horner.evalSqBound cofactor
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have sourceBound := (source_factor_eval_sq_request_le leaf) epsilon
    positive
    parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient analysis * epsilon ^ 2) *
          cofactorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct (cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient_nonneg analysis)
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
    (Curve.Event.Profile.Residual.Lift.sourceFactorResidualCoefficient analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

end ProfileEventLeaf

/-- Coefficient after lifting the profile event through both cleared curve
coordinates of the original Gaussian polynomial. -/
@[expose] def clearedProfileResidualCoefficient
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
      Fraction.Rational :=
  profileGCDResidualCoefficient analysis *
    EventLeaf.curveGCDLiftCoefficient
      p chart

/-- The original denominator-cleared coordinate residual coefficient lifted from this profile is nonnegative. -/
theorem clearedProfileResidualCoefficient_nonneg
    (analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
    0 ≤ clearedProfileResidualCoefficient analysis :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (profileGCDResidualCoefficient_nonneg analysis)
    (EventLeaf.curveGCDLiftCoefficient_nonneg
      p chart)

namespace ProfileEventLeaf

/-- Both denominator-cleared coordinate residuals of the original polynomial
are uniformly small throughout the requested profile event. -/
theorem
  cleared_coordinate_norm_sq_request_le
    {analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis}
    (leaf : SourcePersistentProfileResidualProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (Curve.Substitution.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (Curve.Substitution.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
  let real := Curve.Substitution.realPolynomial p
    chart.parameterization.curve
  let imaginary := Curve.Substitution.imaginaryPolynomial p
    chart.parameterization.curve
  let common := Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve
  let left := Dense.GCD.leftFactor real imaginary
  let right := Dense.GCD.rightFactor real imaginary
  let liftBound :=
    EventLeaf.curveGCDLiftCoefficient
      p chart
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, common] using
      (gcd_eval_sq_request_le leaf) epsilon positive parameter inside
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
      EventLeaf.curveGCDLiftCoefficient] using
        Fraction.Order.Arithmetic.add_le_add_direct leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * epsilon ^ 2) *
          liftBound :=
    Fraction.Order.Arithmetic.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (Fraction.Order.Arithmetic.sq_nonneg_direct (left.eval parameter))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (right.eval parameter)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient_nonneg analysis)
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
    (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, Semiring.Normalization.product_pow, Semiring.Normalization.product_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * epsilon ^ 2) *
        liftBound := productBound
    _ = (Curve.Event.Profile.Residual.Lift.profileGCDResidualCoefficient analysis * liftBound) *
        epsilon ^ 2 := by ring1

/-- Gaussian form of `cleared_coordinate_norm_sq_request_le`. -/
theorem normSq_clearedEval_request_le
    {analysis : SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis}
    (leaf : SourcePersistentProfileResidualProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearedEval p
          chart.parameterization.curve).eval
            (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
      Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
  simpa only [-eq_self, -iff_self, Curve.Substitution.realPolynomial,
    Curve.Substitution.imaginaryPolynomial,
    Curve.clearedReal,
    Curve.clearedImag,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Data.Gaussian.Norm.Basic.normSq] using
      (cleared_coordinate_norm_sq_request_le leaf) epsilon positive
        parameter
        inside

end ProfileEventLeaf

/-- Coefficient converting the homogeneous profile residual into an
original-polynomial residual at affine chart points in `targetBox`. -/
@[expose] def affineProfileResidualCoefficient
    {targetBox : Box} (analysis :
      SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
    Fraction.Rational :=
  clearedProfileResidualCoefficient analysis /
    chart.affineDenominatorPowerNormSqLower p targetBox

/-- The original affine profile residual coefficient is nonnegative because the retained denominator-power lower bound
is positive. -/
theorem affineProfileResidualCoefficient_nonneg
    {targetBox : Box} (analysis :
      SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :
    0 ≤ affineProfileResidualCoefficient (targetBox := targetBox) analysis :=
  Fraction.Order.Field.div_nonneg_direct
    (clearedProfileResidualCoefficient_nonneg analysis)
    (chart.affineDenominatorPowerNormSqLower_pos p targetBox).le

namespace ProfileEventLeaf

/-- Every affine point where the requested profile event meets a displayed
box has a uniformly small original-polynomial residual. -/
theorem
  normSq_eval_point_request_le_of_inside
    {targetBox : Box} {analysis :
      SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis}
    (leaf : SourcePersistentProfileResidualProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (parameter : Fraction.Rational)
    (parameterInside :
      (leaf.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      Curve.Event.Profile.Residual.Lift.affineProfileResidualCoefficient (targetBox := targetBox) analysis *
        epsilon ^ 2 := open Purelib.Algebra.Field in by
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
  have clearedBound := (normSq_clearedEval_request_le leaf) epsilon
    positive
    parameter parameterInside
  have semantics := Curve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      Data.Gaussian.Norm.Basic.normSq power * residual ≤
        Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [-eq_self, -iff_self, curve, power, residual, semantics,
      Gaussian.Norm.Basic.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      Data.Gaussian.Norm.Basic.normSq power * residual :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct powerLower
      (Gaussian.Norm.Basic.normSq_nonneg _)
  change residual ≤
    (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis * epsilon ^ 2) /
          lower := by
      apply (Fraction.Order.Field.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          Fraction.Field.mul_comm _ _
        _ ≤ Data.Gaussian.Norm.Basic.normSq power * residual :=
          lowerProductBound
        _ ≤ Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis * epsilon ^ 2 :=
          clearedProductBound
    _ = (Curve.Event.Profile.Residual.Lift.clearedProfileResidualCoefficient analysis / lower) *
        epsilon ^ 2 := by
      simp only [-eq_self, -iff_self, ExplicitField.div_eq_mul_inv]
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.mul_comm (epsilon ^ 2),
        ← Fraction.Field.mul_assoc]

end ProfileEventLeaf

end Profile

end Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift

end
