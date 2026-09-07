import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.ProfileBoundaryEvents

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

namespace CCL.PersistentCCLProfileResidual

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev ProfileAnalysis
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :=
  CCL.PersistentCCLConditionProfiles.ProfileAnalysis
    factorAnalysis
abbrev ProfileEventLeaf
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :=
  CCL.PersistentCCLConditionProfiles.ProfileEventLeaf analysis
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary
abbrev BoundaryProfileEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
    boundary

section Profile

variable {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
variable {chart : BoundedChart form}
variable {data : CCL.CurveEvents.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : SquarefreeFactorAnalysis p box chart data
  gcdDegreePositive}

/-- Coefficient obtained by lifting the profile-factor residual through its
displayed cofactor in the source squarefree factor. -/
def sourceFactorResidualCoefficient
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
      analysis *
    RFAP.PathClearance.evalSqBound analysis.profile.cofactor
      chart.cell.interval

theorem sourceFactorResidualCoefficient_nonneg
    (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ sourceFactorResidualCoefficient analysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
      analysis)
    (RFAP.PathClearance.evalSqBound_nonneg
      analysis.profile.cofactor chart.cell.interval)

namespace ProfileEventLeaf

/-- The original squarefree factor containing this profile is uniformly
small throughout the requested profile event. -/
theorem source_factor_eval_sq_request_le
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      sourceFactorResidualCoefficient analysis * epsilon ^ 2 := by
  let cofactorBound := RFAP.PathClearance.evalSqBound
    analysis.profile.cofactor chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have profileBound := leaf.factor_eval_sq_request_le epsilon positive
    parameter inside
  have cofactorEvalBound : analysis.profile.cofactor.eval parameter ^ 2 ≤
      cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound
      analysis.profile.cofactor chart.cell.interval parameterInsideChart
  have productBound :
      analysis.profile.factor.polynomial.eval parameter ^ 2 *
          analysis.profile.cofactor.eval parameter ^ 2 ≤
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
            analysis * epsilon ^ 2) * cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct profileBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (analysis.profile.cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have identity : factorAnalysis.factor.polynomial.eval parameter =
      analysis.profile.factor.polynomial.eval parameter *
        analysis.profile.cofactor.eval parameter :=
    CCL.CoordinateFactorization.eval_factorization
      analysis.profile.factorization parameter
  rw [identity, mul_pow]
  change analysis.profile.factor.polynomial.eval parameter ^ 2 *
      analysis.profile.cofactor.eval parameter ^ 2 ≤
    (CCL.PersistentCCLConditionProfiles.ProfileEventLeaf.factorResidualCoefficient
        analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

end ProfileEventLeaf

/-- Coefficient obtained after multiplying the source squarefree factor by
the explicitly computed product of all other curve-gcd factors. -/
def profileGCDResidualCoefficient
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  sourceFactorResidualCoefficient analysis *
    RFAP.PathClearance.evalSqBound
      (CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDCofactor
        factorAnalysis) chart.cell.interval

theorem profileGCDResidualCoefficient_nonneg
    (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ profileGCDResidualCoefficient analysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (sourceFactorResidualCoefficient_nonneg analysis)
    (RFAP.PathClearance.evalSqBound_nonneg
      (CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDCofactor
        factorAnalysis) chart.cell.interval)

namespace ProfileEventLeaf

/-- The complete real/imaginary curve gcd is uniformly small throughout the
requested profile event. -/
theorem gcd_eval_sq_request_le
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      profileGCDResidualCoefficient analysis * epsilon ^ 2 := by
  let decomposition := CCL.CurveEvents.eventDecomposition data
    gcdDegreePositive
  let cofactor :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDCofactor
      factorAnalysis
  let cofactorBound := RFAP.PathClearance.evalSqBound cofactor
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have sourceBound := leaf.source_factor_eval_sq_request_le epsilon positive
    parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (sourceFactorResidualCoefficient analysis * epsilon ^ 2) *
          cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct sourceBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (sourceFactorResidualCoefficient_nonneg analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have identity :
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
        factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
    calc
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
          (CCL.CoordinateFactorization.factorProduct
            decomposition.factors).eval parameter :=
        decomposition.evalIdentity parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          (CCL.CoordinateFactorization.factorCofactor
            factorAnalysis.factor.polynomial decomposition.factors).eval
              parameter :=
        CCL.CoordinateFactorization.factorProduct_eval_eq_factor_mul_cofactor
          factorAnalysis.factor decomposition.factors factorAnalysis.member
            parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by rfl
  rw [identity, mul_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (sourceFactorResidualCoefficient analysis * cofactorBound) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

end ProfileEventLeaf

/-- Coefficient after lifting the profile event through both cleared curve
coordinates of the original Gaussian polynomial. -/
def clearedProfileResidualCoefficient
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  profileGCDResidualCoefficient analysis *
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient
      p chart

theorem clearedProfileResidualCoefficient_nonneg
    (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ clearedProfileResidualCoefficient analysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (profileGCDResidualCoefficient_nonneg analysis)
    (CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient_nonneg
      p chart)

namespace ProfileEventLeaf

/-- Both denominator-cleared coordinate residuals of the original polynomial
are uniformly small throughout the requested profile event. -/
theorem cleared_coordinate_norm_sq_request_le
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (CCL.CurveClear.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (CCL.CurveClear.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
  let real := CCL.CurveClear.realPolynomial p
    chart.parameterization.curve
  let imaginary := CCL.CurveClear.imaginaryPolynomial p
    chart.parameterization.curve
  let common := CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve
  let left := RFAP.ComputableGCD.leftFactor real imaginary
  let right := RFAP.ComputableGCD.rightFactor real imaginary
  let liftBound :=
    CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient
      p chart
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      profileGCDResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [common] using
      leaf.gcd_eval_sq_request_le epsilon positive parameter inside
  have leftEvalBound : left.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound left chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound left
      chart.cell.interval parameterInsideChart
  have rightEvalBound : right.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound right chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound right
      chart.cell.interval parameterInsideChart
  have cofactorSumBound :
      left.eval parameter ^ 2 + right.eval parameter ^ 2 ≤ liftBound := by
    simpa only [left, right, real, imaginary, liftBound,
      CCL.PersistentCCLCurveEvents.EventLeaf.curveGCDLiftCoefficient] using
        add_le_add leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (profileGCDResidualCoefficient analysis * epsilon ^ 2) *
          liftBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left.eval parameter))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (right.eval parameter)))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (profileGCDResidualCoefficient_nonneg analysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [real, imaginary, common, left,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [real, imaginary, common, right,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (profileGCDResidualCoefficient analysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, mul_pow, mul_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (profileGCDResidualCoefficient analysis * epsilon ^ 2) *
        liftBound := productBound
    _ = (profileGCDResidualCoefficient analysis * liftBound) *
        epsilon ^ 2 := by ring1

/-- Gaussian form of `cleared_coordinate_norm_sq_request_le`. -/
theorem normSq_clearedEval_request_le
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.RationalCurve.clearedEval p
          chart.parameterization.curve).eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
      clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
  simpa only [CCL.CurveClear.realPolynomial,
    CCL.CurveClear.imaginaryPolynomial,
    CCL.RationalCurve.clearedReal,
    CCL.RationalCurve.clearedImag,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    RFAP.ConstructiveGaussian.Gaussian.normSq] using
      leaf.cleared_coordinate_norm_sq_request_le epsilon positive parameter
        inside

end ProfileEventLeaf

/-- Coefficient converting the homogeneous profile residual into an
original-polynomial residual at affine chart points in `targetBox`. -/
def affineProfileResidualCoefficient
    {targetBox : Box} (analysis : ProfileAnalysis factorAnalysis) :
    Coordinate :=
  clearedProfileResidualCoefficient analysis /
    chart.affineDenominatorPowerNormSqLower p targetBox

theorem affineProfileResidualCoefficient_nonneg
    {targetBox : Box} (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ affineProfileResidualCoefficient (targetBox := targetBox) analysis :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (clearedProfileResidualCoefficient_nonneg analysis)
    (chart.affineDenominatorPowerNormSqLower_pos p targetBox).le

namespace ProfileEventLeaf

/-- Every affine point where the requested profile event meets a displayed
box has a uniformly small original-polynomial residual. -/
theorem normSq_eval_point_request_le_of_inside
    {targetBox : Box} {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (parameterInside :
      (leaf.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      affineProfileResidualCoefficient (targetBox := targetBox) analysis *
        epsilon ^ 2 := by
  let curve := chart.parameterization.curve
  let power :=
    (CCL.RationalCurve.clearingState p curve).denominatorPower.eval
      (RFAP.PathPolynomial.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := RFAP.ConstructiveGaussian.Gaussian.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power := by
    simpa only [lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound := leaf.normSq_clearedEval_request_le epsilon positive
    parameter parameterInside
  have semantics := CCL.RationalCurve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual ≤
        clearedProfileResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [curve, power, residual, semantics,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct powerLower
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
  change residual ≤
    (clearedProfileResidualCoefficient analysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (clearedProfileResidualCoefficient analysis * epsilon ^ 2) /
          lower := by
      apply (RFAP.ConstructiveFraction.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
          lowerProductBound
        _ ≤ clearedProfileResidualCoefficient analysis * epsilon ^ 2 :=
          clearedProductBound
    _ = (clearedProfileResidualCoefficient analysis / lower) *
        epsilon ^ 2 := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm (epsilon ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

end ProfileEventLeaf

end Profile

section Boundary

variable {p : GaussianPolynomial} {reference : Mat2} {current : Box}
variable {denominatorMargin : Coordinate}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : CCL.CCLFormula.Atom}
variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}

namespace BoundaryProfileEventEntry

/-- Coefficient-computable original-polynomial residual bound for portions
of this condition-profile boundary event lying in a displayed affine box. -/
def affineResidualCoefficient
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) : Coordinate :=
  affineProfileResidualCoefficient (targetBox := targetBox) entry.event.1

theorem affineResidualCoefficient_nonneg
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) : 0 ≤ affineResidualCoefficient entry targetBox :=
  affineProfileResidualCoefficient_nonneg
    (targetBox := targetBox) entry.event.1

/-- Every affine meeting of a requested profile event with `targetBox` has a
uniformly small original-polynomial residual. -/
theorem normSq_eval_point_requestAt_le_of_inside
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (targetBox : Box) (epsilon : Coordinate) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (parameterInside :
      (entry.requestAt epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.parent.chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (entry.parent.chart.parameterization.curve.point parameter)) ≤
      affineResidualCoefficient entry targetBox * epsilon ^ 2 :=
  ProfileEventLeaf.normSq_eval_point_request_le_of_inside entry.event.2
    epsilon positive parameter parameterInside denominatorNonzero pointInside

/-- The explicit residual budget at the same request used for profile signs
and separated-region ownership. -/
def combinedAffineResidualBudget
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) : Coordinate :=
  affineResidualCoefficient entry targetBox *
    CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
      entry boxes pairwise ^ 2

theorem combinedAffineResidualBudget_nonneg
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) :
    0 ≤ combinedAffineResidualBudget entry boxes pairwise targetBox :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (affineResidualCoefficient_nonneg entry targetBox)
    (RFAP.ConstructiveFraction.sq_nonneg_direct
      (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
        entry boxes pairwise))

/-- Event-wide original-polynomial residual bound at the shared finite
sign-and-ownership request. -/
theorem normSq_eval_point_combined_le_of_inside
    (entry :
      CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
        boundary)
    (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (targetBox : Box) (parameter : Coordinate)
    (parameterInside :
      (entry.requestAt
        (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
          entry boxes pairwise)).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.parent.chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (entry.parent.chart.parameterization.curve.point parameter)) ≤
      combinedAffineResidualBudget entry boxes pairwise targetBox :=
  normSq_eval_point_requestAt_le_of_inside entry targetBox
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
      entry boxes pairwise)
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth_pos
      entry boxes pairwise)
    parameter parameterInside denominatorNonzero pointInside

end BoundaryProfileEventEntry

/-! ## Executable sampling and ownership at the combined request -/

/-- A denominator-safe rational parameter computed inside one requested
condition-profile event interval. -/
structure NonpoleProfileRequestSample
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Coordinate) where
  parameter : Coordinate
  parameterInside :
    (entry.requestAt epsilon).cell.interval.Contains parameter
  denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0

/-- Bounded interior search for a non-pole rational parameter in any profile
request.  Only the chart's displayed nondegeneracy certificate is used. -/
def nonpoleProfileRequestSample
    (entry : BoundaryProfileEventEntry boundary) (epsilon : Coordinate) :
    NonpoleProfileRequestSample entry epsilon := by
  let curve := entry.parent.chart.parameterization.curve
  let interval := (entry.requestAt epsilon).cell.interval
  let denominatorPolynomial :=
    CCL.CurveBoxConditions.denominatorNormSq curve
  have chartMember :=
    CCL.PersistentCCLCurveClear.chart_mem_of_analysis_mem
      boundary entry.parent.analysisMember
  have nondegenerate :=
    CCL.CCLChartNondegenerate.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive
        entry.parent.chart chartMember
  have intervalProper : interval.lower < interval.upper := by
    simpa only [interval] using (entry.requestAt epsilon).cell.proper
  let parameter := RFAP.SafeCandidates.interiorSearchValue
    denominatorPolynomial denominatorPolynomial.natDegree intervalProper
      nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  have specification :=
    RFAP.SafeCandidates.interiorSearchValue_spec
      denominatorPolynomial denominatorPolynomial.natDegree intervalProper
        nondegenerate.denominatorNormNonzero (Nat.le_refl _)
  exact
    { parameter := parameter
      parameterInside := ⟨specification.2.1.le, specification.2.2.le⟩
      denominatorNonzero := by
        intro denominatorZero
        apply specification.1
        change denominatorPolynomial.eval parameter = 0
        rw [show denominatorPolynomial.eval parameter =
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (curve.denominatorAt parameter) by
              exact CCL.CurveBoxConditions.eval_denominatorNormSq
                curve parameter,
          denominatorZero,
          RFAP.ConstructiveGaussian.Gaussian.normSq_zero] }

/-- Total result of classifying one displayed non-pole profile sample against
the complete finite family of separated boxes. -/
inductive CombinedProfileSampleClassification
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (sample : NonpoleProfileRequestSample entry
      (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
        entry boxes pairwise)) where
  | meeting
      (owner :
        CCL.PersistentCCLProfileBoundaryEvents.CombinedProfileRequestMeeting
          entry boxes pairwise)
  | outside (proof : ∀ index : Fin boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.chart.parameterization.curve.point sample.parameter))

/-- Execute every finite box-membership comparison for a displayed combined-
request profile sample. -/
def classifyCombinedProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (sample : NonpoleProfileRequestSample entry
      (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
        entry boxes pairwise)) :
    CombinedProfileSampleClassification entry boxes pairwise sample := by
  let point :=
    entry.parent.chart.parameterization.curve.point sample.parameter
  match found :
      CCL.PersistentCCLRegionOwnership.findContainingBoxIndex
        boxes point with
  | some index =>
      exact .meeting
        { index := index
          parameter := sample.parameter
          parameterInside := sample.parameterInside
          denominatorNonzero := sample.denominatorNonzero
          pointInside :=
            CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_sound
              boxes point index found }
  | none =>
      exact .outside
        (CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_none
          boxes point found)

/-- Fully computed non-pole sample and finite owner/outside classification
for the shared sign-and-separation request. -/
structure RequestedCombinedProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) where
  sample : NonpoleProfileRequestSample entry
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
      entry boxes pairwise)
  classification :
    CombinedProfileSampleClassification entry boxes pairwise sample

def classifyRequestedCombinedProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right) :
    RequestedCombinedProfileSample entry boxes pairwise :=
  let sample := nonpoleProfileRequestSample entry
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
      entry boxes pairwise)
  { sample := sample
    classification := classifyCombinedProfileSample entry boxes pairwise
      sample }

namespace CombinedProfileRequestMeeting

/-- Every explicit owner meeting at the combined request carries the new
event-wide original-polynomial residual bound in its owning box. -/
theorem residual_le
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (meeting :
      CCL.PersistentCCLProfileBoundaryEvents.CombinedProfileRequestMeeting
        entry boxes pairwise) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.chart.parameterization.curve.point
          meeting.parameter)) ≤
      BoundaryProfileEventEntry.combinedAffineResidualBudget entry boxes
        pairwise (boxes.get meeting.index) :=
  BoundaryProfileEventEntry.normSq_eval_point_combined_le_of_inside entry
    boxes pairwise (boxes.get meeting.index) meeting.parameter
      meeting.parameterInside meeting.denominatorNonzero meeting.pointInside

end CombinedProfileRequestMeeting

/-! ## One request below a supplied residual target in every possible owner -/

/-- Positive request width making the affine profile residual coefficient for
one displayed box smaller than `target`. -/
def boxResidualRequestWidth
    (entry : BoundaryProfileEventEntry boundary) (targetBox : Box)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth
    (BoundaryProfileEventEntry.affineResidualCoefficient entry targetBox)
    target

theorem boxResidualRequestWidth_pos
    (entry : BoundaryProfileEventEntry boundary) (targetBox : Box)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < boxResidualRequestWidth entry targetBox target :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
    (BoundaryProfileEventEntry.affineResidualCoefficient_nonneg entry
      targetBox) targetPositive

/-- Every possible owner box contributes one executable residual width. -/
def profileResidualRequestWidths
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (target : Coordinate) : List Coordinate :=
  boxes.map fun targetBox => boxResidualRequestWidth entry targetBox target

theorem profileResidualRequestWidth_mem
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (target : Coordinate) (index : Fin boxes.length) :
    boxResidualRequestWidth entry (boxes.get index) target ∈
      profileResidualRequestWidths entry boxes target :=
  QuotientFreeList.mem_map.mpr ⟨boxes.get index, List.get_mem boxes index, rfl⟩

theorem profileResidualRequestWidths_positive
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    {target : Coordinate} (targetPositive : 0 < target) :
    ∀ width ∈ profileResidualRequestWidths entry boxes target, 0 < width := by
  intro width member
  rw [profileResidualRequestWidths, QuotientFreeList.mem_map] at member
  rcases member with ⟨targetBox, _targetBoxMember, rfl⟩
  exact boxResidualRequestWidth_pos entry targetBox targetPositive

/-- A positive finite minimum below the residual width of every possible
owner box.  The empty family retains the harmless width `1`. -/
def profileResidualFamilyRequestWidth
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    (profileResidualRequestWidths entry boxes target)

theorem profileResidualFamilyRequestWidth_pos
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < profileResidualFamilyRequestWidth entry boxes target :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    (profileResidualRequestWidths_positive entry boxes targetPositive)

theorem profileResidualFamilyRequestWidth_le_box
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (target : Coordinate) (index : Fin boxes.length) :
    profileResidualFamilyRequestWidth entry boxes target ≤
      boxResidualRequestWidth entry (boxes.get index) target :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
    (profileResidualRequestWidth_mem entry boxes target index)

/-- One request width satisfying profile signs, pairwise region separation,
and the residual target in every possible owner box. -/
def controlledProfileRequestWidth
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) : Coordinate :=
  min
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
      entry boxes pairwise)
    (profileResidualFamilyRequestWidth entry boxes target)

theorem controlledProfileRequestWidth_pos
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < controlledProfileRequestWidth entry boxes pairwise target :=
  lt_min
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth_pos
      entry boxes pairwise)
    (profileResidualFamilyRequestWidth_pos entry boxes targetPositive)

theorem controlledProfileRequestWidth_le_combined
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth
        entry boxes pairwise :=
  min_le_left _ _

theorem controlledProfileRequestWidth_le_sign
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      CCL.PersistentCCLConditionProfiles.profileSignWidth
        entry.event.1 :=
  (controlledProfileRequestWidth_le_combined entry boxes pairwise target).trans
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth_le_sign
      entry boxes pairwise)

theorem controlledProfileRequestWidth_le_family
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) :
    controlledProfileRequestWidth entry boxes pairwise target ≤
      CCL.PersistentCCLProfileBoundaryEvents.profileFamilyRequestWidth
        entry boxes pairwise :=
  (controlledProfileRequestWidth_le_combined entry boxes pairwise target).trans
    (CCL.PersistentCCLProfileBoundaryEvents.combinedProfileRequestWidth_le_family
      entry boxes pairwise)

/-- At the controlled width, the affine residual budget is strictly below
the supplied positive target for every possible owner index. -/
theorem controlledProfileResidual_lt
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target)
    (index : Fin boxes.length) :
    BoundaryProfileEventEntry.affineResidualCoefficient entry
        (boxes.get index) *
      controlledProfileRequestWidth entry boxes pairwise target ^ 2 <
        target := by
  let controlled := controlledProfileRequestWidth entry boxes pairwise target
  let familyWidth := profileResidualFamilyRequestWidth entry boxes target
  let boxWidth := boxResidualRequestWidth entry (boxes.get index) target
  let coefficient := BoundaryProfileEventEntry.affineResidualCoefficient
    entry (boxes.get index)
  have controlledPositive : 0 < controlled := by
    simpa only [controlled] using
      controlledProfileRequestWidth_pos entry boxes pairwise targetPositive
  have controlledLeFamily : controlled ≤ familyWidth := by
    exact (min_le_right _ _)
  have familyLeBox : familyWidth ≤ boxWidth := by
    simpa only [familyWidth, boxWidth] using
      profileResidualFamilyRequestWidth_le_box entry boxes target index
  have squareOrder : controlled ^ 2 ≤ boxWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct controlledPositive.le
      (controlledLeFamily.trans familyLeBox) 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      BoundaryProfileEventEntry.affineResidualCoefficient_nonneg entry
        (boxes.get index)
  have scaled : coefficient * controlled ^ 2 ≤
      coefficient * boxWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative
  exact scaled.trans_lt (by
    simpa only [coefficient, boxWidth, boxResidualRequestWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative targetPositive)

/-- Exact affine profile classification at the controlled request width. -/
def classifyControlledProfileEventAffine
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target) :
    CCL.PersistentCCLConditionProfiles.ProfileEventAffineClassification
      entry.event.2
        (controlledProfileRequestWidth entry boxes pairwise target) :=
  CCL.PersistentCCLConditionProfiles.classifyProfileEventAffine
    entry.event.2 (controlledProfileRequestWidth entry boxes pairwise target)
      (controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      (controlledProfileRequestWidth_le_sign entry boxes pairwise target)

/-- The controlled request remains narrow enough to meet at most one member
of the separated family. -/
theorem controlledProfileRequest_not_spanning
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    {target : Coordinate} (targetPositive : 0 < target)
    (left right : Fin boxes.length) (different : left ≠ right) :
    ∀ {leftParameter rightParameter : Coordinate},
      (entry.requestAt
        (controlledProfileRequestWidth entry boxes pairwise target)).cell.interval.Contains
          leftParameter →
      (entry.requestAt
        (controlledProfileRequestWidth entry boxes pairwise target)).cell.interval.Contains
          rightParameter →
      entry.parent.chart.parameterization.curve.denominatorAt
        leftParameter ≠ 0 →
      entry.parent.chart.parameterization.curve.denominatorAt
        rightParameter ≠ 0 →
      (boxes.get left).Contains
        (entry.parent.chart.parameterization.curve.point leftParameter) →
      (boxes.get right).Contains
        (entry.parent.chart.parameterization.curve.point rightParameter) →
      False :=
  CCL.PersistentCCLProfileBoundaryEvents.profileRequest_not_spanning_of_le_family
    entry boxes pairwise
      (controlledProfileRequestWidth entry boxes pairwise target)
      (controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      (controlledProfileRequestWidth_le_family entry boxes pairwise target)
      left right different

/-- An explicit owner meeting at the single sign-, separation-, and
residual-controlled request. -/
structure ControlledProfileRequestMeeting
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) where
  index : Fin boxes.length
  parameter : Coordinate
  parameterInside : (entry.requestAt
    (controlledProfileRequestWidth entry boxes pairwise target)).cell.interval.Contains
      parameter
  denominatorNonzero :
    entry.parent.chart.parameterization.curve.denominatorAt parameter ≠ 0
  pointInside : (boxes.get index).Contains
    (entry.parent.chart.parameterization.curve.point parameter)

namespace ControlledProfileRequestMeeting

theorem index_unique
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (left right : ControlledProfileRequestMeeting entry boxes pairwise
      target) :
    left.index = right.index := by
  by_cases same : left.index = right.index
  · exact same
  · exact (controlledProfileRequest_not_spanning entry boxes pairwise
      targetPositive left.index right.index same left.parameterInside
      right.parameterInside left.denominatorNonzero right.denominatorNonzero
      left.pointInside right.pointInside).elim

/-- An owned displayed rational sample has original-polynomial residual
strictly below the caller's target. -/
theorem residual_lt
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    {target : Coordinate} (targetPositive : 0 < target)
    (meeting : ControlledProfileRequestMeeting entry boxes pairwise target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.chart.parameterization.curve.point
          meeting.parameter)) < target := by
  have upper :=
    BoundaryProfileEventEntry.normSq_eval_point_requestAt_le_of_inside
      entry (boxes.get meeting.index)
      (controlledProfileRequestWidth entry boxes pairwise target)
      (controlledProfileRequestWidth_pos entry boxes pairwise targetPositive)
      meeting.parameter meeting.parameterInside meeting.denominatorNonzero
      meeting.pointInside
  exact upper.trans_lt
    (controlledProfileResidual_lt entry boxes pairwise targetPositive
      meeting.index)

/-- At the squarefree derivative threshold, every owned event sample has a
nonzero polynomial derivative.  This is the finite Newton datum needed by the
next winding-one comparison; no polynomial root is inferred. -/
theorem derivative_ne_zero
    {ambient : Box} (squarefree : SquarefreeCertificate p)
    {entry : BoundaryProfileEventEntry boundary} {boxes : List Box}
    {pairwise : boxes.Pairwise fun left right => left.Separated right}
    (boxesRefine : ∀ index : Fin boxes.length,
      (boxes.get index).Refines ambient)
    (meeting : ControlledProfileRequestMeeting entry boxes pairwise
      (RFAP.LocalExtraction.derivativeThreshold squarefree
        ambient)) :
    (RFAP.ConstructiveGCD.derivative p).eval
        (entry.parent.chart.parameterization.curve.point
          meeting.parameter) ≠ 0 := by
  let point := entry.parent.chart.parameterization.curve.point
    meeting.parameter
  have pointInsideAmbient : ambient.Contains point :=
    (boxesRefine meeting.index).contains meeting.pointInside
  have residualSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval point) ≤
        RFAP.LocalExtraction.derivativeThreshold squarefree
          ambient :=
    (meeting.residual_lt
      (RFAP.LocalExtraction.derivativeThreshold_pos squarefree
        ambient)).le
  exact RFAP.LocalExtraction.derivative_ne_zero_of_small_residual
    squarefree ambient pointInsideAmbient residualSmall

end ControlledProfileRequestMeeting

/-- Total finite owner/outside result for one non-pole sample at the
residual-controlled request. -/
inductive ControlledProfileSampleClassification
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate)
    (sample : NonpoleProfileRequestSample entry
      (controlledProfileRequestWidth entry boxes pairwise target)) where
  | meeting
      (owner : ControlledProfileRequestMeeting entry boxes pairwise target)
  | outside (proof : ∀ index : Fin boxes.length,
      ¬(boxes.get index).Contains
        (entry.parent.chart.parameterization.curve.point sample.parameter))

def classifyControlledProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate)
    (sample : NonpoleProfileRequestSample entry
      (controlledProfileRequestWidth entry boxes pairwise target)) :
    ControlledProfileSampleClassification entry boxes pairwise target
      sample := by
  let point :=
    entry.parent.chart.parameterization.curve.point sample.parameter
  match found :
      CCL.PersistentCCLRegionOwnership.findContainingBoxIndex
        boxes point with
  | some index =>
      exact .meeting
        { index := index
          parameter := sample.parameter
          parameterInside := sample.parameterInside
          denominatorNonzero := sample.denominatorNonzero
          pointInside :=
            CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_sound
              boxes point index found }
  | none =>
      exact .outside
        (CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_none
          boxes point found)

/-- Fully computed sample/classification pair at the controlled request. -/
structure RequestedControlledProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) where
  sample : NonpoleProfileRequestSample entry
    (controlledProfileRequestWidth entry boxes pairwise target)
  classification : ControlledProfileSampleClassification entry boxes pairwise
    target sample

def classifyRequestedControlledProfileSample
    (entry : BoundaryProfileEventEntry boundary) (boxes : List Box)
    (pairwise : boxes.Pairwise fun left right => left.Separated right)
    (target : Coordinate) :
    RequestedControlledProfileSample entry boxes pairwise target :=
  let sample := nonpoleProfileRequestSample entry
    (controlledProfileRequestWidth entry boxes pairwise target)
  { sample := sample
    classification := classifyControlledProfileSample entry boxes pairwise
      target sample }

end Boundary

end CCL.PersistentCCLProfileResidual
