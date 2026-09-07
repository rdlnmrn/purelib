import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Charts
import mathlib.RFAP.ConstructiveFiniteRoots
import RFAP.Isolation.SafeCandidates

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace CCL.CCLChartNondegenerate

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev CurveSource := CCL.CCLBoundaryDescription.CurveSource
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

namespace RationalCurve

/-- The two finite facts needed from a genuine affine chart. -/
structure Nondegenerate (curve : RationalCurve) : Prop where
  denominatorNormNonzero :
    (CCL.CurveBoxConditions.denominatorNormSq curve).isZero = false
  pointInjective : ∀ {left right : Coordinate},
    curve.denominatorAt left ≠ 0 → curve.denominatorAt right ≠ 0 →
      curve.point left = curve.point right → left = right

end RationalCurve

private theorem denominator_zero_unique
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {left right : Gaussian}
    (leftZero : CCL.RawParser.denominator matrix left = 0)
    (rightZero : CCL.RawParser.denominator matrix right = 0) :
    left = right := by
  by_cases lowerLeftZero : matrix.c = 0
  · have lowerRightZero : matrix.d = 0 := by
      change matrix.c * left + matrix.d = 0 at leftZero
      rw [lowerLeftZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add] at leftZero
      exact leftZero
    apply (determinantNonzero ?_).elim
    simp only [CCL.CCLPullback.determinant,
      CCL.Chordal.Mat2.det, lowerLeftZero, lowerRightZero,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_self]
  · have leftProduct : matrix.c * left = -matrix.d := by
      change matrix.c * left + matrix.d = 0 at leftZero
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re leftZero
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_re] at real ⊢
        calc
          (matrix.c * left).re =
              (matrix.c * left).re + matrix.d.re - matrix.d.re := by ring1
          _ = -matrix.d.re := by rw [real]; ring1
      · have imaginary := congrArg RFAP.ConstructiveGaussian.Gaussian.im leftZero
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.zero_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] at imaginary ⊢
        calc
          (matrix.c * left).im =
              (matrix.c * left).im + matrix.d.im - matrix.d.im := by ring1
          _ = -matrix.d.im := by rw [imaginary]; ring1
    have rightProduct : matrix.c * right = -matrix.d := by
      change matrix.c * right + matrix.d = 0 at rightZero
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re rightZero
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_re] at real ⊢
        calc
          (matrix.c * right).re =
              (matrix.c * right).re + matrix.d.re - matrix.d.re := by ring1
          _ = -matrix.d.re := by rw [real]; ring1
      · have imaginary := congrArg RFAP.ConstructiveGaussian.Gaussian.im rightZero
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.zero_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] at imaginary ⊢
        calc
          (matrix.c * right).im =
              (matrix.c * right).im + matrix.d.im - matrix.d.im := by ring1
          _ = -matrix.d.im := by rw [imaginary]; ring1
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne lowerLeftZero
    calc
      left * matrix.c = matrix.c * left :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = -matrix.d := leftProduct
      _ = matrix.c * right := rightProduct.symm
      _ = right * matrix.c :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

private theorem transformedDenominator_eq
    (matrix : Mat2) (source : RationalCurve) (parameter : Coordinate)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0) :
    (source.transform
      (CCL.CCLPullback.adjugate matrix)).denominatorAt parameter =
        CCL.RawParser.denominator
            (CCL.CCLPullback.adjugate matrix)
            (source.point parameter) * source.denominatorAt parameter :=
  CCL.RationalCurve.RationalCurve.denominatorAt_transform_eq
    (CCL.CCLPullback.adjugate matrix) source parameter
      sourceDenominatorNonzero

private theorem adjugateDenominator_ne_of_transformed
    (matrix : Mat2) (source : RationalCurve) (parameter : Coordinate)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (transformedDenominatorNonzero :
      (source.transform
        (CCL.CCLPullback.adjugate matrix)).denominatorAt
          parameter ≠ 0) :
    CCL.RawParser.denominator
        (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) ≠ 0 := by
  intro zero
  apply transformedDenominatorNonzero
  rw [transformedDenominator_eq matrix source parameter
    sourceDenominatorNonzero, zero,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul]

private theorem transformed_point_injective
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point)
    {left right : Coordinate}
    (leftDenominator :
      (source.transform
        (CCL.CCLPullback.adjugate matrix)).denominatorAt left ≠ 0)
    (rightDenominator :
      (source.transform
        (CCL.CCLPullback.adjugate matrix)).denominatorAt right ≠ 0)
    (equal :
      (source.transform
          (CCL.CCLPullback.adjugate matrix)).point left =
        (source.transform
          (CCL.CCLPullback.adjugate matrix)).point right) :
    left = right := by
  have leftAdjugate := adjugateDenominator_ne_of_transformed matrix source left
    (sourceTotal left) leftDenominator
  have rightAdjugate := adjugateDenominator_ne_of_transformed matrix source right
    (sourceTotal right) rightDenominator
  have imageEqual :
      CCL.RawParser.homographic
          (CCL.CCLPullback.adjugate matrix) (source.point left) =
        CCL.RawParser.homographic
          (CCL.CCLPullback.adjugate matrix)
            (source.point right) := by
    rw [← CCL.RationalCurve.RationalCurve.point_transform
          (CCL.CCLPullback.adjugate matrix) source left
            (sourceTotal left) leftAdjugate,
      ← CCL.RationalCurve.RationalCurve.point_transform
          (CCL.CCLPullback.adjugate matrix) source right
            (sourceTotal right) rightAdjugate]
    exact equal
  apply sourceInjective
  apply CCL.RawParserSemantics.homographic_injective
    (CCL.CCLPullback.adjugate matrix)
  · change CCL.CCLPullback.determinant
      (CCL.CCLPullback.adjugate matrix) ≠ 0
    rw [CCL.CCLPullback.determinant_adjugate]
    exact determinantNonzero
  · exact leftAdjugate
  · exact rightAdjugate
  · exact imageEqual

private theorem transformed_denominators_not_both_zero
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point) :
    ¬ ((source.transform
          (CCL.CCLPullback.adjugate matrix)).denominatorAt 0 = 0 ∧
       (source.transform
          (CCL.CCLPullback.adjugate matrix)).denominatorAt 1 = 0) := by
  rintro ⟨zeroAtZero, zeroAtOne⟩
  have adjugateZeroAtZero :
      CCL.RawParser.denominator
          (CCL.CCLPullback.adjugate matrix) (source.point 0) = 0 := by
    by_cases nonzero : CCL.RawParser.denominator
        (CCL.CCLPullback.adjugate matrix) (source.point 0) ≠ 0
    · exact (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct nonzero
        (sourceTotal 0) (by
          rw [← transformedDenominator_eq matrix source 0 (sourceTotal 0)]
          exact zeroAtZero)).elim
    · by_cases zero : CCL.RawParser.denominator
          (CCL.CCLPullback.adjugate matrix) (source.point 0) = 0
      · exact zero
      · exact (nonzero zero).elim
  have adjugateZeroAtOne :
      CCL.RawParser.denominator
          (CCL.CCLPullback.adjugate matrix) (source.point 1) = 0 := by
    by_cases nonzero : CCL.RawParser.denominator
        (CCL.CCLPullback.adjugate matrix) (source.point 1) ≠ 0
    · exact (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct nonzero
        (sourceTotal 1) (by
          rw [← transformedDenominator_eq matrix source 1 (sourceTotal 1)]
          exact zeroAtOne)).elim
    · by_cases zero : CCL.RawParser.denominator
          (CCL.CCLPullback.adjugate matrix) (source.point 1) = 0
      · exact zero
      · exact (nonzero zero).elim
  have sourcePointsEqual := denominator_zero_unique
    (CCL.CCLPullback.adjugate matrix) (by
      rw [CCL.CCLPullback.determinant_adjugate]
      exact determinantNonzero) adjugateZeroAtZero adjugateZeroAtOne
  have parametersEqual : (0 : Coordinate) = 1 :=
    sourceInjective sourcePointsEqual
  exact (show (0 : Coordinate) ≠ 1 by decide) parametersEqual

private theorem transformed_nondegenerate
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (sourceInjective : Function.Injective source.point) :
    RationalCurve.Nondegenerate
      (source.transform (CCL.CCLPullback.adjugate matrix)) := by
  let curve := source.transform (CCL.CCLPullback.adjugate matrix)
  have notBothZero := transformed_denominators_not_both_zero matrix
    determinantNonzero source sourceTotal sourceInjective
  refine
    { denominatorNormNonzero := ?_
      pointInjective := ?_ }
  · by_cases nonzero :
        (CCL.CurveBoxConditions.denominatorNormSq curve).isZero =
          false
    · exact nonzero
    · have zero :
          (CCL.CurveBoxConditions.denominatorNormSq curve).isZero =
            true := by
        cases value :
            (CCL.CurveBoxConditions.denominatorNormSq curve).isZero <;>
          simp_all
      have zeroAt (parameter : Coordinate) : curve.denominatorAt parameter = 0 := by
        apply normSq_eq_zero.mp
        rw [← CCL.CurveBoxConditions.eval_denominatorNormSq]
        exact eval_eq_zero_of_isZero zero parameter
      exact (notBothZero ⟨zeroAt 0, zeroAt 1⟩).elim
  · intro left right leftDenominator rightDenominator equal
    exact transformed_point_injective matrix determinantNonzero source
      sourceTotal sourceInjective leftDenominator rightDenominator equal

namespace BoundedChart

def Nondegenerate {form : HermitianForm} (chart : BoundedChart form) : Prop :=
  RationalCurve.Nondegenerate chart.parameterization.curve

end BoundedChart

/-- Every chart emitted by the complete bounded source family is genuinely
nondegenerate.  Radius-zero norm comparisons were classified as finite
singleton boundaries before reaching this function. -/
theorem nondegenerate_of_mem_charts
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form)
    (box : RFAP.Boxes.Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (chart : BoundedChart form)
    (member : chart ∈ CCL.CCLBoundaryCharts.charts source box
      denominatorMargin marginPositive) :
    chart.Nondegenerate := by
  cases source with
  | norm matrix determinantNonzero lowerRow base baseNonzero form_eq =>
      subst form
      simp only [CCL.CCLBoundaryCharts.charts, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with primary | reciprocal
      · subst chart
        exact transformed_nondegenerate matrix determinantNonzero
          (CCL.CanonicalCurves.circle base)
          (CCL.CanonicalCurves.circle_denominator_ne base)
          (CCL.CanonicalCurves.circle_point_injective base
            baseNonzero)
      · subst chart
        exact transformed_nondegenerate matrix determinantNonzero
          (CCL.CanonicalCurves.reciprocalCircle base)
          (CCL.CanonicalCurves.reciprocalCircle_denominator_ne base)
          (CCL.CanonicalCurves.reciprocalCircle_point_injective
            base baseNonzero)
  | real matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      simp only [CCL.CCLBoundaryCharts.charts, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst chart
      exact transformed_nondegenerate matrix determinantNonzero
        (CCL.CanonicalCurves.realLine threshold)
        (CCL.CanonicalCurves.realLine_denominator_ne threshold)
        (CCL.CanonicalCurves.realLine_point_injective threshold)
  | imaginary matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      simp only [CCL.CCLBoundaryCharts.charts, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst chart
      exact transformed_nondegenerate matrix determinantNonzero
        (CCL.CanonicalCurves.imaginaryLine threshold)
        (CCL.CanonicalCurves.imaginaryLine_denominator_ne threshold)
        (CCL.CanonicalCurves.imaginaryLine_point_injective threshold)

private theorem unitIntervalProper (index : Nat) :
    (index : Coordinate) < (index : Coordinate) + 1 := by
  have added := RFAP.ConstructiveFraction.add_lt_add_left_direct
    (show (0 : Coordinate) < 1 by decide) (index : Coordinate)
  calc
    (index : Coordinate) = (index : Coordinate) + 0 := by ring1
    _ < (index : Coordinate) + 1 := added

private def safeParameter
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) (index : Nat) : Coordinate :=
  RFAP.SafeCandidates.centralSearchValue
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve)
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve).natDegree
    (a := (index : Coordinate)) (b := (index : Coordinate) + 1)
    (unitIntervalProper index) nondegenerate.denominatorNormNonzero (by rfl)

private theorem safeParameter_spec
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) (index : Nat) :
    chart.parameterization.curve.denominatorAt
        (safeParameter chart nondegenerate index) ≠ 0 ∧
      (index : Coordinate) < safeParameter chart nondegenerate index ∧
      safeParameter chart nondegenerate index < (index : Coordinate) + 1 := by
  change RationalCurve.Nondegenerate chart.parameterization.curve at nondegenerate
  have specification := RFAP.SafeCandidates.centralSearchValue_spec
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve)
    (CCL.CurveBoxConditions.denominatorNormSq
      chart.parameterization.curve).natDegree
    (a := (index : Coordinate)) (b := (index : Coordinate) + 1)
    (unitIntervalProper index) nondegenerate.denominatorNormNonzero (by rfl)
  refine ⟨?_, specification.2.1, specification.2.2⟩
  change chart.parameterization.curve.denominatorAt
      (RFAP.SafeCandidates.centralSearchValue
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve)
        (CCL.CurveBoxConditions.denominatorNormSq
          chart.parameterization.curve).natDegree
        (unitIntervalProper index) nondegenerate.denominatorNormNonzero
          (by rfl)) ≠ 0
  intro denominatorZero
  apply specification.1
  rw [CCL.CurveBoxConditions.eval_denominatorNormSq]
  exact congrArg normSq denominatorZero |>.trans normSq_zero

private theorem safeParameter_injective
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) :
    Function.Injective (safeParameter chart nondegenerate) := by
  apply StrictMono.injective
  intro left right less
  have leftBounds := safeParameter_spec chart nondegenerate left
  have rightBounds := safeParameter_spec chart nondegenerate right
  have separated :
      ((left + 1 : Nat) : Coordinate) ≤ (right : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct (Nat.succ_le_of_lt less)
  exact (leftBounds.2.2.trans_le separated).trans rightBounds.2.1

private theorem nodup_ofFn_direct {n : Nat} (f : Fin n → Gaussian)
    (injective : Function.Injective f) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.nodup_nil]
  | succ n inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_ofFn] at member
        rcases member with ⟨index, equal⟩
        have impossible : index.succ = (0 : Fin (n + 1)) :=
          injective equal
        exact Fin.succ_ne_zero index impossible
      · apply inductionHypothesis
        intro first second equal
        apply Fin.ext
        have values := congrArg Fin.val (injective equal)
        simp only [Fin.val_succ] at values
        exact Nat.add_right_cancel values

/-- Both denominator-cleared coordinates cannot vanish identically on an
active nondegenerate chart of a positive-degree displayed polynomial. -/
theorem not_identicallyZero
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) :
    ¬ ((CCL.CurveClear.realPolynomial p
          chart.parameterization.curve).isZero = true ∧
       (CCL.CurveClear.imaginaryPolynomial p
          chart.parameterization.curve).isZero = true) := by
  rintro ⟨realZero, imaginaryZero⟩
  have polynomialNonzero : p.isZero = false :=
    RFAP.GlobalWinding.isZero_false_of_natDegree_pos degreePositive
  let parameter : Fin (p.natDegree + 1) → Coordinate := fun index =>
    safeParameter chart nondegenerate index.val
  let point : Fin (p.natDegree + 1) → Gaussian := fun index =>
    chart.parameterization.curve.point (parameter index)
  have denominatorAt (index : Fin (p.natDegree + 1)) :
      chart.parameterization.curve.denominatorAt (parameter index) ≠ 0 :=
    (safeParameter_spec chart nondegenerate index.val).1
  have pointInjective : Function.Injective point := by
    intro left right equal
    apply Fin.ext
    apply safeParameter_injective chart nondegenerate
    exact nondegenerate.pointInjective (denominatorAt left)
      (denominatorAt right) equal
  let points := List.ofFn point
  have pointsNodup : points.Nodup := nodup_ofFn_direct point pointInjective
  have roots : ∀ value ∈ points, p.eval value = 0 := by
    intro value member
    change value ∈ List.ofFn point at member
    rw [List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    apply (CCL.RationalCurve.cleared_pair_zero_iff p
      chart.parameterization.curve (parameter index)
      (denominatorAt index)).1
    exact ⟨eval_eq_zero_of_isZero realZero (parameter index),
      eval_eq_zero_of_isZero imaginaryZero (parameter index)⟩
  have tooMany := RFAP.ConstructiveFiniteRoots.nodup_zeros_length_lt_degreeCount
    p polynomialNonzero points pointsNodup roots
  rw [QuotientFreeList.length_ofFn,
    natDegree_add_one_eq_degreeCount polynomialNonzero] at tooMany
  exact Nat.lt_irrefl p.degreeCount tooMany

end CCL.CCLChartNondegenerate
