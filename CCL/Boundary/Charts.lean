import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Analysis
import CCL.Boundary.Curve.BoxEventPartition
import CCL.Boundary.Curve.ResidualClearance
import RFAP.Polynomial.Bounds
import CCL.Boundary.Curve.RationalBounds

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace CCL.CCLBoundaryCharts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev CurveSource := CCL.CCLBoundaryDescription.CurveSource
abbrev Parametrization := CCL.CCLBoundaryCurves.Parametrization
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Cell := RFAP.SturmEventPartition.Cell

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

namespace CurveSource

def matrix {reference : Mat2} {form : HermitianForm} :
    CurveSource reference form → Mat2
  | .norm matrix _ _ _ _ _ | .real matrix _ _ _ _ |
      .imaginary matrix _ _ _ _ => matrix

/-- Every source matrix has the same affine denominator as its displayed
reference matrix. -/
theorem denominator_eq_reference
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (value : Gaussian) :
    CCL.RawParser.denominator source.matrix value =
      CCL.RawParser.denominator reference value := by
  cases source with
  | norm matrix _ lowerRow _ _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]
  | real matrix _ lowerRow _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]
  | imaginary matrix _ lowerRow _ _ =>
      rcases lowerRow with ⟨left, right⟩
      change matrix.c * value + matrix.d =
        reference.c * value + reference.d
      rw [left, right]

end CurveSource

/-- The affine numerator `a*z+b` as a finite dense Gaussian polynomial. -/
def affineNumeratorPolynomial (matrix : Mat2) : GaussianPolynomial :=
  ⟨[matrix.a, matrix.b]⟩

@[simp] theorem eval_affineNumeratorPolynomial
    (matrix : Mat2) (value : Gaussian) :
    (affineNumeratorPolynomial matrix).eval value =
      CCL.RawParser.numerator matrix value := by
  simp [affineNumeratorPolynomial,
    RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
    CCL.RawParser.numerator]

/-- Coefficient-computed upper bound for the squared norm of a decoded point
throughout a box with the displayed denominator lower bound. -/
def decodedNormMajorant
    (matrix : Mat2) (box : Box) (denominatorMargin : Coordinate) :
    Coordinate :=
  RFAP.PolynomialBounds.denseEvalNormMajorant
      (affineNumeratorPolynomial matrix) box /
    denominatorMargin

theorem decodedNormMajorant_pos
    (matrix : Mat2) (box : Box) {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin) :
    0 < decodedNormMajorant matrix box denominatorMargin :=
  RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
      (affineNumeratorPolynomial matrix) box)
    marginPositive

theorem denominator_ne_of_margin
    {denominatorMargin : Coordinate} (marginPositive : 0 < denominatorMargin)
    {denominatorValue : Gaussian}
    (lower : denominatorMargin ≤ normSq denominatorValue) :
    denominatorValue ≠ 0 := by
  intro zero
  have positive : 0 < normSq denominatorValue := marginPositive.trans_le lower
  rw [zero, normSq_zero] at positive
  exact (lt_irrefl 0 positive).elim

/-- The rational homographic value is uniformly norm-bounded on the box once
its denominator has the supplied positive lower bound. -/
theorem normSq_homographic_le_decodedNormMajorant
    (matrix : Mat2) (box : Box) {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin) {value : Gaussian}
    (inside : box.Contains value)
    (denominatorLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator matrix value)) :
    normSq (CCL.RawParser.homographic matrix value) ≤
      decodedNormMajorant matrix box denominatorMargin := by
  let denominatorNorm :=
    normSq (CCL.RawParser.denominator matrix value)
  let numeratorNorm :=
    normSq (CCL.RawParser.numerator matrix value)
  let majorant :=
    RFAP.PolynomialBounds.denseEvalNormMajorant
      (affineNumeratorPolynomial matrix) box
  have denominatorPositive : 0 < denominatorNorm :=
    marginPositive.trans_le denominatorLower
  have denominatorNonzero :
      CCL.RawParser.denominator matrix value ≠ 0 := by
    intro zero
    change 0 < normSq
      (CCL.RawParser.denominator matrix value) at denominatorPositive
    rw [zero, normSq_zero] at denominatorPositive
    exact (lt_irrefl 0 denominatorPositive).elim
  have numeratorBound : numeratorNorm ≤ majorant := by
    simpa only [numeratorNorm, eval_affineNumeratorPolynomial] using
      RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
        (affineNumeratorPolynomial matrix) inside
  have sameDenominator : numeratorNorm / denominatorNorm ≤
      majorant / denominatorNorm := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    calc
      numeratorNorm ≤ majorant := numeratorBound
      _ = majorant / denominatorNorm * denominatorNorm :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne majorant
          denominatorNorm denominatorPositive.ne').symm
  have majorantNonnegative : 0 ≤ majorant :=
    (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
      (affineNumeratorPolynomial matrix) box).le
  have largerDenominator : majorant / denominatorNorm ≤
      majorant / denominatorMargin :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      majorantNonnegative marginPositive denominatorLower
  rw [CCL.CCLGeometry.normSq_homographic matrix value
    denominatorNonzero]
  change numeratorNorm * denominatorNorm⁻¹ ≤ _
  simpa only [RFAP.ExplicitField.div_eq_mul_inv, decodedNormMajorant,
    numeratorNorm, denominatorNorm, majorant] using
      sameDenominator.trans largerDenominator

/-- A rational coordinate is bounded by its square plus one, avoiding a
square-root operation in line-chart bounds. -/
theorem coordinate_le_sq_add_one (value : Coordinate) :
    value ≤ value ^ 2 + 1 := by
  by_cases nonpositive : value ≤ 0
  · exact nonpositive.trans
      (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct value)
        (show (0 : Coordinate) ≤ 1 by decide))
  · have positive : 0 < value := lt_of_not_ge nonpositive
    by_cases atMostOne : value ≤ 1
    · have oneBound : (1 : Coordinate) ≤ value ^ 2 + 1 := by
        have added := RFAP.ConstructiveFraction.add_le_add_right_direct
          (RFAP.ConstructiveFraction.sq_nonneg_direct value) 1
        calc
          1 = 0 + 1 := (RFAP.ConstructiveFraction.zero_add 1).symm
          _ ≤ value ^ 2 + 1 := added
      exact atMostOne.trans oneBound
    · have oneLe : (1 : Coordinate) ≤ value := (lt_of_not_ge atMostOne).le
      have squareBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          oneLe positive.le
      have valueLeSquare : value ≤ value ^ 2 := by
        simpa only [RFAP.ConstructiveFraction.mul_one_direct, pow_two] using
          squareBound
      have addOne : value ^ 2 ≤ value ^ 2 + 1 := by
        have added := RFAP.ConstructiveFraction.add_le_add_right_direct
          (show (0 : Coordinate) ≤ 1 by decide) (value ^ 2)
        calc
          value ^ 2 = 0 + value ^ 2 :=
            (RFAP.ConstructiveFraction.zero_add _).symm
          _ ≤ 1 + value ^ 2 := added
          _ = value ^ 2 + 1 := RFAP.ConstructiveFraction.add_comm _ _
      exact valueLeSquare.trans addOne

theorem neg_coordinate_le_sq_add_one (value : Coordinate) :
    -value ≤ value ^ 2 + 1 := by
  simpa only [neg_sq] using coordinate_le_sq_add_one (-value)

theorem le_one_of_sq_le_one {value : Coordinate}
    (square : value ^ 2 ≤ 1) : value ≤ 1 := by
  by_cases atMostOne : value ≤ 1
  · exact atMostOne
  · have oneLess : (1 : Coordinate) < value := lt_of_not_ge atMostOne
    have positive : 0 < value := (show (0 : Coordinate) < 1 by decide).trans
      oneLess
    have valueLessSquare : value < value ^ 2 := by
      have multiplied :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct oneLess
          positive
      simpa only [RFAP.ConstructiveFraction.one_mul, pow_two] using
        multiplied
    have impossible : (1 : Coordinate) < 1 :=
      oneLess.trans (valueLessSquare.trans_le square)
    exact (lt_irrefl 1 impossible).elim

theorem neg_one_le_of_sq_le_one {value : Coordinate}
    (square : value ^ 2 ≤ 1) : (-1 : Coordinate) ≤ value := by
  have negated : -value ≤ (1 : Coordinate) :=
    le_one_of_sq_le_one (value := -value) (by
      simpa only [neg_sq] using square)
  simpa only [_root_.neg_neg] using
    RFAP.ConstructiveFraction.neg_le_neg_direct negated

/-- Each coordinate of a Gaussian rational is bounded by its squared norm
plus one. -/
theorem coordinate_bounds_of_normSq_le
    (value : Gaussian) {bound : Coordinate} (normBound : normSq value ≤ bound) :
    - (bound + 1) ≤ value.re ∧ value.re ≤ bound + 1 ∧
      - (bound + 1) ≤ value.im ∧ value.im ≤ bound + 1 := by
  have realSquare : value.re ^ 2 ≤ normSq value := by
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct value.im) (value.re ^ 2)
    calc
      value.re ^ 2 = 0 + value.re ^ 2 :=
        (RFAP.ConstructiveFraction.zero_add _).symm
      _ ≤ value.im ^ 2 + value.re ^ 2 := added
      _ = normSq value := RFAP.ConstructiveFraction.add_comm _ _
  have imaginarySquare : value.im ^ 2 ≤ normSq value := by
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct value.re) (value.im ^ 2)
    calc
      value.im ^ 2 = 0 + value.im ^ 2 :=
        (RFAP.ConstructiveFraction.zero_add _).symm
      _ ≤ value.re ^ 2 + value.im ^ 2 := added
      _ = normSq value := rfl
  have realSquareBound := realSquare.trans normBound
  have imaginarySquareBound := imaginarySquare.trans normBound
  have realUpper : value.re ≤ bound + 1 :=
    (coordinate_le_sq_add_one value.re).trans
      (RFAP.ConstructiveFraction.add_le_add_right_direct realSquareBound 1)
  have realNegUpper : -value.re ≤ bound + 1 :=
    (neg_coordinate_le_sq_add_one value.re).trans
      (RFAP.ConstructiveFraction.add_le_add_right_direct realSquareBound 1)
  have imaginaryUpper : value.im ≤ bound + 1 :=
    (coordinate_le_sq_add_one value.im).trans
      (RFAP.ConstructiveFraction.add_le_add_right_direct imaginarySquareBound 1)
  have imaginaryNegUpper : -value.im ≤ bound + 1 :=
    (neg_coordinate_le_sq_add_one value.im).trans
      (RFAP.ConstructiveFraction.add_le_add_right_direct imaginarySquareBound 1)
  exact ⟨by
      simpa only [_root_.neg_neg] using
        RFAP.ConstructiveFraction.neg_le_neg_direct realNegUpper,
    realUpper,
    by
      simpa only [_root_.neg_neg] using
        RFAP.ConstructiveFraction.neg_le_neg_direct imaginaryNegUpper,
    imaginaryUpper⟩

/-- Positive symmetric radius for the single coordinate-line chart.  Adding
one avoids a square root while retaining a direct parameter bound. -/
def lineParameterRadius
    (matrix : Mat2) (box : Box) (denominatorMargin : Coordinate) :
    Coordinate :=
  decodedNormMajorant matrix box denominatorMargin + 1

theorem lineParameterRadius_pos
    (matrix : Mat2) (box : Box) {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin) :
    0 < lineParameterRadius matrix box denominatorMargin := by
  let majorant := decodedNormMajorant matrix box denominatorMargin
  have majorantPositive : 0 < majorant :=
    decodedNormMajorant_pos matrix box marginPositive
  have addOne := RFAP.ConstructiveFraction.add_lt_add_left_direct
    (show (0 : Coordinate) < 1 by decide) majorant
  calc
    0 < majorant := majorantPositive
    _ = majorant + 0 := by ring1
    _ < majorant + 1 := addOne
    _ = lineParameterRadius matrix box denominatorMargin := rfl

/-- Fixed unit parameter cell used by both circle charts. -/
def unitCell : Cell where
  interval := ⟨-1, 1, by decide⟩
  proper := by decide

/-- Symmetric proper cell for a positive displayed line radius. -/
def symmetricCell (radius : Coordinate) (positive : 0 < radius) : Cell where
  interval := ⟨-radius, radius,
    (RFAP.ConstructiveFraction.neg_le_neg_direct positive.le).trans
      positive.le⟩
  proper := by
    have negative : -radius < 0 := by
      simpa only [neg_zero] using
        (RFAP.ConstructiveFraction.neg_lt_neg_direct positive)
    exact negative.trans positive

/-- Pulling a canonical point back through an invertible matrix recovers the
original affine input, with a nonzero transformed curve denominator. -/
theorem inverseTransform_point
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve) (parameter : Coordinate)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (value : Gaussian)
    (matrixDenominatorNonzero :
      CCL.RawParser.denominator matrix value ≠ 0)
    (sourcePoint : source.point parameter =
      CCL.RawParser.homographic matrix value) :
    let transformed := source.transform
      (CCL.CCLPullback.adjugate matrix)
    transformed.denominatorAt parameter ≠ 0 ∧
      transformed.point parameter = value := by
  let inverse := CCL.CCLPullback.adjugate matrix
  let transformed := source.transform inverse
  have inverseDenominatorNonzero :
      CCL.RawParser.denominator inverse
        (source.point parameter) ≠ 0 := by
    rw [sourcePoint]
    exact CCL.CCLPullback.adjugate_denominator_homographic_ne
      matrix value determinantNonzero matrixDenominatorNonzero
  have transformedDenominatorNonzero :
      transformed.denominatorAt parameter ≠ 0 := by
    rw [CCL.RationalCurve.RationalCurve.denominatorAt_transform_eq
      inverse source parameter sourceDenominatorNonzero]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      inverseDenominatorNonzero sourceDenominatorNonzero
  refine ⟨transformedDenominatorNonzero, ?_⟩
  calc
    transformed.point parameter =
        CCL.RawParser.homographic inverse
          (source.point parameter) :=
      CCL.RationalCurve.RationalCurve.point_transform
        inverse source parameter sourceDenominatorNonzero
          inverseDenominatorNonzero
    _ = CCL.RawParser.homographic inverse
        (CCL.RawParser.homographic matrix value) := by
      rw [sourcePoint]
    _ = value :=
      CCL.CCLPullback.homographic_adjugate_forward_inverse
        matrix value determinantNonzero matrixDenominatorNonzero

/-- One parameterization paired with its finite proper parameter cell. -/
structure BoundedChart (form : HermitianForm) where
  parameterization : Parametrization form
  cell : Cell

namespace BoundedChart

/-- Homogeneous projective value of one bounded boundary chart. -/
def projective {form : HermitianForm} (chart : BoundedChart form)
    (parameter : Coordinate) : CCL.Chordal.Proj :=
  CCL.RationalCurveBounds.projective
    chart.parameterization.curve parameter

/-- Every displayed chart parameter is a genuine homogeneous projective
point, including parameters at which its affine denominator vanishes. -/
theorem projective_valid
    {form : HermitianForm} (chart : BoundedChart form)
    (parameter : Coordinate) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      (chart.projective parameter) :=
  chart.parameterization.projectiveValid parameter

/-- The parameterization's coefficient-computed positive projective-weight
lower bound applies uniformly to every displayed chart parameter. -/
theorem weightLower_le_projective
    {form : HermitianForm} (chart : BoundedChart form)
    (parameter : Coordinate) :
    chart.parameterization.weightLower ≤
      CCL.Chordal.Proj.weight (chart.projective parameter) :=
  chart.parameterization.weightLower_le parameter

theorem projective_weight_pos
    {form : HermitianForm} (chart : BoundedChart form)
    (parameter : Coordinate) :
    0 < CCL.Chordal.Proj.weight (chart.projective parameter) :=
  chart.parameterization.weightLowerPositive.trans_le
    (chart.weightLower_le_projective parameter)

/-- Uniform lower bound for the affine curve-denominator quadrance whenever
the represented point lies in a displayed finite box.  It is obtained from
the chart's homogeneous-weight lower bound and the box's finite norm
majorant, so no affine compactness argument is involved. -/
def affineDenominatorNormSqLower
    {form : HermitianForm} (chart : BoundedChart form) (box : Box) :
    Coordinate :=
  chart.parameterization.weightLower / (box.normSqBound + 1)

theorem affineDenominatorNormSqLower_pos
    {form : HermitianForm} (chart : BoundedChart form) (box : Box) :
    0 < chart.affineDenominatorNormSqLower box :=
  RFAP.ConstructiveFraction.div_pos_direct
    chart.parameterization.weightLowerPositive
    (add_pos_of_nonneg_of_pos box.normSqBound_nonneg (by decide))

theorem affineDenominatorNormSqLower_le
    {form : HermitianForm} (chart : BoundedChart form) (box : Box)
    (parameter : Coordinate)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (inside : box.Contains
      (chart.parameterization.curve.point parameter)) :
    chart.affineDenominatorNormSqLower box ≤
      normSq (chart.parameterization.curve.denominatorAt parameter) := by
  let curve := chart.parameterization.curve
  let pointNorm := normSq (curve.point parameter)
  let denominatorNorm := normSq (curve.denominatorAt parameter)
  let scale := box.normSqBound + 1
  have scalePositive : 0 < scale := by
    exact add_pos_of_nonneg_of_pos box.normSqBound_nonneg (by decide)
  have pointBound : pointNorm ≤ box.normSqBound := by
    simpa only [pointNorm, curve] using box.normSq_le_normSqBound inside
  have scaleBound : pointNorm + 1 ≤ scale := by
    exact add_le_add pointBound le_rfl
  have weightIdentity :
      CCL.Chordal.Proj.weight (chart.projective parameter) =
        (pointNorm + 1) * denominatorNorm := by
    have numeratorIdentity :=
      curve.numeratorAt_eq_point_mul_denominatorAt parameter
        denominatorNonzero
    simp only [BoundedChart.projective,
      CCL.RationalCurveBounds.projective,
      CCL.Chordal.Proj.weight]
    rw [numeratorIdentity, normSq_mul]
    dsimp only [pointNorm, denominatorNorm]
    ring1
  apply (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).2
  calc
    chart.parameterization.weightLower ≤
        CCL.Chordal.Proj.weight (chart.projective parameter) :=
      chart.weightLower_le_projective parameter
    _ = (pointNorm + 1) * denominatorNorm := weightIdentity
    _ ≤ scale * denominatorNorm :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scaleBound
        (normSq_nonneg _)
    _ = denominatorNorm * scale :=
      RFAP.ConstructiveFraction.mul_comm _ _

/-- Uniform lower bound for the finite Horner denominator power over affine
chart points lying in a displayed box. -/
def affineDenominatorPowerNormSqLower
    (p : GaussianPolynomial) {form : HermitianForm}
    (chart : BoundedChart form) (box : Box) : Coordinate :=
  chart.affineDenominatorNormSqLower box ^ p.coeffs.length

theorem affineDenominatorPowerNormSqLower_pos
    (p : GaussianPolynomial) {form : HermitianForm}
    (chart : BoundedChart form) (box : Box) :
    0 < chart.affineDenominatorPowerNormSqLower p box :=
  RFAP.ConstructiveFraction.pow_pos_direct
    (chart.affineDenominatorNormSqLower_pos box) p.coeffs.length

theorem affineDenominatorPowerNormSqLower_le
    (p : GaussianPolynomial) {form : HermitianForm}
    (chart : BoundedChart form) (box : Box) (parameter : Coordinate)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (inside : box.Contains
      (chart.parameterization.curve.point parameter)) :
    chart.affineDenominatorPowerNormSqLower p box ≤
      normSq
        ((CCL.RationalCurve.clearingState p
          chart.parameterization.curve).denominatorPower.eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) := by
  rw [CCL.RationalCurve.eval_denominatorPower, normSq_pow]
  exact RFAP.ConstructiveFraction.pow_le_pow_direct
    (chart.affineDenominatorNormSqLower_pos box).le
    (chart.affineDenominatorNormSqLower_le box parameter
      denominatorNonzero inside) p.coeffs.length

/-- Pole-safe coefficient for squared-chordal variation.  Unlike the older
affine-denominator coefficient, this divides by a lower bound for the full
homogeneous weight and therefore remains valid when the affine chart passes
through infinity. -/
def uniformChordalVariationCoefficient
    {form : HermitianForm} (chart : BoundedChart form) : Coordinate :=
  CCL.RationalCurveBounds.crossVariationCoefficient
      chart.parameterization.curve chart.cell.interval /
    chart.parameterization.weightLower ^ 2

theorem uniformChordalVariationCoefficient_nonneg
    {form : HermitianForm} (chart : BoundedChart form) :
    0 ≤ chart.uniformChordalVariationCoefficient :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (CCL.RationalCurveBounds.crossVariationCoefficient_nonneg
      chart.parameterization.curve chart.cell.interval)
    (RFAP.ConstructiveFraction.pow_pos_direct
      chart.parameterization.weightLowerPositive 2).le

/-- Genuine squared-chordal variation of a bounded chart, with no affine
denominator-clearance hypothesis and hence no exceptional pole case. -/
theorem chordalSq_le_uniform
    {form : HermitianForm} (chart : BoundedChart form)
    {left right : Coordinate}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * (left - right) ^ 2 := by
  let leftPoint := chart.projective left
  let rightPoint := chart.projective right
  let actualDenominator :=
    CCL.Chordal.Proj.weight leftPoint *
      CCL.Chordal.Proj.weight rightPoint
  let lowerSq := chart.parameterization.weightLower ^ 2
  let upper :=
    CCL.RationalCurveBounds.crossVariationCoefficient
        chart.parameterization.curve chart.cell.interval *
      (left - right) ^ 2
  have leftWeightPositive :
      0 < CCL.Chordal.Proj.weight leftPoint :=
    chart.projective_weight_pos left
  have rightWeightPositive :
      0 < CCL.Chordal.Proj.weight rightPoint :=
    chart.projective_weight_pos right
  have actualPositive : 0 < actualDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have lowerSqPositive : 0 < lowerSq :=
    RFAP.ConstructiveFraction.pow_pos_direct
      chart.parameterization.weightLowerPositive 2
  have actualLower : lowerSq ≤ actualDenominator := by
    dsimp only [lowerSq, actualDenominator]
    simpa only [pow_two] using
      (RFAP.ConstructiveFraction.mul_le_mul_direct
        (chart.weightLower_le_projective left)
        (chart.weightLower_le_projective right)
        chart.parameterization.weightLowerPositive.le
        leftWeightPositive.le)
  have upperNonnegative : 0 ≤ upper :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.RationalCurveBounds.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval)
      (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))
  calc
    CCL.Chordal.chordalSq leftPoint rightPoint =
        normSq (CCL.Chordal.Proj.cross leftPoint rightPoint) /
          actualDenominator := rfl
    _ ≤ upper / actualDenominator := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos actualPositive).2
      have cancel : upper / actualDenominator * actualDenominator = upper :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne upper
          actualDenominator actualPositive.ne'
      rw [cancel]
      exact CCL.RationalCurveBounds.normSq_cross_le
        chart.parameterization.curve chart.cell.interval
          leftInside rightInside
    _ ≤ upper / lowerSq :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        upperNonnegative lowerSqPositive actualLower
    _ = chart.uniformChordalVariationCoefficient * (left - right) ^ 2 := by
      simp only [uniformChordalVariationCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm ((left - right) ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

/-- Width-only pole-safe squared-chordal diameter bound for a complete
bounded chart. -/
theorem chordalSq_le_uniformWidth
    {form : HermitianForm} (chart : BoundedChart form)
    {left right : Coordinate}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient *
        chart.cell.interval.width ^ 2 :=
  (chart.chordalSq_le_uniform leftInside rightInside).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
        chart.cell.interval leftInside rightInside)
      chart.uniformChordalVariationCoefficient_nonneg)

/-- The homogeneous cross product of any two parameters in a bounded chart
shrinks quadratically with the displayed parameter-cell width, even across
an affine pole. -/
theorem normSq_cross_le_width
    {form : HermitianForm} (chart : BoundedChart form)
    {left right : Coordinate}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    normSq (CCL.Chordal.Proj.cross
        (chart.projective left) (chart.projective right)) ≤
      CCL.RationalCurveBounds.crossVariationCoefficient
          chart.parameterization.curve chart.cell.interval *
        chart.cell.interval.width ^ 2 := by
  have crossBound :=
    CCL.RationalCurveBounds.normSq_cross_le
      chart.parameterization.curve chart.cell.interval
      leftInside rightInside
  have widthBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      chart.cell.interval leftInside rightInside
  exact crossBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct widthBound
      (CCL.RationalCurveBounds.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval))

/-- Once a positive affine-denominator clearance is supplied, the same
bounded chart has a squared-chordal image diameter proportional to width
squared. -/
theorem chordalSq_le_width
    {form : HermitianForm} (chart : BoundedChart form)
    (clearance : CCL.RationalCurveBounds.DenominatorClearance
      (CCL.CurveBoxConditions.denominatorReal
        chart.parameterization.curve)
      (CCL.CurveBoxConditions.denominatorImaginary
        chart.parameterization.curve)
      chart.cell.interval)
    {left right : Coordinate}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (chart.projective left) (chart.projective right) ≤
      CCL.RationalCurveBounds.chordalVariationCoefficient
          chart.parameterization.curve chart.cell.interval clearance *
        chart.cell.interval.width ^ 2 :=
  CCL.RationalCurveBounds.chordalSq_projective_le_width
    chart.parameterization.curve chart.cell.interval clearance
      leftInside rightInside

end BoundedChart

/-- A displayed point is reached by one parameter inside a bounded chart. -/
def PointCoverage {form : HermitianForm}
    (value : Gaussian) (chart : BoundedChart form) : Prop :=
  ∃ parameter,
    chart.cell.interval.Contains parameter ∧
      chart.parameterization.curve.denominatorAt parameter ≠ 0 ∧
      chart.parameterization.curve.point parameter = value

/-- The complete finite chart family: exactly two unit cells for a norm
circle, and exactly one coefficient-bounded cell for a coordinate line. -/
def charts
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form)
    (box : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) : List (BoundedChart form) :=
  match source with
  | .norm matrix determinantNonzero _lowerRow base _baseNonzero form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            CCL.CCLBoundaryCurves.normComparison matrix
              determinantNonzero base
         cell := unitCell },
       { parameterization :=
          form_eq.symm ▸
            CCL.CCLBoundaryCurves.normComparisonReciprocal matrix
              determinantNonzero base
         cell := unitCell }]
  | .real matrix determinantNonzero _lowerRow threshold form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            CCL.CCLBoundaryCurves.realComparison matrix
              determinantNonzero threshold
         cell := symmetricCell
           (lineParameterRadius matrix box denominatorMargin)
           (lineParameterRadius_pos matrix box marginPositive) }]
  | .imaginary matrix determinantNonzero _lowerRow threshold form_eq =>
      [{ parameterization :=
          form_eq.symm ▸
            CCL.CCLBoundaryCurves.imaginaryComparison matrix
              determinantNonzero threshold
         cell := symmetricCell
           (lineParameterRadius matrix box denominatorMargin)
           (lineParameterRadius_pos matrix box marginPositive) }]

/-- Coverage by one member of the finite chart family. -/
def Covered
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (box : Box)
    (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) (value : Gaussian) : Prop :=
  ∃ chart, chart ∈ charts source box denominatorMargin marginPositive ∧
    PointCoverage value chart

/-- Executable proof-bearing form of finite chart coverage.  Unlike the
propositional `Covered` wrapper, this record can be consumed by later finite
algorithms without eliminating an existential proposition into data. -/
structure Coverage
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (box : Box)
    (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) (value : Gaussian) where
  chart : BoundedChart form
  chartMember : chart ∈ charts source box denominatorMargin marginPositive
  parameter : Coordinate
  parameterInside : chart.cell.interval.Contains parameter
  curveDenominatorNonzero :
    chart.parameterization.curve.denominatorAt parameter ≠ 0
  point_eq : chart.parameterization.curve.point parameter = value

theorem Coverage.covered
    {reference : Mat2} {form : HermitianForm}
    {source : CurveSource reference form} {box : Box}
    {denominatorMargin : Coordinate}
    {marginPositive : 0 < denominatorMargin} {value : Gaussian}
    (coverage : Coverage source box denominatorMargin marginPositive value) :
    Covered source box denominatorMargin marginPositive value :=
  ⟨coverage.chart, coverage.chartMember, coverage.parameter,
    coverage.parameterInside, coverage.curveDenominatorNonzero,
    coverage.point_eq⟩

/-- The bounded vertical-line chart covers every point of the corresponding
pulled-back boundary inside the current box. -/
def realSource_cover
    (reference matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (threshold : Coordinate) (box : Box)
    {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin)
    (value : Gaussian) (inside : box.Contains value)
    (onBoundary :
      (CCL.CCLGeometry.realComparisonForm matrix threshold).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator reference value)) :
    Coverage
      (.real matrix determinantNonzero lowerRow threshold rfl)
      box denominatorMargin marginPositive value := by
  let tail := CCL.RawParser.homographic matrix value
  have denominatorIdentity :
      CCL.RawParser.denominator matrix value =
        CCL.RawParser.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [CCL.RawParser.denominator, left, right]
  have denominatorLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      CCL.RawParser.denominator matrix value ≠ 0 :=
    denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : normSq tail ≤
      decodedNormMajorant matrix box denominatorMargin :=
    normSq_homographic_le_decodedNormMajorant matrix box marginPositive
      inside denominatorLower
  have bounds := coordinate_bounds_of_normSq_le tail tailNorm
  have realEquality : tail.re = threshold :=
    (CCL.CCLGeometry.real_homographic_eq_iff
      matrix value threshold denominatorNonzero).2 onBoundary
  have sourcePoint :
      (CCL.CanonicalCurves.realLine threshold).point tail.im =
        tail := by
    rw [CCL.CanonicalCurves.realLine_point]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact realEquality.symm
    · rfl
  have transformed := inverseTransform_point matrix determinantNonzero
    (CCL.CanonicalCurves.realLine threshold) tail.im
    (CCL.CanonicalCurves.realLine_denominator_ne threshold tail.im)
    value denominatorNonzero sourcePoint
  let chart : BoundedChart
      (CCL.CCLGeometry.realComparisonForm matrix threshold) :=
    { parameterization :=
        CCL.CCLBoundaryCurves.realComparison matrix
          determinantNonzero threshold
      cell := symmetricCell
        (lineParameterRadius matrix box denominatorMargin)
        (lineParameterRadius_pos matrix box marginPositive) }
  refine ⟨chart, ?_, tail.im, ?_, ?_, ?_⟩
  · simp only [charts, List.mem_singleton]
    rfl
  · change -lineParameterRadius matrix box denominatorMargin ≤ tail.im ∧
      tail.im ≤ lineParameterRadius matrix box denominatorMargin
    simpa only [lineParameterRadius] using ⟨bounds.2.2.1, bounds.2.2.2⟩
  · change ((CCL.CanonicalCurves.realLine threshold).transform
      (CCL.CCLPullback.adjugate matrix)).denominatorAt tail.im ≠ 0
    exact transformed.1
  · change ((CCL.CanonicalCurves.realLine threshold).transform
      (CCL.CCLPullback.adjugate matrix)).point tail.im = value
    exact transformed.2

/-- The bounded horizontal-line chart covers every point of the
corresponding pulled-back boundary inside the current box. -/
def imaginarySource_cover
    (reference matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (threshold : Coordinate) (box : Box)
    {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin)
    (value : Gaussian) (inside : box.Contains value)
    (onBoundary :
      (CCL.CCLGeometry.imagComparisonForm matrix threshold).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator reference value)) :
    Coverage
      (.imaginary matrix determinantNonzero lowerRow threshold rfl)
      box denominatorMargin marginPositive value := by
  let tail := CCL.RawParser.homographic matrix value
  have denominatorIdentity :
      CCL.RawParser.denominator matrix value =
        CCL.RawParser.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [CCL.RawParser.denominator, left, right]
  have denominatorLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      CCL.RawParser.denominator matrix value ≠ 0 :=
    denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : normSq tail ≤
      decodedNormMajorant matrix box denominatorMargin :=
    normSq_homographic_le_decodedNormMajorant matrix box marginPositive
      inside denominatorLower
  have bounds := coordinate_bounds_of_normSq_le tail tailNorm
  have imaginaryEquality : tail.im = threshold :=
    (CCL.CCLGeometry.imag_homographic_eq_iff
      matrix value threshold denominatorNonzero).2 onBoundary
  have sourcePoint :
      (CCL.CanonicalCurves.imaginaryLine threshold).point tail.re =
        tail := by
    rw [CCL.CanonicalCurves.imaginaryLine_point]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · rfl
    · exact imaginaryEquality.symm
  have transformed := inverseTransform_point matrix determinantNonzero
    (CCL.CanonicalCurves.imaginaryLine threshold) tail.re
    (CCL.CanonicalCurves.imaginaryLine_denominator_ne threshold
      tail.re)
    value denominatorNonzero sourcePoint
  let chart : BoundedChart
      (CCL.CCLGeometry.imagComparisonForm matrix threshold) :=
    { parameterization :=
        CCL.CCLBoundaryCurves.imaginaryComparison matrix
          determinantNonzero threshold
      cell := symmetricCell
        (lineParameterRadius matrix box denominatorMargin)
        (lineParameterRadius_pos matrix box marginPositive) }
  refine ⟨chart, ?_, tail.re, ?_, ?_, ?_⟩
  · simp only [charts, List.mem_singleton]
    rfl
  · change -lineParameterRadius matrix box denominatorMargin ≤ tail.re ∧
      tail.re ≤ lineParameterRadius matrix box denominatorMargin
    simpa only [lineParameterRadius] using ⟨bounds.1, bounds.2.1⟩
  · change ((CCL.CanonicalCurves.imaginaryLine threshold).transform
      (CCL.CCLPullback.adjugate matrix)).denominatorAt tail.re ≠ 0
    exact transformed.1
  · change ((CCL.CanonicalCurves.imaginaryLine threshold).transform
      (CCL.CCLPullback.adjugate matrix)).point tail.re = value
    exact transformed.2

/-- The primary unit-circle chart covers the half with nonnegative real
coordinate, using a parameter in `[-1,1]`. -/
theorem primaryUnitCircle_covers
    (unit : Gaussian) (unitNorm : normSq unit = 1)
    (realNonnegative : 0 ≤ unit.re) :
    let parameter := unit.im / (1 + unit.re)
    (-1 : Coordinate) ≤ parameter ∧ parameter ≤ 1 ∧
      (CCL.CanonicalCurves.circle 1).point parameter = unit := by
  let x := unit.re
  let y := unit.im
  let scale : Coordinate := 1 + x
  let parameter : Coordinate := y / scale
  have xLessScale : x < scale := by
    have added := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (show (0 : Coordinate) < 1 by decide) x
    dsimp only [scale]
    calc
      x = 0 + x := (RFAP.ConstructiveFraction.zero_add x).symm
      _ < 1 + x := added
  have scalePositive : 0 < scale := realNonnegative.trans_lt xLessScale
  have imaginarySquare : y ^ 2 ≤ 1 := by
    have realSquareNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct x
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      realSquareNonnegative (y ^ 2)
    have squareLeNorm : y ^ 2 ≤ normSq unit := by
      dsimp only [x, y]
      calc
        unit.im ^ 2 = 0 + unit.im ^ 2 :=
          (RFAP.ConstructiveFraction.zero_add _).symm
        _ ≤ unit.re ^ 2 + unit.im ^ 2 := added
        _ = normSq unit := rfl
    exact squareLeNorm.trans_eq unitNorm
  have imaginaryLower : (-1 : Coordinate) ≤ y :=
    neg_one_le_of_sq_le_one imaginarySquare
  have imaginaryUpper : y ≤ (1 : Coordinate) :=
    le_one_of_sq_le_one imaginarySquare
  have oneLeScale : (1 : Coordinate) ≤ scale := by
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      realNonnegative 1
    dsimp only [scale]
    calc
      1 = 0 + 1 := (RFAP.ConstructiveFraction.zero_add 1).symm
      _ ≤ x + 1 := added
      _ = 1 + x := RFAP.ConstructiveFraction.add_comm _ _
  have negScaleLe : -scale ≤ y :=
    (RFAP.ConstructiveFraction.neg_le_neg_direct oneLeScale).trans
      imaginaryLower
  have yLeScale : y ≤ scale := imaginaryUpper.trans oneLeScale
  have parameterLower : (-1 : Coordinate) ≤ parameter := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos scalePositive).2
    calc
      (-1 : Coordinate) * scale = -scale := by ring1
      _ ≤ y := negScaleLe
  have parameterUpper : parameter ≤ (1 : Coordinate) := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).2
    calc
      y ≤ scale := yLeScale
      _ = (1 : Coordinate) * scale :=
        (RFAP.ConstructiveFraction.one_mul scale).symm
  have parameterScale : parameter * scale = y := by
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne y scale
      scalePositive.ne'
  have factored : (1 - x) * scale = y ^ 2 := by
    dsimp only [x, y, scale]
    dsimp only [normSq] at unitNorm
    calc
      (1 - unit.re) * (1 + unit.re) =
          1 - (unit.re ^ 2 + unit.im ^ 2) + unit.im ^ 2 := by ring1
      _ = unit.im ^ 2 := by rw [unitNorm]; ring1
  have parameterFactored : (parameter ^ 2 * scale) * scale = y ^ 2 := by
    calc
      (parameter ^ 2 * scale) * scale = (parameter * scale) ^ 2 := by
        ring1
      _ = y ^ 2 := by rw [parameterScale]
  have relation : 1 - x = parameter ^ 2 * scale :=
    RFAP.ConstructiveFraction.mul_right_cancel_of_ne scalePositive.ne'
      (factored.trans parameterFactored.symm)
  have relationExpanded :
      1 - x = parameter ^ 2 * (1 + x) := by
    simpa only [scale] using relation
  have realIdentity :
      1 - parameter ^ 2 = x * (parameter ^ 2 + 1) := by
    calc
      1 - parameter ^ 2 = x + (1 - x) - parameter ^ 2 := by ring1
      _ = x + parameter ^ 2 * (1 + x) - parameter ^ 2 := by
        rw [relationExpanded]
      _ = x * (parameter ^ 2 + 1) := by ring1
  have scaleIdentity : scale * (1 + parameter ^ 2) = 2 := by
    calc
      scale * (1 + parameter ^ 2) = scale + parameter ^ 2 * scale := by
        ring1
      _ = scale + (1 - x) := by rw [← relation]
      _ = 2 := by dsimp only [scale]; ring1
  have imaginaryIdentity :
      2 * parameter = y * (parameter ^ 2 + 1) := by
    calc
      2 * parameter = parameter * 2 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = parameter * (scale * (1 + parameter ^ 2)) := by
        rw [scaleIdentity]
      _ = (parameter * scale) * (parameter ^ 2 + 1) := by ring1
      _ = y * (parameter ^ 2 + 1) := by rw [parameterScale]
  have directionIdentity :
      (⟨1 - parameter ^ 2, 2 * parameter⟩ : Gaussian) =
        unit * ⟨parameter ^ 2 + 1, 0⟩ := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · change 1 - parameter ^ 2 =
        x * (parameter ^ 2 + 1) - y * 0
      calc
        1 - parameter ^ 2 = x * (parameter ^ 2 + 1) := realIdentity
        _ = x * (parameter ^ 2 + 1) - y * 0 := by ring1
    · change 2 * parameter = x * 0 + y * (parameter ^ 2 + 1)
      simpa only [RFAP.ConstructiveFraction.mul_zero_direct,
        RFAP.ConstructiveFraction.zero_add] using imaginaryIdentity
  have pointIdentity :
      (CCL.CanonicalCurves.circle 1).point parameter = unit := by
    have denominatorNonzero :=
      CCL.CanonicalCurves.circle_denominator_ne 1 parameter
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      denominatorNonzero
    calc
      (CCL.CanonicalCurves.circle 1).point parameter *
          (CCL.CanonicalCurves.circle 1).denominatorAt parameter =
          (CCL.CanonicalCurves.circle 1).numeratorAt parameter :=
        (CCL.RationalCurve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
          (CCL.CanonicalCurves.circle 1) parameter
            denominatorNonzero).symm
      _ = (1 : Gaussian) *
          ⟨1 - parameter ^ 2, 2 * parameter⟩ :=
        CCL.CanonicalCurves.circle_numeratorAt 1 parameter
      _ = ⟨1 - parameter ^ 2, 2 * parameter⟩ :=
        RFAP.ConstructiveGaussian.Gaussian.one_mul _
      _ = unit * ⟨parameter ^ 2 + 1, 0⟩ := directionIdentity
      _ = unit *
          (CCL.CanonicalCurves.circle 1).denominatorAt parameter := by
        rw [CCL.CanonicalCurves.circle_denominatorAt]
  exact ⟨parameterLower, parameterUpper, pointIdentity⟩

/-- The reciprocal unit-circle chart covers the half with nonpositive real
coordinate, again using a parameter in `[-1,1]`. -/
theorem reciprocalUnitCircle_covers
    (unit : Gaussian) (unitNorm : normSq unit = 1)
    (realNonpositive : unit.re ≤ 0) :
    let parameter := unit.im / (1 - unit.re)
    (-1 : Coordinate) ≤ parameter ∧ parameter ≤ 1 ∧
      (CCL.CanonicalCurves.reciprocalCircle 1).point parameter =
        unit := by
  let x := unit.re
  let y := unit.im
  let scale : Coordinate := 1 - x
  let parameter : Coordinate := y / scale
  have xLessOne : x < (1 : Coordinate) :=
    realNonpositive.trans_lt (show (0 : Coordinate) < 1 by decide)
  have scalePositive : 0 < scale := by
    dsimp only [scale]
    exact RFAP.ConstructiveFraction.sub_pos_direct xLessOne
  have imaginarySquare : y ^ 2 ≤ 1 := by
    have realSquareNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct x
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      realSquareNonnegative (y ^ 2)
    have squareLeNorm : y ^ 2 ≤ normSq unit := by
      dsimp only [x, y]
      calc
        unit.im ^ 2 = 0 + unit.im ^ 2 :=
          (RFAP.ConstructiveFraction.zero_add _).symm
        _ ≤ unit.re ^ 2 + unit.im ^ 2 := added
        _ = normSq unit := rfl
    exact squareLeNorm.trans_eq unitNorm
  have imaginaryLower : (-1 : Coordinate) ≤ y :=
    neg_one_le_of_sq_le_one imaginarySquare
  have imaginaryUpper : y ≤ (1 : Coordinate) :=
    le_one_of_sq_le_one imaginarySquare
  have negXNonnegative : 0 ≤ -x := by
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct realNonpositive
    simpa only [_root_.neg_zero] using negated
  have oneLeScale : (1 : Coordinate) ≤ scale := by
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      negXNonnegative 1
    dsimp only [scale]
    calc
      1 = 0 + 1 := (RFAP.ConstructiveFraction.zero_add 1).symm
      _ ≤ -x + 1 := added
      _ = 1 - x := by ring1
  have negScaleLe : -scale ≤ y :=
    (RFAP.ConstructiveFraction.neg_le_neg_direct oneLeScale).trans
      imaginaryLower
  have yLeScale : y ≤ scale := imaginaryUpper.trans oneLeScale
  have parameterLower : (-1 : Coordinate) ≤ parameter := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos scalePositive).2
    calc
      (-1 : Coordinate) * scale = -scale := by ring1
      _ ≤ y := negScaleLe
  have parameterUpper : parameter ≤ (1 : Coordinate) := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).2
    calc
      y ≤ scale := yLeScale
      _ = (1 : Coordinate) * scale :=
        (RFAP.ConstructiveFraction.one_mul scale).symm
  have parameterScale : parameter * scale = y :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne y scale scalePositive.ne'
  have factored : (1 + x) * scale = y ^ 2 := by
    dsimp only [x, y, scale]
    dsimp only [normSq] at unitNorm
    calc
      (1 + unit.re) * (1 - unit.re) =
          1 - (unit.re ^ 2 + unit.im ^ 2) + unit.im ^ 2 := by ring1
      _ = unit.im ^ 2 := by rw [unitNorm]; ring1
  have parameterFactored : (parameter ^ 2 * scale) * scale = y ^ 2 := by
    calc
      (parameter ^ 2 * scale) * scale = (parameter * scale) ^ 2 := by
        ring1
      _ = y ^ 2 := by rw [parameterScale]
  have relation : 1 + x = parameter ^ 2 * scale :=
    RFAP.ConstructiveFraction.mul_right_cancel_of_ne scalePositive.ne'
      (factored.trans parameterFactored.symm)
  have realIdentity :
      parameter ^ 2 - 1 = x * (parameter ^ 2 + 1) := by
    calc
      parameter ^ 2 - 1 =
          parameter ^ 2 * scale + x * parameter ^ 2 - 1 := by
        dsimp only [scale]
        ring1
      _ = (1 + x) + x * parameter ^ 2 - 1 := by rw [← relation]
      _ = x * (parameter ^ 2 + 1) := by ring1
  have scaleIdentity : scale * (1 + parameter ^ 2) = 2 := by
    calc
      scale * (1 + parameter ^ 2) = scale + parameter ^ 2 * scale := by
        ring1
      _ = scale + (1 + x) := by rw [← relation]
      _ = 2 := by dsimp only [scale]; ring1
  have imaginaryIdentity :
      2 * parameter = y * (parameter ^ 2 + 1) := by
    calc
      2 * parameter = parameter * 2 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = parameter * (scale * (1 + parameter ^ 2)) := by
        rw [scaleIdentity]
      _ = (parameter * scale) * (parameter ^ 2 + 1) := by ring1
      _ = y * (parameter ^ 2 + 1) := by rw [parameterScale]
  have directionIdentity :
      (⟨parameter ^ 2 - 1, 2 * parameter⟩ : Gaussian) =
        unit * ⟨parameter ^ 2 + 1, 0⟩ := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · change parameter ^ 2 - 1 =
        x * (parameter ^ 2 + 1) - y * 0
      calc
        parameter ^ 2 - 1 = x * (parameter ^ 2 + 1) := realIdentity
        _ = x * (parameter ^ 2 + 1) - y * 0 := by ring1
    · change 2 * parameter = x * 0 + y * (parameter ^ 2 + 1)
      simpa only [RFAP.ConstructiveFraction.mul_zero_direct,
        RFAP.ConstructiveFraction.zero_add] using imaginaryIdentity
  have pointIdentity :
      (CCL.CanonicalCurves.reciprocalCircle 1).point parameter =
        unit := by
    have denominatorNonzero :=
      CCL.CanonicalCurves.reciprocalCircle_denominator_ne
        1 parameter
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      denominatorNonzero
    calc
      (CCL.CanonicalCurves.reciprocalCircle 1).point parameter *
          (CCL.CanonicalCurves.reciprocalCircle 1).denominatorAt
            parameter =
          (CCL.CanonicalCurves.reciprocalCircle 1).numeratorAt
            parameter :=
        (CCL.RationalCurve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
          (CCL.CanonicalCurves.reciprocalCircle 1) parameter
            denominatorNonzero).symm
      _ = (1 : Gaussian) *
          ⟨parameter ^ 2 - 1, 2 * parameter⟩ :=
        CCL.CanonicalCurves.reciprocalCircle_numeratorAt 1 parameter
      _ = ⟨parameter ^ 2 - 1, 2 * parameter⟩ :=
        RFAP.ConstructiveGaussian.Gaussian.one_mul _
      _ = unit * ⟨parameter ^ 2 + 1, 0⟩ := directionIdentity
      _ = unit *
          (CCL.CanonicalCurves.reciprocalCircle 1).denominatorAt
            parameter := by
        rw [CCL.CanonicalCurves.reciprocalCircle_denominatorAt]
  exact ⟨parameterLower, parameterUpper, pointIdentity⟩

/-- The two bounded circle charts cover every point of the corresponding
pulled-back norm boundary inside the current box. -/
def normSource_cover
    (reference matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (lowerRow : matrix.c = reference.c ∧ matrix.d = reference.d)
    (base : Gaussian) (baseNonzero : base ≠ 0) (box : Box)
    {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin)
    (value : Gaussian) (_inside : box.Contains value)
    (onBoundary :
      (CCL.CCLGeometry.normComparisonForm matrix (normSq base)).eval
        value = 0)
    (referenceLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator reference value)) :
    Coverage
      (.norm matrix determinantNonzero lowerRow base baseNonzero rfl)
      box denominatorMargin marginPositive value := by
  let tail := CCL.RawParser.homographic matrix value
  have denominatorIdentity :
      CCL.RawParser.denominator matrix value =
        CCL.RawParser.denominator reference value := by
    rcases lowerRow with ⟨left, right⟩
    simp only [CCL.RawParser.denominator, left, right]
  have denominatorLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator matrix value) := by
    rw [denominatorIdentity]
    exact referenceLower
  have denominatorNonzero :
      CCL.RawParser.denominator matrix value ≠ 0 :=
    denominator_ne_of_margin marginPositive denominatorLower
  have tailNorm : normSq tail = normSq base :=
    (CCL.CCLGeometry.norm_homographic_eq_iff matrix value
      (normSq base) denominatorNonzero).2 onBoundary
  by_cases baseZero : base = 0
  · exact (baseNonzero baseZero).elim
  · let unit := base⁻¹ * tail
    have baseNormNonzero : normSq base ≠ 0 :=
      fun zero => baseZero (normSq_eq_zero.mp zero)
    have unitNorm : normSq unit = 1 := by
      dsimp only [unit]
      rw [normSq_mul]
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        normSq_inv base baseZero, tailNorm,
        RFAP.ConstructiveFraction.inv_mul_cancel _ baseNormNonzero]
    have baseUnit : base * unit = tail := by
      dsimp only [unit]
      calc
        base * (base⁻¹ * tail) = (base * base⁻¹) * tail :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = 1 * tail := by
          rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
            RFAP.ConstructiveGaussian.Gaussian.mul_inv base baseZero]
        _ = tail := RFAP.ConstructiveGaussian.Gaussian.one_mul _
    by_cases realNonnegative : 0 ≤ unit.re
    · let parameter := unit.im / (1 + unit.re)
      have covered := primaryUnitCircle_covers unit unitNorm realNonnegative
      have sourcePoint :
          (CCL.CanonicalCurves.circle base).point parameter =
            tail := by
        rw [CCL.CanonicalCurves.circle_point_scale]
        calc
          base * (CCL.CanonicalCurves.circle 1).point parameter =
              base * unit := by rw [covered.2.2]
          _ = tail := baseUnit
      have transformed := inverseTransform_point matrix determinantNonzero
        (CCL.CanonicalCurves.circle base) parameter
        (CCL.CanonicalCurves.circle_denominator_ne base parameter)
        value denominatorNonzero sourcePoint
      let chart : BoundedChart
          (CCL.CCLGeometry.normComparisonForm matrix
            (normSq base)) :=
        { parameterization :=
            CCL.CCLBoundaryCurves.normComparison matrix
              determinantNonzero base
          cell := unitCell }
      refine ⟨chart, ?_, parameter, ?_, ?_, ?_⟩
      · simp only [charts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inl rfl
      · exact ⟨covered.1, covered.2.1⟩
      · change ((CCL.CanonicalCurves.circle base).transform
          (CCL.CCLPullback.adjugate matrix)).denominatorAt
            parameter ≠ 0
        exact transformed.1
      · change ((CCL.CanonicalCurves.circle base).transform
          (CCL.CCLPullback.adjugate matrix)).point parameter = value
        exact transformed.2
    · have realNonpositive : unit.re ≤ 0 :=
        (lt_of_not_ge realNonnegative).le
      let parameter := unit.im / (1 - unit.re)
      have covered :=
        reciprocalUnitCircle_covers unit unitNorm realNonpositive
      have sourcePoint :
          (CCL.CanonicalCurves.reciprocalCircle base).point
              parameter = tail := by
        rw [CCL.CanonicalCurves.reciprocalCircle_point_scale]
        calc
          base *
              (CCL.CanonicalCurves.reciprocalCircle 1).point
                parameter = base * unit := by rw [covered.2.2]
          _ = tail := baseUnit
      have transformed := inverseTransform_point matrix determinantNonzero
        (CCL.CanonicalCurves.reciprocalCircle base) parameter
        (CCL.CanonicalCurves.reciprocalCircle_denominator_ne
          base parameter)
        value denominatorNonzero sourcePoint
      let chart : BoundedChart
          (CCL.CCLGeometry.normComparisonForm matrix
            (normSq base)) :=
        { parameterization :=
            CCL.CCLBoundaryCurves.normComparisonReciprocal matrix
              determinantNonzero base
          cell := unitCell }
      refine ⟨chart, ?_, parameter, ?_, ?_, ?_⟩
      · simp only [charts, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inr rfl
      · exact ⟨covered.1, covered.2.1⟩
      · change
          ((CCL.CanonicalCurves.reciprocalCircle base).transform
            (CCL.CCLPullback.adjugate matrix)).denominatorAt
              parameter ≠ 0
        exact transformed.1
      · change
          ((CCL.CanonicalCurves.reciprocalCircle base).transform
            (CCL.CCLPullback.adjugate matrix)).point parameter =
              value
        exact transformed.2

/-- Every curve-source boundary point in the current box is represented by
one of the finite charts that is actually sent to event analysis. -/
def CurveSource.cover
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (box : Box)
    {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin)
    (value : Gaussian) (inside : box.Contains value)
    (onBoundary : form.eval value = 0)
    (referenceLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator reference value)) :
    Coverage source box denominatorMargin marginPositive value := by
  cases source with
  | norm matrix determinantNonzero lowerRow base baseNonzero form_eq =>
      subst form
      exact normSource_cover reference matrix determinantNonzero lowerRow
        base baseNonzero box marginPositive value inside onBoundary
          referenceLower
  | real matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      exact realSource_cover reference matrix determinantNonzero lowerRow
        threshold box marginPositive value inside onBoundary referenceLower
  | imaginary matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      exact imaginarySource_cover reference matrix determinantNonzero lowerRow
        threshold box marginPositive value inside onBoundary referenceLower

/-- Propositional compatibility wrapper around the executable coverage
record. -/
theorem CurveSource.covers
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (box : Box)
    {denominatorMargin : Coordinate}
    (marginPositive : 0 < denominatorMargin)
    (value : Gaussian) (inside : box.Contains value)
    (onBoundary : form.eval value = 0)
    (referenceLower : denominatorMargin ≤
      normSq (CCL.RawParser.denominator reference value)) :
    Covered source box denominatorMargin marginPositive value :=
  (source.cover box marginPositive value inside onBoundary
    referenceLower).covered

theorem charts_ne_nil
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form)
    (box : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) :
    charts source box denominatorMargin marginPositive ≠ [] := by
  cases source <;> simp [charts]

theorem charts_length_le_two
    {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form)
    (box : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) :
    (charts source box denominatorMargin marginPositive).length ≤ 2 := by
  cases source <;> simp [charts]

/-- One squarefree occurrence of the curve-gcd parameter polynomial, paired
with its aligned root/box event partition. -/
structure SquarefreeFactorAnalysis
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree) where
  factor : CCL.CoordinateFactorization.Factor
  member : factor ∈
    (CCL.CurveEvents.eventDecomposition data
      gcdDegreePositive).factors
  conditionProfiles :
    CCL.CoordinateFactorization.ConditionProfiles factor
      (CCL.CurveBoxConditions.profiledConditionPolynomials
        chart.parameterization.curve box)
  partition :
    CCL.CurveBoxEventPartition.SquarefreeEventPartition
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell

def analyzeSquarefreeFactors
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree) :
    List (SquarefreeFactorAnalysis p box chart data gcdDegreePositive) :=
  (CCL.CurveEvents.eventDecomposition data
    gcdDegreePositive).factors.attach.map fun entry =>
      { factor := entry.1
        member := entry.2
        conditionProfiles :=
          CCL.CoordinateFactorization.classifyConditions entry.1
            (CCL.CurveBoxConditions.profiledConditionPolynomials
              chart.parameterization.curve box)
        partition :=
          CCL.CurveBoxEventPartition.classifySquarefreeEvents
            entry.1.polynomial entry.1.nonzero entry.1.squarefree
            chart.parameterization.curve box chart.cell }

/-- One fully condition-profiled squarefree divisor of an original curve-gcd
factor, paired with a fresh aligned event partition for that divisor. -/
structure ConditionProfileAnalysis
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (conditions : List
      CCL.CoordinateFactorization.Polynomial :=
        CCL.CurveBoxConditions.profiledConditionPolynomials
          chart.parameterization.curve box) where
  profile : CCL.CoordinateFactorization.ConditionProfile
    factorAnalysis.factor conditions
  partition :
    CCL.CurveBoxEventPartition.SquarefreeEventPartition
      profile.factor.polynomial profile.factor.nonzero
        profile.factor.squarefree chart.parameterization.curve box chart.cell

/-- Execute aligned event partitions for every equality/apart condition
profile of one original squarefree curve factor. -/
def analyzeConditionProfiles
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    List (ConditionProfileAnalysis factorAnalysis) :=
  factorAnalysis.conditionProfiles.profiles.attach.map fun entry =>
    { profile := entry.1
      partition :=
        CCL.CurveBoxEventPartition.classifySquarefreeEvents
          entry.1.factor.polynomial entry.1.factor.nonzero
            entry.1.factor.squarefree chart.parameterization.curve box
              chart.cell }

/-- Executed finite curve analysis, including a concrete Sturm event
partition on the chart cell in the nonconstant-gcd case. -/
inductive BoundedAnalysis
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form) where
  | identicallyZero
      (realZero :
        (CCL.CurveClear.realPolynomial p
          chart.parameterization.curve).isZero = true)
      (imaginaryZero :
        (CCL.CurveClear.imaginaryPolynomial p
          chart.parameterization.curve).isZero = true)
  | clear
      (certificate : CCL.CurveClear.GlobalClear p
        chart.parameterization.curve)
      (residual : CCL.CurveResidualClearance.Certificate p
        chart.parameterization.curve chart.cell.interval)
  | events
      (data : CCL.CurveEvents.Nontrivial p
        chart.parameterization.curve)
      (gcdDegreePositive : 0 <
        (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).natDegree)
      (squarefreeFactors :
        List (SquarefreeFactorAnalysis p box chart data gcdDegreePositive))
      (factors_eq : squarefreeFactors =
        analyzeSquarefreeFactors p box chart data gcdDegreePositive)

/-- A displayed curve root located in the aligned partition of one
squarefree parameter factor.  This is the repeated-factor-safe event
interface used by the owner layer. -/
structure LocatedSquarefreeCurveRoot
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (parameter : Coordinate) where
  factor : CCL.CoordinateFactorization.Factor
  factorMember : factor ∈
    (CCL.CurveEvents.eventDecomposition data
      gcdDegreePositive).factors
  factorZero : factor.polynomial.eval parameter = 0
  partition :
    CCL.CurveBoxEventPartition.SquarefreeEventPartition
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell
  partition_eq : partition =
    CCL.CurveBoxEventPartition.classifySquarefreeEvents
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell
  location :
    CCL.CurveBoxEventPartition.LocatedSquarefreeParameter
      partition parameter
  boxConditions : CCL.CurveBoxConditions.Holds
    chart.parameterization.curve box parameter

/-- Execute the finite first-zero-factor scan and locate the result in its
already coefficient-bounded aligned partition. -/
def locateSquarefreeCurveRoot
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (parameter : Coordinate)
    (parameterInside : chart.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (root : p.eval (chart.parameterization.curve.point parameter) = 0)
    (inside : box.Contains (chart.parameterization.curve.point parameter)) :
    LocatedSquarefreeCurveRoot p box chart data gcdDegreePositive parameter := by
  let locatedFactor := CCL.CurveEvents.locateFactorRoot data
    gcdDegreePositive parameter denominatorNonzero root
  let partition :=
    CCL.CurveBoxEventPartition.classifySquarefreeEvents
      locatedFactor.factor.polynomial locatedFactor.factor.nonzero
      locatedFactor.factor.squarefree
      chart.parameterization.curve box chart.cell
  exact
    { factor := locatedFactor.factor
      factorMember := locatedFactor.member
      factorZero := locatedFactor.zero
      partition := partition
      partition_eq := rfl
      location := partition.locate parameter parameterInside
      boxConditions :=
        (CCL.CurveBoxConditions.holds_iff_contains
          chart.parameterization.curve box parameter denominatorNonzero).2
            inside }

/-- Analyze one bounded chart and execute its event partition immediately. -/
def analyzeChart
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form) : BoundedAnalysis p box chart := by
  match CCL.CurveEvents.analyze p chart.parameterization.curve with
  | .identicallyZero realZero imaginaryZero =>
      exact .identicallyZero realZero imaginaryZero
  | .clear certificate =>
      exact .clear certificate
        (CCL.CurveResidualClearance.certificate certificate
          chart.cell.interval)
  | .events data degreePositive =>
      exact .events data degreePositive
        (analyzeSquarefreeFactors p box chart data degreePositive) rfl

/-- Analyze every member of the finite bounded chart family. -/
def analyzeCharts
    (p : GaussianPolynomial) {reference : Mat2} {form : HermitianForm}
    (source : CurveSource reference form) (box : Box)
    (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) :
    List (Sigma fun chart : BoundedChart form => BoundedAnalysis p box chart) :=
  (charts source box denominatorMargin marginPositive).map fun chart =>
    ⟨chart, analyzeChart p box chart⟩

/-- Finite bounded analysis corresponding to every kind of boundary
description.  Curve cases retain the executed chart list; finite and
universal zero sets retain their exact pointwise analysis. -/
inductive Outcome
    (p : GaussianPolynomial) (box : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    {reference : Mat2} {form : HermitianForm} :
    CCL.CCLBoundaryDescription.Description reference form → Type
  | curve (source : CurveSource reference form)
      (analyses : List
        (Sigma fun chart : BoundedChart form => BoundedAnalysis p box chart))
      (analyses_eq : analyses =
        analyzeCharts p source box denominatorMargin marginPositive) :
      Outcome p box denominatorMargin marginPositive (.curve source)
  | finite (points : List Gaussian)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
      (evaluations : List
        (CCL.CCLBoundaryAnalysis.EvaluatedPoint p))
      (evaluations_eq : evaluations =
        CCL.CCLBoundaryAnalysis.evaluatePoints p points) :
      Outcome p box denominatorMargin marginPositive
        (.finite points complete nonnegative)
  | universal (zero : ∀ value, form.eval value = 0) :
      Outcome p box denominatorMargin marginPositive (.universal zero)

/-- A boundary description paired with the finite analyses of precisely the
bounded charts relevant to the current box. -/
structure AnalyzedBoundary
    (p : GaussianPolynomial) (reference : Mat2) (form : HermitianForm)
    (box : Box) (denominatorMargin : Coordinate) where
  marginPositive : 0 < denominatorMargin
  description :
    CCL.CCLBoundaryDescription.Description reference form
  outcome : Outcome p box denominatorMargin marginPositive description

/-- Generate and execute all bounded analyses for one described boundary. -/
def analyze
    (p : GaussianPolynomial) (box : Box)
    (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    {reference : Mat2} {form : HermitianForm}
    (description :
      CCL.CCLBoundaryDescription.Description reference form) :
    AnalyzedBoundary p reference form box denominatorMargin := by
  cases description with
  | curve source =>
      exact
        { marginPositive := marginPositive
          description := .curve source
          outcome := .curve source
            (analyzeCharts p source box denominatorMargin marginPositive) rfl }
  | finite points complete nonnegative =>
      exact
        { marginPositive := marginPositive
          description := .finite points complete nonnegative
          outcome := .finite points complete nonnegative
            (CCL.CCLBoundaryAnalysis.evaluatePoints p points) rfl }
  | universal zero =>
      exact
        { marginPositive := marginPositive
          description := .universal zero
          outcome := .universal zero }

end CCL.CCLBoundaryCharts
