import FTA.CCLBranchPlan
import FTA.GaussianPolynomialBounds
import FTA.CCLPathIntersection

/-!
# Finite bounded charts for CCL branch curves

The circle boundaries in Section 10.1 are covered by two fixed rational
parameter intervals `[-1,1]`.  A coordinate-line boundary needs one additional
finite bound: if its inverse image meets a rational root box on which the
decoder denominator has squared norm at least `δ > 0`, then its affine line
parameter is bounded by a coefficient evaluation majorant divided by `δ`.

This module packages those intervals as finite proof-bearing chart records.
It is the bounded input required by the common Sturm partition and curve-count
pipeline in Theorem 10.2.
-/

namespace FTA
namespace CCLBranchCharts

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.GaussianPolynomialBounds
open FTA.CCLGeometry
open FTA.CCLBoundaryPath
open FTA.CCLBranchPlan
open FTA.CCLBranchPlan.BoundarySource
open FTA.CCLFormulaPullback
open FTA.ProjectivePath

abbrev QI := CCL.GaussianRat
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- The affine numerator `aZ+b` of a displayed branch homography, in the
sparse polynomial representation consumed by the global box evaluator. -/
def affineNumeratorPolynomial (matrix : Mat2 QI) : DensePolynomial QI :=
  ⟨[matrix.a, matrix.b]⟩

@[simp] theorem eval_affineNumeratorPolynomial (matrix : Mat2 QI) (z : QI) :
    (affineNumeratorPolynomial matrix).eval z = matrix.a * z + matrix.b := by
  simp [affineNumeratorPolynomial, DensePolynomial.eval,
    DensePolynomial.evalCoeffs]

/-- Coefficient-computed upper bound for the squared norm of the decoded
point throughout a box with a positive denominator lower bound. -/
def decodedNormMajorant
    (source : BoundarySource) (box : RatBox) (denominatorLower : ℚ) : ℚ :=
  denseEvalNormMajorant (affineNumeratorPolynomial source.matrix) box /
    denominatorLower

theorem decodedNormMajorant_pos
    (source : BoundarySource) (box : RatBox) {denominatorLower : ℚ}
    (positive : 0 < denominatorLower) :
    0 < decodedNormMajorant source box denominatorLower := by
  exact div_pos
    (zero_lt_one.trans_le
      (one_le_denseEvalNormMajorant
        (affineNumeratorPolynomial source.matrix) box))
    positive

/-- The finite symmetric radius used for a coordinate-line chart.  Adding
one avoids a square root while retaining a strict positive radius. -/
def lineParameterRadius
    (source : BoundarySource) (box : RatBox) (denominatorLower : ℚ) : ℚ :=
  decodedNormMajorant source box denominatorLower + 1

theorem lineParameterRadius_pos
    (source : BoundarySource) (box : RatBox) {denominatorLower : ℚ}
    (positive : 0 < denominatorLower) :
    0 < lineParameterRadius source box denominatorLower := by
  have hmajorant := decodedNormMajorant_pos source box positive
  dsimp [lineParameterRadius]
  linarith

/-- The affine homography value is uniformly norm-bounded on the input box
once its displayed denominator has the supplied positive lower bound. -/
theorem normSq_homographic_le_decodedNormMajorant
    (source : BoundarySource) (box : RatBox) {denominatorLower : ℚ}
    (lowerPositive : 0 < denominatorLower) {z : QI}
    (contains : box.Contains z)
    (denominatorLowerBound :
      denominatorLower ≤
        normSq (source.matrix.c * z + source.matrix.d)) :
    normSq (RatBox.homographic source.matrix z) ≤
      decodedNormMajorant source box denominatorLower := by
  have denominatorPositive :
      0 < normSq (source.matrix.c * z + source.matrix.d) :=
    lowerPositive.trans_le denominatorLowerBound
  have denominatorNonzero : source.matrix.c * z + source.matrix.d ≠ 0 :=
    by
      intro zero
      rw [zero, normSq_zero] at denominatorPositive
      linarith
  have numeratorBound :
      normSq (source.matrix.a * z + source.matrix.b) ≤
        denseEvalNormMajorant
          (affineNumeratorPolynomial source.matrix) box := by
    simpa only [eval_affineNumeratorPolynomial] using
      normSq_dense_eval_le_denseEvalNormMajorant
        (affineNumeratorPolynomial source.matrix) contains
  rw [normSq_homographic source.matrix z denominatorNonzero]
  apply (div_le_div_iff₀ denominatorPositive lowerPositive).2
  calc
    normSq (source.matrix.a * z + source.matrix.b) * denominatorLower ≤
        denseEvalNormMajorant
          (affineNumeratorPolynomial source.matrix) box *
          denominatorLower := by
      exact mul_le_mul_of_nonneg_right numeratorBound lowerPositive.le
    _ ≤ denseEvalNormMajorant
          (affineNumeratorPolynomial source.matrix) box *
          normSq (source.matrix.c * z + source.matrix.d) := by
      exact mul_le_mul_of_nonneg_left denominatorLowerBound
        (zero_le_one.trans
          (one_le_denseEvalNormMajorant
            (affineNumeratorPolynomial source.matrix) box))

private theorem abs_le_majorant_add_one {t majorant : ℚ}
    (majorantNonnegative : 0 ≤ majorant) (squareBound : t ^ 2 ≤ majorant) :
    |t| ≤ majorant + 1 := by
  have radiusNonnegative : 0 ≤ majorant + 1 := by linarith
  apply (sq_le_sq₀ (abs_nonneg t) radiusNonnegative).1
  rw [sq_abs]
  exact squareBound.trans (by nlinarith [sq_nonneg majorant])

/-- Every real-boundary parameter whose inverse path meets the box lies in
the computed finite symmetric interval. -/
theorem real_parameter_abs_le
    (matrix : Mat2 QI) (threshold : ℚ) (box : RatBox)
    {denominatorLower t : ℚ} (lowerPositive : 0 < denominatorLower)
    (determinantNonzero : determinant matrix ≠ 0)
    (pathDenominator :
      (BoundarySource.real matrix threshold).path.denominator.eval
        (PathPolynomial.ofRat t) ≠ 0)
    (contains : box.Contains
      ((BoundarySource.real matrix threshold).path.value t))
    (denominatorLowerBound :
      denominatorLower ≤ normSq
        (matrix.c * (BoundarySource.real matrix threshold).path.value t +
          matrix.d)) :
    |t| ≤ lineParameterRadius
      (.real matrix threshold) box denominatorLower := by
  let source : BoundarySource := .real matrix threshold
  have decoded := source.decoded_path_value t determinantNonzero pathDenominator
  have decodedBound := normSq_homographic_le_decodedNormMajorant
    source box lowerPositive contains denominatorLowerBound
  have coordinate :
      (RatBox.homographic matrix
        ((BoundarySource.real matrix threshold).path.value t)).im = t := by
    have decoded' :
        RatBox.homographic matrix
            ((BoundarySource.real matrix threshold).path.value t) =
          (linePath ⟨threshold, 0⟩ ⟨0, 1⟩).value t := by
      simpa [source, BoundarySource.matrix,
        BoundarySource.standardPath] using decoded
    rw [decoded']
    simp [linePath_value,
      CCLGeometry.ofRat]
  have decodedBound' :
      normSq (RatBox.homographic matrix
        ((BoundarySource.real matrix threshold).path.value t)) ≤
        decodedNormMajorant
          (.real matrix threshold) box denominatorLower := by
    simpa [source, BoundarySource.matrix] using decodedBound
  have squareBound :
      t ^ 2 ≤ decodedNormMajorant
        (.real matrix threshold) box denominatorLower := by
    rw [normSq] at decodedBound'
    rw [coordinate] at decodedBound'
    nlinarith [sq_nonneg
      (RatBox.homographic matrix
        ((BoundarySource.real matrix threshold).path.value t)).re]
  exact abs_le_majorant_add_one
    (decodedNormMajorant_pos
      (.real matrix threshold) box lowerPositive).le squareBound

/-- Every imaginary-boundary parameter whose inverse path meets the box lies
in the computed finite symmetric interval. -/
theorem imag_parameter_abs_le
    (matrix : Mat2 QI) (threshold : ℚ) (box : RatBox)
    {denominatorLower t : ℚ} (lowerPositive : 0 < denominatorLower)
    (determinantNonzero : determinant matrix ≠ 0)
    (pathDenominator :
      (BoundarySource.imag matrix threshold).path.denominator.eval
        (PathPolynomial.ofRat t) ≠ 0)
    (contains : box.Contains
      ((BoundarySource.imag matrix threshold).path.value t))
    (denominatorLowerBound :
      denominatorLower ≤ normSq
        (matrix.c * (BoundarySource.imag matrix threshold).path.value t +
          matrix.d)) :
    |t| ≤ lineParameterRadius
      (.imag matrix threshold) box denominatorLower := by
  let source : BoundarySource := .imag matrix threshold
  have decoded := source.decoded_path_value t determinantNonzero pathDenominator
  have decodedBound := normSq_homographic_le_decodedNormMajorant
    source box lowerPositive contains denominatorLowerBound
  have coordinate :
      (RatBox.homographic matrix
        ((BoundarySource.imag matrix threshold).path.value t)).re = t := by
    have decoded' :
        RatBox.homographic matrix
            ((BoundarySource.imag matrix threshold).path.value t) =
          (linePath ⟨0, threshold⟩ ⟨1, 0⟩).value t := by
      simpa [source, BoundarySource.matrix,
        BoundarySource.standardPath] using decoded
    rw [decoded']
    simp [linePath_value,
      CCLGeometry.ofRat]
  have decodedBound' :
      normSq (RatBox.homographic matrix
        ((BoundarySource.imag matrix threshold).path.value t)) ≤
        decodedNormMajorant
          (.imag matrix threshold) box denominatorLower := by
    simpa [source, BoundarySource.matrix] using decodedBound
  have squareBound :
      t ^ 2 ≤ decodedNormMajorant
        (.imag matrix threshold) box denominatorLower := by
    rw [normSq] at decodedBound'
    rw [coordinate] at decodedBound'
    nlinarith [sq_nonneg
      (RatBox.homographic matrix
        ((BoundarySource.imag matrix threshold).path.value t)).im]
  exact abs_le_majorant_add_one
    (decodedNormMajorant_pos
      (.imag matrix threshold) box lowerPositive).le squareBound

/-! ## Complete bounded coverage of norm-circle parameters -/

/-- Every affine parameter of the primary norm-circle path is either already
in `[-1,1]` or represents the same inverse-image point in the reciprocal
chart at a parameter in `[-1,1]`.  The reciprocal chart at zero additionally
contains the primary chart's missing projective point. -/
theorem norm_primary_parameter_covered
    (matrix : Mat2 QI) (scaleValue : QI) (t : ℚ) :
    (-1 ≤ t ∧ t ≤ 1) ∨
      ∃ s : ℚ, -1 ≤ s ∧ s ≤ 1 ∧
        (inverseScaledCirclePath matrix scaleValue).value t =
          (inverseReciprocalScaledCirclePath matrix scaleValue).value s := by
  by_cases bounded : |t| ≤ 1
  · exact Or.inl (abs_le.mp bounded)
  · have large : 1 < |t| := lt_of_not_ge bounded
    have absPositive : 0 < |t| := zero_lt_one.trans large
    have nonzero : t ≠ 0 := abs_pos.mp absPositive
    let s : ℚ := 1 / t
    have reciprocalAbs : |s| < 1 := by
      dsimp [s]
      rw [abs_div, abs_one]
      exact (div_lt_one absPositive).2 large
    rcases abs_le.mp reciprocalAbs.le with ⟨lower, upper⟩
    refine Or.inr ⟨s, lower, upper, ?_⟩
    have primaryValue :
        (inverseScaledCirclePath matrix scaleValue).value t =
          RatBox.homographic (adjugate matrix)
            ((scaledCirclePath scaleValue).value t) := by
      exact actPath_value (adjugate matrix)
        (scaledCirclePath scaleValue) t
        (unitCirclePath_denominator_ne t)
    have reciprocalValue :
        (inverseReciprocalScaledCirclePath matrix scaleValue).value s =
          RatBox.homographic (adjugate matrix)
            ((reciprocalScaledCirclePath scaleValue).value s) := by
      exact actPath_value (adjugate matrix)
        (reciprocalScaledCirclePath scaleValue) s
        (reciprocalUnitCirclePath_denominator_ne s)
    rw [primaryValue, reciprocalValue, scaledCirclePath_value,
      reciprocalScaledCirclePath_value]
    rw [unitCircleParam_eq_reciprocalUnitCircleParam_inv nonzero]

/-- One bounded affine chart of a displayed branch source. -/
structure BoundedChart (source : BoundarySource) where
  path : Path
  interval : RationalInterval
  proper : interval.Proper
  pathMember : path ∈ source.paths

/-- Every planned bounded chart inherits the explicit homogeneous norm floor
of its standard circle or line through the adjugate matrix estimate. -/
theorem BoundedChart.adjugateHomogeneousLower_le
    {source : BoundarySource} (chart : BoundedChart source) (t : ℚ) :
    CCLBoundaryPath.adjugateHomogeneousLower source.matrix ≤
      normSq (chart.path.numerator.eval (PathPolynomial.ofRat t)) +
        normSq (chart.path.denominator.eval (PathPolynomial.ofRat t)) := by
  cases source with
  | norm matrix scaleValue =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rcases member with primary | reciprocal
      · rw [primary]
        exact CCLBoundaryPath.adjugateHomogeneousLower_le matrix
          (scaledCirclePath scaleValue) t
            (scaledCirclePath_homogeneousNorm_one_le scaleValue t)
      · rw [reciprocal]
        exact CCLBoundaryPath.adjugateHomogeneousLower_le matrix
          (reciprocalScaledCirclePath scaleValue) t
            (reciprocalScaledCirclePath_homogeneousNorm_one_le scaleValue t)
  | real matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member]
      exact CCLBoundaryPath.adjugateHomogeneousLower_le matrix
        (linePath ⟨threshold, 0⟩ ⟨0, 1⟩) t
          (linePath_homogeneousNorm_one_le ⟨threshold, 0⟩ ⟨0, 1⟩ t)
  | imag matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member]
      exact CCLBoundaryPath.adjugateHomogeneousLower_le matrix
        (linePath ⟨0, threshold⟩ ⟨1, 0⟩) t
          (linePath_homogeneousNorm_one_le ⟨0, threshold⟩ ⟨1, 0⟩ t)

/-- Denominator-norm threshold below which an affine value cannot remain in
the displayed bounded box. -/
def BoundedChart.poleDenominatorThreshold
    {source : BoundarySource} (_chart : BoundedChart source)
    (box : RatBox) : ℚ :=
  CCLBoundaryPath.adjugateHomogeneousLower source.matrix /
    (FTA.boxNormBound box + 1)

theorem BoundedChart.poleDenominatorThreshold_pos
    {source : BoundarySource} (chart : BoundedChart source)
    (box : RatBox) (determinantNonzero : determinant source.matrix ≠ 0) :
    0 < chart.poleDenominatorThreshold box :=
  div_pos (CCLBoundaryPath.adjugateHomogeneousLower_pos source.matrix
    determinantNonzero) (by
      linarith [FTA.one_le_boxNormBound box])

/-- Quantitative pole exclusion: if the homogeneous denominator is small
relative to the transported homogeneous norm floor, an affine chart value is
too large to lie in the bounded box. -/
theorem BoundedChart.not_contains_of_denominatorNorm_lt_threshold
    {source : BoundarySource} (chart : BoundedChart source)
    (box : RatBox) (t : ℚ)
    (denominatorNonzero :
      chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (denominatorSmall :
      normSq (chart.path.denominator.eval (PathPolynomial.ofRat t)) <
        chart.poleDenominatorThreshold box) :
    ¬box.Contains (chart.path.value t) := by
  intro contains
  let numerator := chart.path.numerator.eval (PathPolynomial.ofRat t)
  let denominator := chart.path.denominator.eval (PathPolynomial.ofRat t)
  let value := chart.path.value t
  let lower := CCLBoundaryPath.adjugateHomogeneousLower source.matrix
  let boxBound := FTA.boxNormBound box
  have denominatorNormPositive : 0 < normSq denominator :=
    normSq_pos denominatorNonzero
  have valueBound : normSq value ≤ boxBound := by
    exact FTA.normSq_le_boxNormBound contains
  have normIdentity : normSq numerator =
      normSq denominator * normSq value := by
    change normSq numerator =
      normSq denominator * normSq (numerator * inv denominator)
    rw [normSq_mul, normSq_inv _ denominatorNonzero]
    simp only [one_div]
    change normSq numerator = normSq denominator *
      (normSq numerator * (normSq denominator)⁻¹)
    have denominatorNormNonzero : normSq denominator ≠ 0 :=
      denominatorNormPositive.ne'
    have cancel : (normSq denominator)⁻¹ * normSq denominator = 1 :=
      inv_mul_cancel₀ denominatorNormNonzero
    calc
      normSq numerator = normSq numerator * 1 := by ring
      _ = normSq numerator *
          ((normSq denominator)⁻¹ * normSq denominator) := by rw [cancel]
      _ = normSq denominator *
          (normSq numerator * (normSq denominator)⁻¹) := by ring
  have homogeneousLower : lower ≤
      normSq numerator + normSq denominator := by
    simpa only [lower, numerator, denominator] using
      chart.adjugateHomogeneousLower_le t
  have boundedHomogeneous :
      normSq numerator + normSq denominator ≤
        normSq denominator * (boxBound + 1) := by
    rw [normIdentity]
    calc
      normSq denominator * normSq value + normSq denominator =
          normSq denominator * (normSq value + 1) := by ring
      _ ≤ normSq denominator * (boxBound + 1) :=
        mul_le_mul_of_nonneg_left (by linarith)
          denominatorNormPositive.le
  have thresholdIdentity : chart.poleDenominatorThreshold box =
      lower / (boxBound + 1) := rfl
  rw [thresholdIdentity] at denominatorSmall
  have boxFactorPositive : 0 < boxBound + 1 := by
    dsimp only [boxBound]
    linarith [FTA.one_le_boxNormBound box]
  have scaledSmall : normSq denominator * (boxBound + 1) < lower := by
    exact (lt_div_iff₀ boxFactorPositive).mp denominatorSmall
  exact (not_lt_of_ge (homogeneousLower.trans boundedHomogeneous)) scaledSmall

/-- Every nondegenerate bounded chart of an invertible source has a
nonzero rational denominator-norm polynomial. -/
theorem BoundedChart.denominatorNorm_isZero_false
    {source : BoundarySource} (chart : BoundedChart source)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    (CCLPathIntersection.denominatorNorm chart.path).isZero = false := by
  have ofWitness {path : Path}
      (witness :
        path.denominator.eval (PathPolynomial.ofRat 0) ≠ 0 ∨
          path.denominator.eval (PathPolynomial.ofRat 1) ≠ 0) :
      (CCLPathIntersection.denominatorNorm path).isZero = false := by
    rcases witness with nonzero | nonzero
    · exact CCLPathIntersection.denominatorNorm_isZero_false_of_eval_ne
        path 0 nonzero
    · exact CCLPathIntersection.denominatorNorm_isZero_false_of_eval_ne
        path 1 nonzero
  cases source with
  | norm matrix scaleValue =>
      have scaleNonzero : scaleValue ≠ 0 := by
        simpa [BoundarySource.ParametrizationNondegenerate] using nondegenerate
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rcases member with primary | reciprocal
      · rw [primary]
        exact ofWitness
          (inverseScaledCirclePath_denominator_ne_at_zero_or_one
            matrix scaleValue determinantNonzero scaleNonzero)
      · rw [reciprocal]
        exact ofWitness
          (inverseReciprocalScaledCirclePath_denominator_ne_at_zero_or_one
            matrix scaleValue determinantNonzero scaleNonzero)
  | real matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member]
      exact ofWitness
        (inverseRealBoundaryPath_denominator_ne_at_zero_or_one
          matrix threshold determinantNonzero)
  | imag matrix threshold =>
      have member := chart.pathMember
      simp [BoundarySource.paths] at member
      rw [member]
      exact ofWitness
        (inverseImagBoundaryPath_denominator_ne_at_zero_or_one
          matrix threshold determinantNonzero)

/-- The complete finite chart input: two fixed unit intervals for a norm
circle, or one coefficient-bounded symmetric interval for a coordinate line. -/
def charts (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    List (BoundedChart source) :=
  match source with
  | .norm matrix scaleValue =>
      [{ path := inverseScaledCirclePath matrix scaleValue
         interval := ⟨-1, 1⟩
         proper := by
           show (-1 : ℚ) < 1
           norm_num
         pathMember := by simp [BoundarySource.paths] },
       { path := inverseReciprocalScaledCirclePath matrix scaleValue
         interval := ⟨-1, 1⟩
         proper := by
           show (-1 : ℚ) < 1
           norm_num
         pathMember := by simp [BoundarySource.paths] }]
  | .real matrix threshold =>
      [{ path := inverseRealBoundaryPath matrix threshold
         interval :=
           let radius := lineParameterRadius
             (.real matrix threshold) box denominatorLower
           ⟨-radius, radius⟩
         proper := by
           dsimp
           have := lineParameterRadius_pos
             (.real matrix threshold) box lowerPositive
           show -lineParameterRadius
             (.real matrix threshold) box denominatorLower <
               lineParameterRadius
                 (.real matrix threshold) box denominatorLower
           linarith
         pathMember := by simp [BoundarySource.paths] }]
  | .imag matrix threshold =>
      [{ path := inverseImagBoundaryPath matrix threshold
         interval :=
           let radius := lineParameterRadius
             (.imag matrix threshold) box denominatorLower
           ⟨-radius, radius⟩
         proper := by
           dsimp
           have := lineParameterRadius_pos
             (.imag matrix threshold) box lowerPositive
           show -lineParameterRadius
             (.imag matrix threshold) box denominatorLower <
               lineParameterRadius
                 (.imag matrix threshold) box denominatorLower
           linarith
         pathMember := by simp [BoundarySource.paths] }]

theorem charts_ne_nil
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    charts source box denominatorLower lowerPositive ≠ [] := by
  cases source <;> simp [charts]

theorem charts_length_le_two
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    (charts source box denominatorLower lowerPositive).length ≤ 2 := by
  cases source <;> simp [charts]

/-! ## Reverse coverage of rational boundary points -/

/-- A rational point on a decoded norm circle is represented by one of the
two bounded rational circle charts.  The result also retains the nonzero
polynomial denominator needed by the downstream Sturm partition. -/
theorem norm_boundary_bounded_chart
    (matrix : Mat2 QI) (scaleValue point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (scaleNonzero : scaleValue ≠ 0)
    (denominatorNonzero : matrix.c * point + matrix.d ≠ 0)
    (boundary : (normComparisonForm matrix (normSq scaleValue)).eval point = 0) :
    (∃ t : ℚ, -1 ≤ t ∧ t ≤ 1 ∧
      (inverseScaledCirclePath matrix scaleValue).denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
      (inverseScaledCirclePath matrix scaleValue).value t = point) ∨
    (∃ t : ℚ, -1 ≤ t ∧ t ≤ 1 ∧
      (inverseReciprocalScaledCirclePath matrix scaleValue).denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
      (inverseReciprocalScaledCirclePath matrix scaleValue).value t = point) := by
  let decoded := RatBox.homographic matrix point
  have denominatorNormNonzero : normSq (matrix.c * point + matrix.d) ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  have decodedNorm : normSq decoded = normSq scaleValue := by
    rw [normSq_homographic matrix point denominatorNonzero]
    rw [eval_normComparisonForm] at boundary
    apply (div_eq_iff denominatorNormNonzero).2
    linarith
  let unit := decoded * inv scaleValue
  have unitNorm : normSq unit = 1 := by
    dsimp only [unit]
    rw [normSq_mul, normSq_inv scaleValue scaleNonzero, decodedNorm]
    have scaleNormNonzero : normSq scaleValue ≠ 0 :=
      fun zero => scaleNonzero (normSq_eq_zero.mp zero)
    field_simp [scaleNormNonzero]
  by_cases missing : unit.re = -1
  · have standardValue :
        (reciprocalScaledCirclePath scaleValue).value 0 = decoded := by
      rw [reciprocalScaledCirclePath_value,
        reciprocalUnitCircleParam_zero_of_missing unit unitNorm missing]
      dsimp only [unit]
      calc
        scaleValue * (decoded * inv scaleValue) =
            decoded * (scaleValue * inv scaleValue) := by ring
        _ = decoded := by rw [mul_inv _ scaleNonzero, mul_one]
    have inverseDenominator := adjugate_denominator_homographic_ne matrix point
      determinantNonzero denominatorNonzero
    have pathDenominator := actPath_denominator_ne_of_homographic
      (adjugate matrix) (reciprocalScaledCirclePath scaleValue) 0
        (reciprocalUnitCirclePath_denominator_ne 0) (by
          rw [standardValue]
          exact inverseDenominator)
    refine Or.inr ⟨0, by norm_num, by norm_num, ?_, ?_⟩
    · simpa [inverseReciprocalScaledCirclePath] using pathDenominator
    rw [inverseReciprocalScaledCirclePath]
    rw [actPath_value (adjugate matrix) (reciprocalScaledCirclePath scaleValue)
      0 (reciprocalUnitCirclePath_denominator_ne 0), standardValue]
    exact homographic_adjugate_forward_inverse matrix point
      determinantNonzero denominatorNonzero
  · let t := unit.im / (1 + unit.re)
    have standardValue :
        (scaledCirclePath scaleValue).value t = decoded := by
      rw [scaledCirclePath_value, unitCircleParam_inverse unit unitNorm missing]
      dsimp only [unit]
      calc
        scaleValue * (decoded * inv scaleValue) =
            decoded * (scaleValue * inv scaleValue) := by ring
        _ = decoded := by rw [mul_inv _ scaleNonzero, mul_one]
    have inverseDenominator := adjugate_denominator_homographic_ne matrix point
      determinantNonzero denominatorNonzero
    have primaryDenominator := actPath_denominator_ne_of_homographic
      (adjugate matrix) (scaledCirclePath scaleValue) t
        (unitCirclePath_denominator_ne t) (by
          rw [standardValue]
          exact inverseDenominator)
    have primaryValue :
        (inverseScaledCirclePath matrix scaleValue).value t = point := by
      rw [inverseScaledCirclePath]
      rw [actPath_value (adjugate matrix) (scaledCirclePath scaleValue) t
        (unitCirclePath_denominator_ne t), standardValue]
      exact homographic_adjugate_forward_inverse matrix point
        determinantNonzero denominatorNonzero
    by_cases bounded : |t| ≤ 1
    · exact Or.inl ⟨t, (abs_le.mp bounded).1, (abs_le.mp bounded).2,
        by simpa [inverseScaledCirclePath] using primaryDenominator,
        primaryValue⟩
    · have large : 1 < |t| := lt_of_not_ge bounded
      have nonzero : t ≠ 0 := by
        intro zero
        rw [zero, abs_zero] at large
        norm_num at large
      let s : ℚ := 1 / t
      have reciprocalAbs : |s| < 1 := by
        dsimp only [s]
        rw [abs_div, abs_one]
        exact (div_lt_one (abs_pos.mpr nonzero)).2 large
      have reciprocalStandardValue :
          (reciprocalScaledCirclePath scaleValue).value s = decoded := by
        rw [reciprocalScaledCirclePath_value,
          ← unitCircleParam_eq_reciprocalUnitCircleParam_inv nonzero,
          ← scaledCirclePath_value]
        exact standardValue
      have reciprocalDenominator := actPath_denominator_ne_of_homographic
        (adjugate matrix) (reciprocalScaledCirclePath scaleValue) s
          (reciprocalUnitCirclePath_denominator_ne s) (by
            rw [reciprocalStandardValue]
            exact inverseDenominator)
      rcases abs_le.mp reciprocalAbs.le with ⟨lower, upper⟩
      refine Or.inr ⟨s, lower, upper, ?_, ?_⟩
      · simpa [inverseReciprocalScaledCirclePath] using reciprocalDenominator
      rw [inverseReciprocalScaledCirclePath]
      rw [actPath_value (adjugate matrix)
        (reciprocalScaledCirclePath scaleValue) s
          (reciprocalUnitCirclePath_denominator_ne s), reciprocalStandardValue]
      exact homographic_adjugate_forward_inverse matrix point
        determinantNonzero denominatorNonzero

/-- Exact rational parameter of a rational point on an inverse real-coordinate
boundary, including the acted-path denominator certificate. -/
theorem real_boundary_parameter
    (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominatorNonzero : matrix.c * point + matrix.d ≠ 0)
    (boundary : (realComparisonForm matrix threshold).eval point = 0) :
    ∃ t : ℚ,
      (inverseRealBoundaryPath matrix threshold).denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
        (inverseRealBoundaryPath matrix threshold).value t = point := by
  let decoded := RatBox.homographic matrix point
  let t := decoded.im
  have decodedReal : decoded.re = threshold :=
    (real_homographic_eq_iff matrix point threshold denominatorNonzero).2 boundary
  have standardValue :
      (linePath ⟨threshold, 0⟩ ⟨0, 1⟩).value t = decoded := by
    rw [linePath_value]
    apply GaussianRat.ext
    · simp [CCLGeometry.ofRat, decodedReal]
    · simp [CCLGeometry.ofRat, t]
  have inverseDenominator := adjugate_denominator_homographic_ne matrix point
    determinantNonzero denominatorNonzero
  have pathDenominator := actPath_denominator_ne_of_homographic
    (adjugate matrix) (linePath ⟨threshold, 0⟩ ⟨0, 1⟩) t
      (linePath_denominator_ne _ _ t) (by
        rw [standardValue]
        exact inverseDenominator)
  refine ⟨t, ?_, ?_⟩
  · simpa [inverseRealBoundaryPath, inverseLinePath] using pathDenominator
  · rw [inverseRealBoundaryPath, inverseLinePath,
      actPath_value (adjugate matrix) (linePath ⟨threshold, 0⟩ ⟨0, 1⟩) t
        (linePath_denominator_ne _ _ t), standardValue]
    exact homographic_adjugate_forward_inverse matrix point
      determinantNonzero denominatorNonzero

/-- Exact rational parameter of a rational point on an inverse imaginary-
coordinate boundary, including the acted-path denominator certificate. -/
theorem imag_boundary_parameter
    (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominatorNonzero : matrix.c * point + matrix.d ≠ 0)
    (boundary : (imagComparisonForm matrix threshold).eval point = 0) :
    ∃ t : ℚ,
      (inverseImagBoundaryPath matrix threshold).denominator.eval
          (PathPolynomial.ofRat t) ≠ 0 ∧
        (inverseImagBoundaryPath matrix threshold).value t = point := by
  let decoded := RatBox.homographic matrix point
  let t := decoded.re
  have decodedImag : decoded.im = threshold :=
    (imag_homographic_eq_iff matrix point threshold denominatorNonzero).2 boundary
  have standardValue :
      (linePath ⟨0, threshold⟩ ⟨1, 0⟩).value t = decoded := by
    rw [linePath_value]
    apply GaussianRat.ext
    · simp [CCLGeometry.ofRat, t]
    · simp [CCLGeometry.ofRat, decodedImag]
  have inverseDenominator := adjugate_denominator_homographic_ne matrix point
    determinantNonzero denominatorNonzero
  have pathDenominator := actPath_denominator_ne_of_homographic
    (adjugate matrix) (linePath ⟨0, threshold⟩ ⟨1, 0⟩) t
      (linePath_denominator_ne _ _ t) (by
        rw [standardValue]
        exact inverseDenominator)
  refine ⟨t, ?_, ?_⟩
  · simpa [inverseImagBoundaryPath, inverseLinePath] using pathDenominator
  · rw [inverseImagBoundaryPath, inverseLinePath,
      actPath_value (adjugate matrix) (linePath ⟨0, threshold⟩ ⟨1, 0⟩) t
        (linePath_denominator_ne _ _ t), standardValue]
    exact homographic_adjugate_forward_inverse matrix point
      determinantNonzero denominatorNonzero

/-- Every rational affine point of a planned generalized-circle boundary is
covered by one of its finite bounded rational charts.  This is the reverse
direction of `BoundedChart.onBoundary` and turns all-clear chart exclusion
into exclusion of actual rational boundary points. -/
theorem BoundarySource.charts_cover_boundary_point
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate)
    (point : QI) (contains : box.Contains point)
    (denominatorLowerBound : denominatorLower ≤
      normSq (source.matrix.c * point + source.matrix.d))
    (boundary : source.form.eval point = 0) :
    ∃ chart ∈ charts source box denominatorLower lowerPositive,
      ∃ t : ℚ,
        chart.interval.lower ≤ t ∧ t ≤ chart.interval.upper ∧
        chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 ∧
        chart.path.value t = point := by
  have denominatorPositive :
      0 < normSq (source.matrix.c * point + source.matrix.d) :=
    lowerPositive.trans_le denominatorLowerBound
  have denominatorNonzero : source.matrix.c * point + source.matrix.d ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at denominatorPositive
    linarith
  cases source with
  | norm matrix scaleValue =>
      have scaleNonzero : scaleValue ≠ 0 := by
        simpa [BoundarySource.ParametrizationNondegenerate] using nondegenerate
      rcases norm_boundary_bounded_chart matrix scaleValue point
          determinantNonzero scaleNonzero denominatorNonzero boundary with
        ⟨t, lower, upper, pathDenominator, pathValue⟩ |
          ⟨t, lower, upper, pathDenominator, pathValue⟩
      · let chart : BoundedChart (.norm matrix scaleValue) :=
          { path := inverseScaledCirclePath matrix scaleValue
            interval := ⟨-1, 1⟩
            proper := by
              show (-1 : ℚ) < 1
              norm_num
            pathMember := by simp [BoundarySource.paths] }
        refine ⟨chart, ?_, t, ?_, ?_, ?_, ?_⟩
        · simp [charts, chart]
        · simpa [chart] using lower
        · simpa [chart] using upper
        · simpa [chart] using pathDenominator
        · simpa [chart] using pathValue
      · let chart : BoundedChart (.norm matrix scaleValue) :=
          { path := inverseReciprocalScaledCirclePath matrix scaleValue
            interval := ⟨-1, 1⟩
            proper := by
              show (-1 : ℚ) < 1
              norm_num
            pathMember := by simp [BoundarySource.paths] }
        refine ⟨chart, ?_, t, ?_, ?_, ?_, ?_⟩
        · simp [charts, chart]
        · simpa [chart] using lower
        · simpa [chart] using upper
        · simpa [chart] using pathDenominator
        · simpa [chart] using pathValue
  | real matrix threshold =>
      rcases real_boundary_parameter matrix threshold point
          determinantNonzero denominatorNonzero boundary with
        ⟨t, pathDenominator, pathValue⟩
      have pathContains : box.Contains
          ((BoundarySource.real matrix threshold).path.value t) := by
        rw [BoundarySource.path_real, pathValue]
        exact contains
      have pathDenominatorLower : denominatorLower ≤ normSq
          (matrix.c * (BoundarySource.real matrix threshold).path.value t +
            matrix.d) := by
        rw [BoundarySource.path_real, pathValue]
        exact denominatorLowerBound
      have bounded := real_parameter_abs_le matrix threshold box lowerPositive
        determinantNonzero pathDenominator pathContains pathDenominatorLower
      rcases abs_le.mp bounded with ⟨lower, upper⟩
      let chart : BoundedChart (.real matrix threshold) :=
        { path := inverseRealBoundaryPath matrix threshold
          interval :=
            let radius := lineParameterRadius
              (.real matrix threshold) box denominatorLower
            ⟨-radius, radius⟩
          proper := by
            dsimp
            have radiusPositive := lineParameterRadius_pos
              (.real matrix threshold) box lowerPositive
            exact neg_lt_self radiusPositive
          pathMember := by simp [BoundarySource.paths] }
      refine ⟨chart, ?_, t, ?_, ?_, ?_, ?_⟩
      · simp [charts, chart]
      · simpa [chart] using lower
      · simpa [chart] using upper
      · simpa [chart] using pathDenominator
      · simpa [chart] using pathValue
  | imag matrix threshold =>
      rcases imag_boundary_parameter matrix threshold point
          determinantNonzero denominatorNonzero boundary with
        ⟨t, pathDenominator, pathValue⟩
      have pathContains : box.Contains
          ((BoundarySource.imag matrix threshold).path.value t) := by
        rw [BoundarySource.path_imag, pathValue]
        exact contains
      have pathDenominatorLower : denominatorLower ≤ normSq
          (matrix.c * (BoundarySource.imag matrix threshold).path.value t +
            matrix.d) := by
        rw [BoundarySource.path_imag, pathValue]
        exact denominatorLowerBound
      have bounded := imag_parameter_abs_le matrix threshold box lowerPositive
        determinantNonzero pathDenominator pathContains pathDenominatorLower
      rcases abs_le.mp bounded with ⟨lower, upper⟩
      let chart : BoundedChart (.imag matrix threshold) :=
        { path := inverseImagBoundaryPath matrix threshold
          interval :=
            let radius := lineParameterRadius
              (.imag matrix threshold) box denominatorLower
            ⟨-radius, radius⟩
          proper := by
            dsimp
            have radiusPositive := lineParameterRadius_pos
              (.imag matrix threshold) box lowerPositive
            exact neg_lt_self radiusPositive
          pathMember := by simp [BoundarySource.paths] }
      refine ⟨chart, ?_, t, ?_, ?_, ?_, ?_⟩
      · simp [charts, chart]
      · simpa [chart] using lower
      · simpa [chart] using upper
      · simpa [chart] using pathDenominator
      · simpa [chart] using pathValue

/-- Every bounded chart retains the exact source-boundary identity. -/
theorem BoundedChart.onBoundary
    {source : BoundarySource} (chart : BoundedChart source)
    (determinantNonzero : determinant source.matrix ≠ 0)
    {t : ℚ} (pathDenominator :
      chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    source.form.eval (chart.path.value t) = 0 :=
  source.path_mem_onBoundary chart.pathMember t determinantNonzero
    pathDenominator

/-! ## Finite chart families for a parser state -/

/-- A bounded chart paired with the branch source whose form it represents. -/
structure SourceChart where
  source : BoundarySource
  chart : BoundedChart source

/-- Forget the dependent source index while retaining it in the chart record. -/
def sourceCharts (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    List SourceChart :=
  (charts source box denominatorLower lowerPositive).map fun chart =>
    ⟨source, chart⟩

/-- Reverse boundary coverage survives packaging a dependent bounded chart
with its source label. -/
theorem sourceCharts_cover_boundary_point
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate)
    (point : QI) (contains : box.Contains point)
    (denominatorLowerBound : denominatorLower ≤
      normSq (source.matrix.c * point + source.matrix.d))
    (boundary : source.form.eval point = 0) :
    ∃ entry ∈ sourceCharts source box denominatorLower lowerPositive,
      entry.source = source ∧
      ∃ t : ℚ,
        entry.chart.interval.lower ≤ t ∧
        t ≤ entry.chart.interval.upper ∧
        entry.chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 ∧
        entry.chart.path.value t = point := by
  rcases CCLBranchCharts.BoundarySource.charts_cover_boundary_point source box
      denominatorLower lowerPositive determinantNonzero nondegenerate point
      contains denominatorLowerBound boundary with
    ⟨chart, chartMember, t, lower, upper, pathDenominator, pathValue⟩
  let entry : SourceChart := ⟨source, chart⟩
  refine ⟨entry, ?_, rfl, t, ?_, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨chart, chartMember, rfl⟩
  · exact lower
  · exact upper
  · exact pathDenominator
  · exact pathValue

theorem sourceCharts_ne_nil
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    sourceCharts source box denominatorLower lowerPositive ≠ [] := by
  simpa [sourceCharts] using
    charts_ne_nil source box denominatorLower lowerPositive

theorem sourceCharts_length_le_two
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    (sourceCharts source box denominatorLower lowerPositive).length ≤ 2 := by
  simpa [sourceCharts] using
    charts_length_le_two source box denominatorLower lowerPositive

theorem sourceCharts_length_eq_paths_length
    (source : BoundarySource) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    (sourceCharts source box denominatorLower lowerPositive).length =
      source.paths.length := by
  cases source <;> simp [sourceCharts, charts, BoundarySource.paths]

/-- Flatten every one- or two-chart source in the concrete parser plan into
the bounded finite family consumed by the curve controller. -/
def plannedCharts (state : RawParser.State) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    List SourceChart :=
  (inputPlan state).flatMap fun source =>
    sourceCharts source box denominatorLower lowerPositive

/-- Every rational point on a source belonging to the exact parser plan is
represented by a member of the flattened planned-chart family. -/
theorem plannedCharts_cover_boundary_point
    (state : RawParser.State) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower)
    (source : BoundarySource) (sourceMember : source ∈ inputPlan state)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate)
    (point : QI) (contains : box.Contains point)
    (denominatorLowerBound : denominatorLower ≤
      normSq (source.matrix.c * point + source.matrix.d))
    (boundary : source.form.eval point = 0) :
    ∃ entry ∈ plannedCharts state box denominatorLower lowerPositive,
      entry.source = source ∧
      ∃ t : ℚ,
        entry.chart.interval.lower ≤ t ∧
        t ≤ entry.chart.interval.upper ∧
        entry.chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 ∧
        entry.chart.path.value t = point := by
  rcases sourceCharts_cover_boundary_point source box denominatorLower
      lowerPositive determinantNonzero nondegenerate point contains
      denominatorLowerBound boundary with
    ⟨entry, entryMember, sourceEquality, t, lower, upper, pathDenominator,
      pathValue⟩
  refine ⟨entry, ?_, sourceEquality, t, lower, upper, pathDenominator,
    pathValue⟩
  exact List.mem_flatMap.mpr ⟨source, sourceMember, entryMember⟩

theorem plannedCharts_ne_nil
    (state : RawParser.State) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    plannedCharts state box denominatorLower lowerPositive ≠ [] := by
  intro empty
  have planNonempty := inputPlan_ne_nil state
  generalize planEquation : inputPlan state = plan at planNonempty empty
  cases plan with
  | nil => exact planNonempty rfl
  | cons source sources =>
      have headEmpty :
          sourceCharts source box denominatorLower lowerPositive = [] := by
        have flattened :
            sourceCharts source box denominatorLower lowerPositive ++
                sources.flatMap (fun candidate =>
                  sourceCharts candidate box denominatorLower lowerPositive) =
              [] := by
          simpa [plannedCharts, planEquation] using empty
        exact (List.append_eq_nil_iff.mp flattened).1
      exact sourceCharts_ne_nil source box denominatorLower lowerPositive
        headEmpty

theorem plannedCharts_length_le_four
    (state : RawParser.State) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower) :
    (plannedCharts state box denominatorLower lowerPositive).length ≤ 4 := by
  have familyLength : ∀ sources : List BoundarySource,
      (sources.flatMap fun source =>
        sourceCharts source box denominatorLower lowerPositive).length =
          (sources.map fun source => source.paths.length).sum := by
    intro sources
    induction sources with
    | nil => simp
    | cons source sources inductionHypothesis =>
        simp [inductionHypothesis,
          sourceCharts_length_eq_paths_length source box denominatorLower
            lowerPositive]
  rw [plannedCharts, familyLength]
  exact inputPlan_paths_length_sum_le_four state

/-- Membership in the flattened family retains membership of its source in
the exact parser branch plan. -/
theorem source_mem_inputPlan_of_mem_plannedCharts
    (state : RawParser.State) (box : RatBox)
    (denominatorLower : ℚ) (lowerPositive : 0 < denominatorLower)
    {entry : SourceChart}
    (member : entry ∈
      plannedCharts state box denominatorLower lowerPositive) :
    entry.source ∈ inputPlan state := by
  simp only [plannedCharts, List.mem_flatMap] at member
  rcases member with ⟨source, sourceMember, entryMember⟩
  simp only [sourceCharts, List.mem_map] at entryMember
  rcases entryMember with ⟨chart, chartMember, equality⟩
  simpa only [← equality] using sourceMember

theorem SourceChart.onBoundary
    (entry : SourceChart)
    (determinantNonzero : determinant entry.source.matrix ≠ 0)
    {t : ℚ} (pathDenominator :
      entry.chart.path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    entry.source.form.eval (entry.chart.path.value t) = 0 :=
  entry.chart.onBoundary determinantNonzero pathDenominator

end CCLBranchCharts
end FTA
