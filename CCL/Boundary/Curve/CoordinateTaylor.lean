import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Bounds
import RFAP.Cauchy.Resolution
import RFAP.Sturm.RootCount

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace CCL.CoordinateTaylor

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian
abbrev Interval := RFAP.PathClearance.Interval
abbrev Box := RFAP.Boxes.Box

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructiveGaussian.Gaussian

/-- The exact real-axis inclusion into constructive Gaussian coordinates. -/
def ofCoordinate (value : Coordinate) : Gaussian := ⟨value, 0⟩

/-- Coefficientwise real-axis inclusion of a coordinate polynomial. -/
def gaussianPolynomial (p : CoordinatePolynomial) : GaussianPolynomial :=
  ⟨p.coeffs.map ofCoordinate⟩

/-- The degenerate Gaussian box occupied by one coordinate interval. -/
def intervalBox (interval : Interval) : Box where
  xLower := interval.lower
  xUpper := interval.upper
  yLower := 0
  yUpper := 0
  x_valid := interval.valid
  y_valid := le_rfl

@[simp] theorem ofCoordinate_zero : ofCoordinate 0 = 0 := rfl

@[simp] theorem ofCoordinate_add (left right : Coordinate) :
    ofCoordinate (left + right) = ofCoordinate left + ofCoordinate right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · change (0 : Coordinate) = 0 + 0
    rw [RFAP.ConstructiveFraction.zero_add]

@[simp] theorem ofCoordinate_mul (left right : Coordinate) :
    ofCoordinate (left * right) = ofCoordinate left * ofCoordinate right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [ofCoordinate, mul_re, mul_im] <;> ring1

@[simp] theorem ofCoordinate_sub (left right : Coordinate) :
    ofCoordinate (left - right) = ofCoordinate left - ofCoordinate right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · change (0 : Coordinate) = 0 - 0
    rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct, neg_zero,
      RFAP.ConstructiveFraction.zero_add]

@[simp] theorem ofCoordinate_normSq (value : Coordinate) :
    normSq (ofCoordinate value) = value ^ 2 := by
  simp only [normSq, ofCoordinate]
  ring1

private theorem foldl_eval_map
    (coefficients : List Coordinate) (point accumulator : Coordinate) :
    (coefficients.map ofCoordinate).foldl
        (fun value coefficient => value * ofCoordinate point + coefficient)
        (ofCoordinate accumulator) =
      ofCoordinate (coefficients.foldl
        (fun value coefficient => value * point + coefficient) accumulator) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [← ofCoordinate_mul, ← ofCoordinate_add]
      exact inductionHypothesis (accumulator * point + coefficient)

@[simp] theorem eval_gaussianPolynomial
    (p : CoordinatePolynomial) (point : Coordinate) :
    (gaussianPolynomial p).eval (ofCoordinate point) =
      ofCoordinate (p.eval point) := by
  exact foldl_eval_map p.coeffs point 0

private theorem foldl_evalDerivative_map
    (coefficients : List Coordinate) (point value derivativeValue : Coordinate) :
    (coefficients.map ofCoordinate).foldl
        (RFAP.ComputableDerivative.evalDerivativeStep (ofCoordinate point))
        (ofCoordinate value, ofCoordinate derivativeValue) =
      let result := coefficients.foldl
        (RFAP.ComputableDerivative.evalDerivativeStep point)
        (value, derivativeValue)
      (ofCoordinate result.1, ofCoordinate result.2) := by
  induction coefficients generalizing value derivativeValue with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons,
        RFAP.ComputableDerivative.evalDerivativeStep]
      rw [← ofCoordinate_mul, ← ofCoordinate_add,
        ← ofCoordinate_mul, ← ofCoordinate_add]
      exact inductionHypothesis
        (value * point + coefficient) (derivativeValue * point + value)

@[simp] theorem eval_derivative_gaussianPolynomial
    (p : CoordinatePolynomial) (point : Coordinate) :
    (RFAP.ComputableDerivative.derivative (gaussianPolynomial p)).eval
        (ofCoordinate point) =
      ofCoordinate ((RFAP.ComputableDerivative.derivative p).eval point) := by
  rw [RFAP.ComputableDerivative.eval_derivative,
    RFAP.ComputableDerivative.eval_derivative]
  exact congrArg Prod.snd
    (foldl_evalDerivative_map p.coeffs point 0 0)

theorem ofCoordinate_mem_intervalBox
    {interval : Interval} {point : Coordinate}
    (inside : interval.Contains point) :
    (intervalBox interval).Contains (ofCoordinate point) :=
  ⟨inside.1, inside.2, le_rfl, le_rfl⟩

@[simp] theorem intervalBox_diagonalSq (interval : Interval) :
    (intervalBox interval).diagonalSq =
      (interval.upper - interval.lower) ^ 2 := by
  simp only [RFAP.Boxes.Box.diagonalSq, intervalBox]
  ring1

/-- The existing finite Gaussian Horner scan, restricted to the real axis,
is an executable quadratic Taylor majorant for a coordinate polynomial. -/
def taylorRemainderBound
    (p : CoordinatePolynomial) (interval : Interval) : Coordinate :=
  RFAP.PolynomialBounds.denseTaylorRemainderBound
    (gaussianPolynomial p) (intervalBox interval)

theorem taylorRemainderBound_pos
    (p : CoordinatePolynomial) (interval : Interval) :
    0 < taylorRemainderBound p interval :=
  RFAP.PolynomialBounds.denseTaylorRemainderBound_pos
    (gaussianPolynomial p) (intervalBox interval)

/-- Coordinate form of the coefficient-scanned quadratic Taylor estimate. -/
theorem taylor_error_sq_le
    (p : CoordinatePolynomial) {interval : Interval}
    {point center : Coordinate}
    (pointInside : interval.Contains point)
    (centerInside : interval.Contains center) :
    (p.eval point - p.eval center -
        (RFAP.ComputableDerivative.derivative p).eval center *
          (point - center)) ^ 2 ≤
      taylorRemainderBound p interval * (point - center) ^ 4 := by
  have gaussianBound :=
    RFAP.PolynomialBounds.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
        (gaussianPolynomial p)
        (ofCoordinate_mem_intervalBox pointInside)
        (ofCoordinate_mem_intervalBox centerInside)
  let error := p.eval point - p.eval center -
    (RFAP.ComputableDerivative.derivative p).eval center * (point - center)
  have errorIdentity :
      (gaussianPolynomial p).eval (ofCoordinate point) -
          (gaussianPolynomial p).eval (ofCoordinate center) -
          (RFAP.ConstructiveGCD.derivative (gaussianPolynomial p)).eval
              (ofCoordinate center) *
            (ofCoordinate point - ofCoordinate center) =
        ofCoordinate error := by
    rw [eval_gaussianPolynomial, eval_gaussianPolynomial]
    change ofCoordinate (p.eval point) - ofCoordinate (p.eval center) -
        (RFAP.ComputableDerivative.derivative (gaussianPolynomial p)).eval
            (ofCoordinate center) *
          (ofCoordinate point - ofCoordinate center) = ofCoordinate error
    rw [← ofCoordinate_sub (p.eval point) (p.eval center),
      eval_derivative_gaussianPolynomial,
      ← ofCoordinate_sub point center, ← ofCoordinate_mul,
      ← ofCoordinate_sub]
  rw [errorIdentity, ofCoordinate_normSq, ← ofCoordinate_sub,
    ofCoordinate_normSq] at gaussianBound
  change error ^ 2 ≤
    taylorRemainderBound p interval * ((point - center) ^ 2) ^ 2
      at gaussianBound
  simpa only [error] using (calc
    error ^ 2 ≤
        taylorRemainderBound p interval * ((point - center) ^ 2) ^ 2 :=
      gaussianBound
    _ = taylorRemainderBound p interval * (point - center) ^ 4 := by
      ring1)

/-! ## A uniform squarefree root-orientation width -/

abbrev CoprimeCertificate (p q : CoordinatePolynomial) :=
  RFAP.PathClearance.CoprimeCertificate p q

def orientationClearance
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    (root : Interval) : RFAP.PathClearance.Certificate
      p (RFAP.ComputableDerivative.derivative p) root :=
  RFAP.PathClearance.certificateOfCoprime squarefree root

def orientationCoefficient
    (p : CoordinatePolynomial) (root : Interval) : Coordinate :=
  taylorRemainderBound p root +
    RFAP.IntervalSign.denseEvalSqLipschitzBound
      (RFAP.ComputableDerivative.derivative p) root

theorem orientationCoefficient_nonneg
    (p : CoordinatePolynomial) (root : Interval) :
    0 ≤ orientationCoefficient p root :=
  add_nonneg (taylorRemainderBound_pos p root).le
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg
      (RFAP.ComputableDerivative.derivative p) root).2

/-- A positive coefficient-computed width at which both the Taylor error and
the derivative displacement are below the squarefree Bézout clearance. -/
def rootOrientationWidth
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    (root : Interval) : Coordinate :=
  min 1 ((orientationClearance p squarefree root).bound /
    (orientationCoefficient p root + 1))

theorem rootOrientationWidth_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    (root : Interval) :
    0 < rootOrientationWidth p squarefree root := by
  apply lt_min (by decide)
  exact RFAP.ConstructiveFraction.div_pos_direct
    (orientationClearance p squarefree root).positive
    (by
      calc
        0 < 1 := by decide
        _ ≤ orientationCoefficient p root + 1 :=
          add_le_add (orientationCoefficient_nonneg p root) (le_refl 1))

private theorem self_mul_pos_of_ne_zero
    {value : Coordinate} (nonzero : value ≠ 0) : 0 < value * value := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · exact RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
      negative negative
  · exact RFAP.ConstructiveFraction.mul_pos_direct positive positive

/-- Any two displayed points of one coordinate interval are no farther apart
than its displayed width, in squared distance. -/
theorem point_sub_center_sq_le_width_sq
    {interval : Interval} {point center : Coordinate}
    (pointInside : interval.Contains point)
    (centerInside : interval.Contains center) :
    (point - center) ^ 2 ≤
      (interval.upper - interval.lower) ^ 2 := by
  have bound := (intervalBox interval).normSq_sub_le_diagonalSq
    (ofCoordinate_mem_intervalBox pointInside)
    (ofCoordinate_mem_intervalBox centerInside)
  simpa only [← ofCoordinate_sub, ofCoordinate_normSq,
    intervalBox_diagonalSq] using bound

/-- The root-orientation width pays simultaneously for the coordinate
Taylor remainder and for moving the derivative from the root to either
endpoint. -/
theorem orientation_scaled_width_sq_lt
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    (root interval : Interval)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root) :
    taylorRemainderBound p root *
          (interval.upper - interval.lower) ^ 2 <
        (orientationClearance p squarefree root).bound ∧
      RFAP.IntervalSign.denseEvalSqLipschitzBound
          (RFAP.ComputableDerivative.derivative p) root *
            (interval.upper - interval.lower) ^ 2 <
        (orientationClearance p squarefree root).bound := by
  let width := interval.upper - interval.lower
  let coefficient := orientationCoefficient p root
  let bound := (orientationClearance p squarefree root).bound
  have widthPositive : 0 < width :=
    RFAP.ConstructiveFraction.sub_pos_direct proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (min_le_left _ _)
  have widthBelowRatio : width < bound / (coefficient + 1) :=
    widthSmall.trans_le (min_le_right _ _)
  have widthSqBelowWidth : width ^ 2 < width := by
    have multiplied :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    rw [pow_two]
    exact multiplied.trans_eq (RFAP.ConstructiveFraction.one_mul width)
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using orientationCoefficient_nonneg p root
  have coefficientWidthBelow : coefficient * width < bound :=
    RFAP.CauchyResolution.coefficient_mul_lt_of_radius_lt_div_add_one
        coefficientNonnegative widthPositive.le widthBelowRatio
  have coefficientWidthSqBelow : coefficient * width ^ 2 < bound :=
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      widthSqBelowWidth.le coefficientNonnegative).trans_lt
        coefficientWidthBelow
  have taylorNonnegative : 0 ≤ taylorRemainderBound p root :=
    (taylorRemainderBound_pos p root).le
  have derivativeCoefficientNonnegative :
      0 ≤ RFAP.IntervalSign.denseEvalSqLipschitzBound
        (RFAP.ComputableDerivative.derivative p) root :=
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg
      (RFAP.ComputableDerivative.derivative p) root).2
  have widthSqNonnegative : 0 ≤ width ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct width
  constructor
  · exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (show taylorRemainderBound p root ≤ coefficient by
        dsimp only [coefficient, orientationCoefficient]
        exact le_add_of_nonneg_right derivativeCoefficientNonnegative)
      widthSqNonnegative).trans_lt coefficientWidthSqBelow
  · exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (show RFAP.IntervalSign.denseEvalSqLipschitzBound
          (RFAP.ComputableDerivative.derivative p) root ≤ coefficient by
        dsimp only [coefficient, orientationCoefficient]
        exact le_add_of_nonneg_left taylorNonnegative)
      widthSqNonnegative).trans_lt coefficientWidthSqBelow

/-- At a displayed squarefree root, the finite Taylor linear term has the
same strict sign as every distinct point evaluation in the sufficiently
small cell. -/
theorem eval_mul_root_linear_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    {root interval : Interval}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    {parameter point : Coordinate}
    (parameterInside : interval.Contains parameter)
    (pointInside : interval.Contains point)
    (rootZero : p.eval parameter = 0) (different : point ≠ parameter) :
    0 < p.eval point *
      ((RFAP.ComputableDerivative.derivative p).eval parameter *
        (point - parameter)) := by
  let derivativeValue :=
    (RFAP.ComputableDerivative.derivative p).eval parameter
  let distance := point - parameter
  let width := interval.upper - interval.lower
  let clearance := orientationClearance p squarefree root
  let taylor := taylorRemainderBound p root
  let error := p.eval point - p.eval parameter - derivativeValue * distance
  have parameterRoot : root.Contains parameter :=
    ⟨refines.1.trans parameterInside.1,
      parameterInside.2.trans refines.2⟩
  have pointRoot : root.Contains point :=
    ⟨refines.1.trans pointInside.1, pointInside.2.trans refines.2⟩
  have derivativeLower : clearance.bound ≤ derivativeValue ^ 2 := by
    have lower := clearance.lower parameter parameterRoot
    dsimp only [clearance, orientationClearance, derivativeValue] at lower ⊢
    rw [rootZero] at lower
    have zeroSq : (0 : Coordinate) ^ 2 = 0 := by ring1
    rw [zeroSq, RFAP.ConstructiveFraction.zero_add] at lower
    exact lower
  have distanceNonzero : distance ≠ 0 := by
    exact sub_ne_zero.mpr different
  have distanceSqPositive : 0 < distance ^ 2 := by
    simpa only [pow_two] using self_mul_pos_of_ne_zero distanceNonzero
  have distanceSqLeWidthSq : distance ^ 2 ≤ width ^ 2 := by
    simpa only [distance, width] using
      point_sub_center_sq_le_width_sq pointInside parameterInside
  have scaledBounds := orientation_scaled_width_sq_lt p squarefree
    root interval proper widthSmall
  have taylorDistanceBelowDerivative :
      taylor * distance ^ 2 < derivativeValue ^ 2 := by
    calc
      taylor * distance ^ 2 ≤ taylor * width ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          distanceSqLeWidthSq (taylorRemainderBound_pos p root).le
      _ < clearance.bound := by
        simpa only [taylor, width, clearance] using scaledBounds.1
      _ ≤ derivativeValue ^ 2 := derivativeLower
  have errorBound : error ^ 2 ≤ taylor * distance ^ 4 := by
    simpa only [error, taylor, derivativeValue, distance] using
      taylor_error_sq_le p pointRoot parameterRoot
  have errorStrict : error ^ 2 < (derivativeValue * distance) ^ 2 := by
    calc
      error ^ 2 ≤ taylor * distance ^ 4 := errorBound
      _ = (taylor * distance ^ 2) * distance ^ 2 := by ring1
      _ < derivativeValue ^ 2 * distance ^ 2 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          taylorDistanceBelowDerivative distanceSqPositive
      _ = (derivativeValue * distance) ^ 2 := by ring1
  have perturbation :=
    RFAP.CauchyResolution.sub_mul_neg_of_sq_lt_sq
      (a := error) (b := -(derivativeValue * distance)) (by
        simpa only [neg_sq] using errorStrict)
  have errorShift : error - -(derivativeValue * distance) = p.eval point := by
    dsimp only [error, derivativeValue, distance]
    rw [rootZero]
    ring1
  rw [errorShift] at perturbation
  have positiveNegation :
      0 < -(p.eval point * -(derivativeValue * distance)) :=
    neg_pos.mpr perturbation
  simpa only [derivativeValue, distance] using (calc
    0 < -(p.eval point * -(derivativeValue * distance)) := positiveNegation
    _ = p.eval point * (derivativeValue * distance) := by ring1)

/-- The automatic derivative at every point of the small cell has the same
strict sign as its value at the displayed squarefree root. -/
theorem derivative_eval_mul_root_derivative_pos
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    {root interval : Interval}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    {parameter point : Coordinate}
    (parameterInside : interval.Contains parameter)
    (pointInside : interval.Contains point)
    (rootZero : p.eval parameter = 0) :
    0 < (RFAP.ComputableDerivative.derivative p).eval point *
      (RFAP.ComputableDerivative.derivative p).eval parameter := by
  let derivative := RFAP.ComputableDerivative.derivative p
  let derivativeValue := derivative.eval parameter
  let width := interval.upper - interval.lower
  let clearance := orientationClearance p squarefree root
  let lipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound derivative root
  have parameterRoot : root.Contains parameter :=
    ⟨refines.1.trans parameterInside.1,
      parameterInside.2.trans refines.2⟩
  have pointRoot : root.Contains point :=
    ⟨refines.1.trans pointInside.1, pointInside.2.trans refines.2⟩
  have derivativeLower : clearance.bound ≤ derivativeValue ^ 2 := by
    have lower := clearance.lower parameter parameterRoot
    dsimp only [clearance, orientationClearance, derivativeValue, derivative]
      at lower ⊢
    rw [rootZero] at lower
    have zeroSq : (0 : Coordinate) ^ 2 = 0 := by ring1
    rw [zeroSq, RFAP.ConstructiveFraction.zero_add] at lower
    exact lower
  have distanceSqLeWidthSq : (point - parameter) ^ 2 ≤ width ^ 2 := by
    simpa only [width] using
      point_sub_center_sq_le_width_sq pointInside parameterInside
  have scaledBounds := orientation_scaled_width_sq_lt p squarefree
    root interval proper widthSmall
  have displacement := RFAP.IntervalSign.eval_sub_sq_le
    derivative root pointRoot parameterRoot
  have displacementStrict :
      (derivative.eval point - derivativeValue) ^ 2 <
        derivativeValue ^ 2 := by
    calc
      (derivative.eval point - derivativeValue) ^ 2 ≤
          lipschitz * (point - parameter) ^ 2 := by
        simpa only [derivativeValue, lipschitz] using displacement
      _ ≤ lipschitz * width ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          distanceSqLeWidthSq
          (RFAP.IntervalSign.denseHornerSqBounds_nonneg
            derivative root).2
      _ < clearance.bound := by
        simpa only [derivative, lipschitz, width, clearance] using
          scaledBounds.2
      _ ≤ derivativeValue ^ 2 := derivativeLower
  simpa only [derivative, derivativeValue] using
    RFAP.IntervalSign.mul_pos_of_sub_sq_lt_sq
      displacementStrict

private theorem product_neg_of_opposite_and_same
    {left right reference : Coordinate}
    (leftOpposite : left * reference < 0)
    (rightSame : 0 < right * reference) : left * right < 0 := by
  have referenceNonzero : reference ≠ 0 := by
    intro referenceZero
    rw [referenceZero, RFAP.ConstructiveFraction.mul_zero_direct] at rightSame
    exact (lt_irrefl 0 rightSame).elim
  have referenceSquarePositive : 0 < reference * reference :=
    self_mul_pos_of_ne_zero referenceNonzero
  have combinedNegative :
      (left * right) * (reference * reference) < 0 := by
    calc
      (left * right) * (reference * reference) =
          (left * reference) * (right * reference) := by ring1
      _ < 0 := RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        leftOpposite rightSame
  rcases lt_trichotomy (left * right) 0 with
      productNegative | productZero | productPositive
  · exact productNegative
  · rw [productZero, RFAP.ConstructiveFraction.zero_mul_direct]
      at combinedNegative
    exact (lt_irrefl 0 combinedNegative).elim
  · have combinedPositive := RFAP.ConstructiveFraction.mul_pos_direct
      productPositive referenceSquarePositive
    exact (lt_asymm combinedPositive combinedNegative).elim

private theorem product_pos_of_two_same
    {left right reference : Coordinate}
    (leftSame : 0 < left * reference)
    (rightSame : 0 < right * reference) : 0 < left * right := by
  have referenceNonzero : reference ≠ 0 := by
    intro referenceZero
    rw [referenceZero, RFAP.ConstructiveFraction.mul_zero_direct] at rightSame
    exact (lt_irrefl 0 rightSame).elim
  have referenceSquarePositive : 0 < reference * reference :=
    self_mul_pos_of_ne_zero referenceNonzero
  have combinedPositive :
      0 < (left * right) * (reference * reference) := by
    calc
      0 < (left * reference) * (right * reference) :=
        RFAP.ConstructiveFraction.mul_pos_direct leftSame rightSame
      _ = (left * right) * (reference * reference) := by ring1
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
    (left := reference * reference)
    (by simpa only [RFAP.ConstructiveFraction.mul_comm] using combinedPositive)
    referenceSquarePositive.le

/-- Endpoint orientation supplied by one displayed squarefree root.  A root
at a cell endpoint contributes a half-event; otherwise the lower endpoint is
opposite to its derivative and the upper endpoint is aligned with it. -/
structure RootEndpointOrientation
    (p : CoordinatePolynomial) (interval : Interval)
    (parameter : Coordinate) where
  lower : interval.lower = parameter ∨
    p.eval interval.lower *
      (RFAP.ComputableDerivative.derivative p).eval interval.lower < 0
  upper : interval.upper = parameter ∨
    0 < p.eval interval.upper *
      (RFAP.ComputableDerivative.derivative p).eval interval.upper

theorem rootEndpointOrientation
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    {root interval : Interval}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    (parameter : Coordinate) (parameterInside : interval.Contains parameter)
    (rootZero : p.eval parameter = 0) :
    RootEndpointOrientation p interval parameter := by
  let derivativeValue :=
    (RFAP.ComputableDerivative.derivative p).eval parameter
  have lower : interval.lower = parameter ∨
      p.eval interval.lower *
        (RFAP.ComputableDerivative.derivative p).eval interval.lower < 0 := by
    by_cases lowerRoot : interval.lower = parameter
    · exact Or.inl lowerRoot
    · right
      have lowerLinear := eval_mul_root_linear_pos p squarefree refines
        proper widthSmall parameterInside
          ⟨le_rfl, interval.valid⟩ rootZero lowerRoot
      have lowerSame := derivative_eval_mul_root_derivative_pos p squarefree
        refines proper widthSmall parameterInside
          ⟨le_rfl, interval.valid⟩ rootZero
      have lowerLt : interval.lower < parameter :=
        lt_of_le_of_ne parameterInside.1 lowerRoot
      have differenceNegative : interval.lower - parameter < 0 := by
        calc
          interval.lower - parameter = -(parameter - interval.lower) := by
            ring1
          _ < 0 := neg_neg_of_pos
            (RFAP.ConstructiveFraction.sub_pos_direct lowerLt)
      have factored : 0 <
          (p.eval interval.lower * derivativeValue) *
            (interval.lower - parameter) := by
        simpa only [derivativeValue] using (calc
          0 < p.eval interval.lower *
              (derivativeValue * (interval.lower - parameter)) := lowerLinear
          _ = (p.eval interval.lower * derivativeValue) *
              (interval.lower - parameter) := by ring1)
      have lowerOpposite : p.eval interval.lower * derivativeValue < 0 := by
        rcases lt_trichotomy
            (p.eval interval.lower * derivativeValue) 0 with
            productNegative | productZero | productPositive
        · exact productNegative
        · rw [productZero, RFAP.ConstructiveFraction.zero_mul_direct] at factored
          exact (lt_irrefl 0 factored).elim
        · have productNegative :=
            RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
              productPositive differenceNegative
          exact (lt_asymm factored productNegative).elim
      exact product_neg_of_opposite_and_same lowerOpposite lowerSame
  have upper : interval.upper = parameter ∨
      0 < p.eval interval.upper *
        (RFAP.ComputableDerivative.derivative p).eval interval.upper := by
    by_cases upperRoot : interval.upper = parameter
    · exact Or.inl upperRoot
    · right
      have upperLinear := eval_mul_root_linear_pos p squarefree refines
        proper widthSmall parameterInside
          ⟨interval.valid, le_rfl⟩ rootZero upperRoot
      have upperSame := derivative_eval_mul_root_derivative_pos p squarefree
        refines proper widthSmall parameterInside
          ⟨interval.valid, le_rfl⟩ rootZero
      have parameterLt : parameter < interval.upper :=
        lt_of_le_of_ne parameterInside.2 (Ne.symm upperRoot)
      have differencePositive : 0 < interval.upper - parameter :=
        RFAP.ConstructiveFraction.sub_pos_direct parameterLt
      have factored : 0 <
          (p.eval interval.upper * derivativeValue) *
            (interval.upper - parameter) := by
        simpa only [derivativeValue] using (calc
          0 < p.eval interval.upper *
              (derivativeValue * (interval.upper - parameter)) := upperLinear
          _ = (p.eval interval.upper * derivativeValue) *
              (interval.upper - parameter) := by ring1)
      have upperAligned : 0 < p.eval interval.upper * derivativeValue := by
        exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          (left := interval.upper - parameter)
          (by simpa only [RFAP.ConstructiveFraction.mul_comm] using factored)
          differencePositive.le
      exact product_pos_of_two_same upperAligned upperSame
  exact ⟨lower, upper⟩

/-- A displayed rational root in a squarefree, Taylor-resolved cell forces a
nonzero doubled Sturm event.  Endpoint roots contribute one and interior
roots contribute two; the proof does not appeal to a global root-counting
theorem. -/
theorem sturmRootCount2_ne_zero_of_root
    (p : CoordinatePolynomial)
    (squarefree : CoprimeCertificate p
      (RFAP.ComputableDerivative.derivative p))
    {root interval : Interval}
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      rootOrientationWidth p squarefree root)
    (resolution : RFAP.CauchyCells.CauchyEventResolution
      (RFAP.SturmRootCount.reducedNumerator
        (RFAP.ComputableDerivative.derivative p) p)
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative p) p)
      interval)
    (parameter : Coordinate) (parameterInside : interval.Contains parameter)
    (rootZero : p.eval parameter = 0) :
    RFAP.SturmRootCount.sturmRootCount2 p
      interval.lower interval.upper ≠ 0 := by
  let numerator := RFAP.SturmRootCount.reducedNumerator
    (RFAP.ComputableDerivative.derivative p) p
  let denominator := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative p) p
  have denominatorRoot : denominator.eval parameter = 0 := by
    by_cases denominatorZero : denominator.eval parameter = 0
    · exact denominatorZero
    · have originalNonzero :=
        RFAP.SturmRootCount.denominator_eval_ne_zero_of_reduced_of_coprime
            squarefree (by
              simpa only [denominator] using denominatorZero)
      exact (originalNonzero rootZero).elim
  cases resolution with
  | neutral denominatorStable _chain =>
      have impossible := denominatorStable.eval_ne_zero parameterInside
      exact (impossible (by simpa only [denominator] using denominatorRoot)).elim
  | numerator numeratorStable tail =>
      intro countZero
      have orientation := rootEndpointOrientation p squarefree refines proper
        widthSmall parameter parameterInside rootZero
      have countFormula :
          RFAP.SturmRootCount.sturmRootCount2 p
              interval.lower interval.upper =
            (RFAP.Sturm.signJump
                (denominator.eval interval.lower)
                (numerator.eval interval.lower) : Int) -
              RFAP.Sturm.signJump
                (denominator.eval interval.upper)
                (numerator.eval interval.upper) := by
        unfold RFAP.SturmRootCount.sturmRootCount2
          RFAP.SturmRootCount.reducedCauchyIndex2
        exact RFAP.CauchyCells.cauchyIndex2_eq_firstJumps_of_neutralTail
            numeratorStable.polynomial_nonzero tail
      rcases orientation.lower with lowerRoot | lowerNegative
      · rcases orientation.upper with upperRoot | upperPositive
        · rw [lowerRoot, upperRoot] at proper
          exact (lt_irrefl parameter proper).elim
        · have lowerDenominator : denominator.eval interval.lower = 0 := by
            rw [lowerRoot]
            exact denominatorRoot
          have lowerNumerator : numerator.eval interval.lower ≠ 0 :=
            numeratorStable.eval_ne_zero ⟨le_rfl, interval.valid⟩
          have lowerJump : RFAP.Sturm.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 1 := by
            rw [lowerDenominator]
            exact RFAP.Sturm.signJump_zero_of_ne lowerNumerator
          have reducedPositive :=
            RFAP.SturmRootCount.reduced_product_pos_of_original
              squarefree (by simpa only [RFAP.ConstructiveFraction.mul_comm]
                using upperPositive)
          have upperJump : RFAP.Sturm.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 0 :=
            RFAP.Sturm.signJump_eq_zero_of_mul_pos (by
              simpa only [numerator, denominator,
                RFAP.ConstructiveFraction.mul_comm] using reducedPositive)
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 1 - 0) countFormula
      · rcases orientation.upper with upperRoot | upperPositive
        · have upperDenominator : denominator.eval interval.upper = 0 := by
            rw [upperRoot]
            exact denominatorRoot
          have upperNumerator : numerator.eval interval.upper ≠ 0 :=
            numeratorStable.eval_ne_zero ⟨interval.valid, le_rfl⟩
          have reducedNegative :=
            RFAP.SturmRootCount.reduced_product_neg_of_original
              squarefree (by simpa only [RFAP.ConstructiveFraction.mul_comm]
                using lowerNegative)
          have lowerJump : RFAP.Sturm.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 2 :=
            RFAP.Sturm.signJump_eq_two_of_mul_neg (by
              simpa only [numerator, denominator,
                RFAP.ConstructiveFraction.mul_comm] using reducedNegative)
          have upperJump : RFAP.Sturm.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 1 := by
            rw [upperDenominator]
            exact RFAP.Sturm.signJump_zero_of_ne upperNumerator
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 2 - 1) countFormula
        · have reducedNegative :=
            RFAP.SturmRootCount.reduced_product_neg_of_original
              squarefree (by simpa only [RFAP.ConstructiveFraction.mul_comm]
                using lowerNegative)
          have reducedPositive :=
            RFAP.SturmRootCount.reduced_product_pos_of_original
              squarefree (by simpa only [RFAP.ConstructiveFraction.mul_comm]
                using upperPositive)
          have lowerJump : RFAP.Sturm.signJump
              (denominator.eval interval.lower)
              (numerator.eval interval.lower) = 2 :=
            RFAP.Sturm.signJump_eq_two_of_mul_neg (by
              simpa only [numerator, denominator,
                RFAP.ConstructiveFraction.mul_comm] using reducedNegative)
          have upperJump : RFAP.Sturm.signJump
              (denominator.eval interval.upper)
              (numerator.eval interval.upper) = 0 :=
            RFAP.Sturm.signJump_eq_zero_of_mul_pos (by
              simpa only [numerator, denominator,
                RFAP.ConstructiveFraction.mul_comm] using reducedPositive)
          rw [lowerJump, upperJump] at countFormula
          rw [countZero] at countFormula
          exact (by decide : (0 : Int) ≠ 2 - 0) countFormula

end CCL.CoordinateTaylor
