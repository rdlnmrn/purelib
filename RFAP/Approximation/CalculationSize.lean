import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.GaussianDenominatorHeight
import RFAP.Rational.DenominatorHeight
import RFAP.Approximation.HurwitzTrace
import RFAP.Polynomial.NormalizedEvaluation

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace RFAP.CalculationSize

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CommonFraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev HurwitzFraction := RFAP.HurwitzRational.Fraction
abbrev ConvergentPair := RFAP.HurwitzRational.ConvergentPair
abbrev ReducedFraction := RFAP.ConstructiveFraction.ReducedFraction
abbrev WorkingGaussian := RFAP.NormalizedGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-! ## Component bit widths -/

/-- Binary width of a natural component.  Zero is assigned one displayed
bit, matching the fact that it is still an explicit integer component. -/
def natWidth (value : Nat) : Nat := Nat.log2 value + 1

/-- Binary width of a signed integer component. -/
def intWidth (value : Int) : Nat := natWidth value.natAbs

/-- Maximum component width of a Gaussian integer. -/
def gaussianIntWidth (value : GaussianInt) : Nat :=
  max (intWidth value.re) (intWidth value.im)

/-- Width of the explicit numerator and positive denominator of a displayed
common-denominator Gaussian fraction. -/
def commonFractionWidth (fraction : CommonFraction) : Nat :=
  max (gaussianIntWidth fraction.numerator) (natWidth fraction.denominator)

/-- Width of the four integral coordinates in a displayed Gaussian
numerator/denominator record. -/
def hurwitzFractionWidth (fraction : HurwitzFraction) : Nat :=
  max (gaussianIntWidth fraction.numerator)
    (gaussianIntWidth fraction.denominator)

theorem natWidth_mono {left right : Nat} (order : left ≤ right) :
    natWidth left ≤ natWidth right := by
  unfold natWidth
  by_cases leftZero : left = 0
  · rw [leftZero, Nat.log2_zero]
    omega
  · have rightNonzero : right ≠ 0 := by
      intro rightZero
      rw [rightZero] at order
      exact leftZero (Nat.eq_zero_of_le_zero order)
    apply Nat.add_le_add_right
    exact (Nat.le_log2 rightNonzero).2
      ((Nat.log2_self_le leftZero).trans order)

private theorem int_mul_self_nonneg (value : Int) :
    0 ≤ value * value := by
  by_cases nonnegative : 0 ≤ value
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : value ≤ 0 :=
      Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

theorem normNat_eq_component_squares (value : GaussianInt) :
    normNat value = value.re.natAbs ^ 2 + value.im.natAbs ^ 2 := by
  unfold normNat RFAP.ConstructiveGaussianHeight.GaussianInt.normInt
  rw [Int.natAbs_add_of_nonneg (int_mul_self_nonneg value.re)
    (int_mul_self_nonneg value.im), Int.natAbs_mul, Int.natAbs_mul]
  simp only [pow_two]

theorem realComponent_le_normNat (value : GaussianInt) :
    value.re.natAbs ≤ normNat value := by
  rw [normNat_eq_component_squares]
  by_cases zero : value.re.natAbs = 0
  · omega
  · have selfLe : value.re.natAbs ≤ value.re.natAbs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_right value.re.natAbs (Nat.pos_of_ne_zero zero)
    exact selfLe.trans (Nat.le_add_right _ _)

theorem imaginaryComponent_le_normNat (value : GaussianInt) :
    value.im.natAbs ≤ normNat value := by
  rw [normNat_eq_component_squares]
  by_cases zero : value.im.natAbs = 0
  · omega
  · have selfLe : value.im.natAbs ≤ value.im.natAbs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_right value.im.natAbs (Nat.pos_of_ne_zero zero)
    exact selfLe.trans (Nat.le_add_left _ _)

theorem gaussianIntWidth_le_natWidth_normNat (value : GaussianInt) :
    gaussianIntWidth value ≤ natWidth (normNat value) := by
  apply max_le
  · exact natWidth_mono (realComponent_le_normNat value)
  · exact natWidth_mono (imaginaryComponent_le_normNat value)

theorem gaussianIntWidth_le_budget {value : GaussianInt} {budget : Nat}
    (bounded : normNat value ≤ budget) :
    gaussianIntWidth value ≤ natWidth budget :=
  (gaussianIntWidth_le_natWidth_normNat value).trans (natWidth_mono bounded)

/-! ## Normalized rational work records -/

/-- Bit width of the larger reduced numerator/denominator component. -/
def reducedFractionWidth (value : ReducedFraction) : Nat :=
  natWidth (RFAP.NormalizedFraction.componentMagnitude value)

/-- Bit width of the canonical record used when a semantic coordinate enters
the normalized working layer. -/
def rationalRecordWidth (value : Coordinate) : Nat :=
  reducedFractionWidth (RFAP.NormalizedFraction.ofRational value)

/-- Bit width of the largest reduced scalar component of a working Gaussian
record. -/
def workingGaussianWidth (value : WorkingGaussian) : Nat :=
  natWidth (RFAP.NormalizedGaussian.componentMagnitude value)

/-- Bit width of the canonical working record for a semantic Gaussian
rational. -/
def gaussianRecordWidth (value : Gaussian) : Nat :=
  workingGaussianWidth (RFAP.NormalizedGaussian.ofGaussian value)

/-- Source-only bit budget for the result record of normalized addition. -/
def normalizedAddBitBudget (left right : Coordinate) : Nat :=
  natWidth (RFAP.NormalizedFraction.addComponentEnvelope
    (RFAP.NormalizedFraction.ofRational left)
    (RFAP.NormalizedFraction.ofRational right))

/-- Source-only bit budget for the result record of normalized
multiplication. -/
def normalizedMulBitBudget (left right : Coordinate) : Nat :=
  natWidth (RFAP.NormalizedFraction.mulComponentEnvelope
    (RFAP.NormalizedFraction.ofRational left)
    (RFAP.NormalizedFraction.ofRational right))

/-- Source-only bit budget for normalized negation. -/
def normalizedNegBitBudget (source : Coordinate) : Nat :=
  rationalRecordWidth source

/-- Source-only bit budget for normalized subtraction. -/
def normalizedSubBitBudget (left right : Coordinate) : Nat :=
  natWidth (RFAP.NormalizedFraction.additiveMagnitudeEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right)))

/-- Source-only bit budget for normalized inversion. -/
def normalizedInvBitBudget (source : Coordinate) : Nat :=
  rationalRecordWidth source

/-- Source-only bit budget for normalized division. -/
def normalizedDivBitBudget (left right : Coordinate) : Nat :=
  natWidth (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right)))

theorem normalizedAdd_width_le_budget (left right : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedAdd left right) ≤
      normalizedAddBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth normalizedAddBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedAdd]
  exact natWidth_mono
    (RFAP.NormalizedFraction.add_componentMagnitude_le _ _)

theorem normalizedMul_width_le_budget (left right : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedMul left right) ≤
      normalizedMulBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth normalizedMulBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedMul]
  exact natWidth_mono
    (RFAP.NormalizedFraction.mul_componentMagnitude_le _ _)

theorem normalizedNeg_width_le_budget (source : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedNeg source) ≤
      normalizedNegBitBudget source := by
  unfold rationalRecordWidth reducedFractionWidth normalizedNegBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedNeg]
  exact natWidth_mono
    (RFAP.NormalizedFraction.componentMagnitude_neg_le _)

theorem normalizedSub_width_le_budget (left right : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedSub left right) ≤
      normalizedSubBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth normalizedSubBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedSub]
  exact natWidth_mono
    (RFAP.NormalizedFraction.componentMagnitude_sub_le _ _)

theorem normalizedInv_width_le_budget (source : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedInv source) ≤
      normalizedInvBitBudget source := by
  unfold rationalRecordWidth reducedFractionWidth normalizedInvBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedInv]
  exact natWidth_mono
    (RFAP.NormalizedFraction.componentMagnitude_inv_le _)

theorem normalizedDiv_width_le_budget (left right : Coordinate) :
    rationalRecordWidth
        (RFAP.NormalizedFraction.normalizedDiv left right) ≤
      normalizedDivBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth normalizedDivBitBudget
  rw [RFAP.NormalizedFraction.ofRational_normalizedDiv]
  exact natWidth_mono
    (RFAP.NormalizedFraction.componentMagnitude_div_le _ _)

/-- Exact logical Euclidean-clause count for normalized addition on the
canonical source records. -/
def normalizedAddGcdClauses (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.addGcdClauses
    (RFAP.NormalizedFraction.ofRational left)
    (RFAP.NormalizedFraction.ofRational right)

/-- Exact logical Euclidean-clause count for normalized multiplication on the
canonical source records. -/
def normalizedMulGcdClauses (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.mulGcdClauses
    (RFAP.NormalizedFraction.ofRational left)
    (RFAP.NormalizedFraction.ofRational right)

/-- Source-only arithmetic-clause budgets for the six normalized scalar
operations. -/
def normalizedAddStepBudget (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.addStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right))

def normalizedMulStepBudget (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.mulStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right))

def normalizedNegStepBudget (source : Coordinate) : Nat :=
  RFAP.NormalizedFraction.negStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational source))

def normalizedSubStepBudget (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.subStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right))

def normalizedInvStepBudget (source : Coordinate) : Nat :=
  RFAP.NormalizedFraction.invStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational source))

def normalizedDivStepBudget (left right : Coordinate) : Nat :=
  RFAP.NormalizedFraction.divStepEnvelope
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational left))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational right))

theorem normalizedAdd_steps_le_budget (left right : Coordinate) :
    RFAP.NormalizedFraction.addSteps
        (RFAP.NormalizedFraction.ofRational left)
        (RFAP.NormalizedFraction.ofRational right) ≤
      normalizedAddStepBudget left right :=
  RFAP.NormalizedFraction.addSteps_le_envelope _ _

theorem normalizedMul_steps_le_budget (left right : Coordinate) :
    RFAP.NormalizedFraction.mulSteps
        (RFAP.NormalizedFraction.ofRational left)
        (RFAP.NormalizedFraction.ofRational right) ≤
      normalizedMulStepBudget left right :=
  RFAP.NormalizedFraction.mulSteps_le_envelope _ _

theorem normalizedNeg_steps_le_budget (source : Coordinate) :
    RFAP.NormalizedFraction.negSteps
        (RFAP.NormalizedFraction.ofRational source) ≤
      normalizedNegStepBudget source :=
  RFAP.NormalizedFraction.negSteps_le_envelope _

theorem normalizedSub_steps_le_budget (left right : Coordinate) :
    RFAP.NormalizedFraction.subSteps
        (RFAP.NormalizedFraction.ofRational left)
        (RFAP.NormalizedFraction.ofRational right) ≤
      normalizedSubStepBudget left right :=
  RFAP.NormalizedFraction.subSteps_le_envelope _ _

theorem normalizedInv_steps_le_budget (source : Coordinate) :
    RFAP.NormalizedFraction.invSteps
        (RFAP.NormalizedFraction.ofRational source) ≤
      normalizedInvStepBudget source :=
  RFAP.NormalizedFraction.invSteps_le_envelope _

theorem normalizedDiv_steps_le_budget (left right : Coordinate) :
    RFAP.NormalizedFraction.divSteps
        (RFAP.NormalizedFraction.ofRational left)
        (RFAP.NormalizedFraction.ofRational right) ≤
      normalizedDivStepBudget left right :=
  RFAP.NormalizedFraction.divSteps_le_envelope _ _

/-! ## Normalized polynomial and Newton evaluation -/

/-- Source recurrence bounding every normalized Horner accumulator. -/
def normalizedEvaluationBitBudget (polynomial : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  natWidth (RFAP.NormalizedEvaluation.magnitudeEnvelope point
    polynomial.coeffs)

/-- Source recurrence bounding all arithmetic clauses in normalized Horner
evaluation. -/
def normalizedEvaluationStepBudget (polynomial : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  RFAP.NormalizedEvaluation.arithmeticEnvelope point polynomial.coeffs

theorem normalizedEvaluation_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian) :
    workingGaussianWidth (RFAP.NormalizedEvaluation.eval polynomial point) ≤
      normalizedEvaluationBitBudget polynomial point :=
  natWidth_mono (RFAP.NormalizedEvaluation.eval_magnitude_le_envelope
    polynomial point)

theorem normalizedEvaluation_trace_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian)
    {candidate : WorkingGaussian}
    (member : candidate ∈
      RFAP.NormalizedEvaluation.trace point polynomial.coeffs) :
    workingGaussianWidth candidate ≤
      normalizedEvaluationBitBudget polynomial point :=
  natWidth_mono (RFAP.NormalizedEvaluation.trace_magnitude_le_envelope
    point polynomial.coeffs member)

theorem normalizedEvaluation_steps_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian) :
    RFAP.NormalizedEvaluation.steps point polynomial.coeffs ≤
      normalizedEvaluationStepBudget polynomial point :=
  RFAP.NormalizedEvaluation.steps_le_envelope point polynomial.coeffs

/-- A common component envelope for the polynomial trace, derivative trace,
quotient, and returned Newton centre. -/
def normalizedNewtonWorkingEnvelope (polynomial : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  let source := RFAP.NormalizedEvaluation.magnitudeEnvelope point
    polynomial.coeffs
  let derivative := RFAP.NormalizedEvaluation.magnitudeEnvelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs
  let quotient := RFAP.NormalizedGaussian.divMagnitudeEnvelope source derivative
  max source (max derivative
    (max quotient
      (RFAP.NormalizedEvaluation.newtonMagnitudeEnvelope polynomial point)))

def normalizedNewtonBitBudget (polynomial : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  natWidth (normalizedNewtonWorkingEnvelope polynomial point)

def normalizedNewtonStepBudget (polynomial : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  RFAP.NormalizedEvaluation.newtonStepEnvelope polynomial point

/-- Normalized quotient occurring inside the Newton update. -/
def normalizedNewtonQuotient (polynomial : GaussianPolynomial)
    (point : Gaussian) : WorkingGaussian :=
  RFAP.NormalizedGaussian.div
    (RFAP.NormalizedEvaluation.eval polynomial point)
    (RFAP.NormalizedEvaluation.derivativeEval polynomial point)

theorem normalizedNewtonCenter_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian) :
    workingGaussianWidth
        (RFAP.NormalizedEvaluation.newtonCenter polynomial point) ≤
      normalizedNewtonBitBudget polynomial point := by
  apply natWidth_mono
  refine (RFAP.NormalizedEvaluation.newtonCenter_magnitude_le
    polynomial point).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem normalizedNewtonQuotient_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian) :
    workingGaussianWidth (normalizedNewtonQuotient polynomial point) ≤
      normalizedNewtonBitBudget polynomial point := by
  apply natWidth_mono
  have source := RFAP.NormalizedEvaluation.eval_magnitude_le_envelope
    polynomial point
  have derivative := RFAP.NormalizedEvaluation.eval_magnitude_le_envelope
    (RFAP.ComputableDerivative.derivative polynomial) point
  refine (RFAP.NormalizedGaussian.componentMagnitude_div_le _ _).trans
    ((RFAP.NormalizedGaussian.divMagnitudeEnvelope_mono source derivative).trans
      ?_)
  unfold normalizedNewtonWorkingEnvelope
  exact (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem normalizedNewton_steps_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian) :
    RFAP.NormalizedEvaluation.newtonSteps polynomial point ≤
      normalizedNewtonStepBudget polynomial point :=
  RFAP.NormalizedEvaluation.newtonSteps_le_envelope polynomial point

theorem normalizedNewton_sourceTrace_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian)
    {candidate : WorkingGaussian}
    (member : candidate ∈
      RFAP.NormalizedEvaluation.trace point polynomial.coeffs) :
    workingGaussianWidth candidate ≤
      normalizedNewtonBitBudget polynomial point := by
  apply natWidth_mono
  refine (RFAP.NormalizedEvaluation.trace_magnitude_le_envelope
    point polynomial.coeffs member).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact le_max_left _ _

theorem normalizedNewton_derivativeTrace_width_le_budget
    (polynomial : GaussianPolynomial) (point : Gaussian)
    {candidate : WorkingGaussian}
    (member : candidate ∈ RFAP.NormalizedEvaluation.trace point
      (RFAP.ComputableDerivative.derivative polynomial).coeffs) :
    workingGaussianWidth candidate ≤
      normalizedNewtonBitBudget polynomial point := by
  apply natWidth_mono
  refine (RFAP.NormalizedEvaluation.trace_magnitude_le_envelope point
    (RFAP.ComputableDerivative.derivative polynomial).coeffs member).trans ?_
  unfold normalizedNewtonWorkingEnvelope
  exact (le_max_left _ _).trans (le_max_right _ _)

/-! ## Square-threshold scan -/

/-- The successful square threshold is bracketed by the failure of its
predecessor. -/
theorem squareThreshold_predecessor_sq_le (input : Nat) :
    (RFAP.HeightApproximation.squareThreshold input - 1) *
        (RFAP.HeightApproximation.squareThreshold input - 1) ≤ input := by
  let output := RFAP.HeightApproximation.squareThreshold input
  by_cases outputOne : output = 1
  · change (output - 1) * (output - 1) ≤ input
    simp only [outputOne, Nat.reduceSubDiff, Nat.zero_mul, Nat.zero_le]
  · have outputPositive := RFAP.HeightApproximation.squareThreshold_pos input
    have oneLtOutput : 1 < output :=
      Nat.lt_of_le_of_ne outputPositive (Ne.symm outputOne)
    have predecessorPositive : 0 < output - 1 :=
      Nat.sub_pos_of_lt oneLtOutput
    apply le_of_not_gt
    intro predecessorWorks
    have minimal := RFAP.HeightApproximation.squareThreshold_minimal
      predecessorPositive predecessorWorks
    dsimp only [output] at minimal
    exact (Nat.not_lt_of_ge minimal)
      (Nat.sub_lt outputPositive (by decide))

/-- The bounded square scan uses at most `input + 1` comparison-bearing
recursive clauses. -/
def squareThresholdComparisonBudget (input : Nat) : Nat := input + 1

/-- Exact comparison budget used by `squareThreshold`. -/
theorem squareThreshold_fuel_eq_budget (input : Nat) :
    input + 1 = squareThresholdComparisonBudget input := rfl

/-- The selected threshold is no larger than the elementary working
candidate `input + 1`. -/
theorem squareThreshold_le_add_one (input : Nat) :
    RFAP.HeightApproximation.squareThreshold input ≤ input + 1 := by
  apply RFAP.HeightApproximation.squareThreshold_minimal
    (Nat.zero_lt_succ input)
  have oneLe : 1 ≤ input + 1 := Nat.succ_le_succ (Nat.zero_le input)
  have multiplied := Nat.mul_le_mul_left (input + 1) oneLe
  calc
    input < input + 1 := Nat.lt_succ_self input
    _ = (input + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (input + 1) * (input + 1) := multiplied

/-- Ceiling supplied to the residual-target square scan. -/
def targetCeiling (coefficient target : Coordinate) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (coefficient / target)

/-- Number of comparison-bearing clauses budgeted for a residual target. -/
def targetComparisonBudget (coefficient target : Coordinate) : Nat :=
  squareThresholdComparisonBudget (targetCeiling coefficient target)

/-- The target denominator has the exact predecessor/successor square
bracket advertised in the paper. -/
theorem targetDenominator_bracket (coefficient target : Coordinate) :
    let input := targetCeiling coefficient target
    let output := RFAP.HeightApproximation.targetDenominator coefficient target
    (output - 1) * (output - 1) ≤ input ∧ input < output * output := by
  dsimp only [targetCeiling, RFAP.HeightApproximation.targetDenominator]
  exact ⟨squareThreshold_predecessor_sq_le _,
    RFAP.HeightApproximation.squareThreshold_spec _⟩

/-! ## Grid records -/

/-- Squared coordinate error of nearest rounding to a positive natural grid. -/
theorem gridCoordinate_offset_sq_le (center : Coordinate) {denominator : Nat}
    (positive : 0 < denominator) :
    (RFAP.HeightApproximation.gridCoordinate center denominator - center) ^ 2 ≤
      ((1 / 2 : Coordinate) / denominator) ^ 2 := by
  let halfMesh := (1 / 2 : Coordinate) / denominator
  have bounds := RFAP.HeightApproximation.gridCoordinate_bounds center positive
  have lower : -halfMesh ≤
      RFAP.HeightApproximation.gridCoordinate center denominator - center := by
    calc
      -halfMesh = (center - halfMesh) - center := by ring1
      _ ≤ RFAP.HeightApproximation.gridCoordinate center denominator - center :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct bounds.1.le center
  have upper :
      RFAP.HeightApproximation.gridCoordinate center denominator - center ≤
        halfMesh := by
    calc
      RFAP.HeightApproximation.gridCoordinate center denominator - center ≤
          (center + halfMesh) - center :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct bounds.2 center
      _ = halfMesh := by ring1
  have squareBound := RFAP.Boxes.Box.sq_le_endpoint_max lower upper
  dsimp only [halfMesh] at squareBound ⊢
  rw [show (-((1 / 2 : Coordinate) / denominator)) ^ 2 =
      ((1 / 2 : Coordinate) / denominator) ^ 2 by ring1,
    max_self] at squareBound
  exact squareBound

/-- The nearest square-grid point has an explicit squared displacement bound. -/
theorem gridFraction_offset_normSq_le (center : Gaussian) (radius : Coordinate) :
    normSq
        ((RFAP.HeightApproximation.gridFraction center radius).value - center) ≤
      2 * ((1 / 2 : Coordinate) /
        RFAP.HeightApproximation.gridDenominator radius) ^ 2 := by
  have realBound := gridCoordinate_offset_sq_le center.re
    (RFAP.HeightApproximation.gridDenominator_pos radius)
  have imaginaryBound := gridCoordinate_offset_sq_le center.im
    (RFAP.HeightApproximation.gridDenominator_pos radius)
  simp only [normSq,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.HeightApproximation.gridFraction_value_re,
    RFAP.HeightApproximation.gridFraction_value_im]
  calc
    _ ≤
        ((1 / 2 : Coordinate) /
            RFAP.HeightApproximation.gridDenominator radius) ^ 2 +
          ((1 / 2 : Coordinate) /
            RFAP.HeightApproximation.gridDenominator radius) ^ 2 :=
      add_le_add realBound imaginaryBound
    _ = 2 * ((1 / 2 : Coordinate) /
        RFAP.HeightApproximation.gridDenominator radius) ^ 2 := by ring1

/-- A source-only natural envelope for the quadrance of the two integral
coordinates in the grid numerator. -/
def gridNumeratorNormBudget (center : Gaussian) (radius : Coordinate) : Nat :=
  let denominator := RFAP.HeightApproximation.gridDenominator radius
  RFAP.ConstructiveFraction.ceilNat
    ((denominator : Coordinate) ^ 2 *
      (2 * (normSq center +
        2 * ((1 / 2 : Coordinate) / denominator) ^ 2)))

/-- Maximum component width of the returned grid numerator and denominator. -/
def gridRecordBitBudget (center : Gaussian) (radius : Coordinate) : Nat :=
  max (natWidth (gridNumeratorNormBudget center radius))
    (natWidth (RFAP.HeightApproximation.gridDenominator radius))

/-- Exact accounted arithmetic clauses in the three normalized rational
operations used to construct a grid record, plus the fixed floor, rounding,
cast, and assembly work. -/
def gridArithmeticSteps (center : Gaussian) (radius : Coordinate) : Nat :=
  let denominator := RFAP.HeightApproximation.gridDenominator radius
  RFAP.NormalizedFraction.divSteps
      (RFAP.NormalizedFraction.ofRational (1 / 2 : Coordinate))
      (RFAP.NormalizedFraction.ofRational radius) +
    RFAP.NormalizedFraction.mulSteps
      (RFAP.NormalizedFraction.ofRational (denominator : Coordinate))
      (RFAP.NormalizedFraction.ofRational center.re) +
    RFAP.NormalizedFraction.mulSteps
      (RFAP.NormalizedFraction.ofRational (denominator : Coordinate))
      (RFAP.NormalizedFraction.ofRational center.im) + 5

/-- Source-only clause budget for construction of the displayed grid
record. -/
def gridArithmeticStepBudget (center : Gaussian) (radius : Coordinate) : Nat :=
  let denominator := RFAP.HeightApproximation.gridDenominator radius
  normalizedDivStepBudget (1 / 2 : Coordinate) radius +
    normalizedMulStepBudget (denominator : Coordinate) center.re +
    normalizedMulStepBudget (denominator : Coordinate) center.im + 5

theorem gridArithmeticSteps_le_budget (center : Gaussian)
    (radius : Coordinate) :
    gridArithmeticSteps center radius ≤
      gridArithmeticStepBudget center radius := by
  unfold gridArithmeticSteps gridArithmeticStepBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add
      (Nat.add_le_add
        (normalizedDiv_steps_le_budget (1 / 2 : Coordinate) radius)
        (normalizedMul_steps_le_budget
          (RFAP.HeightApproximation.gridDenominator radius : Coordinate)
          center.re))
      (normalizedMul_steps_le_budget
        (RFAP.HeightApproximation.gridDenominator radius : Coordinate)
        center.im)) 5

/-- Maximum bit-width budget for the three normalized scalar results used by
the grid construction.  The source records have their directly computed
`rationalRecordWidth` values. -/
def gridArithmeticBitBudget (center : Gaussian) (radius : Coordinate) : Nat :=
  let denominator : Coordinate :=
    RFAP.HeightApproximation.gridDenominator radius
  max (normalizedDivBitBudget (1 / 2 : Coordinate) radius)
    (max (normalizedMulBitBudget denominator center.re)
      (normalizedMulBitBudget denominator center.im))

theorem gridDivision_width_le_budget (center : Gaussian)
    (radius : Coordinate) :
    rationalRecordWidth (RFAP.NormalizedFraction.normalizedDiv
        (1 / 2 : Coordinate) radius) ≤
      gridArithmeticBitBudget center radius :=
  (normalizedDiv_width_le_budget (1 / 2 : Coordinate) radius).trans
    (le_max_left _ _)

theorem gridRealProduct_width_le_budget (center : Gaussian)
    (radius : Coordinate) :
    rationalRecordWidth (RFAP.NormalizedFraction.normalizedMul
        (RFAP.HeightApproximation.gridDenominator radius : Coordinate)
        center.re) ≤ gridArithmeticBitBudget center radius :=
  (normalizedMul_width_le_budget _ center.re).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem gridImaginaryProduct_width_le_budget (center : Gaussian)
    (radius : Coordinate) :
    rationalRecordWidth (RFAP.NormalizedFraction.normalizedMul
        (RFAP.HeightApproximation.gridDenominator radius : Coordinate)
        center.im) ≤ gridArithmeticBitBudget center radius :=
  (normalizedMul_width_le_budget _ center.im).trans
    ((le_max_right _ _).trans (le_max_right _ _))

/-- Clearing the positive natural denominator gives the exact numerator
quadrance. -/
theorem commonFraction_numerator_norm_identity (fraction : CommonFraction) :
    (normNat fraction.numerator : Coordinate) =
      (fraction.denominator : Coordinate) ^ 2 * normSq fraction.value := by
  have cleared := congrArg normSq fraction.value_mul_denominator
  rw [normSq_mul, normSq_toGaussian, normNat_ofNat, normSq_toGaussian,
    Nat.cast_pow] at cleared
  calc
    (normNat fraction.numerator : Coordinate) =
        normSq fraction.value * (fraction.denominator : Coordinate) ^ 2 :=
      cleared.symm
    _ = (fraction.denominator : Coordinate) ^ 2 * normSq fraction.value := by
      ring1

theorem value_normSq_le_of_offset {value center : Gaussian} {bound : Coordinate}
    (offsetBound : normSq (value - center) ≤ bound) :
    normSq value ≤ 2 * (normSq center + bound) := by
  have sumBound := normSq_add_le_two (value - center) center
  have identity : value - center + center = value := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;>
      ring1
  rw [identity] at sumBound
  apply sumBound.trans
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
    (show (0 : Coordinate) ≤ 2 by decide)
  calc
    normSq (value - center) + normSq center ≤
        bound + normSq center :=
      add_le_add offsetBound (le_refl _)
    _ = normSq center + bound := by ring1

theorem gridFraction_value_normSq_le (center : Gaussian) (radius : Coordinate) :
    normSq (RFAP.HeightApproximation.gridFraction center radius).value ≤
      2 * (normSq center +
        2 * ((1 / 2 : Coordinate) /
          RFAP.HeightApproximation.gridDenominator radius) ^ 2) :=
  value_normSq_le_of_offset (gridFraction_offset_normSq_le center radius)

theorem gridFraction_numerator_norm_le_budget
    (center : Gaussian) (radius : Coordinate) :
    normNat (RFAP.HeightApproximation.gridFraction center radius).numerator ≤
      gridNumeratorNormBudget center radius := by
  let denominator := RFAP.HeightApproximation.gridDenominator radius
  let bound : Coordinate :=
    (denominator : Coordinate) ^ 2 *
      (2 * (normSq center +
        2 * ((1 / 2 : Coordinate) / denominator) ^ 2))
  have denominatorNonnegative : (0 : Coordinate) ≤
      (denominator : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have boundNonnegative : (0 : Coordinate) ≤ bound := by
    exact RFAP.ConstructiveFraction.mul_nonneg_direct denominatorNonnegative
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg (normSq_nonneg _)
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (RFAP.ConstructiveFraction.sq_nonneg_direct _))))
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  rw [commonFraction_numerator_norm_identity]
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (gridFraction_value_normSq_le center radius) denominatorNonnegative
  calc
    (RFAP.HeightApproximation.gridFraction center radius).denominator ^ 2 *
          normSq (RFAP.HeightApproximation.gridFraction center radius).value =
        (denominator : Coordinate) ^ 2 *
          normSq (RFAP.HeightApproximation.gridFraction center radius).value := by
      rfl
    _ ≤ bound := scaled
    _ ≤ (gridNumeratorNormBudget center radius : Coordinate) := by
      dsimp only [gridNumeratorNormBudget, denominator] at boundNonnegative ⊢
      exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
        boundNonnegative

theorem gridFraction_width_le_budget (center : Gaussian) (radius : Coordinate) :
    commonFractionWidth (RFAP.HeightApproximation.gridFraction center radius) ≤
      gridRecordBitBudget center radius := by
  apply max_le
  · exact (gaussianIntWidth_le_budget
      (gridFraction_numerator_norm_le_budget center radius)).trans
      (le_max_left _ _)
  · exact le_max_right _ _

/-! ## Homogeneous Gaussian-integer evaluation -/

/-- Quadrance of a Gaussian-integer sum, expressed entirely in naturals. -/
theorem normNat_add_le_two (left right : GaussianInt) :
    normNat (left + right) ≤ 2 * (normNat left + normNat right) := by
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  calc
    (normNat (left + right) : Coordinate) =
        normSq (toGaussian left + toGaussian right) := by
      rw [← toGaussian_add, normSq_toGaussian]
    _ ≤ 2 * (normSq (toGaussian left) + normSq (toGaussian right)) :=
      normSq_add_le_two _ _
    _ = ((2 * (normNat left + normNat right) : Nat) : Coordinate) := by
      rw [normSq_toGaussian, normSq_toGaussian, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]

@[simp] theorem normNat_pow (value : GaussianInt) (exponent : Nat) :
    normNat (value ^ exponent) = normNat value ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [pow_succ, pow_succ, normNat_mul, inductionHypothesis]

/-- Structural norm envelope matching the homogeneous evaluation recursion. -/
def homogeneousNormEnvelope (numerator denominator : GaussianInt) :
    List GaussianInt → Nat
  | [] => 0
  | coefficient :: remaining =>
      2 *
        (normNat coefficient * normNat numerator ^ remaining.length +
          normNat denominator *
            homogeneousNormEnvelope numerator denominator remaining)

theorem homogeneousEval_norm_le_envelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    normNat
        (RFAP.GaussianDenominatorHeight.homogeneousEval numerator denominator
          coefficients) ≤
      homogeneousNormEnvelope numerator denominator coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      rw [RFAP.GaussianDenominatorHeight.homogeneousEval,
        homogeneousNormEnvelope]
      refine (normNat_add_le_two _ _).trans ?_
      rw [normNat_mul, normNat_mul, normNat_pow]
      exact Nat.mul_le_mul_left 2
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (normNat denominator) inductionHypothesis) _)

/-- One list entry for the base case and each recursive suffix value. -/
def homogeneousTrace (numerator denominator : GaussianInt) :
    List GaussianInt → List GaussianInt
  | [] => [0]
  | coefficients@(_ :: remaining) =>
      RFAP.GaussianDenominatorHeight.homogeneousEval numerator denominator
          coefficients ::
        homogeneousTrace numerator denominator remaining

/-- Maximum of the structural envelopes for all recursive suffixes. -/
def homogeneousWorkingEnvelope (numerator denominator : GaussianInt) :
    List GaussianInt → Nat
  | [] => 0
  | coefficients@(_ :: remaining) =>
      max (homogeneousNormEnvelope numerator denominator coefficients)
        (homogeneousWorkingEnvelope numerator denominator remaining)

theorem homogeneousTrace_norm_le_workingEnvelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt)
    {value : GaussianInt}
    (member : value ∈ homogeneousTrace numerator denominator coefficients) :
    normNat value ≤
      homogeneousWorkingEnvelope numerator denominator coefficients := by
  induction coefficients with
  | nil =>
      simp only [homogeneousTrace, List.mem_singleton] at member
      rw [member]
      rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [homogeneousTrace, List.mem_cons] at member
      rw [homogeneousWorkingEnvelope]
      rcases member with head | tail
      · rw [head]
        exact (homogeneousEval_norm_le_envelope numerator denominator _).trans
          (le_max_left _ _)
      · exact (inductionHypothesis tail).trans (le_max_right _ _)

@[simp] theorem homogeneousTrace_length
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    (homogeneousTrace numerator denominator coefficients).length =
      coefficients.length + 1 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [homogeneousTrace, List.length_cons, inductionHypothesis]

/-- Number of coefficient clauses in the homogeneous evaluation. -/
def homogeneousStepBudget (coefficients : List GaussianInt) : Nat :=
  coefficients.length

/-- A direct multiplication count for the displayed implementation: each
clause computes one power and then performs its two outer products. -/
def homogeneousMultiplicationBudget : List GaussianInt → Nat
  | [] => 0
  | _ :: remaining =>
      remaining.length + 2 + homogeneousMultiplicationBudget remaining

@[simp] theorem homogeneousMultiplicationBudget_eq
    (coefficient : GaussianInt) (remaining : List GaussianInt) :
    homogeneousMultiplicationBudget (coefficient :: remaining) =
      remaining.length + 2 + homogeneousMultiplicationBudget remaining := rfl

/-! ## Hurwitz recursion and continuants -/

/-- Uniform continuant quadrance bound for a list of the given length whose
digits all have quadrance at most `digitBound`. -/
def continuantNormEnvelope (digitBound length : Nat) : Nat :=
  (2 * (digitBound + 1)) ^ length

theorem continuant_norm_le_envelope
    {digits : List GaussianInt} {digitBound : Nat}
    (bounded : ∀ candidate ∈ digits, normNat candidate ≤ digitBound) :
    normNat (RFAP.HurwitzRational.continuant digits).numerator ≤
        continuantNormEnvelope digitBound digits.length ∧
      normNat (RFAP.HurwitzRational.continuant digits).denominator ≤
        continuantNormEnvelope digitBound digits.length := by
  induction digits with
  | nil => exact ⟨le_refl 1, Nat.zero_le 1⟩
  | cons digit digits inductionHypothesis =>
      have digitLe := bounded digit List.mem_cons_self
      have tailBounded : ∀ candidate ∈ digits,
          normNat candidate ≤ digitBound := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem _ member)
      have tail := inductionHypothesis tailBounded
      let envelope := continuantNormEnvelope digitBound digits.length
      have productLe :
          normNat digit *
              normNat (RFAP.HurwitzRational.continuant digits).numerator ≤
            digitBound * envelope :=
        Nat.mul_le_mul digitLe tail.1
      have sumLe :
          normNat digit *
                normNat (RFAP.HurwitzRational.continuant digits).numerator +
              normNat (RFAP.HurwitzRational.continuant digits).denominator ≤
            digitBound * envelope + envelope :=
        Nat.add_le_add productLe tail.2
      have envelopeStep :
          continuantNormEnvelope digitBound (digit :: digits).length =
            2 * (digitBound * envelope + envelope) := by
        simp only [continuantNormEnvelope, List.length_cons, pow_succ, envelope]
        ring1
      constructor
      · rw [RFAP.HurwitzRational.continuant_cons]
        change normNat
            (digit * (RFAP.HurwitzRational.continuant digits).numerator +
              (RFAP.HurwitzRational.continuant digits).denominator) ≤ _
        rw [envelopeStep]
        exact (normNat_add_le_two _ _).trans
          (Nat.mul_le_mul_left 2 (by
            rw [normNat_mul]
            exact sumLe))
      · rw [RFAP.HurwitzRational.continuant_cons]
        change normNat (RFAP.HurwitzRational.continuant digits).numerator ≤ _
        rw [envelopeStep]
        have envelopeLeSum :
            envelope ≤ digitBound * envelope + envelope :=
          Nat.le_add_left envelope (digitBound * envelope)
        have sumLeDouble : digitBound * envelope + envelope ≤
            2 * (digitBound * envelope + envelope) := by
          have scaled := Nat.mul_le_mul_right
            (digitBound * envelope + envelope) (show 1 ≤ 2 by decide)
          simpa only [Nat.one_mul, Nat.two_mul] using scaled
        exact tail.1.trans (envelopeLeSum.trans sumLeDouble)

/-- Source-only envelope for both integral coordinates of every final
continuant numerator and denominator. -/
def hurwitzContinuantNormBudget (fraction : HurwitzFraction) : Nat :=
  continuantNormEnvelope (RFAP.HurwitzRational.digitNormBudget fraction)
    (natWidth (normNat fraction.denominator))

theorem encodedContinuant_norm_le_budget (fraction : HurwitzFraction) :
    normNat
          (RFAP.HurwitzRational.continuant
            (RFAP.HurwitzRational.encode fraction)).numerator ≤
        hurwitzContinuantNormBudget fraction ∧
      normNat
          (RFAP.HurwitzRational.continuant
            (RFAP.HurwitzRational.encode fraction)).denominator ≤
        hurwitzContinuantNormBudget fraction := by
  have actual := continuant_norm_le_envelope
    (fun candidate member =>
      RFAP.HurwitzRational.encode_digit_norm_le fraction member)
  have lengthLe := RFAP.HurwitzRational.encode_length_le_width fraction
  have basePositive : 0 <
      2 * (RFAP.HurwitzRational.digitNormBudget fraction + 1) :=
    Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  have envelopeLe :
      continuantNormEnvelope (RFAP.HurwitzRational.digitNormBudget fraction)
          (RFAP.HurwitzRational.encode fraction).length ≤
        hurwitzContinuantNormBudget fraction := by
    exact Nat.pow_le_pow_right basePositive lengthLe
  exact ⟨actual.1.trans envelopeLe, actual.2.trans envelopeLe⟩

/-- Every recursive suffix pair visited by the continuant calculation. -/
def continuantTrace : List GaussianInt → List ConvergentPair
  | [] => [RFAP.HurwitzRational.continuant []]
  | digits@(_ :: remaining) =>
      RFAP.HurwitzRational.continuant digits :: continuantTrace remaining

theorem continuantTrace_norm_le_envelope
    {digits : List GaussianInt} {digitBound : Nat}
    (bounded : ∀ candidate ∈ digits, normNat candidate ≤ digitBound)
    {pair : ConvergentPair} (member : pair ∈ continuantTrace digits) :
    normNat pair.numerator ≤ continuantNormEnvelope digitBound digits.length ∧
      normNat pair.denominator ≤
        continuantNormEnvelope digitBound digits.length := by
  induction digits with
  | nil =>
      simp only [continuantTrace, List.mem_singleton] at member
      rw [member]
      exact ⟨le_refl 1, Nat.zero_le 1⟩
  | cons digit digits inductionHypothesis =>
      simp only [continuantTrace, List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        exact continuant_norm_le_envelope bounded
      · have tailBounded : ∀ candidate ∈ digits,
            normNat candidate ≤ digitBound := by
          intro candidate candidateMember
          exact bounded candidate (List.mem_cons_of_mem _ candidateMember)
        have tailResult := inductionHypothesis tailBounded tail
        have basePositive : 0 < 2 * (digitBound + 1) :=
          Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
        have envelopeLe :
            continuantNormEnvelope digitBound digits.length ≤
              continuantNormEnvelope digitBound (digit :: digits).length := by
          exact Nat.pow_le_pow_right basePositive (Nat.le_succ _)
        exact ⟨tailResult.1.trans envelopeLe,
          tailResult.2.trans envelopeLe⟩

/-- The executable Hurwitz encoder has at most this many recursive clauses. -/
def hurwitzStepBudget (fraction : HurwitzFraction) : Nat :=
  natWidth (normNat fraction.denominator)

theorem hurwitz_length_le_stepBudget (fraction : HurwitzFraction) :
    (RFAP.HurwitzRational.encode fraction).length ≤
      hurwitzStepBudget fraction :=
  RFAP.HurwitzRational.encode_length_le_width fraction

/-- Two Gaussian-integer arithmetic clauses, multiplication and addition,
for each continuant digit. -/
def continuantArithmeticSteps (digits : List GaussianInt) : Nat :=
  2 * digits.length

def hurwitzContinuantStepBudget (fraction : HurwitzFraction) : Nat :=
  2 * hurwitzStepBudget fraction

theorem encodedContinuant_steps_le_budget (fraction : HurwitzFraction) :
    continuantArithmeticSteps (RFAP.HurwitzRational.encode fraction) ≤
      hurwitzContinuantStepBudget fraction :=
  Nat.mul_le_mul_left 2 (hurwitz_length_le_stepBudget fraction)

/-! ## Protected quotient targets -/

/-- Square-scan budget for a protected quotient-residual target. -/
def protectedTargetComparisonBudget
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (context : RFAP.RationalDenominatorHeight.LocalQuotientContext
      source opposite ambient)
    (target : Coordinate) : Nat :=
  targetComparisonBudget
    (RFAP.RationalDenominatorHeight.targetCoefficient context) target

/-- The protected quotient target uses the same exact threshold bracket as
the polynomial target; only its explicitly computed coefficient differs. -/
theorem protectedTargetDenominator_bracket
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (context : RFAP.RationalDenominatorHeight.LocalQuotientContext
      source opposite ambient)
    (target : Coordinate) :
    let input := targetCeiling
      (RFAP.RationalDenominatorHeight.targetCoefficient context) target
    let output := RFAP.HeightApproximation.targetDenominator
      (RFAP.RationalDenominatorHeight.targetCoefficient context) target
    (output - 1) * (output - 1) ≤ input ∧ input < output * output :=
  targetDenominator_bracket _ _

/-! ## One RFAP-II resource certificate -/

/-- Displayed data consumed by the bounded RFAP-II calculation family.  The
integral coefficient list is the already cleared list used by homogeneous
evaluation; constructing RFAP-I eliminants and the supplied Newton band is
outside this record. -/
structure StageTwoInput where
  polynomial : GaussianPolynomial
  anchor : Gaussian
  radius : Coordinate
  homogeneousNumerator : GaussianInt
  homogeneousDenominator : GaussianInt
  homogeneousCoefficients : List GaussianInt
  hurwitzSource : HurwitzFraction
  targetCoefficient : Coordinate
  target : Coordinate

namespace StageTwoInput

/-- Semantic Newton centre obtained by erasing the normalized working
record. -/
def center (input : StageTwoInput) : Gaussian :=
  RFAP.NormalizedGaussian.value
    (RFAP.NormalizedEvaluation.newtonCenter input.polynomial input.anchor)

end StageTwoInput

/-- Accounted recursive and arithmetic clauses actually executed by the
normalized Newton update, grid construction, homogeneous evaluation, finite
Hurwitz encoding, and square-threshold scan. -/
def stageTwoAccountedSteps (input : StageTwoInput) : Nat :=
  RFAP.NormalizedEvaluation.newtonSteps input.polynomial input.anchor +
    gridArithmeticSteps input.center input.radius +
    homogeneousStepBudget input.homogeneousCoefficients +
    homogeneousMultiplicationBudget input.homogeneousCoefficients +
    (RFAP.HurwitzRational.encode input.hurwitzSource).length +
    continuantArithmeticSteps
      (RFAP.HurwitzRational.encode input.hurwitzSource) +
    (targetCeiling input.targetCoefficient input.target + 1)

/-- Source recurrence bounding the sum of the same accounted clauses. -/
def stageTwoStepBudget (input : StageTwoInput) : Nat :=
  normalizedNewtonStepBudget input.polynomial input.anchor +
    gridArithmeticStepBudget input.center input.radius +
    homogeneousStepBudget input.homogeneousCoefficients +
    homogeneousMultiplicationBudget input.homogeneousCoefficients +
    hurwitzStepBudget input.hurwitzSource +
    hurwitzContinuantStepBudget input.hurwitzSource +
    targetComparisonBudget input.targetCoefficient input.target

/-- Bit-width budget for normalized Newton and grid working records. -/
def stageTwoRationalBitBudget (input : StageTwoInput) : Nat :=
  max (normalizedNewtonBitBudget input.polynomial input.anchor)
    (max (gridArithmeticBitBudget input.center input.radius)
      (gridRecordBitBudget input.center input.radius))

/-- Bit-width budget for integral homogeneous and Hurwitz records. -/
def stageTwoIntegralBitBudget (input : StageTwoInput) : Nat :=
  max (natWidth (homogeneousWorkingEnvelope input.homogeneousNumerator
    input.homogeneousDenominator input.homogeneousCoefficients))
    (max (natWidth (RFAP.HurwitzRational.digitNormBudget
      input.hurwitzSource))
      (natWidth (hurwitzContinuantNormBudget input.hurwitzSource)))

/-- A single source-computed bit-width bound for every working record named
in `StageTwoResourcesWithin`. -/
def stageTwoBitBudget (input : StageTwoInput) : Nat :=
  max (stageTwoRationalBitBudget input)
    (max (stageTwoIntegralBitBudget input)
      (natWidth (targetCeiling input.targetCoefficient input.target + 1)))

/-- The explicit `T`/`B` claim for the fully instrumented RFAP-II
post-processing family.  Each field names an actual trace or returned record;
the budgets themselves are computed only from the displayed input. -/
structure StageTwoResourcesWithin (input : StageTwoInput)
    (steps bits : Nat) : Prop where
  accountedSteps : stageTwoAccountedSteps input ≤ steps
  sourceTrace : ∀ {candidate : WorkingGaussian},
    candidate ∈ RFAP.NormalizedEvaluation.trace input.anchor
        input.polynomial.coeffs →
      workingGaussianWidth candidate ≤ bits
  derivativeTrace : ∀ {candidate : WorkingGaussian},
    candidate ∈ RFAP.NormalizedEvaluation.trace input.anchor
        (RFAP.ComputableDerivative.derivative input.polynomial).coeffs →
      workingGaussianWidth candidate ≤ bits
  newtonCenter : workingGaussianWidth
      (RFAP.NormalizedEvaluation.newtonCenter input.polynomial input.anchor) ≤
    bits
  newtonQuotient : workingGaussianWidth
      (normalizedNewtonQuotient input.polynomial input.anchor) ≤ bits
  gridDivision : rationalRecordWidth
      (RFAP.NormalizedFraction.normalizedDiv (1 / 2 : Coordinate)
        input.radius) ≤ bits
  gridRealProduct : rationalRecordWidth
      (RFAP.NormalizedFraction.normalizedMul
        (RFAP.HeightApproximation.gridDenominator input.radius : Coordinate)
        input.center.re) ≤ bits
  gridImaginaryProduct : rationalRecordWidth
      (RFAP.NormalizedFraction.normalizedMul
        (RFAP.HeightApproximation.gridDenominator input.radius : Coordinate)
        input.center.im) ≤ bits
  gridRecord : commonFractionWidth
      (RFAP.HeightApproximation.gridFraction input.center input.radius) ≤ bits
  homogeneousTrace : ∀ {candidate : GaussianInt},
    candidate ∈ homogeneousTrace input.homogeneousNumerator
        input.homogeneousDenominator input.homogeneousCoefficients →
      gaussianIntWidth candidate ≤ bits
  hurwitzDigit : ∀ {candidate : GaussianInt},
    candidate ∈ RFAP.HurwitzRational.encode input.hurwitzSource →
      gaussianIntWidth candidate ≤ bits
  continuantTrace : ∀ {pair : ConvergentPair},
    pair ∈ continuantTrace (RFAP.HurwitzRational.encode
        input.hurwitzSource) →
      gaussianIntWidth pair.numerator ≤ bits ∧
        gaussianIntWidth pair.denominator ≤ bits
  continuantNumerator : gaussianIntWidth
      (RFAP.HurwitzRational.continuant
        (RFAP.HurwitzRational.encode input.hurwitzSource)).numerator ≤ bits
  continuantDenominator : gaussianIntWidth
      (RFAP.HurwitzRational.continuant
        (RFAP.HurwitzRational.encode input.hurwitzSource)).denominator ≤ bits
  targetDenominator : natWidth
      (RFAP.HeightApproximation.targetDenominator input.targetCoefficient
        input.target) ≤ bits

theorem stageTwoAccountedSteps_le_budget (input : StageTwoInput) :
    stageTwoAccountedSteps input ≤ stageTwoStepBudget input := by
  have newton := normalizedNewton_steps_le_budget
    input.polynomial input.anchor
  have grid := gridArithmeticSteps_le_budget input.center input.radius
  have hurwitz := hurwitz_length_le_stepBudget input.hurwitzSource
  have continuant := encodedContinuant_steps_le_budget input.hurwitzSource
  have combined := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add newton grid)
            (le_refl (homogeneousStepBudget input.homogeneousCoefficients)))
          (le_refl (homogeneousMultiplicationBudget
            input.homogeneousCoefficients))) hurwitz)
        continuant)
    (le_refl (targetCeiling input.targetCoefficient input.target + 1))
  simpa only [stageTwoAccountedSteps, stageTwoStepBudget,
    targetComparisonBudget, squareThresholdComparisonBudget] using combined

/-- The complete stage-two package computes explicit natural numbers `T`
and `B` satisfying all named operation-count and working-width bounds. -/
theorem stageTwo_resource_certificate (input : StageTwoInput) :
    StageTwoResourcesWithin input (stageTwoStepBudget input)
      (stageTwoBitBudget input) := by
  have rationalLe : stageTwoRationalBitBudget input ≤
      stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact le_max_left _ _
  have integralLe : stageTwoIntegralBitBudget input ≤
      stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact (le_max_left _ _).trans (le_max_right _ _)
  have targetLe :
      natWidth (targetCeiling input.targetCoefficient input.target + 1) ≤
        stageTwoBitBudget input := by
    unfold stageTwoBitBudget
    exact (le_max_right _ _).trans (le_max_right _ _)
  refine
    { accountedSteps := stageTwoAccountedSteps_le_budget input
      sourceTrace := ?_
      derivativeTrace := ?_
      newtonCenter := ?_
      newtonQuotient := ?_
      gridDivision := ?_
      gridRealProduct := ?_
      gridImaginaryProduct := ?_
      gridRecord := ?_
      homogeneousTrace := ?_
      hurwitzDigit := ?_
      continuantTrace := ?_
      continuantNumerator := ?_
      continuantDenominator := ?_
      targetDenominator := ?_ }
  · intro candidate member
    exact (normalizedNewton_sourceTrace_width_le_budget
      input.polynomial input.anchor member).trans
        ((le_max_left _ _).trans rationalLe)
  · intro candidate member
    exact (normalizedNewton_derivativeTrace_width_le_budget
      input.polynomial input.anchor member).trans
        ((le_max_left _ _).trans rationalLe)
  · exact (normalizedNewtonCenter_width_le_budget
      input.polynomial input.anchor).trans
        ((le_max_left _ _).trans rationalLe)
  · exact (normalizedNewtonQuotient_width_le_budget
      input.polynomial input.anchor).trans
        ((le_max_left _ _).trans rationalLe)
  · exact (gridDivision_width_le_budget input.center input.radius).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans rationalLe))
  · exact (gridRealProduct_width_le_budget input.center input.radius).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans rationalLe))
  · exact (gridImaginaryProduct_width_le_budget input.center input.radius).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans rationalLe))
  · exact (gridFraction_width_le_budget input.center input.radius).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans rationalLe))
  · intro candidate member
    exact (gaussianIntWidth_le_budget
      (homogeneousTrace_norm_le_workingEnvelope
        input.homogeneousNumerator input.homogeneousDenominator
        input.homogeneousCoefficients member)).trans
          ((le_max_left _ _).trans integralLe)
  · intro candidate member
    exact (gaussianIntWidth_le_budget
      (RFAP.HurwitzRational.encode_digit_norm_le input.hurwitzSource
        member)).trans
          ((le_max_left _ _).trans ((le_max_right _ _).trans integralLe))
  · intro pair member
    have bound := continuantTrace_norm_le_envelope
      (fun candidate candidateMember =>
        RFAP.HurwitzRational.encode_digit_norm_le input.hurwitzSource
          candidateMember) member
    have lengthLe := hurwitz_length_le_stepBudget input.hurwitzSource
    have basePositive : 0 < 2 *
        (RFAP.HurwitzRational.digitNormBudget input.hurwitzSource + 1) := by
      exact Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
    have envelopeLe : continuantNormEnvelope
          (RFAP.HurwitzRational.digitNormBudget input.hurwitzSource)
          (RFAP.HurwitzRational.encode input.hurwitzSource).length ≤
        hurwitzContinuantNormBudget input.hurwitzSource :=
      Nat.pow_le_pow_right basePositive lengthLe
    exact ⟨(gaussianIntWidth_le_budget
      (bound.1.trans envelopeLe)).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans integralLe)),
      (gaussianIntWidth_le_budget
        (bound.2.trans envelopeLe)).trans
          ((le_max_right _ _).trans
            ((le_max_right _ _).trans integralLe))⟩
  · have bound := (encodedContinuant_norm_le_budget input.hurwitzSource).1
    exact (gaussianIntWidth_le_budget bound).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans integralLe))
  · have bound := (encodedContinuant_norm_le_budget input.hurwitzSource).2
    exact (gaussianIntWidth_le_budget bound).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans integralLe))
  · have threshold := squareThreshold_le_add_one
      (targetCeiling input.targetCoefficient input.target)
    have width : natWidth
        (RFAP.HeightApproximation.targetDenominator input.targetCoefficient
          input.target) ≤
        natWidth (targetCeiling input.targetCoefficient input.target + 1) := by
      unfold RFAP.HeightApproximation.targetDenominator targetCeiling
      exact natWidth_mono threshold
    exact width.trans targetLe

end RFAP.CalculationSize
