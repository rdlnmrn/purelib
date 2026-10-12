module

public import Purelib.NumberTheory.Approximation.Best.Cylinder.Basis
public import Purelib.NumberTheory.Approximation.Best.Error.Bounds
import Purelib.NumberTheory.Approximation.Best.Stability.ErrorComparison
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Enumeration
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Rational neighbourhoods of strict pair-basis cylinders

An index-one strict exterior certificate with a bounded window quadrance
has a positive explicit rational source neighbourhood. A two-term error
bound and the determinant identities reduce all possible new competitors
to one finite integral coefficient domain. Its comparison clearances
preserve the complete certificate at every nearby displayed source.
-/

public section

namespace Purelib.NumberTheory.Approximation.Best.Cylinder.Stability

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Data.GaussianInt.Pair
open Purelib.NumberTheory.Approximation.Best
open Purelib.NumberTheory.Approximation.Best.Stability

/-- Compute the source-displacement budget for the finite coefficient cutoff.

The original upper denominator quadrance is read through the direct
integer-backed cast, without repeated rational additions at large scales. -/
@[expose] def coefficientCutoffDistanceSq (center : Gaussian.Basic.Canonical) (lower upper : ConvergentPair) :
    Fraction.Rational :=
  Error.errorQuadrance center lower / (16 * Fraction.Cast.fromInt (Error.denominatorQuadrance upper : Int))

/-- The direct cutoff budget equals the expression using the original natural denominator cast. -/
theorem coefficientCutoffDistanceSq_eq_cast (center : Gaussian.Basic.Canonical) (lower upper : ConvergentPair) :
    coefficientCutoffDistanceSq center lower upper =
      Error.errorQuadrance center lower / (16 * (Error.denominatorQuadrance upper : Fraction.Rational)) := by
  rewrite [Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- The strict certificate gives positive lower error and upper denominator quadrances. -/
private theorem baseline_positive {center : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper) :
    0 < Error.errorQuadrance center lower ∧ (0 : Fraction.Rational) < Error.denominatorQuadrance upper :=
  ⟨(Gaussian.Norm.Basic.normSq_nonneg _).trans_lt certificate.errorOrder,
    Fraction.Cast.Order.natCast_pos_direct (GaussianInt.normNat_pos certificate.upperDenominatorNonzero)⟩

/-- Every strict certificate gives a positive coefficient-cutoff displacement budget. -/
theorem coefficientCutoffDistanceSq_pos {center : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper) :
    0 < coefficientCutoffDistanceSq center lower upper := by
  rewrite [coefficientCutoffDistanceSq_eq_cast]
  exact Fraction.Order.Field.div_pos_direct (baseline_positive certificate).1
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (baseline_positive certificate).2)

/-- The cutoff budget bounds the sampled lower error by twenty-five sixteenths of its original quadrance. -/
private theorem lower_errorQuadrance_le_of_distance
    {center sample : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper)
    (small : Gaussian.Norm.Basic.normSq (sample - center) ≤ coefficientCutoffDistanceSq center lower upper) :
    Error.errorQuadrance sample lower ≤ (25 / 16) * Error.errorQuadrance center lower := by
  rewrite [coefficientCutoffDistanceSq_eq_cast] at small
  let distance := Gaussian.Norm.Basic.normSq (sample - center)
  let upperNorm : Fraction.Rational := Error.denominatorQuadrance upper
  let lowerNorm : Fraction.Rational := Error.denominatorQuadrance lower
  let errorNorm := Error.errorQuadrance center lower
  have upperPositive : 0 < upperNorm := (baseline_positive certificate).2
  have distancePaid := (Fraction.Order.Field.le_div_iff_pos
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : Fraction.Rational) < 16) upperPositive)).mp small
  have displacementBound : Gaussian.Norm.Basic.normSq
      ((sample - center) * GaussianInt.toGaussian lower.denominator) ≤ errorNorm / 16 := by
    rewrite [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
    apply (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : Fraction.Rational) < 16)).mpr
    calc
      (distance * lowerNorm) * 16 ≤ (distance * upperNorm) * 16 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Cast.Order.natCast_le_direct certificate.denominatorOrder.le)
            (Gaussian.Norm.Basic.normSq_nonneg _)) (by decide)
      _ = distance * (16 * upperNorm) := by ring1
      _ ≤ errorNorm := distancePaid
  have weighted := Gaussian.Norm.Weighted.normSq_add_le_parameter
    (1 / 4) (by decide) (Error.error center lower) ((sample - center) * GaussianInt.toGaussian lower.denominator)
  rewrite [← Error.error_perturbation_identity center sample lower] at weighted
  have firstCoefficient : ((1 / 4 : Fraction.Rational) + 1) = 5 / 4 := by decide
  have secondCoefficient : (((1 / 4 : Fraction.Rational) + 1) / (1 / 4)) = 5 := by decide
  rewrite [secondCoefficient, firstCoefficient] at weighted
  have lossIdentity : errorNorm / 16 = errorNorm * (1 / 16) := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct,
      show ((16 : Fraction.Rational)⁻¹) = 1 / 16 by decide]
    rfl
  calc
    Error.errorQuadrance sample lower ≤ (5 / 4) * errorNorm +
        5 * Gaussian.Norm.Basic.normSq ((sample - center) * GaussianInt.toGaussian lower.denominator) := weighted
    _ ≤ (5 / 4) * errorNorm + 5 * (errorNorm / 16) :=
      Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct displacementBound (by decide))
    _ = ((5 / 4) + 5 * (1 / 16)) * errorNorm := by
      rewrite [lossIdentity]
      ring1
    _ = (25 / 16) * errorNorm := by
      rewrite [show ((5 / 4) + 5 * (1 / 16) : Fraction.Rational) = 25 / 16 by decide]
      rfl

/-- Two pairs inside the same scalar cylinder have determinant quadrance at most four times its product. -/
private theorem indexQuadrance_le_of_cylinder_bounds
    (source : Gaussian.Basic.Canonical) (left right : ConvergentPair)
    {denominatorBound errorBound : Fraction.Rational} (denominatorNonnegative : 0 ≤ denominatorBound)
    (leftDenominator : (Error.denominatorQuadrance left : Fraction.Rational) ≤ denominatorBound)
    (rightDenominator : (Error.denominatorQuadrance right : Fraction.Rational) ≤ denominatorBound)
    (leftError : Error.errorQuadrance source left ≤ errorBound)
    (rightError : Error.errorQuadrance source right ≤ errorBound) :
    (LinearCombination.coefficientIndexQuadrance left right : Fraction.Rational) ≤
      4 * denominatorBound * errorBound := by
  have firstProduct : (Error.denominatorQuadrance left : Fraction.Rational) * Error.errorQuadrance source right ≤
      denominatorBound * errorBound :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftDenominator
      (Gaussian.Norm.Basic.normSq_nonneg _)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightError denominatorNonnegative)
  have secondProduct : (Error.denominatorQuadrance right : Fraction.Rational) * Error.errorQuadrance source left ≤
      denominatorBound * errorBound :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rightDenominator
      (Gaussian.Norm.Basic.normSq_nonneg _)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftError denominatorNonnegative)
  calc
    (LinearCombination.coefficientIndexQuadrance left right : Fraction.Rational) ≤
        2 * ((Error.denominatorQuadrance left : Fraction.Rational) * Error.errorQuadrance source right +
          (Error.denominatorQuadrance right : Fraction.Rational) * Error.errorQuadrance source left) :=
      Error.coefficientIndexQuadrance_le_two_mul source left right
    _ ≤ 2 * (denominatorBound * errorBound + denominatorBound * errorBound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct firstProduct secondProduct) (by decide)
    _ = _ := by ring1

/-- The finite source budget forces every apparent cylinder competitor to have both coefficient quadrances below 32.

The original window product is at most nine halves. Source perturbation
pays a twenty-five-sixteenths factor, and the index-one determinant laws
then bound either coefficient quadrance by 225 eighths, strictly below 32.
-/
theorem coefficient_normNat_lt_thirtyTwo_of_nearby_competitor
    {center sample : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper)
    (windowBound : (Error.denominatorQuadrance upper : Fraction.Rational) * Error.errorQuadrance center lower ≤ 9 / 2)
    (small : Gaussian.Norm.Basic.normSq (sample - center) ≤ coefficientCutoffDistanceSq center lower upper)
    (sampleErrorOrder : Error.errorQuadrance sample upper ≤ Error.errorQuadrance sample lower)
    (left right : GaussianInt)
    (candidateError : Error.errorQuadrance sample (LinearCombination.linearCombination lower upper left right) ≤
      Error.errorQuadrance sample lower)
    (candidateDenominator : Error.denominatorQuadrance (LinearCombination.linearCombination lower upper left right) ≤
      Error.denominatorQuadrance upper) : GaussianInt.normNat left < 32 ∧ GaussianInt.normNat right < 32 := by
  let candidate := LinearCombination.linearCombination lower upper left right
  let upperNorm : Fraction.Rational := Error.denominatorQuadrance upper
  have upperNonnegative : 0 ≤ upperNorm := (baseline_positive certificate).2.le
  have candidateDenominatorCast : (Error.denominatorQuadrance candidate : Fraction.Rational) ≤ upperNorm :=
    Fraction.Cast.Order.natCast_le_direct candidateDenominator
  have lowerDenominatorCast : (Error.denominatorQuadrance lower : Fraction.Rational) ≤ upperNorm :=
    Fraction.Cast.Order.natCast_le_direct certificate.denominatorOrder.le
  have leftIndex : LinearCombination.coefficientIndexQuadrance candidate upper = GaussianInt.normNat left := by
    unfold candidate LinearCombination.coefficientIndexQuadrance
    rewrite [LinearCombination.coefficientDeterminant_linearCombination_right, GaussianInt.normNat_mul]
    change GaussianInt.normNat left * LinearCombination.coefficientIndexQuadrance lower upper = _
    rewrite [certificate.indexOne, Nat.mul_one]
    rfl
  have rightIndex : LinearCombination.coefficientIndexQuadrance lower candidate = GaussianInt.normNat right := by
    unfold candidate LinearCombination.coefficientIndexQuadrance
    rewrite [LinearCombination.coefficientDeterminant_left_linearCombination, GaussianInt.normNat_mul]
    change GaussianInt.normNat right * LinearCombination.coefficientIndexQuadrance lower upper = _
    rewrite [certificate.indexOne, Nat.mul_one]
    rfl
  have leftBound := indexQuadrance_le_of_cylinder_bounds sample candidate upper upperNonnegative
    candidateDenominatorCast (Fraction.Order.Basic.le_refl _) candidateError sampleErrorOrder
  have rightBound := indexQuadrance_le_of_cylinder_bounds sample lower candidate upperNonnegative
    lowerDenominatorCast candidateDenominatorCast (Fraction.Order.Basic.le_refl _) candidateError
  have commonStrict : 4 * upperNorm * Error.errorQuadrance sample lower < (32 : Fraction.Rational) := by
    calc
      4 * upperNorm * Error.errorQuadrance sample lower ≤
          4 * upperNorm * ((25 / 16) * Error.errorQuadrance center lower) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (lower_errorQuadrance_le_of_distance certificate small)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) upperNonnegative)
      _ = (4 * (25 / 16)) * (upperNorm * Error.errorQuadrance center lower) := by ring1
      _ = (25 / 4) * (upperNorm * Error.errorQuadrance center lower) := by
        rewrite [show (4 * (25 / 16) : Fraction.Rational) = 25 / 4 by decide]
        rfl
      _ ≤ (25 / 4) * (9 / 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct windowBound (by decide)
      _ < 32 := by
        change (((25 : Nat) : Fraction.Rational) / ((4 : Nat) : Fraction.Rational)) *
          (((9 : Nat) : Fraction.Rational) / ((2 : Nat) : Fraction.Rational)) < ((32 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 25, Fraction.Cast.natCast_eq_fromInt 4,
          Fraction.Cast.natCast_eq_fromInt 9, Fraction.Cast.natCast_eq_fromInt 2,
          Fraction.Cast.natCast_eq_fromInt 32]
        decide
  constructor
  · apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
    rewrite [← leftIndex]
    exact leftBound.trans_lt commonStrict
  · apply Fraction.Cast.Order.natCast_lt_iff_direct.mp
    rewrite [← rightIndex]
    exact rightBound.trans_lt commonStrict

/-- The retained finite domain of coefficient pairs of component magnitude at most five. -/
private def coefficientDomain : List (GaussianInt × GaussianInt) := GaussianInt.componentSquarePairs 5

/-- Identify mixed coefficient pairs not already excluded by their fixed denominator quadrance. -/
private def NeedsErrorComparison (lower upper : ConvergentPair) (coefficients : GaussianInt × GaussianInt) : Prop :=
  coefficients.1 ≠ 0 ∧ coefficients.2 ≠ 0 ∧
    ¬ Error.denominatorQuadrance upper <
      Error.denominatorQuadrance (LinearCombination.linearCombination lower upper coefficients.1 coefficients.2)

/-- Decide the coefficient-local requirement for an error comparison. -/
private instance needsErrorComparisonDecidable (lower upper : ConvergentPair)
    (coefficients : GaussianInt × GaussianInt) : Decidable (NeedsErrorComparison lower upper coefficients) := by
  unfold NeedsErrorComparison
  infer_instance

/-- Assign the exact strict-error clearance to each coefficient pair needing the error wall. -/
private def coefficientDistanceSq (center : Gaussian.Basic.Canonical) (lower upper : ConvergentPair)
    (coefficients : GaussianInt × GaussianInt) : Fraction.Rational :=
  if NeedsErrorComparison lower upper coefficients then
    ErrorComparison.comparisonDistanceSq center lower
      (LinearCombination.linearCombination lower upper coefficients.1 coefficients.2)
  else 1

/-- Every local comparison receives a positive budget from the original strict certificate. -/
private theorem coefficientDistanceSq_pos {center : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper) (coefficients : GaussianInt × GaussianInt) :
    0 < coefficientDistanceSq center lower upper coefficients := by
  unfold coefficientDistanceSq
  split
  · rename_i needs
    apply ErrorComparison.comparisonDistanceSq_pos
    rcases certificate.bothNonzeroExterior coefficients.1 coefficients.2 needs.1 needs.2.1 with
      errorExterior | denominatorExterior
    · exact errorExterior
    · exact (needs.2.2 denominatorExterior).elim
  · decide

/-- Take the recursive minimum of the original finite coefficient comparison budgets. -/
private def minimumCoefficientDistanceSq (center : Gaussian.Basic.Canonical) (lower upper : ConvergentPair) :
    List (GaussianInt × GaussianInt) → Fraction.Rational
  | [] => 1
  | coefficients :: remaining => min (coefficientDistanceSq center lower upper coefficients)
      (minimumCoefficientDistanceSq center lower upper remaining)

/-- The finite minimum is positive whenever its original certificate is strict. -/
private theorem minimumCoefficientDistanceSq_pos {center : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper)
    (coefficients : List (GaussianInt × GaussianInt)) :
    0 < minimumCoefficientDistanceSq center lower upper coefficients := by
  induction coefficients with
  | nil => exact (by decide : (0 : Fraction.Rational) < 1)
  | cons head remaining inductionHypothesis =>
      exact Fraction.Order.Basic.lt_min (coefficientDistanceSq_pos certificate head) inductionHypothesis

/-- The same finite minimum pays the individual budget of every listed coefficient pair. -/
private theorem minimumCoefficientDistanceSq_le_of_mem (center : Gaussian.Basic.Canonical)
    (lower upper : ConvergentPair)
    {coefficients : GaussianInt × GaussianInt} (list : List (GaussianInt × GaussianInt))
    (member : coefficients ∈ list) : minimumCoefficientDistanceSq center lower upper list ≤
      coefficientDistanceSq center lower upper coefficients := by
  induction list with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | remainingMember
      · rewrite [same]
        exact Fraction.Order.Basic.min_le_left _ _
      · exact (Fraction.Order.Basic.min_le_right _ _).trans (inductionHypothesis remainingMember)

/-- Compute one source-displacement budget preserving the complete strict pair-basis cylinder.

The finite coefficient domain is shared by all comparisons. The minimum
also pays the coefficient cutoff and the upper-to-lower error ordering.
-/
def exteriorDistanceSq (center : Gaussian.Basic.Canonical) (lower upper : ConvergentPair) : Fraction.Rational :=
  min (coefficientCutoffDistanceSq center lower upper)
    (min (ErrorComparison.comparisonDistanceSq center upper lower)
      (minimumCoefficientDistanceSq center lower upper coefficientDomain))

/-- A strict original certificate makes the complete exterior displacement budget positive. -/
theorem exteriorDistanceSq_pos {center : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper) :
    0 < exteriorDistanceSq center lower upper := by
  exact Fraction.Order.Basic.lt_min (coefficientCutoffDistanceSq_pos certificate)
    (Fraction.Order.Basic.lt_min (ErrorComparison.comparisonDistanceSq_pos certificate.errorOrder)
      (minimumCoefficientDistanceSq_pos certificate _))

/-- Every nearby source preserves the original full strict-exterior certificate.

The original window product is bounded by nine halves. Any apparent new
competitor then lies in the same retained finite coefficient domain, whose
individual error clearance rules it out.
-/
theorem strictExteriorCertificate_of_distance
    {center sample : Gaussian.Basic.Canonical} {lower upper : ConvergentPair}
    (certificate : Basis.StrictExteriorCertificate center lower upper)
    (windowBound : (Error.denominatorQuadrance upper : Fraction.Rational) * Error.errorQuadrance center lower ≤ 9 / 2)
    (small : Gaussian.Norm.Basic.normSq (sample - center) < exteriorDistanceSq center lower upper) :
    Basis.StrictExteriorCertificate sample lower upper := by
  have errorOrder : Error.errorQuadrance sample upper < Error.errorQuadrance sample lower :=
    ErrorComparison.errorQuadrance_lt_of_distance certificate.errorOrder
      (small.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  refine
    { indexOne := certificate.indexOne
      lowerDenominatorNonzero := certificate.lowerDenominatorNonzero
      upperDenominatorNonzero := certificate.upperDenominatorNonzero
      errorOrder := errorOrder
      denominatorOrder := certificate.denominatorOrder
      bothNonzeroExterior := ?_ }
  intro left right leftNonzero rightNonzero
  let candidate := LinearCombination.linearCombination lower upper left right
  by_cases denominatorExterior : Error.denominatorQuadrance upper < Error.denominatorQuadrance candidate
  · exact Or.inr denominatorExterior
  · left
    apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
    intro sampleErrorBound
    have bounded := coefficient_normNat_lt_thirtyTwo_of_nearby_competitor certificate windowBound
      ((small.trans_le (Fraction.Order.Basic.min_le_left _ _)).le) errorOrder.le left right sampleErrorBound
      (Nat.le_of_not_gt denominatorExterior)
    have member : (left, right) ∈ coefficientDomain := GaussianInt.mem_componentSquarePairs_of_normNat_lt_square
      (bounded.1.trans (by decide : 32 < (5 + 1) ^ 2)) (bounded.2.trans (by decide : 32 < (5 + 1) ^ 2))
    have needs : NeedsErrorComparison lower upper (left, right) :=
      ⟨leftNonzero, rightNonzero, denominatorExterior⟩
    have individualSmall : Gaussian.Norm.Basic.normSq (sample - center) <
        coefficientDistanceSq center lower upper (left, right) :=
      small.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          (minimumCoefficientDistanceSq_le_of_mem center lower upper _ member)))
    unfold coefficientDistanceSq at individualSmall
    rewrite [if_pos needs] at individualSmall
    have originalExterior : Error.errorQuadrance center lower < Error.errorQuadrance center candidate := by
      rcases certificate.bothNonzeroExterior left right leftNonzero rightNonzero with
        errorExterior | impossible
      · exact errorExterior
      · exact (denominatorExterior impossible).elim
    exact not_lt_of_ge sampleErrorBound (ErrorComparison.errorQuadrance_lt_of_distance originalExterior individualSmall)

end Purelib.NumberTheory.Approximation.Best.Cylinder.Stability
