module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter
import Purelib.Data.Gaussian.Norm.Stability
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.CoefficientBound
import Purelib.Tactic.Ring

/-!
# Critical cylinders with perturbed denominator coordinates

The normalized error coordinate is retained exactly while a Gaussian
rational multiple of that coordinate is subtracted from the normalized
denominator. A finite minimum of explicit rational clearances preserves
both the denominator order and the strict mixed-cylinder exterior.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter

open Purelib.Data
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

/-- Subtract the retained error coordinate times the displayed perturbation from the denominator coordinate. -/
@[expose] def perturbedNormalizedDenominator (errorParameter denominatorParameter : Fraction.Rational)
    (perturbation : Gaussian.Basic.Canonical) (left right : GaussianInt) : Gaussian.Basic.Canonical :=
  normalizedDenominator denominatorParameter left right -
    perturbation * normalizedError errorParameter left right

/-- The retained error ratio cannot enlarge a perturbation quadrance bounded by one eighth. -/
private theorem perturbation_errorRatio_normSq_le
    {errorParameter : Fraction.Rational}
    (certificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation ≤ 1 / 8) :
    Gaussian.Norm.Basic.normSq (perturbation * errorRatio errorParameter) ≤ 1 / 8 := by
  rewrite [Gaussian.Norm.Basic.normSq_mul]
  calc
    Gaussian.Norm.Basic.normSq perturbation * Gaussian.Norm.Basic.normSq (errorRatio errorParameter) ≤
        Gaussian.Norm.Basic.normSq perturbation * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (normSq_errorRatio_lt_one certificate).le (Gaussian.Norm.Basic.normSq_nonneg perturbation)
    _ = Gaussian.Norm.Basic.normSq perturbation := Fraction.Field.mul_one_direct _
    _ ≤ 1 / 8 := small

/-- A perturbation of quadrance at most one eighth leaves the upper denominator quadrance at most nine quarters. -/
theorem perturbed_upper_normSq_le
    {errorParameter : Fraction.Rational}
    (certificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation ≤ 1 / 8) :
    Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) ≤ 9 / 4 := by
  have productBound := perturbation_errorRatio_normSq_le certificate small
  calc
    Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) ≤
        2 * (Gaussian.Norm.Basic.normSq 1 +
          Gaussian.Norm.Basic.normSq (perturbation * errorRatio errorParameter)) :=
      Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (1 + (1 / 8 : Fraction.Rational)) := by
      rewrite [Gaussian.Norm.Basic.normSq_one]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) productBound) (by decide)
    _ = 9 / 4 := by decide

/-- A perturbation of quadrance at most one eighth leaves the upper denominator quadrance at least three eighths.

Adding back the retained correction recovers one. Its two-term quadrance
bound, together with the one-eighth correction budget, gives the explicit
positive lower bound.
-/
theorem threeEighths_le_perturbed_upper_normSq
    {errorParameter : Fraction.Rational}
    (certificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation ≤ 1 / 8) :
    (3 / 8 : Fraction.Rational) ≤
      Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) := by
  have productBound := perturbation_errorRatio_normSq_le certificate small
  have identity : (1 - perturbation * errorRatio errorParameter) +
      perturbation * errorRatio errorParameter = 1 := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
  have sumBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (1 - perturbation * errorRatio errorParameter) (perturbation * errorRatio errorParameter)
  rewrite [identity, Gaussian.Norm.Basic.normSq_one] at sumBound
  have bounded : (1 : Fraction.Rational) ≤
      2 * (Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) + 1 / 8) :=
    sumBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) productBound) (by decide))
  have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct bounded (1 / 4)
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (2 : Fraction.Rational)) _ (by decide)
  calc
    (3 / 8 : Fraction.Rational) * 2 = 1 - 1 / 4 := by decide
    _ ≤ 2 * (Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) + 1 / 8) - 1 / 4 := shifted
    _ = Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) * 2 +
        (2 * (1 / 8) - 1 / 4) := by ring1
    _ = Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) * 2 + 0 := by
      rewrite [show (2 * (1 / 8) - 1 / 4 : Fraction.Rational) = 0 by decide]
      rfl
    _ = _ := by ring1

/-- An apparent competitor after a small denominator perturbation lies in the retained finite coefficient domain. -/
private theorem coefficient_bounds_of_denominator_perturbation
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation ≤ 1 / 8)
    (left right : GaussianInt)
    (errorBound : Gaussian.Norm.Basic.normSq (normalizedError errorParameter left right) ≤ 1)
    (denominatorBound : Gaussian.Norm.Basic.normSq
        (perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right) ≤
      Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter)) :
    GaussianInt.normNat left < 32 ∧ GaussianInt.normNat right < 32 := by
  have productBound : Gaussian.Norm.Basic.normSq
      (perturbation * normalizedError errorParameter left right) ≤ 1 / 8 := by
    rewrite [Gaussian.Norm.Basic.normSq_mul]
    calc
      Gaussian.Norm.Basic.normSq perturbation * Gaussian.Norm.Basic.normSq
          (normalizedError errorParameter left right) ≤ Gaussian.Norm.Basic.normSq perturbation * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorBound (Gaussian.Norm.Basic.normSq_nonneg perturbation)
      _ = Gaussian.Norm.Basic.normSq perturbation := Fraction.Field.mul_one_direct _
      _ ≤ 1 / 8 := small
  have denominatorIdentity : normalizedDenominator denominatorParameter left right =
      perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right +
        perturbation * normalizedError errorParameter left right := by
    unfold perturbedNormalizedDenominator
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
        Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  have originalDenominatorBound : Gaussian.Norm.Basic.normSq
      (normalizedDenominator denominatorParameter left right) ≤ 5 := by
    calc
      Gaussian.Norm.Basic.normSq (normalizedDenominator denominatorParameter left right) =
          Gaussian.Norm.Basic.normSq
            (perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right +
              perturbation * normalizedError errorParameter left right) := congrArg _ denominatorIdentity
      _ ≤ 2 *
          (Gaussian.Norm.Basic.normSq
              (perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right) +
            Gaussian.Norm.Basic.normSq (perturbation * normalizedError errorParameter left right)) :=
        Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((9 / 4 : Fraction.Rational) + 1 / 8) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct
            (denominatorBound.trans (perturbed_upper_normSq_le errorCertificate small)) productBound) (by decide)
      _ ≤ 5 := by decide
  exact coefficient_normNat_lt_thirtyTwo_of_swapped_bounds
    errorCertificate denominatorCertificate left right errorBound originalDenominatorBound

/-- Identify the mixed coefficient pairs whose unchanged error coordinate needs the denominator wall. -/
private def NeedsDenominatorComparison (errorParameter : Fraction.Rational)
    (coefficients : GaussianInt × GaussianInt) : Prop :=
  coefficients.1 ≠ 0 ∧ coefficients.2 ≠ 0 ∧
    ¬ (1 : Fraction.Rational) < Gaussian.Norm.Basic.normSq
      (normalizedError errorParameter coefficients.1 coefficients.2)

/-- Decide the exact mixed-coefficient denominator requirement. -/
private instance needsDenominatorComparisonDecidable (errorParameter : Fraction.Rational)
    (coefficients : GaussianInt × GaussianInt) :
    Decidable (NeedsDenominatorComparison errorParameter coefficients) := by
  unfold NeedsDenominatorComparison
  infer_instance

/-- Assign one affine comparison budget to a mixed candidate needing the denominator wall. -/
private def coefficientDistanceSq (errorParameter denominatorParameter : Fraction.Rational)
    (coefficients : GaussianInt × GaussianInt) : Fraction.Rational :=
  if NeedsDenominatorComparison errorParameter coefficients then
    Gaussian.Norm.Stability.affineComparisonDistanceSq
      1 (normalizedDenominator denominatorParameter coefficients.1 coefficients.2)
      (-errorRatio errorParameter) (-normalizedError errorParameter coefficients.1 coefficients.2)
  else 1

/-- Every coefficient budget is positive for two retained critical parameters. -/
private theorem coefficientDistanceSq_pos
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    (coefficients : GaussianInt × GaussianInt) :
    0 < coefficientDistanceSq errorParameter denominatorParameter coefficients := by
  unfold coefficientDistanceSq
  split
  · rename_i needs
    have exterior := strictExterior errorCertificate denominatorCertificate
      coefficients.1 coefficients.2 needs.1 needs.2.1
    have denominatorExterior : (1 : Fraction.Rational) < Gaussian.Norm.Basic.normSq
        (normalizedDenominator denominatorParameter coefficients.1 coefficients.2) := by
      rcases exterior with errorExterior | denominatorExterior
      · exact (needs.2.2 errorExterior).elim
      · exact denominatorExterior
    apply Gaussian.Norm.Stability.affineComparisonDistanceSq_pos
    rewrite [Gaussian.Norm.Basic.normSq_one]
    exact denominatorExterior
  · decide

/-- Take the recursive finite minimum of the displayed coefficient clearances. -/
private def minimumCoefficientDistanceSq (errorParameter denominatorParameter : Fraction.Rational) :
    List (GaussianInt × GaussianInt) → Fraction.Rational
  | [] => 1
  | coefficients :: remaining => min (coefficientDistanceSq errorParameter denominatorParameter coefficients)
      (minimumCoefficientDistanceSq errorParameter denominatorParameter remaining)

/-- The finite coefficient minimum stays positive. -/
private theorem minimumCoefficientDistanceSq_pos
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    (coefficients : List (GaussianInt × GaussianInt)) :
    0 < minimumCoefficientDistanceSq errorParameter denominatorParameter coefficients := by
  induction coefficients with
  | nil => exact (by decide : (0 : Fraction.Rational) < 1)
  | cons head remaining inductionHypothesis =>
      exact Fraction.Order.Basic.lt_min
        (coefficientDistanceSq_pos errorCertificate denominatorCertificate head) inductionHypothesis

/-- The retained finite minimum pays every listed coefficient clearance. -/
private theorem minimumCoefficientDistanceSq_le_of_mem
    (errorParameter denominatorParameter : Fraction.Rational)
    {coefficients : GaussianInt × GaussianInt} (list : List (GaussianInt × GaussianInt))
    (member : coefficients ∈ list) :
    minimumCoefficientDistanceSq errorParameter denominatorParameter list ≤
      coefficientDistanceSq errorParameter denominatorParameter coefficients := by
  induction list with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | remainingMember
      · rewrite [same]
        exact Fraction.Order.Basic.min_le_left _ _
      · exact (Fraction.Order.Basic.min_le_right _ _).trans (inductionHypothesis remainingMember)

/-- Compute one finite rational budget preserving the entire perturbed denominator cylinder.

The original bounded coefficient enumeration is reused. The budget also
pays the coefficient cutoff and the lower-to-upper denominator comparison.
-/
def denominatorPerturbationDistanceSq (errorParameter denominatorParameter : Fraction.Rational) :
    Fraction.Rational :=
  min (1 / 8)
    (min (Gaussian.Norm.Stability.affineComparisonDistanceSq
      (denominatorRatio denominatorParameter) 1 (-1) (-errorRatio errorParameter))
      (minimumCoefficientDistanceSq errorParameter denominatorParameter
        Robust.CoefficientBound.boundedCoefficientPairs))

/-- The finite denominator perturbation budget always pays its one-eighth coefficient cutoff. -/
theorem denominatorPerturbationDistanceSq_le_oneEighth (errorParameter denominatorParameter : Fraction.Rational) :
    denominatorPerturbationDistanceSq errorParameter denominatorParameter ≤ 1 / 8 :=
  Fraction.Order.Basic.min_le_left _ _

/-- The denominator perturbation budget is positive for two critical parameters. -/
theorem denominatorPerturbationDistanceSq_pos
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter) :
    0 < denominatorPerturbationDistanceSq errorParameter denominatorParameter := by
  have denominatorOrder : Gaussian.Norm.Basic.normSq (denominatorRatio denominatorParameter) <
      Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) := by
    rewrite [normSq_denominatorRatio, Gaussian.Norm.Basic.normSq_one]
    have ordered := normSq_errorRatio_lt_one denominatorCertificate
    rewrite [normSq_errorRatio] at ordered
    exact ordered
  unfold denominatorPerturbationDistanceSq
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min
      (Gaussian.Norm.Stability.affineComparisonDistanceSq_pos _ _ denominatorOrder)
      (minimumCoefficientDistanceSq_pos errorCertificate denominatorCertificate _))

/-- A perturbation inside the common budget retains strict lower-to-upper denominator order. -/
theorem denominatorOrder_of_perturbation
    {errorParameter denominatorParameter : Fraction.Rational}
    (_errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation <
      denominatorPerturbationDistanceSq errorParameter denominatorParameter) :
    Gaussian.Norm.Basic.normSq (denominatorRatio denominatorParameter - perturbation) <
      Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) := by
  have denominatorOrder : Gaussian.Norm.Basic.normSq (denominatorRatio denominatorParameter) <
      Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) := by
    rewrite [normSq_denominatorRatio, Gaussian.Norm.Basic.normSq_one]
    have ordered := normSq_errorRatio_lt_one denominatorCertificate
    rewrite [normSq_errorRatio] at ordered
    exact ordered
  have ordered := Gaussian.Norm.Stability.normSq_affine_lt_of_distance
    (referenceDirection := (-1 : Gaussian.Basic.Canonical))
    (contenderDirection := -errorRatio errorParameter) denominatorOrder
    (small.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have lowerIdentity : denominatorRatio denominatorParameter + perturbation * (-1) =
      denominatorRatio denominatorParameter - perturbation := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
        Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  have upperIdentity : 1 + perturbation * -errorRatio errorParameter =
      1 - perturbation * errorRatio errorParameter := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
  rewrite [lowerIdentity, upperIdentity] at ordered
  exact ordered

/-- The computed cutoff keeps the perturbed lower denominator coordinate nonzero. -/
theorem perturbedLowerDenominator_ne_zero
    {errorParameter denominatorParameter : Fraction.Rational}
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation <
      denominatorPerturbationDistanceSq errorParameter denominatorParameter) :
    denominatorRatio denominatorParameter - perturbation ≠ 0 := by
  have denominatorNorm : Gaussian.Norm.Basic.normSq (denominatorRatio denominatorParameter) =
      (half * denominatorParameter) ^ 2 + 1 / 4 := by
    change (half * denominatorParameter) ^ 2 + (-half) ^ 2 = _
    rewrite [show (-half) ^ 2 = (1 / 4 : Fraction.Rational) by decide]
    rfl
  have quarterLe : (1 / 4 : Fraction.Rational) ≤
      Gaussian.Norm.Basic.normSq (denominatorRatio denominatorParameter) := by
    rewrite [denominatorNorm]
    exact le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have eighthBound : Gaussian.Norm.Basic.normSq perturbation < 1 / 8 :=
    small.trans_le (Fraction.Order.Basic.min_le_left _ _)
  intro zero
  have same : denominatorRatio denominatorParameter = perturbation := by
    calc
      denominatorRatio denominatorParameter =
          (denominatorRatio denominatorParameter - perturbation) + perturbation := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
      _ = perturbation := by
        rewrite [zero, Gaussian.Basic.zero_add]
        rfl
  rewrite [same] at quarterLe
  exact not_lt_of_ge (by decide : (1 / 8 : Fraction.Rational) ≤ 1 / 4)
    (quarterLe.trans_lt eighthBound)

/-- The computed denominator order keeps the perturbed upper denominator coordinate nonzero. -/
theorem perturbedUpperDenominator_ne_zero
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation <
      denominatorPerturbationDistanceSq errorParameter denominatorParameter) :
    1 - perturbation * errorRatio errorParameter ≠ 0 := by
  have ordered := denominatorOrder_of_perturbation errorCertificate denominatorCertificate small
  intro zero
  rewrite [zero, Gaussian.Norm.Basic.normSq_zero] at ordered
  exact not_lt_of_ge (Gaussian.Norm.Basic.normSq_nonneg _) ordered

/-- The common finite clearance preserves the strict mixed-cylinder exterior for every integral coefficient pair. -/
theorem strictExterior_of_denominator_perturbation
    {errorParameter denominatorParameter : Fraction.Rational}
    (errorCertificate : Cylinder.Basic.IsCriticalParameter errorParameter)
    (denominatorCertificate : Cylinder.Basic.IsCriticalParameter denominatorParameter)
    {perturbation : Gaussian.Basic.Canonical}
    (small : Gaussian.Norm.Basic.normSq perturbation <
      denominatorPerturbationDistanceSq errorParameter denominatorParameter)
    (left right : GaussianInt) (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (1 : Fraction.Rational) < Gaussian.Norm.Basic.normSq (normalizedError errorParameter left right) ∨
      Gaussian.Norm.Basic.normSq (1 - perturbation * errorRatio errorParameter) <
        Gaussian.Norm.Basic.normSq
          (perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right) := by
  by_cases errorExterior : (1 : Fraction.Rational) <
      Gaussian.Norm.Basic.normSq (normalizedError errorParameter left right)
  · exact Or.inl errorExterior
  · right
    apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
    intro denominatorBound
    have cutoff := coefficient_bounds_of_denominator_perturbation errorCertificate denominatorCertificate
      ((small.trans_le (Fraction.Order.Basic.min_le_left _ _)).le) left right
      (Fraction.Order.Arithmetic.le_of_not_gt_direct errorExterior) denominatorBound
    have member : (left, right) ∈ Robust.CoefficientBound.boundedCoefficientPairs :=
      Robust.CoefficientBound.mem_boundedCoefficientPairs_of_normNat_lt_thirtyTwo cutoff.1 cutoff.2
    have needs : NeedsDenominatorComparison errorParameter (left, right) :=
      ⟨leftNonzero, rightNonzero, errorExterior⟩
    have coefficientSmall : Gaussian.Norm.Basic.normSq perturbation <
        coefficientDistanceSq errorParameter denominatorParameter (left, right) :=
      small.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          (minimumCoefficientDistanceSq_le_of_mem errorParameter denominatorParameter _ member)))
    unfold coefficientDistanceSq at coefficientSmall
    rewrite [if_pos needs] at coefficientSmall
    have originalExterior : Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) <
        Gaussian.Norm.Basic.normSq (normalizedDenominator denominatorParameter left right) := by
      rewrite [Gaussian.Norm.Basic.normSq_one]
      rcases strictExterior errorCertificate denominatorCertificate left right leftNonzero rightNonzero with
        impossible | denominatorExterior
      · exact (errorExterior impossible).elim
      · exact denominatorExterior
    have preserved := Gaussian.Norm.Stability.normSq_affine_lt_of_distance originalExterior coefficientSmall
    have upperIdentity : 1 + perturbation * -errorRatio errorParameter =
        1 - perturbation * errorRatio errorParameter := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
    have candidateIdentity : normalizedDenominator denominatorParameter left right +
        perturbation * -normalizedError errorParameter left right =
          perturbedNormalizedDenominator errorParameter denominatorParameter perturbation left right := by
      unfold perturbedNormalizedDenominator
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
    rewrite [upperIdentity, candidateIdentity] at preserved
    exact (not_lt_of_ge denominatorBound preserved)

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter
