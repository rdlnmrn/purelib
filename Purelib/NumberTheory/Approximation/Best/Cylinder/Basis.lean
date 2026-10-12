module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Basic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# A finite strict-exterior criterion for consecutive best pairs

An index-one pair basis spans every displayed coefficient pair.  If every
combination using both basis directions lies strictly beyond either the
lower error wall or the upper denominator wall, then the two basis vectors
are consecutive best approximations.  The two coordinate axes require no
search: nonzero Gaussian-integral scaling can only enlarge quadrance.

This criterion is designed for finite box and transition certificates.  It
contains no minimization over an infinite carrier and constructs every
coefficient witness by the existing determinant-one Cramer formula.
-/

namespace Purelib.NumberTheory.Approximation.Best.Cylinder.Basis

/-- Finite local data sufficient to certify that an index-one pair basis is
one consecutive best window for a displayed rational source. -/
structure StrictExteriorCertificate
    (source : Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : Prop where
  /-- The two pairs have coefficient determinant of natural quadrance one. -/ indexOne :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1
  /-- The lower pair has nonzero denominator. -/ lowerDenominatorNonzero : lower.denominator ≠ 0
  /-- The upper pair has nonzero denominator. -/ upperDenominatorNonzero : upper.denominator ≠ 0
  /-- The upper pair has strictly smaller error quadrance. -/ errorOrder :
    Best.Error.errorQuadrance source upper < Best.Error.errorQuadrance source lower
  /-- The upper pair has strictly larger denominator quadrance. -/ denominatorOrder :
    Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper
  /-- Every combination with both coefficients nonzero lies strictly beyond a cylinder boundary.

Its error exceeds the lower pair error, or its denominator quadrance exceeds that of the upper pair. -/
  bothNonzeroExterior :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 → rightCoefficient ≠ 0 →
        Best.Error.errorQuadrance source lower <
            Best.Error.errorQuadrance source
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper
                leftCoefficient rightCoefficient) ∨
          Best.Error.denominatorQuadrance upper <
            Best.Error.denominatorQuadrance
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper
                leftCoefficient rightCoefficient)

/-- With zero lower coefficient, the combination is a scalar multiple of the upper pair. -/
private theorem linearCombination_left_zero
    (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (coefficient : GaussianInt) :
    GaussianInt.Pair.LinearCombination.linearCombination lower upper 0 coefficient =
      GaussianInt.Pair.LinearCombination.scalePair coefficient upper := by
  apply GaussianInt.Pair.LinearCombination.pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.Pair.LinearCombination.scalePair,
      GaussianInt.zero_re,
      GaussianInt.zero_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im,
      GaussianInt.add_re,
      GaussianInt.add_im] <;>
    ring1

/-- With zero upper coefficient, the combination is a scalar multiple of the lower pair. -/
private theorem linearCombination_right_zero
    (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (coefficient : GaussianInt) :
    GaussianInt.Pair.LinearCombination.linearCombination lower upper coefficient 0 =
      GaussianInt.Pair.LinearCombination.scalePair coefficient lower := by
  apply GaussianInt.Pair.LinearCombination.pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.Pair.LinearCombination.scalePair,
      GaussianInt.zero_re,
      GaussianInt.zero_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im,
      GaussianInt.add_re,
      GaussianInt.add_im] <;>
    ring1

/-- A nonzero Gaussian integer has natural quadrance at least one. -/
private theorem one_le_normNat {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) : 1 ≤ Purelib.Data.GaussianInt.normNat coefficient :=
  GaussianInt.normNat_pos nonzero

/-- Scaling the lower pair by a nonzero Gaussian integer cannot decrease its error quadrance. -/
private theorem errorQuadrance_le_left_scale
    (source : Gaussian.Basic.Canonical) (lower : GaussianInt.Pair.Basic.ConvergentPair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    Best.Error.errorQuadrance source lower ≤
      Best.Error.errorQuadrance source (GaussianInt.Pair.LinearCombination.scalePair coefficient lower) := by
  rw [Best.Error.errorQuadrance_scalePair]
  calc
    Best.Error.errorQuadrance source lower =
        (1 : Fraction.Rational) * Best.Error.errorQuadrance source lower := by ring1
    _ ≤ (GaussianInt.normNat coefficient : Fraction.Rational) *
          Best.Error.errorQuadrance source lower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Cast.Order.natCast_le_direct
          (one_le_normNat nonzero))
        (Gaussian.Norm.Basic.normSq_nonneg _)

/-- Scaling the upper pair by a nonzero Gaussian integer cannot decrease its error quadrance. -/
private theorem errorQuadrance_le_upper_scale
    (source : Gaussian.Basic.Canonical) (upper : GaussianInt.Pair.Basic.ConvergentPair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    Best.Error.errorQuadrance source upper ≤
      Best.Error.errorQuadrance source (GaussianInt.Pair.LinearCombination.scalePair coefficient upper) := by
  rw [Best.Error.errorQuadrance_scalePair]
  calc
    Best.Error.errorQuadrance source upper =
        (1 : Fraction.Rational) * Best.Error.errorQuadrance source upper := by ring1
    _ ≤ (GaussianInt.normNat coefficient : Fraction.Rational) *
          Best.Error.errorQuadrance source upper :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Cast.Order.natCast_le_direct
          (one_le_normNat nonzero))
        (Gaussian.Norm.Basic.normSq_nonneg _)

/-- Scaling a pair by a nonzero Gaussian integer cannot decrease its denominator quadrance. -/
private theorem denominatorQuadrance_le_scale
    (pair : GaussianInt.Pair.Basic.ConvergentPair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    Best.Error.denominatorQuadrance pair ≤
      Best.Error.denominatorQuadrance (GaussianInt.Pair.LinearCombination.scalePair coefficient pair) := by
  rw [Best.Error.denominatorQuadrance_scalePair]
  exact Nat.le_mul_of_pos_left _ (one_le_normNat nonzero)

/-- An index-one pair basis expresses every candidate by Gaussian integer coefficients.

The coefficients are the Cramer determinants multiplied by the conjugate of the basis determinant. -/
private theorem exists_coefficients
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (certificate : StrictExteriorCertificate source lower upper)
    (candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    ∃ leftCoefficient rightCoefficient : GaussianInt,
      GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient =
        candidate := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  refine ⟨GaussianInt.conj determinantValue * GaussianInt.Pair.LinearCombination.coefficientDeterminant candidate upper,
    GaussianInt.conj determinantValue * GaussianInt.Pair.LinearCombination.coefficientDeterminant lower candidate, ?_⟩
  exact GaussianInt.Pair.LinearCombination.linearCombination_cramer_of_index_one lower upper candidate
    certificate.indexOne

/-- A nonzero pair cannot have both coefficients zero in a displayed linear expansion. -/
private theorem coefficientNonzero_of_expansion
    (lower upper candidate : GaussianInt.Pair.Basic.ConvergentPair) (candidateNonzero :
      GaussianInt.Pair.LinearCombination.PairNonzero candidate)
    (leftCoefficient rightCoefficient : GaussianInt)
    (expansion :
      GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient =
        candidate) :
    leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 := by
  by_cases leftZero : leftCoefficient = 0
  · right
    intro rightZero
    have candidateZero : candidate = GaussianInt.Pair.LinearCombination.zeroPair := by
      rw [← expansion, leftZero, rightZero]
      apply GaussianInt.Pair.LinearCombination.pair_ext <;>
        apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.Pair.LinearCombination.zeroPair,
          GaussianInt.zero_re,
          GaussianInt.zero_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.add_re,
          GaussianInt.add_im] <;>
        ring1
    rcases candidateNonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero
        (congrArg (fun pair : GaussianInt.Pair.Basic.ConvergentPair => pair.numerator) candidateZero)
    · exact denominatorNonzero
        (congrArg (fun pair : GaussianInt.Pair.Basic.ConvergentPair => pair.denominator) candidateZero)
  · exact Or.inl leftZero

/-- The lower member of a strict exterior certificate is a best approximation.

The index-one expansion splits competitors into scalar multiples of a basis vector and combinations excluded by the
strict exterior condition. -/
private theorem StrictExteriorCertificate.lower_isBest
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (certificate : StrictExteriorCertificate source lower upper) :
    Purelib.NumberTheory.Approximation.Best.Basic.IsBest source lower := by
  refine ⟨certificate.lowerDenominatorNonzero, ?_, ?_⟩
  · intro candidate candidateDenominatorNonzero denominatorSmaller
    rcases exists_coefficients certificate candidate with
      ⟨leftCoefficient, rightCoefficient, expansion⟩
    have coefficientNonzero := coefficientNonzero_of_expansion lower upper
      candidate (Or.inr candidateDenominatorNonzero)
      leftCoefficient rightCoefficient expansion
    by_cases leftZero : leftCoefficient = 0
    · have rightNonzero : rightCoefficient ≠ 0 := by
        rcases coefficientNonzero with impossible | rightNonzero
        · exact (impossible leftZero).elim
        · exact rightNonzero
      have upperLeCandidate : Best.Error.denominatorQuadrance upper ≤
          Best.Error.denominatorQuadrance candidate := by
        rw [← expansion, leftZero, linearCombination_left_zero]
        exact denominatorQuadrance_le_scale upper rightNonzero
      exact (not_lt_of_ge
        (certificate.denominatorOrder.le.trans upperLeCandidate)
        denominatorSmaller).elim
    · by_cases rightZero : rightCoefficient = 0
      · have lowerLeCandidate : Best.Error.denominatorQuadrance lower ≤
            Best.Error.denominatorQuadrance candidate := by
          rw [← expansion, rightZero, linearCombination_right_zero]
          exact denominatorQuadrance_le_scale lower leftZero
        exact (not_lt_of_ge lowerLeCandidate denominatorSmaller).elim
      · rcases certificate.bothNonzeroExterior leftCoefficient
            rightCoefficient leftZero rightZero with
          errorExterior | denominatorExterior
        · rw [expansion] at errorExterior
          exact errorExterior
        · rw [expansion] at denominatorExterior
          exact (not_lt_of_ge
            (certificate.denominatorOrder.le.trans denominatorExterior.le)
            denominatorSmaller).elim
  · intro candidate candidateDenominatorNonzero denominatorNoLarger
    rcases exists_coefficients certificate candidate with
      ⟨leftCoefficient, rightCoefficient, expansion⟩
    have coefficientNonzero := coefficientNonzero_of_expansion lower upper
      candidate (Or.inr candidateDenominatorNonzero)
      leftCoefficient rightCoefficient expansion
    by_cases leftZero : leftCoefficient = 0
    · have rightNonzero : rightCoefficient ≠ 0 := by
        rcases coefficientNonzero with impossible | rightNonzero
        · exact (impossible leftZero).elim
        · exact rightNonzero
      have upperLeCandidate : Best.Error.denominatorQuadrance upper ≤
          Best.Error.denominatorQuadrance candidate := by
        rw [← expansion, leftZero, linearCombination_left_zero]
        exact denominatorQuadrance_le_scale upper rightNonzero
      exact (not_lt_of_ge denominatorNoLarger
        (certificate.denominatorOrder.trans_le upperLeCandidate)).elim
    · by_cases rightZero : rightCoefficient = 0
      · rw [← expansion, rightZero, linearCombination_right_zero]
        exact errorQuadrance_le_left_scale source lower leftZero
      · rcases certificate.bothNonzeroExterior leftCoefficient
            rightCoefficient leftZero rightZero with
          errorExterior | denominatorExterior
        · rw [expansion] at errorExterior
          exact errorExterior.le
        · rw [expansion] at denominatorExterior
          exact (not_lt_of_ge denominatorNoLarger
            (certificate.denominatorOrder.trans denominatorExterior)).elim

/-- The upper member of a strict exterior certificate is a best approximation.

Strict error ordering and the coefficient exterior condition give both best-approximation comparisons for the upper
denominator level. -/
private theorem StrictExteriorCertificate.upper_isBest
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (certificate : StrictExteriorCertificate source lower upper) :
    Purelib.NumberTheory.Approximation.Best.Basic.IsBest source upper := by
  refine ⟨certificate.upperDenominatorNonzero, ?_, ?_⟩
  · intro candidate candidateDenominatorNonzero denominatorSmaller
    rcases exists_coefficients certificate candidate with
      ⟨leftCoefficient, rightCoefficient, expansion⟩
    have coefficientNonzero := coefficientNonzero_of_expansion lower upper
      candidate (Or.inr candidateDenominatorNonzero)
      leftCoefficient rightCoefficient expansion
    by_cases leftZero : leftCoefficient = 0
    · have rightNonzero : rightCoefficient ≠ 0 := by
        rcases coefficientNonzero with impossible | rightNonzero
        · exact (impossible leftZero).elim
        · exact rightNonzero
      have upperLeCandidate : Best.Error.denominatorQuadrance upper ≤
          Best.Error.denominatorQuadrance candidate := by
        rw [← expansion, leftZero, linearCombination_left_zero]
        exact denominatorQuadrance_le_scale upper rightNonzero
      exact (not_lt_of_ge upperLeCandidate denominatorSmaller).elim
    · by_cases rightZero : rightCoefficient = 0
      · have lowerLeCandidate : Best.Error.errorQuadrance source lower ≤
            Best.Error.errorQuadrance source candidate := by
          rw [← expansion, rightZero, linearCombination_right_zero]
          exact errorQuadrance_le_left_scale source lower leftZero
        exact certificate.errorOrder.trans_le lowerLeCandidate
      · rcases certificate.bothNonzeroExterior leftCoefficient
            rightCoefficient leftZero rightZero with
          errorExterior | denominatorExterior
        · rw [expansion] at errorExterior
          exact certificate.errorOrder.trans errorExterior
        · rw [expansion] at denominatorExterior
          exact (not_lt_of_ge denominatorExterior.le denominatorSmaller).elim
  · intro candidate candidateDenominatorNonzero denominatorNoLarger
    rcases exists_coefficients certificate candidate with
      ⟨leftCoefficient, rightCoefficient, expansion⟩
    have coefficientNonzero := coefficientNonzero_of_expansion lower upper
      candidate (Or.inr candidateDenominatorNonzero)
      leftCoefficient rightCoefficient expansion
    by_cases leftZero : leftCoefficient = 0
    · have rightNonzero : rightCoefficient ≠ 0 := by
        rcases coefficientNonzero with impossible | rightNonzero
        · exact (impossible leftZero).elim
        · exact rightNonzero
      rw [← expansion, leftZero, linearCombination_left_zero]
      exact errorQuadrance_le_upper_scale source upper rightNonzero
    · by_cases rightZero : rightCoefficient = 0
      · have lowerLeCandidate : Best.Error.errorQuadrance source lower ≤
            Best.Error.errorQuadrance source candidate := by
          rw [← expansion, rightZero, linearCombination_right_zero]
          exact errorQuadrance_le_left_scale source lower leftZero
        exact certificate.errorOrder.le.trans lowerLeCandidate
      · rcases certificate.bothNonzeroExterior leftCoefficient
            rightCoefficient leftZero rightZero with
          errorExterior | denominatorExterior
        · rw [expansion] at errorExterior
          exact certificate.errorOrder.le.trans errorExterior.le
        · rw [expansion] at denominatorExterior
          exact (not_lt_of_ge denominatorNoLarger denominatorExterior).elim

/-- The mixed cylinder of a strict exterior certificate contains no nonzero pair.

The index-one coefficient expansion reduces candidates to nonzero scalar multiples or to the retained two-coefficient
exterior alternative. -/
private theorem
  StrictExteriorCertificate.mixedCylinderEmpty
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (certificate : StrictExteriorCertificate source lower upper) :
    Best.Consecutive.Basic.MixedCylinderEmpty source lower upper := by
  intro candidate candidateNonzero inside
  rcases exists_coefficients certificate candidate with
    ⟨leftCoefficient, rightCoefficient, expansion⟩
  have coefficientNonzero := coefficientNonzero_of_expansion lower upper
    candidate candidateNonzero leftCoefficient rightCoefficient expansion
  by_cases leftZero : leftCoefficient = 0
  · have rightNonzero : rightCoefficient ≠ 0 := by
      rcases coefficientNonzero with impossible | rightNonzero
      · exact (impossible leftZero).elim
      · exact rightNonzero
    have upperLeCandidate : Best.Error.denominatorQuadrance upper ≤
        Best.Error.denominatorQuadrance candidate := by
      rw [← expansion, leftZero, linearCombination_left_zero]
      exact denominatorQuadrance_le_scale upper rightNonzero
    exact (not_lt_of_ge upperLeCandidate inside.2)
  · by_cases rightZero : rightCoefficient = 0
    · have lowerLeCandidate : Best.Error.errorQuadrance source lower ≤
          Best.Error.errorQuadrance source candidate := by
        rw [← expansion, rightZero, linearCombination_right_zero]
        exact errorQuadrance_le_left_scale source lower leftZero
      exact (not_lt_of_ge lowerLeCandidate inside.1)
    · rcases certificate.bothNonzeroExterior leftCoefficient
          rightCoefficient leftZero rightZero with
        errorExterior | denominatorExterior
      · rw [expansion] at errorExterior
        exact (not_lt_of_ge errorExterior.le inside.1)
      · rw [expansion] at denominatorExterior
        exact (not_lt_of_ge denominatorExterior.le inside.2)

/-- A strict coefficient-local exterior certificate proves the full global
consecutive-best predicate. -/
theorem StrictExteriorCertificate.areConsecutiveBest
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (certificate : StrictExteriorCertificate source lower upper) :
    Best.Consecutive.Basic.AreConsecutiveBest source lower upper := by
  refine ⟨certificate.lower_isBest, certificate.upper_isBest,
    certificate.denominatorOrder, ?_⟩
  intro middle middleBest between
  apply certificate.mixedCylinderEmpty middle (Or.inr middleBest.1)
  exact ⟨middleBest.2.1 lower certificate.lower_isBest.1 between.1,
    between.2⟩

end Purelib.NumberTheory.Approximation.Best.Cylinder.Basis

end
