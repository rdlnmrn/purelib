import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.BestApproximation

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

namespace RFAP.BasisCylinder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- Finite local data sufficient to certify that an index-one pair basis is
one consecutive best window for a displayed rational source. -/
structure StrictExteriorCertificate
    (source : Gaussian) (lower upper : Pair) : Prop where
  indexOne : coefficientIndexQuadrance lower upper = 1
  lowerDenominatorNonzero : lower.denominator ≠ 0
  upperDenominatorNonzero : upper.denominator ≠ 0
  errorOrder :
    errorQuadrance source upper < errorQuadrance source lower
  denominatorOrder :
    denominatorQuadrance lower < denominatorQuadrance upper
  bothNonzeroExterior :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 → rightCoefficient ≠ 0 →
        errorQuadrance source lower <
            errorQuadrance source
              (linearCombination lower upper
                leftCoefficient rightCoefficient) ∨
          denominatorQuadrance upper <
            denominatorQuadrance
              (linearCombination lower upper
                leftCoefficient rightCoefficient)

private theorem linearCombination_left_zero
    (lower upper : Pair) (coefficient : GaussianInt) :
    linearCombination lower upper 0 coefficient =
      scalePair coefficient upper := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [linearCombination, scalePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im] <;>
    ring1

private theorem linearCombination_right_zero
    (lower upper : Pair) (coefficient : GaussianInt) :
    linearCombination lower upper coefficient 0 =
      scalePair coefficient lower := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [linearCombination, scalePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im] <;>
    ring1

private theorem one_le_normNat {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) : 1 ≤ normNat coefficient :=
  normNat_pos nonzero

private theorem errorQuadrance_le_left_scale
    (source : Gaussian) (lower : Pair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    errorQuadrance source lower ≤
      errorQuadrance source (scalePair coefficient lower) := by
  rw [errorQuadrance_scalePair]
  calc
    errorQuadrance source lower =
        (1 : Coordinate) * errorQuadrance source lower := by ring1
    _ ≤ (normNat coefficient : Coordinate) *
          errorQuadrance source lower :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (RFAP.ConstructiveFraction.natCast_le_direct
          (one_le_normNat nonzero))
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)

private theorem errorQuadrance_le_upper_scale
    (source : Gaussian) (upper : Pair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    errorQuadrance source upper ≤
      errorQuadrance source (scalePair coefficient upper) := by
  rw [errorQuadrance_scalePair]
  calc
    errorQuadrance source upper =
        (1 : Coordinate) * errorQuadrance source upper := by ring1
    _ ≤ (normNat coefficient : Coordinate) *
          errorQuadrance source upper :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (RFAP.ConstructiveFraction.natCast_le_direct
          (one_le_normNat nonzero))
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)

private theorem denominatorQuadrance_le_scale
    (pair : Pair) {coefficient : GaussianInt}
    (nonzero : coefficient ≠ 0) :
    denominatorQuadrance pair ≤
      denominatorQuadrance (scalePair coefficient pair) := by
  rw [denominatorQuadrance_scalePair]
  exact Nat.le_mul_of_pos_left _ (one_le_normNat nonzero)

private theorem exists_coefficients
    {source : Gaussian} {lower upper : Pair}
    (certificate : StrictExteriorCertificate source lower upper)
    (candidate : Pair) :
    ∃ leftCoefficient rightCoefficient : GaussianInt,
      linearCombination lower upper leftCoefficient rightCoefficient =
        candidate := by
  let determinantValue := coefficientDeterminant lower upper
  refine ⟨conj determinantValue * coefficientDeterminant candidate upper,
    conj determinantValue * coefficientDeterminant lower candidate, ?_⟩
  exact linearCombination_cramer_of_index_one lower upper candidate
    certificate.indexOne

private theorem coefficientNonzero_of_expansion
    (lower upper candidate : Pair) (candidateNonzero : PairNonzero candidate)
    (leftCoefficient rightCoefficient : GaussianInt)
    (expansion :
      linearCombination lower upper leftCoefficient rightCoefficient =
        candidate) :
    leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 := by
  by_cases leftZero : leftCoefficient = 0
  · right
    intro rightZero
    have candidateZero : candidate = zeroPair := by
      rw [← expansion, leftZero, rightZero]
      apply pair_ext <;>
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [linearCombination, zeroPair,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im] <;>
        ring1
    rcases candidateNonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero
        (congrArg (fun pair : Pair => pair.numerator) candidateZero)
    · exact denominatorNonzero
        (congrArg (fun pair : Pair => pair.denominator) candidateZero)
  · exact Or.inl leftZero

private theorem StrictExteriorCertificate.lower_isBest
    {source : Gaussian} {lower upper : Pair}
    (certificate : StrictExteriorCertificate source lower upper) :
    IsBest source lower := by
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
      have upperLeCandidate : denominatorQuadrance upper ≤
          denominatorQuadrance candidate := by
        rw [← expansion, leftZero, linearCombination_left_zero]
        exact denominatorQuadrance_le_scale upper rightNonzero
      exact (not_lt_of_ge
        (certificate.denominatorOrder.le.trans upperLeCandidate)
        denominatorSmaller).elim
    · by_cases rightZero : rightCoefficient = 0
      · have lowerLeCandidate : denominatorQuadrance lower ≤
            denominatorQuadrance candidate := by
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
      have upperLeCandidate : denominatorQuadrance upper ≤
          denominatorQuadrance candidate := by
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

private theorem StrictExteriorCertificate.upper_isBest
    {source : Gaussian} {lower upper : Pair}
    (certificate : StrictExteriorCertificate source lower upper) :
    IsBest source upper := by
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
      have upperLeCandidate : denominatorQuadrance upper ≤
          denominatorQuadrance candidate := by
        rw [← expansion, leftZero, linearCombination_left_zero]
        exact denominatorQuadrance_le_scale upper rightNonzero
      exact (not_lt_of_ge upperLeCandidate denominatorSmaller).elim
    · by_cases rightZero : rightCoefficient = 0
      · have lowerLeCandidate : errorQuadrance source lower ≤
            errorQuadrance source candidate := by
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
      · have lowerLeCandidate : errorQuadrance source lower ≤
            errorQuadrance source candidate := by
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

private theorem StrictExteriorCertificate.mixedCylinderEmpty
    {source : Gaussian} {lower upper : Pair}
    (certificate : StrictExteriorCertificate source lower upper) :
    MixedCylinderEmpty source lower upper := by
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
    have upperLeCandidate : denominatorQuadrance upper ≤
        denominatorQuadrance candidate := by
      rw [← expansion, leftZero, linearCombination_left_zero]
      exact denominatorQuadrance_le_scale upper rightNonzero
    exact (not_lt_of_ge upperLeCandidate inside.2)
  · by_cases rightZero : rightCoefficient = 0
    · have lowerLeCandidate : errorQuadrance source lower ≤
          errorQuadrance source candidate := by
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
    {source : Gaussian} {lower upper : Pair}
    (certificate : StrictExteriorCertificate source lower upper) :
    AreConsecutiveBest source lower upper := by
  refine ⟨certificate.lower_isBest, certificate.upper_isBest,
    certificate.denominatorOrder, ?_⟩
  intro middle middleBest between
  apply certificate.mixedCylinderEmpty middle (Or.inr middleBest.1)
  exact ⟨middleBest.2.1 lower certificate.lower_isBest.1 between.1,
    between.2⟩

end RFAP.BasisCylinder
