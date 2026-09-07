import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.RepeatedIndex

/-!
# Local finite successors of best Gaussian approximations

This file replaces the existential division in the centered coefficient
coset by an executable coordinate calculation.  It then uses the consecutive
index dichotomy and the no-repeated-index theorem to build a finite successor
search from one adjacent best pair rather than from the full source rectangle.
-/

namespace RFAP.LocalSuccessor

abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair
abbrev Fraction := RFAP.HurwitzRational.Fraction

open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- Coordinatewise exact halving when the input coordinates are even.  The
definition remains total so that it can be used in an executable candidate
list; exactness is proved under the displayed divisibility hypotheses. -/
def halfGaussianInt (value : GaussianInt) : GaussianInt :=
  ⟨value.re / 2, value.im / 2⟩

/-- Divide a displayed Gaussian integer by a quadrance-two divisor by
multiplying by its conjugate and halving both integral coordinates. -/
def divideByNormTwo (divisor value : GaussianInt) : GaussianInt :=
  halfGaussianInt (conj divisor * value)

/-- The coordinate division recovers an explicitly multiplied quotient. -/
theorem divideByNormTwo_mul
    (divisor quotient : GaussianInt) (divisorNorm : normNat divisor = 2) :
    divideByNormTwo divisor (divisor * quotient) = quotient := by
  have conjugateProduct : conj divisor * divisor = ofNat 2 := by
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm, mul_conj,
      divisorNorm]
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
  · dsimp only [divideByNormTwo, halfGaussianInt]
    rw [← RFAP.ConstructiveGaussianHeight.GaussianInt.mul_assoc,
      conjugateProduct]
    simp only [ofNat,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re]
    rw [Int.zero_mul, Int.sub_zero]
    change ((2 : Int) * quotient.re) / 2 = quotient.re
    exact Int.mul_ediv_cancel_left quotient.re (by decide)
  · dsimp only [divideByNormTwo, halfGaussianInt]
    rw [← RFAP.ConstructiveGaussianHeight.GaussianInt.mul_assoc,
      conjugateProduct]
    simp only [ofNat,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im]
    rw [Int.zero_mul, Int.add_zero]
    change ((2 : Int) * quotient.im) / 2 = quotient.im
    exact Int.mul_ediv_cancel_left quotient.im (by decide)

/-- Apply the executable quadrance-two division to both coefficients of a
pair. -/
def dividePairByNormTwo (divisor : GaussianInt) (pair : Pair) : Pair :=
  { numerator := divideByNormTwo divisor pair.numerator
    denominator := divideByNormTwo divisor pair.denominator }

/-- Pairwise quadrance-two division cancels an explicit pair scaling. -/
theorem dividePairByNormTwo_scalePair
    (divisor : GaussianInt) (pair : Pair) (divisorNorm : normNat divisor = 2) :
    dividePairByNormTwo divisor
        (RFAP.BestApproximation.scalePair divisor pair) = pair := by
  apply RFAP.BestApproximation.pair_ext
  · exact divideByNormTwo_mul divisor pair.numerator divisorNorm
  · exact divideByNormTwo_mul divisor pair.denominator divisorNorm

/-- A displayed centered-coset identity can now be solved by the executable
quadrance-two division rather than by retaining an existential quotient. -/
theorem eq_dividePairByNormTwo_of_scalePair_eq
    (divisor : GaussianInt) (pair combination : Pair)
    (divisorNorm : normNat divisor = 2)
    (identity : RFAP.BestApproximation.scalePair divisor pair = combination) :
    pair = dividePairByNormTwo divisor combination := by
  rw [← identity, dividePairByNormTwo_scalePair divisor pair divisorNorm]

/-- A source- and state-computed quadrance bound for the trailing coefficient
in either local successor form. -/
def trailingCoefficientBound (source : Fraction) (previous : Pair) : Nat :=
  4 * (normNat source.denominator +
    RFAP.BestApproximation.denominatorQuadrance previous)

/-- The quadrance-one and quadrance-two possibilities for the leading local
coefficient. -/
def leadingCoefficients : List GaussianInt :=
  [1, -1, RFAP.HurwitzGeometry.imaginaryUnit,
    -RFAP.HurwitzGeometry.imaginaryUnit,
    ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩]

/-- The source/state-bounded trailing coefficient search. -/
def trailingCoefficients (source : Fraction) (previous : Pair) :
    List GaussianInt :=
  componentSquare (trailingCoefficientBound source previous)

theorem mem_leadingCoefficients_of_norm_eq_one_or_two
    {coefficient : GaussianInt}
    (coefficientNorm : normNat coefficient = 1 ∨
      normNat coefficient = 2) :
    coefficient ∈ leadingCoefficients := by
  rcases coefficientNorm with normOne | normTwo
  · have unit := RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one
      normOne
    rcases unit with coefficientCase | coefficientCase | coefficientCase |
      coefficientCase <;> subst coefficient <;> decide
  · have diagonal := RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two
      normTwo
    rcases diagonal with coefficientCase | coefficientCase |
      coefficientCase | coefficientCase <;> subst coefficient <;> decide

theorem mem_trailingCoefficients_of_norm_le
    {source : Fraction} {previous : Pair} {coefficient : GaussianInt}
    (bounded : normNat coefficient ≤ trailingCoefficientBound source previous) :
    coefficient ∈ trailingCoefficients source previous := by
  exact mem_componentSquare_of_normNat_le bounded

/-- The elementary quadrance bound for a Gaussian-integer difference. -/
theorem normNat_sub_le_two (left right : GaussianInt) :
    normNat (left - right) ≤ 2 * (normNat left + normNat right) := by
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  calc
    (normNat (left - right) : RFAP.ConstructiveFraction.Rational) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian left - toGaussian right) := by
      rw [← toGaussian_sub, normSq_toGaussian]
    _ ≤ 2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq (toGaussian left) +
            RFAP.ConstructiveGaussian.Gaussian.normSq (toGaussian right)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
    _ = ((2 * (normNat left + normNat right) : Nat) :
          RFAP.ConstructiveFraction.Rational) := by
      rw [normSq_toGaussian, normSq_toGaussian, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]

/-- Any local coefficient identity whose scale and leading coefficient have
quadrance at most two forces the trailing coefficient into the displayed
source/state bound. -/
theorem trailingCoefficient_norm_le
    {source : Fraction} {previous current next : Pair}
    {scale leftCoefficient rightCoefficient : GaussianInt}
    (currentDenominatorNonzero : current.denominator ≠ 0)
    (nextDenominatorBound :
      RFAP.BestApproximation.denominatorQuadrance next ≤
        normNat source.denominator)
    (scaleNorm : normNat scale ≤ 2)
    (leftCoefficientNorm : normNat leftCoefficient ≤ 2)
    (identity :
      RFAP.BestApproximation.scalePair scale next =
        RFAP.BestApproximation.linearCombination previous current
          leftCoefficient rightCoefficient) :
    normNat rightCoefficient ≤ trailingCoefficientBound source previous := by
  have denominatorIdentity := congrArg
    (fun pair : Pair => pair.denominator) identity
  change scale * next.denominator =
    leftCoefficient * previous.denominator +
      rightCoefficient * current.denominator at denominatorIdentity
  have productIdentity :
      rightCoefficient * current.denominator =
        scale * next.denominator - leftCoefficient * previous.denominator := by
    calc
      rightCoefficient * current.denominator =
          (leftCoefficient * previous.denominator +
            rightCoefficient * current.denominator) -
              leftCoefficient * previous.denominator := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      _ = scale * next.denominator -
          leftCoefficient * previous.denominator := by
        rw [← denominatorIdentity]
  have productBound :
      normNat rightCoefficient * normNat current.denominator ≤
        trailingCoefficientBound source previous := by
    calc
      normNat rightCoefficient * normNat current.denominator =
          normNat (rightCoefficient * current.denominator) :=
        (normNat_mul _ _).symm
      _ = normNat
          (scale * next.denominator -
            leftCoefficient * previous.denominator) := by
        rw [productIdentity]
      _ ≤ 2 *
          (normNat (scale * next.denominator) +
            normNat (leftCoefficient * previous.denominator)) :=
        normNat_sub_le_two _ _
      _ = 2 *
          (normNat scale * RFAP.BestApproximation.denominatorQuadrance next +
            normNat leftCoefficient *
              RFAP.BestApproximation.denominatorQuadrance previous) := by
        rw [normNat_mul, normNat_mul]
        rfl
      _ ≤ 2 *
          (2 * normNat source.denominator +
            2 * RFAP.BestApproximation.denominatorQuadrance previous) := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add
          (Nat.mul_le_mul scaleNorm nextDenominatorBound)
          (Nat.mul_le_mul_right
            (RFAP.BestApproximation.denominatorQuadrance previous)
            leftCoefficientNorm)
      _ = trailingCoefficientBound source previous := by
        unfold trailingCoefficientBound
        ring1
  have currentNormPositive := normNat_pos currentDenominatorNonzero
  calc
    normNat rightCoefficient = normNat rightCoefficient * 1 :=
      (Nat.mul_one _).symm
    _ ≤ normNat rightCoefficient * normNat current.denominator :=
      Nat.mul_le_mul_left _ currentNormPositive
    _ ≤ trailingCoefficientBound source previous := productBound

/-- Integral local successor candidates in the coefficient basis supplied by
the preceding adjacent pair. -/
def integralCandidates (source : Fraction) (previous current : Pair) :
    List Pair :=
  leadingCoefficients.flatMap fun leftCoefficient =>
    (trailingCoefficients source previous).map fun rightCoefficient =>
      RFAP.BestApproximation.linearCombination previous current
        leftCoefficient rightCoefficient

/-- Centered local successor candidates, computed by exact quadrance-two
division.  When the determinant has quadrance one these are harmless extra
records; exact successor completeness chooses the appropriate branch. -/
def centeredCandidates (source : Fraction) (previous current : Pair) :
    List Pair :=
  let determinantValue :=
    RFAP.BestApproximation.coefficientDeterminant previous current
  leadingCoefficients.flatMap fun leftCoefficient =>
    (trailingCoefficients source previous).map fun rightCoefficient =>
      dividePairByNormTwo determinantValue
        (RFAP.BestApproximation.linearCombination previous current
          leftCoefficient rightCoefficient)

/-- Finite local over-enumeration of the next best level from one supplied
adjacent pair. -/
def candidates (source : Fraction) (previous current : Pair) : List Pair :=
  integralCandidates source previous current ++
    centeredCandidates source previous current

theorem integral_mem_candidates
    {source : Fraction} {previous current : Pair}
    {leftCoefficient rightCoefficient : GaussianInt}
    (leftMember : leftCoefficient ∈ leadingCoefficients)
    (rightMember : rightCoefficient ∈ trailingCoefficients source previous) :
    RFAP.BestApproximation.linearCombination previous current
        leftCoefficient rightCoefficient ∈
      candidates source previous current := by
  rw [candidates, List.mem_append]
  left
  apply QuotientFreeList.mem_flatMap.mpr
  exact ⟨leftCoefficient, leftMember,
    QuotientFreeList.mem_map_of_mem rightMember⟩

theorem centered_mem_candidates
    {source : Fraction} {previous current : Pair}
    {leftCoefficient rightCoefficient : GaussianInt}
    (leftMember : leftCoefficient ∈ leadingCoefficients)
    (rightMember : rightCoefficient ∈ trailingCoefficients source previous) :
    dividePairByNormTwo
        (RFAP.BestApproximation.coefficientDeterminant previous current)
        (RFAP.BestApproximation.linearCombination previous current
          leftCoefficient rightCoefficient) ∈
      candidates source previous current := by
  rw [candidates, List.mem_append]
  right
  apply QuotientFreeList.mem_flatMap.mpr
  exact ⟨leftCoefficient, leftMember,
    QuotientFreeList.mem_map_of_mem rightMember⟩

/-- The determinant index of an integral local combination is the preceding
index multiplied by the leading coefficient quadrance. -/
theorem coefficientIndexQuadrance_eq_of_linearCombination
    (previous current next : Pair)
    (leftCoefficient rightCoefficient : GaussianInt)
    (identity : next =
      RFAP.BestApproximation.linearCombination previous current
        leftCoefficient rightCoefficient) :
    RFAP.BestApproximation.coefficientIndexQuadrance current next =
      normNat leftCoefficient *
        RFAP.BestApproximation.coefficientIndexQuadrance previous current := by
  rw [RFAP.BestApproximation.coefficientIndexQuadrance, identity,
    RFAP.BestApproximation.coefficientDeterminant_right_linearCombination,
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg, normNat_mul]
  rfl

/-- The corresponding determinant identity for a centered, scaled local
combination. -/
theorem coefficientIndexQuadrance_scale_eq_of_scalePair_eq
    (previous current next : Pair)
    (scale leftCoefficient rightCoefficient : GaussianInt)
    (identity :
      RFAP.BestApproximation.scalePair scale next =
        RFAP.BestApproximation.linearCombination previous current
          leftCoefficient rightCoefficient) :
    normNat scale *
        RFAP.BestApproximation.coefficientIndexQuadrance current next =
      normNat leftCoefficient *
        RFAP.BestApproximation.coefficientIndexQuadrance previous current := by
  have determinantIdentity := congrArg
    (RFAP.BestApproximation.coefficientDeterminant current) identity
  rw [RFAP.BestApproximation.coefficientDeterminant_scalePair_right,
    RFAP.BestApproximation.coefficientDeterminant_right_linearCombination]
      at determinantIdentity
  have normIdentity := congrArg normNat determinantIdentity
  rw [normNat_mul,
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
    normNat_mul] at normIdentity
  exact normIdentity

theorem scalePair_one (pair : Pair) :
    RFAP.BestApproximation.scalePair 1 pair = pair := by
  apply RFAP.BestApproximation.pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
      simp only [RFAP.BestApproximation.scalePair,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_im] <;>
      ring1

/-- Every actual next consecutive best level occurs in the bounded local
candidate list generated from the preceding adjacent pair.  This is the
no-skipped-level completeness theorem for candidate generation. -/
theorem next_mem_candidates
    {source : Fraction} {previous current next : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value current next) :
    next ∈ candidates source previous current := by
  rcases first.coefficientIndexQuadrance_eq_one_or_two with
    firstIndexOne | firstIndexTwo
  · let determinantValue :=
      RFAP.BestApproximation.coefficientDeterminant previous current
    let leftCoefficient :=
      conj determinantValue *
        RFAP.BestApproximation.coefficientDeterminant next current
    let rightCoefficient :=
      conj determinantValue *
        RFAP.BestApproximation.coefficientDeterminant previous next
    have expansion :=
      RFAP.BestApproximation.linearCombination_cramer_of_index_one
        previous current next firstIndexOne
    have identity :
        next = RFAP.BestApproximation.linearCombination previous current
          leftCoefficient rightCoefficient := by
      simpa only [determinantValue, leftCoefficient, rightCoefficient] using
        expansion.symm
    have indexIdentity := coefficientIndexQuadrance_eq_of_linearCombination
      previous current next leftCoefficient rightCoefficient identity
    have leftCoefficientNorm :
        normNat leftCoefficient = 1 ∨ normNat leftCoefficient = 2 := by
      rcases second.coefficientIndexQuadrance_eq_one_or_two with
        secondIndexOne | secondIndexTwo
      · left
        rw [firstIndexOne, secondIndexOne] at indexIdentity
        simpa only [Nat.mul_one] using indexIdentity.symm
      · right
        rw [firstIndexOne, secondIndexTwo] at indexIdentity
        simpa only [Nat.mul_one] using indexIdentity.symm
    have leftCoefficientBound : normNat leftCoefficient ≤ 2 := by
      rcases leftCoefficientNorm with normOne | normTwo
      · rw [normOne]
        decide
      · rw [normTwo]
    have scaledIdentity :
        RFAP.BestApproximation.scalePair 1 next =
          RFAP.BestApproximation.linearCombination previous current
            leftCoefficient rightCoefficient := by
      rw [scalePair_one]
      exact identity
    have rightCoefficientBound := trailingCoefficient_norm_le
      first.2.1.1 second.2.1.denominatorQuadrance_le_source
      (show normNat (1 : GaussianInt) ≤ 2 by decide)
      leftCoefficientBound scaledIdentity
    rw [identity]
    exact integral_mem_candidates
      (mem_leadingCoefficients_of_norm_eq_one_or_two leftCoefficientNorm)
      (mem_trailingCoefficients_of_norm_le rightCoefficientBound)
  · have secondIndexOne :=
      RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second firstIndexTwo
    rcases first.coefficientSpan_or_centeredCoset next with
      integral | centered
    · rcases integral with
        ⟨leftCoefficient, rightCoefficient, identity⟩
      have indexIdentity := coefficientIndexQuadrance_eq_of_linearCombination
        previous current next leftCoefficient rightCoefficient identity
      rw [firstIndexTwo, secondIndexOne] at indexIdentity
      have twoEqualOne : (2 : Nat) = 1 :=
        Nat.eq_one_of_mul_eq_one_left indexIdentity.symm
      exact ((show (2 : Nat) ≠ 1 by decide) twoEqualOne).elim
    · let determinantValue :=
        RFAP.BestApproximation.coefficientDeterminant previous current
      change ∃ leftCoefficient rightCoefficient : GaussianInt,
        ¬ RFAP.GaussianCoset.Divides determinantValue leftCoefficient ∧
        ¬ RFAP.GaussianCoset.Divides determinantValue rightCoefficient ∧
        RFAP.BestApproximation.scalePair determinantValue next =
          RFAP.BestApproximation.linearCombination previous current
            leftCoefficient rightCoefficient at centered
      rcases centered with
        ⟨leftCoefficient, rightCoefficient, _, _, scaledIdentity⟩
      have determinantNorm : normNat determinantValue = 2 := by
        simpa only [determinantValue,
          RFAP.BestApproximation.coefficientIndexQuadrance] using firstIndexTwo
      have indexIdentity :=
        coefficientIndexQuadrance_scale_eq_of_scalePair_eq previous current
          next determinantValue leftCoefficient rightCoefficient
          scaledIdentity
      have leftCoefficientNorm : normNat leftCoefficient = 1 := by
        rw [determinantNorm, firstIndexTwo, secondIndexOne] at indexIdentity
        apply Nat.mul_right_cancel (show 0 < 2 by decide)
        simpa only [Nat.mul_one, Nat.one_mul] using indexIdentity.symm
      have rightCoefficientBound := trailingCoefficient_norm_le
        first.2.1.1 second.2.1.denominatorQuadrance_le_source
        (by rw [determinantNorm])
        (by rw [leftCoefficientNorm]; decide) scaledIdentity
      have candidateIdentity := eq_dividePairByNormTwo_of_scalePair_eq
        determinantValue next
          (RFAP.BestApproximation.linearCombination previous current
            leftCoefficient rightCoefficient)
          determinantNorm scaledIdentity
      rw [candidateIdentity]
      exact centered_mem_candidates
        (mem_leadingCoefficients_of_norm_eq_one_or_two
          (Or.inl leftCoefficientNorm))
        (mem_trailingCoefficients_of_norm_le rightCoefficientBound)

/-- Select a pair of least denominator quadrance from a finite list.  Ties
retain the earlier displayed record. -/
def selectDenominatorMinimum : List Pair → Option Pair
  | [] => none
  | candidate :: remaining =>
      match selectDenominatorMinimum remaining with
      | none => some candidate
      | some selected =>
          if RFAP.BestApproximation.denominatorQuadrance candidate ≤
              RFAP.BestApproximation.denominatorQuadrance selected then
            some candidate
          else
            some selected

theorem selectDenominatorMinimum_mem
    {list : List Pair} {selected : Pair}
    (selection : selectDenominatorMinimum list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [selectDenominatorMinimum] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectDenominatorMinimum] at selection
      cases recursive : selectDenominatorMinimum remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe :
              RFAP.BestApproximation.denominatorQuadrance candidate ≤
                RFAP.BestApproximation.denominatorQuadrance recursiveSelected
          · simp only [recursive, if_pos candidateLe] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

theorem selectDenominatorMinimum_eq_none_iff (list : List Pair) :
    selectDenominatorMinimum list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectDenominatorMinimum] at impossible
        cases recursive : selectDenominatorMinimum remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases candidateLe :
                RFAP.BestApproximation.denominatorQuadrance candidate ≤
                  RFAP.BestApproximation.denominatorQuadrance selected
            · simp only [recursive, if_pos candidateLe] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe] at impossible
              cases impossible
      · intro impossible
        cases impossible

theorem selectDenominatorMinimum_le_of_mem
    {list : List Pair} {selected candidate : Pair}
    (selection : selectDenominatorMinimum list = some selected)
    (member : candidate ∈ list) :
    RFAP.BestApproximation.denominatorQuadrance selected ≤
      RFAP.BestApproximation.denominatorQuadrance candidate := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [selectDenominatorMinimum] at selection
      cases recursive : selectDenominatorMinimum remaining with
      | none =>
          have remainingEmpty :=
            (selectDenominatorMinimum_eq_none_iff remaining).mp recursive
          subst remaining
          simp only [selectDenominatorMinimum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          simp only [List.mem_singleton] at member
          subst candidate
          exact le_rfl
      | some recursiveSelected =>
          by_cases headLe :
              RFAP.BestApproximation.denominatorQuadrance head ≤
                RFAP.BestApproximation.denominatorQuadrance recursiveSelected
          · simp only [recursive, if_pos headLe] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact le_rfl
            · exact headLe.trans
                (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact Nat.le_of_not_ge headLe
            · exact inductionHypothesis recursive remainingMember

/-- Best pairs strictly above a supplied best denominator, drawn from the
proved finite all-best list.  This list appears only in the correctness proof
of the local update, not in the executable local update itself. -/
def bestStrictlyAbove (source : Fraction) (lower : Pair) : List Pair :=
  (RFAP.BestApproximation.allBest source).filter fun pair =>
    decide (RFAP.BestApproximation.denominatorQuadrance lower <
      RFAP.BestApproximation.denominatorQuadrance pair)

theorem mem_bestStrictlyAbove_iff
    (source : Fraction) (lower pair : Pair) :
    pair ∈ bestStrictlyAbove source lower ↔
      RFAP.BestApproximation.IsBest source.value pair ∧
        RFAP.BestApproximation.denominatorQuadrance lower <
          RFAP.BestApproximation.denominatorQuadrance pair := by
  simp only [bestStrictlyAbove, List.mem_filter, decide_eq_true_eq,
    RFAP.BestApproximation.mem_allBest_iff_isBest]

/-- A displayed later best pair contains a first occupied best denominator
above `lower`.  The witness is selected from a finite list and therefore uses
neither an infinite well-ordering argument nor choice. -/
theorem exists_consecutiveBest_below
    {source : Fraction} {lower later : Pair}
    (lowerBest : RFAP.BestApproximation.IsBest source.value lower)
    (laterBest : RFAP.BestApproximation.IsBest source.value later)
    (ordered : RFAP.BestApproximation.denominatorQuadrance lower <
      RFAP.BestApproximation.denominatorQuadrance later) :
    ∃ next : Pair,
      RFAP.BestApproximation.AreConsecutiveBest source.value lower next ∧
        RFAP.BestApproximation.denominatorQuadrance next ≤
          RFAP.BestApproximation.denominatorQuadrance later := by
  let list := bestStrictlyAbove source lower
  have laterMember : later ∈ list :=
    (mem_bestStrictlyAbove_iff source lower later).mpr
      ⟨laterBest, ordered⟩
  cases selection : selectDenominatorMinimum list with
  | none =>
      have listEmpty := (selectDenominatorMinimum_eq_none_iff list).mp selection
      rw [listEmpty] at laterMember
      exact (List.not_mem_nil laterMember).elim
  | some next =>
      have nextMember := selectDenominatorMinimum_mem selection
      have nextData :=
        (mem_bestStrictlyAbove_iff source lower next).mp nextMember
      have nextNoHigher :=
        selectDenominatorMinimum_le_of_mem selection laterMember
      refine ⟨next, ⟨lowerBest, nextData.1, nextData.2, ?_⟩,
        nextNoHigher⟩
      intro middle middleBest between
      have middleMember : middle ∈ list :=
        (mem_bestStrictlyAbove_iff source lower middle).mpr
          ⟨middleBest, between.1⟩
      have nextLeMiddle :=
        selectDenominatorMinimum_le_of_mem selection middleMember
      exact (Nat.not_le_of_gt between.2) nextLeMiddle

/-- A locally improving record lies strictly above `current`, remains within
the displayed source denominator bound, and has strictly smaller error. -/
def IsLocalImprovement (source : Fraction) (current candidate : Pair) : Prop :=
  candidate.denominator ≠ 0 ∧
    RFAP.BestApproximation.denominatorQuadrance current <
      RFAP.BestApproximation.denominatorQuadrance candidate ∧
    RFAP.BestApproximation.denominatorQuadrance candidate ≤
      normNat source.denominator ∧
    RFAP.BestApproximation.errorQuadrance source.value candidate <
      RFAP.BestApproximation.errorQuadrance source.value current

instance isLocalImprovementDecidable
    (source : Fraction) (current candidate : Pair) :
    Decidable (IsLocalImprovement source current candidate) := by
  unfold IsLocalImprovement
  infer_instance

/-- One locally generated contender does not precede `reference`; on the
same denominator level it also does not improve upon `reference`. -/
def CandidateNotEarlier
    (source : Fraction) (current reference contender : Pair) : Prop :=
  IsLocalImprovement source current contender →
    RFAP.BestApproximation.denominatorQuadrance reference ≤
      RFAP.BestApproximation.denominatorQuadrance contender ∧
    (RFAP.BestApproximation.denominatorQuadrance contender =
        RFAP.BestApproximation.denominatorQuadrance reference →
      RFAP.BestApproximation.errorQuadrance source.value reference ≤
        RFAP.BestApproximation.errorQuadrance source.value contender)

instance candidateNotEarlierDecidable
    (source : Fraction) (current reference contender : Pair) :
    Decidable (CandidateNotEarlier source current reference contender) := by
  unfold CandidateNotEarlier
  infer_instance

/-- Finite conjunction of the local no-earlier-candidate comparisons. -/
def EveryCandidateNotEarlier
    (source : Fraction) (current reference : Pair) : List Pair → Prop
  | [] => True
  | contender :: remaining =>
      CandidateNotEarlier source current reference contender ∧
        EveryCandidateNotEarlier source current reference remaining

instance everyCandidateNotEarlierDecidable
    (source : Fraction) (current reference : Pair) (list : List Pair) :
    Decidable (EveryCandidateNotEarlier source current reference list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons contender remaining inductionHypothesis =>
      letI : Decidable
          (EveryCandidateNotEarlier source current reference remaining) :=
        inductionHypothesis
      change Decidable
        (CandidateNotEarlier source current reference contender ∧
          EveryCandidateNotEarlier source current reference remaining)
      infer_instance

theorem EveryCandidateNotEarlier.of_mem
    {source : Fraction} {current reference contender : Pair} {list : List Pair}
    (every : EveryCandidateNotEarlier source current reference list)
    (member : contender ∈ list) :
    CandidateNotEarlier source current reference contender := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change CandidateNotEarlier source current reference head ∧
        EveryCandidateNotEarlier source current reference remaining at every
      rcases List.mem_cons.mp member with equal | tailMember
      · subst contender
        exact every.1
      · exact inductionHypothesis every.2 tailMember

theorem everyCandidateNotEarlier_of_forall
    {source : Fraction} {current reference : Pair} {list : List Pair}
    (noneEarlier : ∀ contender ∈ list,
      CandidateNotEarlier source current reference contender) :
    EveryCandidateNotEarlier source current reference list := by
  induction list with
  | nil => trivial
  | cons contender remaining inductionHypothesis =>
      exact ⟨noneEarlier contender List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          noneEarlier candidate (List.mem_cons_of_mem _ member))⟩

/-- The wholly coefficient-local successor test.  It compares the proposed
record only with the bounded candidates generated from the adjacent state;
it does not scan the source numerator--denominator rectangle. -/
def PassesLocalSuccessorTest
    (source : Fraction) (previous current candidate : Pair) : Prop :=
  IsLocalImprovement source current candidate ∧
    EveryCandidateNotEarlier source current candidate
      (candidates source previous current)

instance passesLocalSuccessorTestDecidable
    (source : Fraction) (previous current candidate : Pair) :
    Decidable (PassesLocalSuccessorTest source previous current candidate) := by
  unfold PassesLocalSuccessorTest
  infer_instance

/-- An actual next best level passes the coefficient-local test. -/
theorem passesLocalSuccessorTest_of_consecutive
    {source : Fraction} {previous current next : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value current next) :
    PassesLocalSuccessorTest source previous current next := by
  have nextImproves : IsLocalImprovement source current next :=
    ⟨second.2.1.1, second.2.2.1,
      second.2.1.denominatorQuadrance_le_source,
      second.2.1.2.1 current first.2.1.1 second.2.2.1⟩
  refine ⟨nextImproves, ?_⟩
  apply everyCandidateNotEarlier_of_forall
  intro contender _ contenderImproves
  have cylinderEmpty :=
    (RFAP.BestApproximation.areConsecutiveBest_iff_mixedCylinderEmpty
      source current next).mp second |>.2.2.2
  have nextNoHigher :
      RFAP.BestApproximation.denominatorQuadrance next ≤
        RFAP.BestApproximation.denominatorQuadrance contender := by
    apply Nat.le_of_not_gt
    intro contenderEarlier
    exact cylinderEmpty contender (Or.inr contenderImproves.1)
      ⟨contenderImproves.2.2.2, contenderEarlier⟩
  refine ⟨nextNoHigher, ?_⟩
  intro sameHeight
  exact second.2.1.2.2 contender contenderImproves.1 sameHeight.le

/-- Bestness is invariant under replacing a displayed record by another
record at exactly the same denominator and error quadrances. -/
theorem isBest_of_same_quadrances
    {source : RFAP.ConstructiveGaussian.Gaussian} {best tied : Pair}
    (bestness : RFAP.BestApproximation.IsBest source best)
    (tiedDenominatorNonzero : tied.denominator ≠ 0)
    (sameDenominator :
      RFAP.BestApproximation.denominatorQuadrance tied =
        RFAP.BestApproximation.denominatorQuadrance best)
    (sameError : RFAP.BestApproximation.errorQuadrance source tied =
      RFAP.BestApproximation.errorQuadrance source best) :
    RFAP.BestApproximation.IsBest source tied := by
  refine ⟨tiedDenominatorNonzero, ?_, ?_⟩
  · intro competitor competitorNonzero denominatorSmaller
    rw [sameDenominator] at denominatorSmaller
    rw [sameError]
    exact bestness.2.1 competitor competitorNonzero denominatorSmaller
  · intro competitor competitorNonzero denominatorNoLarger
    rw [sameDenominator] at denominatorNoLarger
    rw [sameError]
    exact bestness.2.2 competitor competitorNonzero denominatorNoLarger

/-- Passing the coefficient-local test is sound whenever the supplied state
is one adjacent best pair. -/
theorem consecutive_of_passesLocalSuccessorTest
    {source : Fraction} {previous current candidate : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current)
    (passes : PassesLocalSuccessorTest source previous current candidate) :
    RFAP.BestApproximation.AreConsecutiveBest
      source.value current candidate := by
  obtain ⟨later, laterBest, laterNoHigher, laterErrorNoLarger⟩ :=
    RFAP.BestApproximation.exists_best_below_of_small passes.1.1
      passes.1.2.2.1
      (passes.1.2.2.2.le.trans first.2.1.errorQuadrance_le_half)
  have currentBelowLater :
      RFAP.BestApproximation.denominatorQuadrance current <
        RFAP.BestApproximation.denominatorQuadrance later := by
    apply Nat.lt_of_not_ge
    intro laterNoHigherThanCurrent
    have currentErrorNoLarger := first.2.1.2.2 later laterBest.1
      laterNoHigherThanCurrent
    exact (not_lt_of_ge (currentErrorNoLarger.trans laterErrorNoLarger))
      passes.1.2.2.2
  obtain ⟨next, second, nextNoHigher⟩ :=
    exists_consecutiveBest_below first.2.1 laterBest currentBelowLater
  have nextMember := next_mem_candidates first second
  have nextImproves : IsLocalImprovement source current next :=
    ⟨second.2.1.1, second.2.2.1,
      second.2.1.denominatorQuadrance_le_source,
      second.2.1.2.1 current first.2.1.1 second.2.2.1⟩
  have candidateNoHigher :=
    (EveryCandidateNotEarlier.of_mem passes.2 nextMember nextImproves).1
  have nextNoHigherThanCandidate :
      RFAP.BestApproximation.denominatorQuadrance next ≤
        RFAP.BestApproximation.denominatorQuadrance candidate :=
    nextNoHigher.trans laterNoHigher
  have sameDenominator :
      RFAP.BestApproximation.denominatorQuadrance candidate =
        RFAP.BestApproximation.denominatorQuadrance next :=
    Nat.le_antisymm candidateNoHigher nextNoHigherThanCandidate
  have candidateErrorNoLarger :
      RFAP.BestApproximation.errorQuadrance source.value candidate ≤
        RFAP.BestApproximation.errorQuadrance source.value next :=
    (EveryCandidateNotEarlier.of_mem passes.2 nextMember nextImproves).2
      sameDenominator.symm
  have nextErrorNoLarger :
      RFAP.BestApproximation.errorQuadrance source.value next ≤
        RFAP.BestApproximation.errorQuadrance source.value candidate :=
    second.2.1.2.2 candidate passes.1.1 sameDenominator.le
  have sameError :
      RFAP.BestApproximation.errorQuadrance source.value candidate =
        RFAP.BestApproximation.errorQuadrance source.value next :=
    le_antisymm candidateErrorNoLarger nextErrorNoLarger
  have candidateBest := isBest_of_same_quadrances second.2.1 passes.1.1
    sameDenominator sameError
  refine ⟨first.2.1, candidateBest, ?_, ?_⟩
  · rw [sameDenominator]
    exact second.2.2.1
  · intro middle middleBest between
    apply second.2.2.2 middle middleBest
    rw [sameDenominator] at between
    exact between

/-- Exact logical specification of the coefficient-local validation test,
assuming the supplied state is one adjacent best pair. -/
theorem passesLocalSuccessorTest_iff
    {source : Fraction} {previous current candidate : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current) :
    PassesLocalSuccessorTest source previous current candidate ↔
      RFAP.BestApproximation.AreConsecutiveBest
        source.value current candidate := by
  constructor
  · exact consecutive_of_passesLocalSuccessorTest first
  · exact passesLocalSuccessorTest_of_consecutive first

/-- Execute only the coefficient-local comparisons on the locally generated
candidate list. -/
def successors (source : Fraction) (previous current : Pair) : List Pair :=
  (candidates source previous current).filter fun candidate =>
    decide (PassesLocalSuccessorTest source previous current candidate)

/-- Exactness of the local successor calculation, assuming the supplied
state really is one adjacent best pair.  Both candidate generation and
validation use only the bounded coefficient list derived from that state. -/
theorem mem_successors_iff
    {source : Fraction} {previous current : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current)
    (candidate : Pair) :
    candidate ∈ successors source previous current ↔
      RFAP.BestApproximation.AreConsecutiveBest
        source.value current candidate := by
  simp only [successors, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro selected
    exact consecutive_of_passesLocalSuccessorTest first selected.2
  · intro consecutive
    exact ⟨next_mem_candidates first consecutive,
      passesLocalSuccessorTest_of_consecutive first consecutive⟩

private theorem length_flatMap_map_constant
    {Outer Inner Result : Type} (outer : List Outer) (inner : List Inner)
    (combine : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (combine left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem leadingCoefficients_length : leadingCoefficients.length = 8 := rfl

/-- The locally generated candidate list has a quadratic coefficient-space
bound.  It avoids the source numerator bound used by the global rectangle. -/
theorem candidates_length_le (source : Fraction) (previous current : Pair) :
    (candidates source previous current).length ≤
      64 * (trailingCoefficientBound source previous + 1) ^ 2 := by
  have trailingLength :
      (trailingCoefficients source previous).length =
        4 * (trailingCoefficientBound source previous + 1) ^ 2 := by
    rw [trailingCoefficients, componentSquare_length]
  have integralLength :
      (integralCandidates source previous current).length =
        leadingCoefficients.length *
          (trailingCoefficients source previous).length := by
    rw [integralCandidates, length_flatMap_map_constant]
  have centeredLength :
      (centeredCandidates source previous current).length =
        leadingCoefficients.length *
          (trailingCoefficients source previous).length := by
    rw [centeredCandidates]
    exact length_flatMap_map_constant _ _ _
  rw [candidates, List.length_append, integralLength, centeredLength,
    trailingLength]
  rw [leadingCoefficients_length]
  calc
    8 *
          (4 * (trailingCoefficientBound source previous + 1) ^ 2) +
        8 *
          (4 * (trailingCoefficientBound source previous + 1) ^ 2) =
        64 * (trailingCoefficientBound source previous + 1) ^ 2 := by
      ring1
    _ ≤ 64 * (trailingCoefficientBound source previous + 1) ^ 2 := le_rfl

end RFAP.LocalSuccessor
