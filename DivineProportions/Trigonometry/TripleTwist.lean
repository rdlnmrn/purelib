import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.TripleSpread

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Turn of an ordered pair of non-perpendicular lines. -/
def turn (first second : Line K)
    (_notPerpendicular : ¬ first.Perpendicular second) : K :=
  (first.a * second.b - second.a * first.b) /
    (first.a * second.a + first.b * second.b)

/-- The rational addition law for two successive turns.  The operation is
total as field arithmetic, while the geometric theorem below carries the
nonzero-denominator certificate needed for its intended quotient meaning. -/
def turnComposition (first second : K) : K :=
  (first + second) / (1 - first * second)

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Reversing the ordered pair of lines negates its turn. -/
theorem turn_reverse
    (first second : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondFirstNotPerpendicular : ¬ second.Perpendicular first) :
    turn second first secondFirstNotPerpendicular =
      -turn first second firstSecondNotPerpendicular := by
  have denominatorEqual :
      second.a * first.a + second.b * first.b =
        first.a * second.a + first.b * second.b := by ring1
  unfold turn
  rw [denominatorEqual]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- A twist is the square of its oriented turn. -/
theorem twist_eq_turn_square
    (first second : Line K)
    (notPerpendicular : ¬ first.Perpendicular second) :
    twist first second notPerpendicular =
      turn first second notPerpendicular ^ 2 := by
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  have dotNonzero : dot ≠ 0 := notPerpendicular
  have dotSquareNonzero : dot ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (RFAP.ExplicitField.mul_ne_zero dotNonzero dotNonzero)
  unfold twist turn
  change determinant ^ 2 / dot ^ 2 = (determinant / dot) ^ 2
  apply eq_of_mul_eq_mul_right dotSquareNonzero
  calc
    (determinant ^ 2 / dot ^ 2) * dot ^ 2 = determinant ^ 2 :=
      RFAP.ExplicitField.div_mul_cancel (determinant ^ 2) dotSquareNonzero
    _ = ((determinant / dot) * dot) ^ 2 := by
      rw [RFAP.ExplicitField.div_mul_cancel determinant dotNonzero]
    _ = (determinant / dot) ^ 2 * dot ^ 2 := by ring1

/-- Twist is symmetric although turn is antisymmetric. -/
theorem twist_symm
    (first second : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondFirstNotPerpendicular : ¬ second.Perpendicular first) :
    twist first second firstSecondNotPerpendicular =
      twist second first secondFirstNotPerpendicular := by
  unfold twist
  congr 1 <;> ring1

/-- Theorem 61 (Triple turn formula), proved here because it is the shortest
constructive route to Theorem 50. -/
theorem triple_turn_formula
    (first second third : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (thirdFirstNotPerpendicular : ¬ third.Perpendicular first) :
    let r₁ := turn second third secondThirdNotPerpendicular
    let r₂ := turn third first thirdFirstNotPerpendicular
    let r₃ := turn first second firstSecondNotPerpendicular
    r₁ + r₂ + r₃ = r₁ * r₂ * r₃ := by
  dsimp only
  let firstNumerator := second.a * third.b - third.a * second.b
  let secondNumerator := third.a * first.b - first.a * third.b
  let thirdNumerator := first.a * second.b - second.a * first.b
  let firstDenominator := second.a * third.a + second.b * third.b
  let secondDenominator := third.a * first.a + third.b * first.b
  let thirdDenominator := first.a * second.a + first.b * second.b
  let denominator := firstDenominator * secondDenominator * thirdDenominator
  have firstDenominatorNonzero : firstDenominator ≠ 0 :=
    secondThirdNotPerpendicular
  have secondDenominatorNonzero : secondDenominator ≠ 0 :=
    thirdFirstNotPerpendicular
  have thirdDenominatorNonzero : thirdDenominator ≠ 0 :=
    firstSecondNotPerpendicular
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstDenominatorNonzero
        secondDenominatorNonzero)
      thirdDenominatorNonzero
  have firstCancel :
      (firstNumerator / firstDenominator) * firstDenominator =
        firstNumerator :=
    RFAP.ExplicitField.div_mul_cancel firstNumerator firstDenominatorNonzero
  have secondCancel :
      (secondNumerator / secondDenominator) * secondDenominator =
        secondNumerator :=
    RFAP.ExplicitField.div_mul_cancel secondNumerator secondDenominatorNonzero
  have thirdCancel :
      (thirdNumerator / thirdDenominator) * thirdDenominator =
        thirdNumerator :=
    RFAP.ExplicitField.div_mul_cancel thirdNumerator thirdDenominatorNonzero
  have numeratorIdentity :
      firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator =
        firstNumerator * secondNumerator * thirdNumerator := by
    unfold firstNumerator secondNumerator thirdNumerator
    unfold firstDenominator secondDenominator thirdDenominator
    ring1
  unfold turn
  change
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      (firstNumerator / firstDenominator) *
        (secondNumerator / secondDenominator) *
        (thirdNumerator / thirdDenominator)
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator) * denominator =
      ((firstNumerator / firstDenominator) * firstDenominator) *
          secondDenominator * thirdDenominator +
        ((secondNumerator / secondDenominator) * secondDenominator) *
          firstDenominator * thirdDenominator +
        ((thirdNumerator / thirdDenominator) * thirdDenominator) *
          firstDenominator * secondDenominator := by
            unfold denominator
            ring1
    _ = firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator := by
      rw [firstCancel, secondCancel, thirdCancel]
    _ = firstNumerator * secondNumerator * thirdNumerator := numeratorIdentity
    _ =
        ((firstNumerator / firstDenominator) *
            (secondNumerator / secondDenominator) *
            (thirdNumerator / thirdDenominator)) * denominator := by
      unfold denominator
      calc
        firstNumerator * secondNumerator * thirdNumerator =
            ((firstNumerator / firstDenominator) * firstDenominator) *
              ((secondNumerator / secondDenominator) * secondDenominator) *
              ((thirdNumerator / thirdDenominator) * thirdDenominator) := by
                rw [firstCancel, secondCancel, thirdCancel]
        _ =
            ((firstNumerator / firstDenominator) *
                (secondNumerator / secondDenominator) *
                (thirdNumerator / thirdDenominator)) *
              (firstDenominator * secondDenominator * thirdDenominator) := by
                ring1

/-- Exercise 9.2: two successive finite turns compose by the rational
addition law.  The displayed premise records the source's tacit exceptional
case `1-u*v = 0`; over fields admitting null directions it does not follow
merely from the three pairwise turns being defined. -/
theorem exercise_9_2
    (first second third : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (compositionDenominatorNonzero :
      1 - turn first second firstSecondNotPerpendicular *
        turn second third secondThirdNotPerpendicular ≠ 0) :
    turn first third firstThirdNotPerpendicular =
      turnComposition
        (turn first second firstSecondNotPerpendicular)
        (turn second third secondThirdNotPerpendicular) := by
  have thirdFirstNotPerpendicular : ¬ third.Perpendicular first := by
    intro perpendicular
    exact firstThirdNotPerpendicular (Line.perpendicular_symm perpendicular)
  let u := turn first second firstSecondNotPerpendicular
  let v := turn second third secondThirdNotPerpendicular
  let w := turn first third firstThirdNotPerpendicular
  have reverseTurn :
      turn third first thirdFirstNotPerpendicular = -w := by
    exact turn_reverse first third firstThirdNotPerpendicular
      thirdFirstNotPerpendicular
  have cyclicEquation :=
    triple_turn_formula first second third firstSecondNotPerpendicular
      secondThirdNotPerpendicular thirdFirstNotPerpendicular
  change v + turn third first thirdFirstNotPerpendicular + u =
      v * turn third first thirdFirstNotPerpendicular * u at cyclicEquation
  rw [reverseTurn] at cyclicEquation
  change 1 - u * v ≠ 0 at compositionDenominatorNonzero
  have clearedComposition : w * (1 - u * v) = u + v := by
    have differenceZero : w * (1 - u * v) - (u + v) = 0 := by
      calc
        w * (1 - u * v) - (u + v) =
            -((v + -w + u) - v * (-w) * u) := by ring1
        _ = 0 := by rw [cyclicEquation]; ring1
    exact sub_eq_zero.mp differenceZero
  change w = turnComposition u v
  unfold turnComposition
  apply eq_of_mul_eq_mul_right compositionDenominatorNonzero
  calc
    w * (1 - u * v) = u + v := clearedComposition
    _ = ((u + v) / (1 - u * v)) * (1 - u * v) :=
      (RFAP.ExplicitField.div_mul_cancel (u + v)
        compositionDenominatorNonzero).symm

/-- Exercise 9.2's equal-successive-turn specialization. -/
theorem exercise_9_2_equal_turns
    (first second third : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (turnsEqual :
      turn first second firstSecondNotPerpendicular =
        turn second third secondThirdNotPerpendicular)
    (compositionDenominatorNonzero :
      1 - turn first second firstSecondNotPerpendicular *
        turn second third secondThirdNotPerpendicular ≠ 0) :
    turn first third firstThirdNotPerpendicular =
      (2 * turn first second firstSecondNotPerpendicular) /
        (1 - turn first second firstSecondNotPerpendicular ^ 2) := by
  calc
    turn first third firstThirdNotPerpendicular =
        turnComposition
          (turn first second firstSecondNotPerpendicular)
          (turn second third secondThirdNotPerpendicular) :=
      exercise_9_2 first second third firstSecondNotPerpendicular
        secondThirdNotPerpendicular firstThirdNotPerpendicular
        compositionDenominatorNonzero
    _ = (2 * turn first second firstSecondNotPerpendicular) /
        (1 - turn first second firstSecondNotPerpendicular ^ 2) := by
      rw [← turnsEqual]
      unfold turnComposition
      congr 1 <;> ring1

/-- Exercise 7.12: squaring any triple-turn relation gives a triple-twist
relation. -/
theorem exercise_7_12
    (r₁ r₂ r₃ : K) (turnEquation : r₁ + r₂ + r₃ = r₁ * r₂ * r₃) :
    let t₁ := r₁ ^ 2
    let t₂ := r₂ ^ 2
    let t₃ := r₃ ^ 2
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ + 2 * t₁ * t₂ * t₃) := by
  dsimp only
  have turnDifference : r₁ + r₂ + r₃ - r₁ * r₂ * r₃ = 0 := by
    rw [turnEquation]
    ring1
  have differenceZero :
      (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 -
            r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) ^ 2 -
          4 * (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 +
            r₂ ^ 2 * r₃ ^ 2 + 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) = 0 := by
    calc
      (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 -
              r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) ^ 2 -
            4 * (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 +
              r₂ ^ 2 * r₃ ^ 2 + 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) =
        -(r₁ + r₂ + r₃ - r₁ * r₂ * r₃) *
          (r₁ + r₂ - r₃ + r₁ * r₂ * r₃) *
          (r₁ - r₂ + r₃ + r₁ * r₂ * r₃) *
          (-r₁ + r₂ + r₃ + r₁ * r₂ * r₃) := by ring1
      _ = 0 := by rw [turnDifference]; ring1
  exact sub_eq_zero.mp differenceZero

/-- Theorem 50 (Triple twist formula), valid uniformly for null and non-null
lines whenever the three displayed turns are defined. -/
theorem triple_twist_formula
    (first second third : Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third) :
    let t₁ := twist second third secondThirdNotPerpendicular
    let t₂ := twist first third firstThirdNotPerpendicular
    let t₃ := twist first second firstSecondNotPerpendicular
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ + 2 * t₁ * t₂ * t₃) := by
  dsimp only
  have thirdFirstNotPerpendicular : ¬ third.Perpendicular first := by
    intro perpendicular
    exact firstThirdNotPerpendicular (Line.perpendicular_symm perpendicular)
  let r₁ := turn second third secondThirdNotPerpendicular
  let r₂ := turn third first thirdFirstNotPerpendicular
  let r₃ := turn first second firstSecondNotPerpendicular
  have turnEquation : r₁ + r₂ + r₃ = r₁ * r₂ * r₃ :=
    triple_turn_formula first second third firstSecondNotPerpendicular
      secondThirdNotPerpendicular thirdFirstNotPerpendicular
  have twistOne :
      twist second third secondThirdNotPerpendicular = r₁ ^ 2 :=
    twist_eq_turn_square second third secondThirdNotPerpendicular
  have twistTwo :
      twist first third firstThirdNotPerpendicular = r₂ ^ 2 := by
    calc
      twist first third firstThirdNotPerpendicular =
          twist third first thirdFirstNotPerpendicular :=
        twist_symm first third firstThirdNotPerpendicular
          thirdFirstNotPerpendicular
      _ = r₂ ^ 2 := twist_eq_turn_square third first
        thirdFirstNotPerpendicular
  have twistThree :
      twist first second firstSecondNotPerpendicular = r₃ ^ 2 :=
    twist_eq_turn_square first second firstSecondNotPerpendicular
  rw [twistOne, twistTwo, twistThree]
  exact exercise_7_12 r₁ r₂ r₃ turnEquation

/-- Exercise 7.10: the Triple twist relation as a quadratic in `t₃`,
followed by its denominator-free completed-square normal form. -/
theorem exercise_7_10
    (t₁ t₂ t₃ : K)
    (tripleTwist :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃)) :
    (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2 = 0 ∧
      (((1 - t₁ * t₂) ^ 2 * t₃ -
          ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂)) ^ 2 =
        4 * t₁ * t₂ *
          ((1 + t₁) * (1 + t₂)) ^ 2) := by
  have twistDifference :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
          4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
            2 * t₁ * t₂ * t₃) = 0 := by
    rw [tripleTwist]
    ring1
  have quadraticZero :
      (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2 = 0 := by
    calc
      (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
            2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
              4 * t₁ * t₂) * t₃ +
            (t₁ - t₂) ^ 2 =
        (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
          4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
            2 * t₁ * t₂ * t₃) := by ring1
      _ = 0 := twistDifference
  refine ⟨quadraticZero, ?_⟩
  apply sub_eq_zero.mp
  calc
    ((1 - t₁ * t₂) ^ 2 * t₃ -
          ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂)) ^ 2 -
        4 * t₁ * t₂ *
          ((1 + t₁) * (1 + t₂)) ^ 2 =
      (1 - t₁ * t₂) ^ 2 *
        ((1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2) := by ring1
    _ = 0 := by rw [quadraticZero]; ring1

/-- Exercise 7.11: the symmetric-looking alternative form of the Triple
twist relation. -/
theorem exercise_7_11
    (t₁ t₂ t₃ : K)
    (tripleTwist :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃)) :
    (t₁ + t₂ - t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * t₁ * t₂ * (1 + t₃) ^ 2 := by
  apply sub_eq_zero.mp
  calc
    (t₁ + t₂ - t₃ - t₁ * t₂ * t₃) ^ 2 -
        4 * t₁ * t₂ * (1 + t₃) ^ 2 =
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃) := by ring1
    _ = 0 := by rw [tripleTwist]; ring1

end DivineProportions
