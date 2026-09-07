import DivineProportions.Plane.AltitudeFoot

/-!
# Divine Proportions, Exercises 3.3–3.10

These line relations and coordinate formulas use only the three displayed
coefficients of each line.  Parallel directions are related by an explicit
nonzero scale; no slope quotient or projective representative is selected.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Exercise 3.4: a line parallel to `first` is parallel to every parallel
representative of `first`, and a line perpendicular to `first` is
perpendicular to every such representative. -/
theorem exercise_3_4 [DecidableEq K]
    (first second third : Line K) (firstSecond : first.Parallel second) :
    (third.Parallel first → third.Parallel second) ∧
      (third.Perpendicular first → third.Perpendicular second) := by
  constructor
  · intro thirdFirst
    exact line_parallel_trans thirdFirst firstSecond
  · intro thirdFirst
    rcases direction_scale_of_parallel first second firstSecond with
      ⟨scale, _scaleNonzero, secondA, secondB⟩
    unfold Line.Perpendicular at thirdFirst ⊢
    rw [secondA, secondB]
    calc
      third.a * (scale * first.a) + third.b * (scale * first.b) =
          scale * (third.a * first.a + third.b * first.b) := by ring1
      _ = 0 := by rw [thirdFirst]; ring1

/-- Exercise 3.5: two lines perpendicular to the same displayed line are
parallel. -/
theorem exercise_3_5
    (first second third : Line K)
    (firstSecond : first.Perpendicular second)
    (secondThird : second.Perpendicular third) :
    first.Parallel third := by
  let origin : Point K := ⟨0, 0⟩
  let commonAltitude := altitudeThrough origin second
  have firstAltitude : first.Parallel commonAltitude := by
    unfold Line.Parallel commonAltitude altitudeThrough
    unfold Line.Perpendicular at firstSecond
    calc
      first.a * second.a - -second.b * first.b =
          first.a * second.a + first.b * second.b := by ring1
      _ = 0 := firstSecond
  have altitudeThird : commonAltitude.Parallel third := by
    unfold Line.Parallel commonAltitude altitudeThrough
    unfold Line.Perpendicular at secondThird
    calc
      -second.b * third.b - third.a * second.a =
          -(second.a * third.a + second.b * third.b) := by ring1
      _ = 0 := by rw [secondThird]; ring1
  exact line_parallel_trans firstAltitude altitudeThird

/-- A null line of the source's first displayed family `⟨1:i:d⟩`. -/
def positiveNullLine [Nontrivial K] (root offset : K) : Line K where
  a := 1
  b := root
  c := offset
  direction_nonzero := Or.inl one_ne_zero

/-- A null line of the source's second displayed family `⟨1:-i:d⟩`. -/
def negativeNullLine [Nontrivial K] (root offset : K) : Line K where
  a := 1
  b := -root
  c := offset
  direction_nonzero := Or.inl one_ne_zero

/-- The first displayed null direction through a requested point. -/
def positiveNullLineThrough [Nontrivial K]
    (root : K) (point : Point K) : Line K :=
  positiveNullLine root (-point.x - root * point.y)

/-- The second displayed null direction through a requested point. -/
def negativeNullLineThrough [Nontrivial K]
    (root : K) (point : Point K) : Line K :=
  negativeNullLine root (-point.x + root * point.y)

private theorem nullLine_first_coefficient_nonzero
    [DecidableEq K] (line : Line K) (nullLine : line.IsNull) :
    line.a ≠ 0 := by
  intro firstZero
  rcases line.direction_nonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · have secondSquareZero : line.b ^ 2 = 0 := by
      unfold Line.IsNull at nullLine
      calc
        line.b ^ 2 = line.a ^ 2 + line.b ^ 2 := by
          rw [firstZero]
          ring1
        _ = 0 := nullLine
    have secondProductZero : line.b * line.b = 0 := by
      calc
        line.b * line.b = line.b ^ 2 := by ring1
        _ = 0 := secondSquareZero
    exact (RFAP.ExplicitField.mul_ne_zero secondNonzero secondNonzero)
      secondProductZero

/-- Any displayed null line constructively supplies a square root of `-1`.
The witness is its second direction coefficient divided by its first. -/
theorem squareRootNegativeOne_of_nullLine [DecidableEq K]
    (line : Line K) (nullLine : line.IsNull) :
    ∃ root : K, root ^ 2 = -1 := by
  have firstNonzero := nullLine_first_coefficient_nonzero line nullLine
  have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel line.a firstNonzero
  have secondSquare : line.b ^ 2 = -(line.a ^ 2) := by
    unfold Line.IsNull at nullLine
    calc
      line.b ^ 2 =
          -(line.a ^ 2) + (line.a ^ 2 + line.b ^ 2) := by ring1
      _ = -(line.a ^ 2) := by rw [nullLine]; ring1
  refine ⟨line.b / line.a, ?_⟩
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (line.b * line.a⁻¹) ^ 2 =
        line.b ^ 2 * (line.a⁻¹) ^ 2 := by ring1
    _ = -(line.a ^ 2) * (line.a⁻¹) ^ 2 := by rw [secondSquare]
    _ = -(line.a * line.a⁻¹) ^ 2 := by ring1
    _ = -1 := by rw [firstCancel]; ring1

private theorem root_ne_zero_of_square_eq_negative_one [Nontrivial K]
    (root : K) (rootSquare : root ^ 2 = -1) : root ≠ 0 := by
  intro rootZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = -(-1) := by ring1
    _ = -(root ^ 2) := by rw [rootSquare]
    _ = 0 := by rw [rootZero]; ring1

/-- Every null line through `point` has one of the two displayed null
directions.  Equality is the project's quotient-free `Line.Equivalent`
relation on coefficient triples. -/
theorem nullLine_through_equivalent_positive_or_negative
    [Nontrivial K] [DecidableEq K]
    (root : K) (rootSquare : root ^ 2 = -1)
    (point : Point K) (line : Line K)
    (contains : line.Contains point) (nullLine : line.IsNull) :
    line.Equivalent (positiveNullLineThrough root point) ∨
      line.Equivalent (negativeNullLineThrough root point) := by
  have factorZero :
      (line.b - root * line.a) * (line.b + root * line.a) = 0 := by
    unfold Line.IsNull at nullLine
    calc
      (line.b - root * line.a) * (line.b + root * line.a) =
          line.b ^ 2 - root ^ 2 * line.a ^ 2 := by ring1
      _ = line.b ^ 2 + line.a ^ 2 := by rw [rootSquare]; ring1
      _ = line.a ^ 2 + line.b ^ 2 := by ring1
      _ = 0 := nullLine
  by_cases positiveFactorZero : line.b - root * line.a = 0
  · have secondCoefficient : line.b = root * line.a := by
      calc
        line.b = (line.b - root * line.a) + root * line.a := by ring1
        _ = root * line.a := by rw [positiveFactorZero]; ring1
    have constantCoefficient :
        line.c = line.a * (-point.x - root * point.y) := by
      unfold Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
        _ = line.a * (-point.x - root * point.y) := by
          rw [secondCoefficient]
          ring1
    left
    unfold Line.Equivalent positiveNullLineThrough positiveNullLine
    exact ⟨by rw [secondCoefficient]; ring1,
      by rw [constantCoefficient]; ring1,
      by rw [secondCoefficient, constantCoefficient]; ring1⟩
  · have negativeFactorZero : line.b + root * line.a = 0 := by
      by_cases negativeZero : line.b + root * line.a = 0
      · exact negativeZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero positiveFactorZero negativeZero)
            factorZero)
    have secondCoefficient : line.b = -root * line.a := by
      calc
        line.b = (line.b + root * line.a) - root * line.a := by ring1
        _ = -root * line.a := by rw [negativeFactorZero]; ring1
    have constantCoefficient :
        line.c = line.a * (-point.x + root * point.y) := by
      unfold Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
        _ = line.a * (-point.x + root * point.y) := by
          rw [secondCoefficient]
          ring1
    right
    unfold Line.Equivalent negativeNullLineThrough negativeNullLine
    exact ⟨by rw [secondCoefficient]; ring1,
      by rw [constantCoefficient]; ring1,
      by rw [secondCoefficient, constantCoefficient]; ring1⟩

/-- When `2 ≠ 0`, the two displayed null directions are inequivalent. -/
theorem positiveNullLineThrough_not_equivalent_negative
    [Nontrivial K]
    (root : K) (rootSquare : root ^ 2 = -1)
    (point : Point K) (twoNonzero : (2 : K) ≠ 0) :
    ¬ (positiveNullLineThrough root point).Equivalent
        (negativeNullLineThrough root point) := by
  intro equivalent
  have negativeRootEqualsRoot : -root = root := by
    calc
      -root = (1 : K) * -root := by ring1
      _ = 1 * root := equivalent.1
      _ = root := by ring1
  have twiceRootZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root - (-root) := by ring1
      _ = 0 := by rw [negativeRootEqualsRoot]; ring1
  exact (RFAP.ExplicitField.mul_ne_zero twoNonzero
    (root_ne_zero_of_square_eq_negative_one root rootSquare)) twiceRootZero

/-- Exercise 3.3: from the existence of one null line, construct exactly two
inequivalent null lines through any requested point and classify every other
null line through that point into one of those two directions. -/
theorem exercise_3_3 [Nontrivial K] [DecidableEq K]
    (point : Point K) (witness : Line K)
    (witnessNull : witness.IsNull) (twoNonzero : (2 : K) ≠ 0) :
    ∃ positive negative : Line K,
      positive.Contains point ∧ positive.IsNull ∧
        negative.Contains point ∧ negative.IsNull ∧
        ¬ positive.Equivalent negative ∧
        ∀ line : Line K,
          line.Contains point → line.IsNull →
            line.Equivalent positive ∨ line.Equivalent negative := by
  rcases squareRootNegativeOne_of_nullLine witness witnessNull with
    ⟨root, rootSquare⟩
  let positive := positiveNullLineThrough root point
  let negative := negativeNullLineThrough root point
  refine ⟨positive, negative, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold positive positiveNullLineThrough positiveNullLine Line.Contains
    ring1
  · unfold positive positiveNullLineThrough positiveNullLine Line.IsNull
    rw [rootSquare]
    ring1
  · unfold negative negativeNullLineThrough negativeNullLine Line.Contains
    ring1
  · unfold negative negativeNullLineThrough negativeNullLine Line.IsNull
    rw [show (-root) ^ 2 = root ^ 2 by ring1, rootSquare]
    ring1
  · unfold positive negative
    exact positiveNullLineThrough_not_equivalent_negative root rootSquare
      point twoNonzero
  · intro line contains nullLine
    unfold positive negative
    exact nullLine_through_equivalent_positive_or_negative
      root rootSquare point line contains nullLine

/-- Exercise 3.6: within either displayed null family, every pair of lines is
both parallel and perpendicular. -/
theorem exercise_3_6 [Nontrivial K]
    (root firstOffset secondOffset : K)
    (rootSquare : root ^ 2 = -1) :
    (positiveNullLine root firstOffset).IsNull ∧
      (positiveNullLine root secondOffset).IsNull ∧
      (positiveNullLine root firstOffset).Parallel
        (positiveNullLine root secondOffset) ∧
      (positiveNullLine root firstOffset).Perpendicular
        (positiveNullLine root secondOffset) ∧
      (negativeNullLine root firstOffset).IsNull ∧
      (negativeNullLine root secondOffset).IsNull ∧
      (negativeNullLine root firstOffset).Parallel
        (negativeNullLine root secondOffset) ∧
      (negativeNullLine root firstOffset).Perpendicular
        (negativeNullLine root secondOffset) := by
  have positiveNullIdentity : (1 : K) ^ 2 + root ^ 2 = 0 := by
    rw [rootSquare]
    ring1
  have negativeNullIdentity : (1 : K) ^ 2 + (-root) ^ 2 = 0 := by
    rw [show (-root) ^ 2 = root ^ 2 by ring1, rootSquare]
    ring1
  constructor
  · exact positiveNullIdentity
  constructor
  · exact positiveNullIdentity
  constructor
  · unfold Line.Parallel positiveNullLine
    ring1
  constructor
  · unfold Line.Perpendicular positiveNullLine
    calc
      (1 : K) * 1 + root * root = 1 ^ 2 + root ^ 2 := by ring1
      _ = 0 := positiveNullIdentity
  constructor
  · exact negativeNullIdentity
  constructor
  · exact negativeNullIdentity
  constructor
  · unfold Line.Parallel negativeNullLine
    ring1
  · unfold Line.Perpendicular negativeNullLine
    calc
      (1 : K) * 1 + -root * -root = 1 ^ 2 + (-root) ^ 2 := by ring1
      _ = 0 := negativeNullIdentity

/-- Exercise 3.7: lines that are simultaneously parallel and perpendicular
are both null. -/
theorem exercise_3_7 [DecidableEq K]
    (first second : Line K) (parallel : first.Parallel second)
    (perpendicular : first.Perpendicular second) :
    first.IsNull ∧ second.IsNull := by
  rcases direction_scale_of_parallel first second parallel with
    ⟨scale, scaleNonzero, secondA, secondB⟩
  have scaledFirstNorm : scale * (first.a ^ 2 + first.b ^ 2) = 0 := by
    unfold Line.Perpendicular at perpendicular
    rw [secondA, secondB] at perpendicular
    calc
      scale * (first.a ^ 2 + first.b ^ 2) =
          first.a * (scale * first.a) +
            first.b * (scale * first.b) := by ring1
      _ = 0 := perpendicular
  have firstNull : first.IsNull := by
    unfold Line.IsNull
    by_cases normZero : first.a ^ 2 + first.b ^ 2 = 0
    · exact normZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero scaleNonzero normZero)
          scaledFirstNorm)
  constructor
  · exact firstNull
  · unfold Line.IsNull at firstNull ⊢
    rw [secondA, secondB]
    calc
      (scale * first.a) ^ 2 + (scale * first.b) ^ 2 =
          scale ^ 2 * (first.a ^ 2 + first.b ^ 2) := by ring1
      _ = 0 := by rw [firstNull]; ring1

/-- Exercise 3.8: the printed coefficients of the parallel through `point` to
the line through `first` and `second`. -/
theorem exercise_3_8 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second) :
    let parallel := parallelThrough point (lineThrough first second distinct)
    parallel.a = first.y - second.y ∧
      parallel.b = second.x - first.x ∧
      parallel.c =
        (second.y - first.y) * point.x +
          (first.x - second.x) * point.y := by
  dsimp only [parallelThrough, lineThrough]
  exact ⟨rfl, rfl, by ring1⟩

/-- Exercise 3.9: the printed coefficients of the altitude through `point` to
the line through `first` and `second`. -/
theorem exercise_3_9 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second) :
    let altitude := altitudeThrough point (lineThrough first second distinct)
    altitude.a = first.x - second.x ∧
      altitude.b = first.y - second.y ∧
      altitude.c =
        (second.x - first.x) * point.x +
          (second.y - first.y) * point.y := by
  dsimp only [altitudeThrough, lineThrough]
  exact ⟨by ring1, rfl, by ring1⟩

/-- Exercise 3.10: the printed altitude-foot coordinates for the non-null line
through two distinct points. -/
theorem exercise_3_10 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (lineThrough first second distinct).IsNull) :
    altitudeFoot point (lineThrough first second distinct) nonNull =
      { x :=
          ((second.x - first.x) ^ 2 * point.x -
            (first.y - second.y) * (second.x - first.x) * point.y -
            (first.y - second.y) *
              (first.x * second.y - second.x * first.y)) /
            ((second.x - first.x) ^ 2 + (first.y - second.y) ^ 2)
        y :=
          ((first.y - second.y) ^ 2 * point.y -
            (first.y - second.y) * (second.x - first.x) * point.x -
            (second.x - first.x) *
              (first.x * second.y - second.x * first.y)) /
            ((second.x - first.x) ^ 2 + (first.y - second.y) ^ 2) } := by
  apply Point.ext
  · change
      (((second.x - first.x) ^ 2 * point.x -
        (first.y - second.y) * (second.x - first.x) * point.y -
        (first.y - second.y) *
          (first.x * second.y - second.x * first.y)) /
        ((first.y - second.y) ^ 2 + (second.x - first.x) ^ 2)) = _
    rw [show
      (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
        (second.x - first.x) ^ 2 + (first.y - second.y) ^ 2 by ring1]
  · change
      ((-(first.y - second.y) * (second.x - first.x) * point.x +
        (first.y - second.y) ^ 2 * point.y -
        (second.x - first.x) *
          (first.x * second.y - second.x * first.y)) /
        ((first.y - second.y) ^ 2 + (second.x - first.x) ^ 2)) = _
    rw [show
      -(first.y - second.y) * (second.x - first.x) * point.x +
          (first.y - second.y) ^ 2 * point.y -
          (second.x - first.x) *
            (first.x * second.y - second.x * first.y) =
        (first.y - second.y) ^ 2 * point.y -
          (first.y - second.y) * (second.x - first.x) * point.x -
          (second.x - first.x) *
            (first.x * second.y - second.x * first.y) by ring1,
      show
        (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
          (second.x - first.x) ^ 2 + (first.y - second.y) ^ 2 by ring1]

end DivineProportions
