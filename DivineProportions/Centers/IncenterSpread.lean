import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.Incenter

/-!
# Divine Proportions, §12.5: the incenter spread theorem

This module formalizes the source's translated-coordinate proof.  The
incenter is the origin; `firstMirror` and `secondMirror` are the first two
vertex bisectors, and `target` is the side joining their triangle vertices.
Reflecting `target` in those mirrors gives the other two sides.  The displayed
third line joins the origin to their intersection.

The key computation is denominator-free: the third line's spread with the
first reflected side equals the cross of the two initial mirrors.  Fibonacci's
spread-plus-cross identity then gives the printed complementary spread.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- First direction coefficient of the line from the origin to the
intersection of the two reflected sides. -/
def incenterThirdDirectionA
    (firstMirror secondMirror target : Line K) : K :=
  lineNorm secondMirror * reflectedLineA firstMirror target -
    lineNorm firstMirror * reflectedLineA secondMirror target

/-- Second direction coefficient of the same line. -/
def incenterThirdDirectionB
    (firstMirror secondMirror target : Line K) : K :=
  lineNorm secondMirror * reflectedLineB firstMirror target -
    lineNorm firstMirror * reflectedLineB secondMirror target

/-- The polynomial norm identity ensuring that the displayed third direction
is nonzero. -/
theorem incenterThirdDirection_norm
    (firstMirror secondMirror target : Line K) :
    incenterThirdDirectionA firstMirror secondMirror target ^ 2 +
        incenterThirdDirectionB firstMirror secondMirror target ^ 2 =
      4 * lineNorm firstMirror * lineNorm secondMirror *
        (firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b) ^ 2 * lineNorm target := by
  unfold incenterThirdDirectionA incenterThirdDirectionB reflectedLineA
    reflectedLineB lineNorm
  ring1

private theorem square_ne_zero {value : K} (nonzero : value ≠ 0) :
    value ^ 2 ≠ 0 := by
  simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero nonzero nonzero

/-- The third line used in the normalized proof of Theorem 89. -/
def normalizedIncenterThirdLine [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := incenterThirdDirectionA firstMirror secondMirror target
  b := incenterThirdDirectionB firstMirror secondMirror target
  c := 0
  direction_nonzero := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    have fourNonzero : (4 : K) ≠ 0 := by
      rw [fourAsProduct]
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    have mirrorDeterminantNonzero :
        firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b ≠ 0 := mirrorsNonparallel
    have normNonzero :
        4 * lineNorm firstMirror * lineNorm secondMirror *
          (firstMirror.a * secondMirror.b -
            secondMirror.a * firstMirror.b) ^ 2 * lineNorm target ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero
            (RFAP.ExplicitField.mul_ne_zero fourNonzero firstMirrorNonNull)
            secondMirrorNonNull)
          (square_ne_zero mirrorDeterminantNonzero))
        targetNonNull
    by_cases firstNonzero :
        incenterThirdDirectionA firstMirror secondMirror target ≠ 0
    · exact Or.inl firstNonzero
    · right
      intro secondZero
      apply normNonzero
      rw [← incenterThirdDirection_norm firstMirror secondMirror target]
      have firstZero :
          incenterThirdDirectionA firstMirror secondMirror target = 0 := by
        by_cases equality :
            incenterThirdDirectionA firstMirror secondMirror target = 0
        · exact equality
        · exact False.elim (firstNonzero equality)
      rw [firstZero, secondZero]
      ring1

/-- The displayed third line is non-null. -/
theorem normalizedIncenterThirdLine_nonNull [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero).IsNull := by
  intro nullThird
  have mirrorDeterminantNonzero :
      firstMirror.a * secondMirror.b -
        secondMirror.a * firstMirror.b ≠ 0 := mirrorsNonparallel
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have rightNonzero :
      4 * lineNorm firstMirror * lineNorm secondMirror *
        (firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b) ^ 2 * lineNorm target ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero fourNonzero firstMirrorNonNull)
          secondMirrorNonNull)
        (square_ne_zero mirrorDeterminantNonzero))
      targetNonNull
  apply rightNonzero
  rw [← incenterThirdDirection_norm firstMirror secondMirror target]
  exact nullThird

/-- The third-line spread computed in the source is the cross of the two
initial bisectors. -/
theorem normalized_incenter_third_spread_eq_cross
    [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero
    let reflectedSideNonNull := reflectLine_nonNull firstMirror target
      firstMirrorNonNull targetNonNull
    spread thirdLine (reflectLine firstMirror target firstMirrorNonNull)
        thirdLineNonNull reflectedSideNonNull =
      cross firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull := by
  dsimp only
  let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
    firstMirrorNonNull secondMirrorNonNull targetNonNull mirrorsNonparallel
    twoNonzero
  let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
    firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
    targetNonNull mirrorsNonparallel twoNonzero
  let reflectedSide := reflectLine firstMirror target firstMirrorNonNull
  let reflectedSideNonNull := reflectLine_nonNull firstMirror target
    firstMirrorNonNull targetNonNull
  have leftDenominatorNonzero :
      lineNorm thirdLine * lineNorm reflectedSide ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero thirdLineNonNull reflectedSideNonNull
  have rightDenominatorNonzero :
      lineNorm firstMirror * lineNorm secondMirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstMirrorNonNull secondMirrorNonNull
  unfold spread cross
  apply ratio_eq_of_cross_product leftDenominatorNonzero
    rightDenominatorNonzero
  unfold thirdLine reflectedSide normalizedIncenterThirdLine
    incenterThirdDirectionA incenterThirdDirectionB reflectLine
    reflectedLineA reflectedLineB lineNorm
  ring1

/-- The third line passes through the translated incenter `[0,0]`. -/
theorem normalizedIncenterThirdLine_contains_origin [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero).Contains (⟨0, 0⟩ : Point K) := by
  unfold normalizedIncenterThirdLine Line.Contains
  ring1

/-- When the reflected sides meet, the displayed third line also contains
their intersection. -/
theorem normalizedIncenterThirdLine_contains_reflected_intersection
    [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0)
    (firstMirrorThroughOrigin : firstMirror.c = 0)
    (secondMirrorThroughOrigin : secondMirror.c = 0)
    (reflectedSidesNonparallel :
      ¬ (reflectLine firstMirror target firstMirrorNonNull).Parallel
        (reflectLine secondMirror target secondMirrorNonNull)) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    thirdLine.Contains
      (lineIntersection
        (reflectLine firstMirror target firstMirrorNonNull)
        (reflectLine secondMirror target secondMirrorNonNull)
        reflectedSidesNonparallel) := by
  dsimp only
  apply lineIntersection_on_third_of_determinant_eq_zero
    (reflectLine firstMirror target firstMirrorNonNull)
    (reflectLine secondMirror target secondMirrorNonNull)
    (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero)
    reflectedSidesNonparallel
  unfold lineDeterminant normalizedIncenterThirdLine
    incenterThirdDirectionA incenterThirdDirectionB reflectLine
    reflectedLineA reflectedLineB reflectedLineC lineNorm
  rw [firstMirrorThroughOrigin, secondMirrorThroughOrigin]
  ring1

/-- Theorem 89 (Incenter spread), in the translated coordinates used by the
book's proof.  The first two conjuncts certify that `thirdLine` is exactly the
line from the incenter to the third vertex. -/
theorem incenter_spread
    [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0)
    (firstMirrorThroughOrigin : firstMirror.c = 0)
    (secondMirrorThroughOrigin : secondMirror.c = 0)
    (reflectedSidesNonparallel :
      ¬ (reflectLine firstMirror target firstMirrorNonNull).Parallel
        (reflectLine secondMirror target secondMirrorNonNull)) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero
    let reflectedSideNonNull := reflectLine_nonNull firstMirror target
      firstMirrorNonNull targetNonNull
    thirdLine.Contains (⟨0, 0⟩ : Point K) ∧
      thirdLine.Contains
        (lineIntersection
          (reflectLine firstMirror target firstMirrorNonNull)
          (reflectLine secondMirror target secondMirrorNonNull)
          reflectedSidesNonparallel) ∧
      spread firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull =
        1 - spread thirdLine
          (reflectLine firstMirror target firstMirrorNonNull)
          thirdLineNonNull reflectedSideNonNull := by
  dsimp only
  have thirdSpread := normalized_incenter_third_spread_eq_cross
    firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
    targetNonNull mirrorsNonparallel twoNonzero
  have fibonacci := spread_add_cross firstMirror secondMirror
    firstMirrorNonNull secondMirrorNonNull
  refine ⟨normalizedIncenterThirdLine_contains_origin firstMirror secondMirror
    target firstMirrorNonNull secondMirrorNonNull targetNonNull
    mirrorsNonparallel twoNonzero, ?_, ?_⟩
  · apply normalizedIncenterThirdLine_contains_reflected_intersection
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero firstMirrorThroughOrigin
      secondMirrorThroughOrigin reflectedSidesNonparallel
  · calc
      spread firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull =
          1 - cross firstMirror secondMirror firstMirrorNonNull
            secondMirrorNonNull := by
              rw [← fibonacci]
              ring1
      _ = 1 - spread
          (normalizedIncenterThirdLine firstMirror secondMirror target
            firstMirrorNonNull secondMirrorNonNull targetNonNull
            mirrorsNonparallel twoNonzero)
          (reflectLine firstMirror target firstMirrorNonNull)
          (normalizedIncenterThirdLine_nonNull firstMirror secondMirror target
            firstMirrorNonNull secondMirrorNonNull targetNonNull
            mirrorsNonparallel twoNonzero)
          (reflectLine_nonNull firstMirror target firstMirrorNonNull
            targetNonNull) := by rw [thirdSpread]

/-- Exercise 12.6, first polynomial identity. -/
theorem exercise_12_6_identity (a b c : K) :
    tripleSpreadFunction a b (1 - c) =
      2 * (a + b + c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) - 1 -
        tripleSpreadFunction a b c := by
  unfold tripleSpreadFunction
  ring1

/-- Exercise 12.6, the three complementary triple-spread values agree. -/
theorem exercise_12_6 (a b c : K) :
    tripleSpreadFunction a b (1 - c) =
        tripleSpreadFunction a (1 - b) c ∧
      tripleSpreadFunction a (1 - b) c =
        tripleSpreadFunction (1 - a) b c := by
  constructor <;> unfold tripleSpreadFunction <;> ring1

end DivineProportions
