import DivineProportions.Conics.GrammolaUniqueness
import DivineProportions.Trigonometry.VertexBisector

/-!
# Divine Proportions, Exercise 15.18

The two axes of a grammola are constructed from an explicit square witness
for the product of its diagonal norms.  Reflection in either normalized
vertex bisector swaps the two weighted squared line values, so it preserves
the grammola equation.  Conversely, two finite reflection probes show that
every axis satisfies the equal-spread bisector equation.
-/

namespace DivineProportions

namespace Grammola

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

private theorem eq_of_mul_eq_mul_left
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have differenceZero : factor * (left - right) = 0 := by
    calc
      factor * (left - right) = factor * left - factor * right := by ring1
      _ = 0 := by rw [productsEqual]; ring1
  have cancelled := eq_zero_of_mul_eq_zero_left factorNonzero differenceZero
  calc
    left = (left - right) + right := by ring1
    _ = right := by rw [cancelled]; ring1

private theorem ratio_eq_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel]
            ring1
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel]
      ring1

private theorem root_nonzero
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal) :
    root ≠ 0 := by
  intro rootZero
  have productNonzero := RFAP.ExplicitField.mul_ne_zero firstNonNull
    secondNonNull
  apply productNonzero
  calc
    lineNorm firstDiagonal * lineNorm secondDiagonal = root ^ 2 :=
      rootEquation.symm
    _ = 0 := by rw [rootZero]; ring1

/-- Reflection changes a displayed line value by the usual finite projection
formula.  This denominator-cleared identity is reused for both axes. -/
theorem lineValue_reflectPoint (mirror target : Line K)
    (mirrorNonNull : ¬ mirror.IsNull) (point : Point K) :
    lineValue target (reflectPoint mirror mirrorNonNull point) =
      (lineNorm mirror * lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            lineValue mirror point) /
        lineNorm mirror := by
  have normCancel : lineNorm mirror * (lineNorm mirror)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [reflectPoint_formula]
  change
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
              2 * mirror.a * mirror.b * point.y -
              2 * mirror.a * mirror.c) /
            lineNorm mirror) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
              (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
              2 * mirror.b * mirror.c) /
            lineNorm mirror) + target.c =
      (lineNorm mirror *
            (target.a * point.x + target.b * point.y + target.c) -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            (mirror.a * point.x + mirror.b * point.y + mirror.c)) /
        lineNorm mirror
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
              2 * mirror.a * mirror.b * point.y -
              2 * mirror.a * mirror.c) * (lineNorm mirror)⁻¹) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
              (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
              2 * mirror.b * mirror.c) * (lineNorm mirror)⁻¹) +
        target.c =
      (lineNorm mirror * lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            lineValue mirror point) * (lineNorm mirror)⁻¹ +
        target.c *
          (1 - lineNorm mirror * (lineNorm mirror)⁻¹) := by
            unfold lineValue lineNorm
            ring1
    _ = (lineNorm mirror * lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            lineValue mirror point) * (lineNorm mirror)⁻¹ := by
      rw [normCancel]
      ring1

private theorem positive_reflection_swaps_first [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal)
    (point : Point K) :
    let axis := positiveVertexBisector firstDiagonal secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := positiveVertexBisector_nonNull firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    root * lineValue firstDiagonal (reflectPoint axis axisNonNull point) =
      -lineNorm firstDiagonal * lineValue secondDiagonal point := by
  dsimp only
  let axis := positiveVertexBisector firstDiagonal secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := positiveVertexBisector_nonNull firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := positiveVertexBisector_norm firstDiagonal secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : lineNorm axis * (lineNorm axis)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ axisNonNull
  have firstDotAxis :
      firstDiagonal.a * axis.a + firstDiagonal.b * axis.b =
        lineNorm firstDiagonal *
          (root + (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b)) := by
    change
      firstDiagonal.a *
            (root * firstDiagonal.a +
              lineNorm firstDiagonal * secondDiagonal.a) +
          firstDiagonal.b *
            (root * firstDiagonal.b +
              lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold lineNorm
    ring1
  have axisValue : lineValue axis point =
      root * lineValue firstDiagonal point +
        lineNorm firstDiagonal * lineValue secondDiagonal point := by
    change
      (root * firstDiagonal.a +
            lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b +
            lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c +
            lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold lineValue
    ring1
  rw [lineValue_reflectPoint axis firstDiagonal axisNonNull point]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    root *
        ((lineNorm axis * lineValue firstDiagonal point -
            2 *
                (firstDiagonal.a * axis.a + firstDiagonal.b * axis.b) *
              lineValue axis point) *
          (lineNorm axis)⁻¹) =
      root *
        ((lineNorm axis * lineValue firstDiagonal point -
            2 *
                (lineNorm firstDiagonal *
                  (root + (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b))) *
              (root * lineValue firstDiagonal point +
                lineNorm firstDiagonal * lineValue secondDiagonal point)) *
          (lineNorm axis)⁻¹) := by rw [firstDotAxis, axisValue]
    _ =
      (-lineNorm firstDiagonal * lineValue secondDiagonal point) *
        (lineNorm axis * (lineNorm axis)⁻¹) := by
          rw [axisNorm]
          ring1
    _ = -lineNorm firstDiagonal * lineValue secondDiagonal point := by
      rw [normCancel]
      ring1

private theorem positive_reflection_swaps_second [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal)
    (point : Point K) :
    let axis := positiveVertexBisector firstDiagonal secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := positiveVertexBisector_nonNull firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    lineNorm firstDiagonal *
        lineValue secondDiagonal (reflectPoint axis axisNonNull point) =
      -root * lineValue firstDiagonal point := by
  dsimp only
  let axis := positiveVertexBisector firstDiagonal secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := positiveVertexBisector_nonNull firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := positiveVertexBisector_norm firstDiagonal secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : lineNorm axis * (lineNorm axis)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ axisNonNull
  have secondDotAxis :
      secondDiagonal.a * axis.a + secondDiagonal.b * axis.b =
        root * (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b) +
          lineNorm firstDiagonal * lineNorm secondDiagonal := by
    change
      secondDiagonal.a *
            (root * firstDiagonal.a +
              lineNorm firstDiagonal * secondDiagonal.a) +
          secondDiagonal.b *
            (root * firstDiagonal.b +
              lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold lineNorm
    ring1
  have axisValue : lineValue axis point =
      root * lineValue firstDiagonal point +
        lineNorm firstDiagonal * lineValue secondDiagonal point := by
    change
      (root * firstDiagonal.a +
            lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b +
            lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c +
            lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold lineValue
    ring1
  rw [lineValue_reflectPoint axis secondDiagonal axisNonNull point]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    lineNorm firstDiagonal *
        ((lineNorm axis * lineValue secondDiagonal point -
            2 *
                (secondDiagonal.a * axis.a + secondDiagonal.b * axis.b) *
              lineValue axis point) *
          (lineNorm axis)⁻¹) =
      lineNorm firstDiagonal *
        ((lineNorm axis * lineValue secondDiagonal point -
            2 *
                (root * (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b) +
                  lineNorm firstDiagonal * lineNorm secondDiagonal) *
              (root * lineValue firstDiagonal point +
                lineNorm firstDiagonal * lineValue secondDiagonal point)) *
          (lineNorm axis)⁻¹) := by rw [secondDotAxis, axisValue]
    _ =
      (-root * lineValue firstDiagonal point) *
        (lineNorm axis * (lineNorm axis)⁻¹) := by
          rw [axisNorm]
          rw [← rootEquation]
          ring1
    _ = -root * lineValue firstDiagonal point := by
      rw [normCancel]
      ring1

private theorem negative_reflection_swaps_first [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal)
    (point : Point K) :
    let axis := negativeVertexBisector firstDiagonal secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := negativeVertexBisector_nonNull firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    root * lineValue firstDiagonal (reflectPoint axis axisNonNull point) =
      lineNorm firstDiagonal * lineValue secondDiagonal point := by
  dsimp only
  let axis := negativeVertexBisector firstDiagonal secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := negativeVertexBisector_nonNull firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := negativeVertexBisector_norm firstDiagonal secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : lineNorm axis * (lineNorm axis)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ axisNonNull
  have firstDotAxis :
      firstDiagonal.a * axis.a + firstDiagonal.b * axis.b =
        lineNorm firstDiagonal *
          (root - (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b)) := by
    change
      firstDiagonal.a *
            (root * firstDiagonal.a -
              lineNorm firstDiagonal * secondDiagonal.a) +
          firstDiagonal.b *
            (root * firstDiagonal.b -
              lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold lineNorm
    ring1
  have axisValue : lineValue axis point =
      root * lineValue firstDiagonal point -
        lineNorm firstDiagonal * lineValue secondDiagonal point := by
    change
      (root * firstDiagonal.a -
            lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b -
            lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c -
            lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold lineValue
    ring1
  rw [lineValue_reflectPoint axis firstDiagonal axisNonNull point]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    root *
        ((lineNorm axis * lineValue firstDiagonal point -
            2 *
                (firstDiagonal.a * axis.a + firstDiagonal.b * axis.b) *
              lineValue axis point) *
          (lineNorm axis)⁻¹) =
      root *
        ((lineNorm axis * lineValue firstDiagonal point -
            2 *
                (lineNorm firstDiagonal *
                  (root - (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b))) *
              (root * lineValue firstDiagonal point -
                lineNorm firstDiagonal * lineValue secondDiagonal point)) *
          (lineNorm axis)⁻¹) := by rw [firstDotAxis, axisValue]
    _ =
      (lineNorm firstDiagonal * lineValue secondDiagonal point) *
        (lineNorm axis * (lineNorm axis)⁻¹) := by
          rw [axisNorm]
          ring1
    _ = lineNorm firstDiagonal * lineValue secondDiagonal point := by
      rw [normCancel]
      ring1

private theorem negative_reflection_swaps_second [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal)
    (point : Point K) :
    let axis := negativeVertexBisector firstDiagonal secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := negativeVertexBisector_nonNull firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    lineNorm firstDiagonal *
        lineValue secondDiagonal (reflectPoint axis axisNonNull point) =
      root * lineValue firstDiagonal point := by
  dsimp only
  let axis := negativeVertexBisector firstDiagonal secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := negativeVertexBisector_nonNull firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := negativeVertexBisector_norm firstDiagonal secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : lineNorm axis * (lineNorm axis)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ axisNonNull
  have secondDotAxis :
      secondDiagonal.a * axis.a + secondDiagonal.b * axis.b =
        root * (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b) -
          lineNorm firstDiagonal * lineNorm secondDiagonal := by
    change
      secondDiagonal.a *
            (root * firstDiagonal.a -
              lineNorm firstDiagonal * secondDiagonal.a) +
          secondDiagonal.b *
            (root * firstDiagonal.b -
              lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold lineNorm
    ring1
  have axisValue : lineValue axis point =
      root * lineValue firstDiagonal point -
        lineNorm firstDiagonal * lineValue secondDiagonal point := by
    change
      (root * firstDiagonal.a -
            lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b -
            lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c -
            lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold lineValue
    ring1
  rw [lineValue_reflectPoint axis secondDiagonal axisNonNull point]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    lineNorm firstDiagonal *
        ((lineNorm axis * lineValue secondDiagonal point -
            2 *
                (secondDiagonal.a * axis.a + secondDiagonal.b * axis.b) *
              lineValue axis point) *
          (lineNorm axis)⁻¹) =
      lineNorm firstDiagonal *
        ((lineNorm axis * lineValue secondDiagonal point -
            2 *
                (root * (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b) -
                  lineNorm firstDiagonal * lineNorm secondDiagonal) *
              (root * lineValue firstDiagonal point -
                lineNorm firstDiagonal * lineValue secondDiagonal point)) *
          (lineNorm axis)⁻¹) := by rw [secondDotAxis, axisValue]
    _ =
      (root * lineValue firstDiagonal point) *
        (lineNorm axis * (lineNorm axis)⁻¹) := by
          rw [axisNorm]
          rw [← rootEquation]
          ring1
    _ = root * lineValue firstDiagonal point := by
      rw [normCancel]
      ring1

private theorem weightedSquares_preserved
    (firstNorm secondNorm root firstValue secondValue
      reflectedFirst reflectedSecond : K)
    (firstNormNonzero : firstNorm ≠ 0) (rootNonzero : root ≠ 0)
    (rootEquation : root ^ 2 = firstNorm * secondNorm)
    (firstSwap : root * reflectedFirst = -firstNorm * secondValue)
    (secondSwap : firstNorm * reflectedSecond = -root * firstValue) :
    secondNorm * reflectedFirst ^ 2 + firstNorm * reflectedSecond ^ 2 =
      secondNorm * firstValue ^ 2 + firstNorm * secondValue ^ 2 := by
  have firstSquare :
      root ^ 2 * reflectedFirst ^ 2 = firstNorm ^ 2 * secondValue ^ 2 := by
    calc
      root ^ 2 * reflectedFirst ^ 2 = (root * reflectedFirst) ^ 2 := by ring1
      _ = (-firstNorm * secondValue) ^ 2 := by rw [firstSwap]
      _ = firstNorm ^ 2 * secondValue ^ 2 := by ring1
  have secondSquare :
      firstNorm ^ 2 * reflectedSecond ^ 2 = root ^ 2 * firstValue ^ 2 := by
    calc
      firstNorm ^ 2 * reflectedSecond ^ 2 =
          (firstNorm * reflectedSecond) ^ 2 := by ring1
      _ = (-root * firstValue) ^ 2 := by rw [secondSwap]
      _ = root ^ 2 * firstValue ^ 2 := by ring1
  have rootSquareNonzero : root ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero rootNonzero rootNonzero
  have factorNonzero : firstNorm * root ^ 2 ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNormNonzero rootSquareNonzero
  apply eq_of_mul_eq_mul_left factorNonzero
  calc
    (firstNorm * root ^ 2) *
        (secondNorm * reflectedFirst ^ 2 +
          firstNorm * reflectedSecond ^ 2) =
      firstNorm * secondNorm *
          (root ^ 2 * reflectedFirst ^ 2) +
        root ^ 2 *
          (firstNorm ^ 2 * reflectedSecond ^ 2) := by ring1
    _ = firstNorm * secondNorm *
          (firstNorm ^ 2 * secondValue ^ 2) +
        root ^ 2 * (root ^ 2 * firstValue ^ 2) := by
          rw [firstSquare, secondSquare]
    _ = (firstNorm * root ^ 2) *
        (secondNorm * firstValue ^ 2 +
          firstNorm * secondValue ^ 2) := by
            rw [rootEquation]
            ring1

/-- The positive normalized vertex bisector is an axis of the grammola. -/
theorem positiveVertexBisector_isAxis [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance root : K)
    (presentation :
      Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal) :
    let axis := positiveVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    (conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis axis := by
  dsimp only
  let axis := positiveVertexBisector firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.notParallel
  let axisNonNull := positiveVertexBisector_nonNull firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation
  refine ⟨axisNonNull, ?_⟩
  intro point
  have rootNonzero := root_nonzero firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.secondNonNull rootEquation
  have firstSwap := positive_reflection_swaps_first firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have secondSwap := positive_reflection_swaps_second firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have squares := weightedSquares_preserved
    (lineNorm firstDiagonal) (lineNorm secondDiagonal) root
    (lineValue firstDiagonal point) (lineValue secondDiagonal point)
    (lineValue firstDiagonal (reflectPoint axis axisNonNull point))
    (lineValue secondDiagonal (reflectPoint axis axisNonNull point))
    presentation.firstNonNull rootNonzero rootEquation firstSwap secondSwap
  rw [conic_evaluate, conic_evaluate]
  unfold clearedEvaluate
  rw [squares]

/-- The negative normalized vertex bisector is the second grammola axis. -/
theorem negativeVertexBisector_isAxis [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance root : K)
    (presentation :
      Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal) :
    let axis := negativeVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    (conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis axis := by
  dsimp only
  let axis := negativeVertexBisector firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.notParallel
  let axisNonNull := negativeVertexBisector_nonNull firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation
  refine ⟨axisNonNull, ?_⟩
  intro point
  have rootNonzero := root_nonzero firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.secondNonNull rootEquation
  have firstSwap := negative_reflection_swaps_first firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have secondSwapUnsigned := negative_reflection_swaps_second firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have firstSwapSigned :
      root * lineValue firstDiagonal (reflectPoint axis axisNonNull point) =
        -lineNorm firstDiagonal * (-lineValue secondDiagonal point) := by
    rw [firstSwap]
    ring1
  have secondSwapSigned :
      lineNorm firstDiagonal *
          lineValue secondDiagonal (reflectPoint axis axisNonNull point) =
        -root * (-lineValue firstDiagonal point) := by
    rw [secondSwapUnsigned]
    ring1
  have squares := weightedSquares_preserved
    (lineNorm firstDiagonal) (lineNorm secondDiagonal) root
    (-lineValue firstDiagonal point) (-lineValue secondDiagonal point)
    (lineValue firstDiagonal (reflectPoint axis axisNonNull point))
    (lineValue secondDiagonal (reflectPoint axis axisNonNull point))
    presentation.firstNonNull rootNonzero rootEquation firstSwapSigned
    secondSwapSigned
  rw [conic_evaluate, conic_evaluate]
  unfold clearedEvaluate
  calc
    lineNorm secondDiagonal *
          lineValue firstDiagonal (reflectPoint axis axisNonNull point) ^ 2 +
        lineNorm firstDiagonal *
          lineValue secondDiagonal (reflectPoint axis axisNonNull point) ^ 2 -
        associatedQuadrance * lineNorm firstDiagonal *
          lineNorm secondDiagonal =
      lineNorm secondDiagonal * (-lineValue firstDiagonal point) ^ 2 +
        lineNorm firstDiagonal * (-lineValue secondDiagonal point) ^ 2 -
        associatedQuadrance * lineNorm firstDiagonal *
          lineNorm secondDiagonal := by rw [squares]
    _ = lineNorm secondDiagonal * lineValue firstDiagonal point ^ 2 +
        lineNorm firstDiagonal * lineValue secondDiagonal point ^ 2 -
        associatedQuadrance * lineNorm firstDiagonal *
          lineNorm secondDiagonal := by ring1

private theorem reflectPoint_rotateInPoint (axis : Line K)
    (axisNonNull : ¬ axis.IsNull) (center point : Point K) :
    reflectPoint axis axisNonNull (rotateInPoint center point) =
      rotateInPoint (reflectPoint axis axisNonNull center)
        (reflectPoint axis axisNonNull point) := by
  have affine := reflectPoint_affine axis axisNonNull center point
    (2 : K) (-1 : K) (by ring1)
  calc
    reflectPoint axis axisNonNull (rotateInPoint center point) =
      reflectPoint axis axisNonNull
        (affineCombination 2 center (-1) point) := by
          congr 1
          apply Point.ext <;> unfold rotateInPoint affineCombination <;> ring1
    _ = affineCombination 2 (reflectPoint axis axisNonNull center)
        (-1) (reflectPoint axis axisNonNull point) := affine
    _ = rotateInPoint (reflectPoint axis axisNonNull center)
        (reflectPoint axis axisNonNull point) := by
          apply Point.ext <;> unfold rotateInPoint affineCombination <;> ring1

private theorem reflected_center_isCenter (displayedConic : Conic K)
    (axis : Line K) (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Point K,
      displayedConic.evaluate (reflectPoint axis axisNonNull point) =
        displayedConic.evaluate point)
    (center : Point K) (isCenter : displayedConic.IsCenter center)
    (twoNonzero : (2 : K) ≠ 0) :
    displayedConic.IsCenter (reflectPoint axis axisNonNull center) := by
  have centerInvariant :=
    (Conic.isCenter_iff_rotationInvariant displayedConic center twoNonzero).1
      isCenter
  apply (Conic.isCenter_iff_rotationInvariant displayedConic
    (reflectPoint axis axisNonNull center) twoNonzero).2
  intro point
  have commute :
      reflectPoint axis axisNonNull
          (rotateInPoint center (reflectPoint axis axisNonNull point)) =
        rotateInPoint (reflectPoint axis axisNonNull center) point := by
    calc
      reflectPoint axis axisNonNull
          (rotateInPoint center (reflectPoint axis axisNonNull point)) =
        rotateInPoint (reflectPoint axis axisNonNull center)
          (reflectPoint axis axisNonNull
            (reflectPoint axis axisNonNull point)) :=
              reflectPoint_rotateInPoint axis axisNonNull center
                (reflectPoint axis axisNonNull point)
      _ = rotateInPoint (reflectPoint axis axisNonNull center) point := by
        rw [reflectPoint_involutive]
  calc
    displayedConic.evaluate
        (rotateInPoint (reflectPoint axis axisNonNull center) point) =
      displayedConic.evaluate
        (reflectPoint axis axisNonNull
          (rotateInPoint center (reflectPoint axis axisNonNull point))) := by
            rw [commute]
    _ = displayedConic.evaluate
        (rotateInPoint center (reflectPoint axis axisNonNull point)) :=
          equationInvariant _
    _ = displayedConic.evaluate (reflectPoint axis axisNonNull point) :=
      centerInvariant _
    _ = displayedConic.evaluate point := equationInvariant _

private theorem contains_of_reflectPoint_fixed (axis : Line K)
    (axisNonNull : ¬ axis.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) (fixed : reflectPoint axis axisNonNull point = point) :
    axis.Contains point := by
  have xFixed := congrArg Point.x fixed
  have yFixed := congrArg Point.y fixed
  have twiceXZero :
      2 * ((altitudeFoot point axis axisNonNull).x - point.x) = 0 := by
    change 2 * (altitudeFoot point axis axisNonNull).x - point.x = point.x
      at xFixed
    calc
      2 * ((altitudeFoot point axis axisNonNull).x - point.x) =
          (2 * (altitudeFoot point axis axisNonNull).x - point.x) -
            point.x := by ring1
      _ = 0 := by rw [xFixed]; ring1
  have twiceYZero :
      2 * ((altitudeFoot point axis axisNonNull).y - point.y) = 0 := by
    change 2 * (altitudeFoot point axis axisNonNull).y - point.y = point.y
      at yFixed
    calc
      2 * ((altitudeFoot point axis axisNonNull).y - point.y) =
          (2 * (altitudeFoot point axis axisNonNull).y - point.y) -
            point.y := by ring1
      _ = 0 := by rw [yFixed]; ring1
  have footEqualsPoint : altitudeFoot point axis axisNonNull = point := by
    apply Point.ext
    · have differenceZero := eq_zero_of_mul_eq_zero_left twoNonzero twiceXZero
      calc
        (altitudeFoot point axis axisNonNull).x =
            ((altitudeFoot point axis axisNonNull).x - point.x) + point.x := by
              ring1
        _ = point.x := by rw [differenceZero]; ring1
    · have differenceZero := eq_zero_of_mul_eq_zero_left twoNonzero twiceYZero
      calc
        (altitudeFoot point axis axisNonNull).y =
            ((altitudeFoot point axis axisNonNull).y - point.y) + point.y := by
              ring1
        _ = point.y := by rw [differenceZero]; ring1
  rw [← footEqualsPoint]
  exact altitudeFoot_on_line point axis axisNonNull

private def positiveAxisProbe (center : Point K) (axis : Line K) : Point K :=
  ⟨center.x + axis.b + axis.a, center.y - axis.a + axis.b⟩

private def negativeAxisProbe (center : Point K) (axis : Line K) : Point K :=
  ⟨center.x + axis.b - axis.a, center.y - axis.a - axis.b⟩

private theorem reflectPoint_positiveAxisProbe (axis : Line K)
    (axisNonNull : ¬ axis.IsNull) (center : Point K)
    (centerOnAxis : axis.Contains center) :
    reflectPoint axis axisNonNull (positiveAxisProbe center axis) =
      negativeAxisProbe center axis := by
  have normCancel : lineNorm axis * (lineNorm axis)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ axisNonNull
  rw [reflectPoint_formula]
  apply Point.ext
  · change
      (((axis.b ^ 2 - axis.a ^ 2) *
              (center.x + axis.b + axis.a) -
            2 * axis.a * axis.b * (center.y - axis.a + axis.b) -
            2 * axis.a * axis.c) /
          lineNorm axis) = center.x + axis.b - axis.a
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      ((axis.b ^ 2 - axis.a ^ 2) *
              (center.x + axis.b + axis.a) -
            2 * axis.a * axis.b * (center.y - axis.a + axis.b) -
            2 * axis.a * axis.c) * (lineNorm axis)⁻¹ =
        (lineNorm axis * (center.x + axis.b - axis.a) -
            2 * axis.a *
              (axis.a * center.x + axis.b * center.y + axis.c)) *
          (lineNorm axis)⁻¹ := by unfold lineNorm; ring1
      _ = (lineNorm axis * (center.x + axis.b - axis.a)) *
          (lineNorm axis)⁻¹ := by
            unfold Line.Contains at centerOnAxis
            rw [centerOnAxis]
            ring1
      _ = (center.x + axis.b - axis.a) *
          (lineNorm axis * (lineNorm axis)⁻¹) := by ring1
      _ = center.x + axis.b - axis.a := by rw [normCancel]; ring1
  · change
      ((-2 * axis.a * axis.b * (center.x + axis.b + axis.a) +
            (axis.a ^ 2 - axis.b ^ 2) *
              (center.y - axis.a + axis.b) -
            2 * axis.b * axis.c) /
          lineNorm axis) = center.y - axis.a - axis.b
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-2 * axis.a * axis.b * (center.x + axis.b + axis.a) +
              (axis.a ^ 2 - axis.b ^ 2) *
                (center.y - axis.a + axis.b) -
              2 * axis.b * axis.c) * (lineNorm axis)⁻¹ =
        (lineNorm axis * (center.y - axis.a - axis.b) -
            2 * axis.b *
              (axis.a * center.x + axis.b * center.y + axis.c)) *
          (lineNorm axis)⁻¹ := by unfold lineNorm; ring1
      _ = (lineNorm axis * (center.y - axis.a - axis.b)) *
          (lineNorm axis)⁻¹ := by
            unfold Line.Contains at centerOnAxis
            rw [centerOnAxis]
            ring1
      _ = (center.y - axis.a - axis.b) *
          (lineNorm axis * (lineNorm axis)⁻¹) := by ring1
      _ = center.y - axis.a - axis.b := by rw [normCancel]; ring1

private def axisCrossForm (displayedConic : Conic K) (axis : Line K) : K :=
  2 * (displayedConic.d - displayedConic.f) * axis.a * axis.b +
    displayedConic.e * (axis.b ^ 2 - axis.a ^ 2)

private theorem axisCrossForm_eq_zero_of_axis
    (displayedConic : Conic K) (axis : Line K)
    (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Point K,
      displayedConic.evaluate (reflectPoint axis axisNonNull point) =
        displayedConic.evaluate point)
    (center : Point K) (isCenter : displayedConic.IsCenter center)
    (centerOnAxis : axis.Contains center)
    (twoNonzero : (2 : K) ≠ 0) :
    axisCrossForm displayedConic axis = 0 := by
  have reflectedProbe := reflectPoint_positiveAxisProbe axis axisNonNull center
    centerOnAxis
  have evaluationsEqual :
      displayedConic.evaluate (negativeAxisProbe center axis) =
        displayedConic.evaluate (positiveAxisProbe center axis) := by
    rw [← reflectedProbe]
    exact equationInvariant _
  have twiceFormZero : 2 * axisCrossForm displayedConic axis = 0 := by
    calc
      2 * axisCrossForm displayedConic axis =
        displayedConic.evaluate (positiveAxisProbe center axis) -
          displayedConic.evaluate (negativeAxisProbe center axis) -
          2 * (axis.a *
              (2 * displayedConic.d * center.x +
                displayedConic.e * center.y + displayedConic.a) +
            axis.b *
              (displayedConic.e * center.x +
                2 * displayedConic.f * center.y + displayedConic.b)) := by
                  unfold axisCrossForm Conic.evaluate positiveAxisProbe
                    negativeAxisProbe
                  ring1
      _ = 0 := by rw [isCenter.1, isCenter.2, evaluationsEqual]; ring1
  exact eq_zero_of_mul_eq_zero_left twoNonzero twiceFormZero

private def lineDot (first second : Line K) : K :=
  first.a * second.a + first.b * second.b

private def bisectorFactor (first second axis : Line K) : K :=
  (first.a * axis.b - axis.a * first.b) *
      (second.a * axis.a + second.b * axis.b) +
    (first.a * axis.a + first.b * axis.b) *
      (second.a * axis.b - axis.a * second.b)

private theorem axisCrossForm_conic_factor [DecidableEq K]
    (firstDiagonal secondDiagonal axis : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    axisCrossForm
          (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
            associatedQuadrance twoNonzero) axis =
      2 * lineDot firstDiagonal secondDiagonal *
        bisectorFactor firstDiagonal secondDiagonal axis := by
  unfold axisCrossForm lineDot bisectorFactor conic conicD conicE conicF
    lineNorm
  ring1

private theorem bisector_balance_factor
    (firstDiagonal secondDiagonal axis : Line K) :
    lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
        lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
      (firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b) *
        bisectorFactor firstDiagonal secondDiagonal axis := by
  unfold lineNorm bisectorFactor
  ring1

/-- Every equation-preserving mirror of a valid grammola is a vertex
bisector of its two diagonal lines. -/
theorem axis_isVertexBisector [DecidableEq K]
    (firstDiagonal secondDiagonal axis : Line K)
    (associatedQuadrance : K)
    (presentation :
      Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (isAxis :
      (conic firstDiagonal secondDiagonal presentation.firstNonNull
        presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis
          axis) :
    IsVertexBisector firstDiagonal secondDiagonal axis
      presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel := by
  let displayedConic := conic firstDiagonal secondDiagonal
    presentation.firstNonNull presentation.secondNonNull associatedQuadrance
    twoNonzero
  let center := lineIntersection firstDiagonal secondDiagonal
    presentation.notParallel
  rcases isAxis with ⟨axisNonNull, equationInvariant⟩
  have centerIsCenter : displayedConic.IsCenter center := by
    unfold displayedConic center
    exact exercise_15_15 firstDiagonal secondDiagonal associatedQuadrance
      presentation twoNonzero
  have discriminantNonzero : displayedConic.centerDiscriminant ≠ 0 := by
    unfold displayedConic
    exact conic_centerDiscriminant_nonzero firstDiagonal secondDiagonal
      associatedQuadrance presentation twoNonzero
  have reflectedCenterIsCenter :
      displayedConic.IsCenter (reflectPoint axis axisNonNull center) :=
    reflected_center_isCenter displayedConic axis axisNonNull
      equationInvariant center centerIsCenter twoNonzero
  have reflectedCenterFixed :
      reflectPoint axis axisNonNull center = center := by
    have reflectedFormula := Conic.center_eq_centerPoint displayedConic
      (reflectPoint axis axisNonNull center) discriminantNonzero
      reflectedCenterIsCenter
    have centerFormula := Conic.center_eq_centerPoint displayedConic center
      discriminantNonzero centerIsCenter
    exact reflectedFormula.trans centerFormula.symm
  have centerOnAxis : axis.Contains center :=
    contains_of_reflectPoint_fixed axis axisNonNull twoNonzero center
      reflectedCenterFixed
  have crossFormZero : axisCrossForm displayedConic axis = 0 :=
    axisCrossForm_eq_zero_of_axis displayedConic axis axisNonNull
      equationInvariant center centerIsCenter centerOnAxis twoNonzero
  have dotNonzero : lineDot firstDiagonal secondDiagonal ≠ 0 := by
    exact presentation.notPerpendicular
  have factorNonzero : 2 * lineDot firstDiagonal secondDiagonal ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero dotNonzero
  have factorZero : bisectorFactor firstDiagonal secondDiagonal axis = 0 := by
    apply eq_zero_of_mul_eq_zero_left factorNonzero
    calc
      (2 * lineDot firstDiagonal secondDiagonal) *
          bisectorFactor firstDiagonal secondDiagonal axis =
        axisCrossForm displayedConic axis := by
          unfold displayedConic
          rw [axisCrossForm_conic_factor]
      _ = 0 := by rw [crossFormZero]
  have balance :
      lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 =
        lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
    have differenceZero :
        lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
          0 := by
      calc
        lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
          (firstDiagonal.a * secondDiagonal.b -
              secondDiagonal.a * firstDiagonal.b) *
            bisectorFactor firstDiagonal secondDiagonal axis :=
              bisector_balance_factor firstDiagonal secondDiagonal axis
        _ = 0 := by rw [factorZero]; ring1
    calc
      lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 =
        (lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2) +
          lineNorm firstDiagonal *
            (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
              ring1
      _ = lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
            rw [differenceZero]
            ring1
  have firstDenominatorNonzero :
      lineNorm firstDiagonal * lineNorm axis ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero presentation.firstNonNull axisNonNull
  have secondDenominatorNonzero :
      lineNorm secondDiagonal * lineNorm axis ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero presentation.secondNonNull axisNonNull
  refine ⟨axisNonNull, centerOnAxis, ?_⟩
  unfold spread
  apply ratio_eq_of_cross_mul firstDenominatorNonzero
    secondDenominatorNonzero
  calc
    (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 *
        (lineNorm secondDiagonal * lineNorm axis) =
      (lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2) *
        lineNorm axis := by ring1
    _ = (lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2) *
        lineNorm axis := by rw [balance]
    _ = (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 *
        (lineNorm firstDiagonal * lineNorm axis) := by ring1

/-- Exactly two axes means two inequivalent displayed mirrors which exhaust
all equation-preserving mirrors up to line equivalence. -/
def HasExactlyTwoAxes (displayedConic : Conic K) : Prop :=
  ∃ firstAxis secondAxis : Line K,
    displayedConic.IsAxis firstAxis ∧
      displayedConic.IsAxis secondAxis ∧
      ¬ firstAxis.Equivalent secondAxis ∧
      ∀ axis : Line K, displayedConic.IsAxis axis →
        axis.Equivalent firstAxis ∨ axis.Equivalent secondAxis

/-- Exercise 15.18: a grammola has exactly two axes precisely when its
diagonal vertex is square.  Every axis is, constructively, a vertex bisector
of the two diagonals. -/
theorem exercise_15_18 [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance : K)
    (presentation :
      Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    HasExactlyTwoAxes
        (conic firstDiagonal secondDiagonal presentation.firstNonNull
          presentation.secondNonNull associatedQuadrance twoNonzero) ↔
      IsNonzeroSquare
        (spread firstDiagonal secondDiagonal presentation.firstNonNull
          presentation.secondNonNull) := by
  constructor
  · rintro ⟨firstAxis, _secondAxis, firstIsAxis, _secondIsAxis,
      _distinct, _exhaustive⟩
    have firstIsBisector := axis_isVertexBisector firstDiagonal
      secondDiagonal firstAxis associatedQuadrance presentation twoNonzero
      firstIsAxis
    exact (spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
      firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull presentation.notParallel).2
        (normProduct_isNonzeroSquare_of_isVertexBisector firstDiagonal
          secondDiagonal firstAxis presentation.firstNonNull
          presentation.secondNonNull presentation.notParallel
          firstIsBisector)
  · intro spreadSquare
    have normProductSquare :=
      (spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare firstDiagonal
        secondDiagonal presentation.firstNonNull presentation.secondNonNull
        presentation.notParallel).1 spreadSquare
    rcases normProductSquare with ⟨root, _rootNonzero, rootEquationReversed⟩
    have rootEquation :
        root ^ 2 = lineNorm firstDiagonal * lineNorm secondDiagonal :=
      rootEquationReversed.symm
    let positive := positiveVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    let negative := negativeVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    have positiveAxis := positiveVertexBisector_isAxis firstDiagonal
      secondDiagonal associatedQuadrance root presentation twoNonzero
      rootEquation
    have negativeAxis := negativeVertexBisector_isAxis firstDiagonal
      secondDiagonal associatedQuadrance root presentation twoNonzero
      rootEquation
    have axesDistinct := vertexBisectors_not_equivalent firstDiagonal
      secondDiagonal root presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel twoNonzero rootEquation
    refine ⟨positive, negative, positiveAxis, negativeAxis, axesDistinct, ?_⟩
    intro axis isAxis
    have isBisector := axis_isVertexBisector firstDiagonal secondDiagonal axis
      associatedQuadrance presentation twoNonzero isAxis
    exact vertex_bisector_classification firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel rootEquation axis isBisector

end Grammola

end DivineProportions
