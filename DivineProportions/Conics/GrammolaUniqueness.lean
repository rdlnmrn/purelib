import DivineProportions.Conics.Grammola
import DivineProportions.Conics.Quadrola

/-!
# Divine Proportions, Exercise 15.14

The quadratic coefficients of a grammola determine a binary quadratic whose
two factors are its diagonal directions.  This avoids diagonalizing a matrix
or selecting square roots.  The unique center then restores the affine line
offsets, and evaluation at that center restores the associated quadrance.
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

private theorem eq_zero_of_mul_eq_zero_right
    {left right : K} (rightNonzero : right ≠ 0)
    (productZero : left * right = 0) : left = 0 := by
  apply eq_zero_of_mul_eq_zero_left rightNonzero
  calc
    right * left = left * right := by ring1
    _ = 0 := productZero

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

/-- The homogeneous quadratic part of a displayed conic. -/
def quadraticValue (conic : Conic K) (x y : K) : K :=
  conic.d * x ^ 2 + conic.e * x * y + conic.f * y ^ 2

/-- Four times the determinant of the symmetric quadratic coefficient
matrix, written without dividing the mixed coefficient by two. -/
def fourQuadraticDeterminant (conic : Conic K) : K :=
  4 * conic.d * conic.f - conic.e ^ 2

/-- The conic-determined binary quadratic whose factors are the two grammola
diagonal directions. -/
def diagonalRecoveryValue (conic : Conic K) (x y : K) : K :=
  2 * (conic.d + conic.f) * quadraticValue conic x y -
    fourQuadraticDeterminant conic * (x ^ 2 + y ^ 2)

/-- The homogeneous product of two displayed line direction forms. -/
def directionProduct (first second : Line K) (x y : K) : K :=
  (first.a * x + first.b * y) * (second.a * x + second.b * y)

/-- For a grammola conic, the recovery quadratic is a visibly nonzero scalar
multiple of the product of its two diagonal direction forms. -/
theorem diagonalRecoveryValue_conic [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (x y : K) :
    diagonalRecoveryValue
        (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
          associatedQuadrance twoNonzero) x y =
      8 * lineNorm firstDiagonal * lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b) *
        directionProduct firstDiagonal secondDiagonal x y := by
  unfold diagonalRecoveryValue quadraticValue fourQuadraticDeterminant
    directionProduct conic conicD conicE conicF lineNorm
  ring1

/-- A nonparallel pair of line directions is determined, up to swapping, by
the product of its two linear forms up to a nonzero scale. -/
theorem directionPairs_unique_of_product_scale [DecidableEq K]
    (firstOne firstTwo secondOne secondTwo : Line K)
    (firstNotParallel : ¬ firstOne.Parallel firstTwo)
    (scale : K) (scaleNonzero : scale ≠ 0)
    (productsEqual : ∀ x y : K,
      directionProduct firstOne firstTwo x y =
        scale * directionProduct secondOne secondTwo x y) :
    ((firstOne.Parallel secondOne ∧ firstTwo.Parallel secondTwo) ∨
      (firstOne.Parallel secondTwo ∧ firstTwo.Parallel secondOne)) := by
  have firstDirection := productsEqual firstOne.b (-firstOne.a)
  have secondDirection := productsEqual firstTwo.b (-firstTwo.a)
  have firstProductZero :
      (secondOne.a * firstOne.b - secondOne.b * firstOne.a) *
          (secondTwo.a * firstOne.b - secondTwo.b * firstOne.a) = 0 := by
    apply eq_zero_of_mul_eq_zero_left scaleNonzero
    calc
      scale *
          ((secondOne.a * firstOne.b - secondOne.b * firstOne.a) *
            (secondTwo.a * firstOne.b - secondTwo.b * firstOne.a)) =
        scale * directionProduct secondOne secondTwo
          firstOne.b (-firstOne.a) := by
            unfold directionProduct
            ring1
      _ = directionProduct firstOne firstTwo
          firstOne.b (-firstOne.a) := firstDirection.symm
      _ = 0 := by unfold directionProduct; ring1
  have secondProductZero :
      (secondOne.a * firstTwo.b - secondOne.b * firstTwo.a) *
          (secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a) = 0 := by
    apply eq_zero_of_mul_eq_zero_left scaleNonzero
    calc
      scale *
          ((secondOne.a * firstTwo.b - secondOne.b * firstTwo.a) *
            (secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a)) =
        scale * directionProduct secondOne secondTwo
          firstTwo.b (-firstTwo.a) := by
            unfold directionProduct
            ring1
      _ = directionProduct firstOne firstTwo
          firstTwo.b (-firstTwo.a) := secondDirection.symm
      _ = 0 := by unfold directionProduct; ring1
  have parallelIffFactorZero (source target : Line K) :
      source.Parallel target ↔
        target.a * source.b - target.b * source.a = 0 := by
    unfold Line.Parallel
    constructor <;> intro equation
    · calc
        target.a * source.b - target.b * source.a =
            -(source.a * target.b - target.a * source.b) := by ring1
        _ = 0 := by rw [equation]; ring1
    · calc
        source.a * target.b - target.a * source.b =
            -(target.a * source.b - target.b * source.a) := by ring1
        _ = 0 := by rw [equation]; ring1
  by_cases firstFactorZero :
      secondOne.a * firstOne.b - secondOne.b * firstOne.a = 0
  · have firstToSecondOne : firstOne.Parallel secondOne :=
      (parallelIffFactorZero firstOne secondOne).2 firstFactorZero
    have secondOneAtFirstTwoNonzero :
        secondOne.a * firstTwo.b - secondOne.b * firstTwo.a ≠ 0 := by
      intro factorZero
      have firstTwoToSecondOne : firstTwo.Parallel secondOne :=
        (parallelIffFactorZero firstTwo secondOne).2 factorZero
      apply firstNotParallel
      exact line_parallel_trans firstToSecondOne
        (Line.parallel_symm firstTwoToSecondOne)
    have secondTwoAtFirstTwoZero :
        secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a = 0 := by
      exact eq_zero_of_mul_eq_zero_left secondOneAtFirstTwoNonzero
        secondProductZero
    have firstTwoToSecondTwo : firstTwo.Parallel secondTwo :=
      (parallelIffFactorZero firstTwo secondTwo).2 secondTwoAtFirstTwoZero
    exact Or.inl ⟨firstToSecondOne, firstTwoToSecondTwo⟩
  · have secondTwoAtFirstOneZero :
        secondTwo.a * firstOne.b - secondTwo.b * firstOne.a = 0 := by
      exact eq_zero_of_mul_eq_zero_left firstFactorZero firstProductZero
    have firstToSecondTwo : firstOne.Parallel secondTwo :=
      (parallelIffFactorZero firstOne secondTwo).2 secondTwoAtFirstOneZero
    have secondTwoAtFirstTwoNonzero :
        secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a ≠ 0 := by
      intro factorZero
      have firstTwoToSecondTwo : firstTwo.Parallel secondTwo :=
        (parallelIffFactorZero firstTwo secondTwo).2 factorZero
      apply firstNotParallel
      exact line_parallel_trans firstToSecondTwo
        (Line.parallel_symm firstTwoToSecondTwo)
    have secondOneAtFirstTwoZero :
        secondOne.a * firstTwo.b - secondOne.b * firstTwo.a = 0 := by
      exact eq_zero_of_mul_eq_zero_right secondTwoAtFirstTwoNonzero
        secondProductZero
    have firstTwoToSecondOne : firstTwo.Parallel secondOne :=
      (parallelIffFactorZero firstTwo secondOne).2 secondOneAtFirstTwoZero
    exact Or.inr ⟨firstToSecondTwo, firstTwoToSecondOne⟩

/-- The center discriminant of a grammola is a nonzero scalar times the
square of its diagonal direction determinant. -/
theorem conic_centerDiscriminant [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
      associatedQuadrance twoNonzero).centerDiscriminant =
      -4 * lineNorm firstDiagonal * lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b) ^ 2 := by
  unfold Conic.centerDiscriminant conic conicD conicE conicF lineNorm
  ring1

/-- A valid grammola has a unique center because its quadratic center system
has nonzero discriminant. -/
theorem conic_centerDiscriminant_nonzero [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance : K)
    (presentation : Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance
      twoNonzero).centerDiscriminant ≠ 0 := by
  rw [conic_centerDiscriminant]
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero : (2 : K) * 2 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have negativeFourNonzero : (-4 : K) ≠ 0 := by
    intro negativeFourZero
    apply fourNonzero
    calc
      (4 : K) = -(-4) := by ring1
      _ = 0 := by rw [negativeFourZero]; ring1
  have determinantNonzero :
      firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b ≠ 0 := by
    exact presentation.notParallel
  have determinantSquareNonzero :
      (firstDiagonal.a * secondDiagonal.b -
        secondDiagonal.a * firstDiagonal.b) ^ 2 ≠ 0 := by
    simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero
      determinantNonzero determinantNonzero
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero negativeFourNonzero
        presentation.firstNonNull)
      presentation.secondNonNull)
    determinantSquareNonzero

/-- The recovery quadratic scales quadratically when all six conic
coefficients are rescaled. -/
theorem diagonalRecoveryValue_coefficientScale
    {source target : Conic K} {scale : K}
    (sameConic : Quadrola.CoefficientScale source target scale)
    (x y : K) :
    diagonalRecoveryValue source x y =
      scale ^ 2 * diagonalRecoveryValue target x y := by
  unfold diagonalRecoveryValue quadraticValue fourQuadraticDeterminant
  rw [sameConic.d, sameConic.e, sameConic.f]
  ring1

/-- The scalar in the diagonal recovery factorization is nonzero for a valid
grammola. -/
theorem diagonalRecoveryFactor_nonzero
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance : K)
    (presentation : Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    8 * lineNorm firstDiagonal * lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b) ≠ 0 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero : (2 : K) * 2 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have eightNonzero : (8 : K) ≠ 0 := by
    have productNonzero : (4 : K) * 2 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero fourNonzero twoNonzero
    simpa only [show (8 : K) = 4 * 2 by ring1] using productNonzero
  have dotNonzero :
      firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b ≠ 0 :=
    presentation.notPerpendicular
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero eightNonzero
        presentation.firstNonNull)
      presentation.secondNonNull)
    dotNonzero

/-- At the intersection of the diagonals, twice the conic evaluation is the
negative associated quadrance times the quadratic trace. -/
theorem center_evaluation_relation [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance : K)
    (presentation : Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    let center := lineIntersection firstDiagonal secondDiagonal
      presentation.notParallel
    let grammolaConic :=
      conic firstDiagonal secondDiagonal presentation.firstNonNull
        presentation.secondNonNull associatedQuadrance twoNonzero
    2 * grammolaConic.evaluate center =
      -associatedQuadrance * (grammolaConic.d + grammolaConic.f) := by
  dsimp only
  let center := lineIntersection firstDiagonal secondDiagonal
    presentation.notParallel
  have onFirst : firstDiagonal.Contains center :=
    lineIntersection_on_first firstDiagonal secondDiagonal
      presentation.notParallel
  have onSecond : secondDiagonal.Contains center :=
    lineIntersection_on_second firstDiagonal secondDiagonal
      presentation.notParallel
  unfold Line.Contains at onFirst onSecond
  rw [conic_evaluate, conic_trace]
  unfold clearedEvaluate lineValue
  rw [onFirst, onSecond]
  ring1

/-- Exercise 15.14: two valid grammola presentations of the same displayed
conic proportion have the same associated quadrance and the same unordered
pair of diagonal lines. -/
theorem exercise_15_14 [DecidableEq K]
    (firstDiagonal₁ firstDiagonal₂ secondDiagonal₁ secondDiagonal₂ :
      Line K)
    (firstAssociated secondAssociated : K)
    (firstPresentation :
      Presentation firstDiagonal₁ firstDiagonal₂ firstAssociated)
    (secondPresentation :
      Presentation secondDiagonal₁ secondDiagonal₂ secondAssociated)
    (twoNonzero : (2 : K) ≠ 0) (scale : K) (scaleNonzero : scale ≠ 0)
    (sameConic :
      Quadrola.CoefficientScale
        (conic firstDiagonal₁ firstDiagonal₂
          firstPresentation.firstNonNull firstPresentation.secondNonNull
          firstAssociated twoNonzero)
        (conic secondDiagonal₁ secondDiagonal₂
          secondPresentation.firstNonNull secondPresentation.secondNonNull
          secondAssociated twoNonzero)
        scale) :
    firstAssociated = secondAssociated ∧
      (((firstDiagonal₁.Equivalent secondDiagonal₁) ∧
          (firstDiagonal₂.Equivalent secondDiagonal₂)) ∨
        ((firstDiagonal₁.Equivalent secondDiagonal₂) ∧
          (firstDiagonal₂.Equivalent secondDiagonal₁))) := by
  let firstConic :=
    conic firstDiagonal₁ firstDiagonal₂ firstPresentation.firstNonNull
      firstPresentation.secondNonNull firstAssociated twoNonzero
  let secondConic :=
    conic secondDiagonal₁ secondDiagonal₂ secondPresentation.firstNonNull
      secondPresentation.secondNonNull secondAssociated twoNonzero
  let firstCenter := lineIntersection firstDiagonal₁ firstDiagonal₂
    firstPresentation.notParallel
  let secondCenter := lineIntersection secondDiagonal₁ secondDiagonal₂
    secondPresentation.notParallel
  have firstDiscriminantNonzero : firstConic.centerDiscriminant ≠ 0 := by
    unfold firstConic
    exact conic_centerDiscriminant_nonzero firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have firstIsCenter : firstConic.IsCenter firstCenter := by
    unfold firstConic firstCenter
    exact exercise_15_15 firstDiagonal₁ firstDiagonal₂ firstAssociated
      firstPresentation twoNonzero
  have secondIsCenter : secondConic.IsCenter secondCenter := by
    unfold secondConic secondCenter
    exact exercise_15_15 secondDiagonal₁ secondDiagonal₂ secondAssociated
      secondPresentation twoNonzero
  have secondCenterForFirst : firstConic.IsCenter secondCenter :=
    sameConic.isCenter secondCenter secondIsCenter
  have centersEqual : firstCenter = secondCenter := by
    have firstFormula := Conic.center_eq_centerPoint firstConic firstCenter
      firstDiscriminantNonzero firstIsCenter
    have secondFormula := Conic.center_eq_centerPoint firstConic secondCenter
      firstDiscriminantNonzero secondCenterForFirst
    exact firstFormula.trans secondFormula.symm
  have traceScale :
      firstConic.d + firstConic.f =
        scale * (secondConic.d + secondConic.f) := by
    rw [sameConic.d, sameConic.f]
    ring1
  have firstTraceNonzero : firstConic.d + firstConic.f ≠ 0 := by
    unfold firstConic
    exact conic_trace_nonzero firstDiagonal₁ firstDiagonal₂
      firstPresentation.firstNonNull firstPresentation.secondNonNull
      firstAssociated twoNonzero
  have firstCenterRelation :
      2 * firstConic.evaluate firstCenter =
        -firstAssociated * (firstConic.d + firstConic.f) := by
    unfold firstConic firstCenter
    exact center_evaluation_relation firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have secondCenterRelation :
      2 * secondConic.evaluate secondCenter =
        -secondAssociated * (secondConic.d + secondConic.f) := by
    unfold secondConic secondCenter
    exact center_evaluation_relation secondDiagonal₁ secondDiagonal₂
      secondAssociated secondPresentation twoNonzero
  have evaluationScale := sameConic.evaluate secondCenter
  have associatedTraceProducts :
      firstConic.d + firstConic.f |> fun trace => trace * firstAssociated =
        (firstConic.d + firstConic.f) * secondAssociated := by
    calc
      (firstConic.d + firstConic.f) * firstAssociated =
          -(-firstAssociated * (firstConic.d + firstConic.f)) := by ring1
      _ = -(2 * firstConic.evaluate firstCenter) := by
        rw [firstCenterRelation]
      _ = -(2 * firstConic.evaluate secondCenter) := by rw [centersEqual]
      _ = -(2 * (scale * secondConic.evaluate secondCenter)) := by
        rw [evaluationScale]
      _ = -scale *
          (2 * secondConic.evaluate secondCenter) := by ring1
      _ = -scale *
          (-secondAssociated * (secondConic.d + secondConic.f)) := by
            rw [secondCenterRelation]
      _ = (scale * (secondConic.d + secondConic.f)) *
          secondAssociated := by ring1
      _ = (firstConic.d + firstConic.f) * secondAssociated := by
        rw [traceScale]
  have associatedEqual : firstAssociated = secondAssociated :=
    eq_of_mul_eq_mul_left firstTraceNonzero associatedTraceProducts
  have firstRecoveryFactorNonzero :=
    diagonalRecoveryFactor_nonzero firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have secondRecoveryFactorNonzero :=
    diagonalRecoveryFactor_nonzero secondDiagonal₁ secondDiagonal₂
      secondAssociated secondPresentation twoNonzero
  let firstFactor :=
    8 * lineNorm firstDiagonal₁ * lineNorm firstDiagonal₂ *
      (firstDiagonal₁.a * firstDiagonal₂.a +
        firstDiagonal₁.b * firstDiagonal₂.b)
  let secondFactor :=
    8 * lineNorm secondDiagonal₁ * lineNorm secondDiagonal₂ *
      (secondDiagonal₁.a * secondDiagonal₂.a +
        secondDiagonal₁.b * secondDiagonal₂.b)
  let productScale := scale ^ 2 * secondFactor / firstFactor
  have productScaleNonzero : productScale ≠ 0 := by
    have scaleSquareNonzero : scale ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
    apply RFAP.ExplicitField.div_ne_zero
    · exact RFAP.ExplicitField.mul_ne_zero scaleSquareNonzero
        secondRecoveryFactorNonzero
    · exact firstRecoveryFactorNonzero
  have productScaleCancel : productScale * firstFactor =
      scale ^ 2 * secondFactor := by
    unfold productScale
    exact RFAP.ExplicitField.div_mul_cancel _ firstRecoveryFactorNonzero
  have directionProductsEqual (x y : K) :
      directionProduct firstDiagonal₁ firstDiagonal₂ x y =
        productScale *
          directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
    apply eq_of_mul_eq_mul_left firstRecoveryFactorNonzero
    calc
      firstFactor * directionProduct firstDiagonal₁ firstDiagonal₂ x y =
          diagonalRecoveryValue firstConic x y := by
            unfold firstFactor firstConic
            exact (diagonalRecoveryValue_conic firstDiagonal₁ firstDiagonal₂
              firstPresentation.firstNonNull firstPresentation.secondNonNull
              firstAssociated twoNonzero x y).symm
      _ = scale ^ 2 * diagonalRecoveryValue secondConic x y :=
        diagonalRecoveryValue_coefficientScale sameConic x y
      _ = scale ^ 2 *
          (secondFactor *
            directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
              unfold secondFactor secondConic
              rw [diagonalRecoveryValue_conic]
      _ = firstFactor *
          (productScale *
            directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
              calc
                scale ^ 2 *
                    (secondFactor *
                      directionProduct secondDiagonal₁ secondDiagonal₂ x y) =
                    (scale ^ 2 * secondFactor) *
                      directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
                        ring1
                _ = (productScale * firstFactor) *
                    directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
                      rw [productScaleCancel]
                _ = firstFactor *
                    (productScale *
                      directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
                        ring1
  have directionPairs := directionPairs_unique_of_product_scale
    firstDiagonal₁ firstDiagonal₂ secondDiagonal₁ secondDiagonal₂
      firstPresentation.notParallel productScale productScaleNonzero
      directionProductsEqual
  have firstOneContains : firstDiagonal₁.Contains firstCenter :=
    lineIntersection_on_first firstDiagonal₁ firstDiagonal₂
      firstPresentation.notParallel
  have firstTwoContains : firstDiagonal₂.Contains firstCenter :=
    lineIntersection_on_second firstDiagonal₁ firstDiagonal₂
      firstPresentation.notParallel
  have secondOneContains : secondDiagonal₁.Contains firstCenter := by
    rw [centersEqual]
    exact lineIntersection_on_first secondDiagonal₁ secondDiagonal₂
      secondPresentation.notParallel
  have secondTwoContains : secondDiagonal₂.Contains firstCenter := by
    rw [centersEqual]
    exact lineIntersection_on_second secondDiagonal₁ secondDiagonal₂
      secondPresentation.notParallel
  refine ⟨associatedEqual, ?_⟩
  rcases directionPairs with ordered | swapped
  · exact Or.inl ⟨
      line_equivalent_of_parallel_and_common_point firstDiagonal₁
        secondDiagonal₁ firstCenter ordered.1 firstOneContains
        secondOneContains,
      line_equivalent_of_parallel_and_common_point firstDiagonal₂
        secondDiagonal₂ firstCenter ordered.2 firstTwoContains
        secondTwoContains⟩
  · exact Or.inr ⟨
      line_equivalent_of_parallel_and_common_point firstDiagonal₁
        secondDiagonal₂ firstCenter swapped.1 firstOneContains
        secondTwoContains,
      line_equivalent_of_parallel_and_common_point firstDiagonal₂
        secondDiagonal₁ firstCenter swapped.2 firstTwoContains
        secondOneContains⟩

end Grammola

end DivineProportions
