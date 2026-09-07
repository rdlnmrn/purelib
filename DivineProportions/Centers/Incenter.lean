import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.AffineOrthocenter
import DivineProportions.Trigonometry.SpreadReflection
import DivineProportions.Trigonometry.VertexBisector

/-!
# Divine Proportions, §12.5: incenters

The triangle is represented by its three non-null, pairwise nonparallel side
lines.  A chosen bisector at each of the first two vertices is input data,
matching the constructive existence condition from Theorem 45.  Reflection
shows that those bisectors cannot be parallel.  Their intersection has equal
quadrance to all three side lines, and explicit square witnesses then select a
third vertex bisector through the same point.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Every point on a displayed vertex bisector has equal quadrance to the two
vertex lines. -/
theorem equal_pointLineQuadrance_of_isVertexBisector_contains
    [Nontrivial K] [DecidableEq K]
    (first second bisector : Line K)
    (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (isBisector : IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel)
    (point : Point K) (onBisector : bisector.Contains point) :
    pointLineQuadrance point first firstNonNull =
      pointLineQuadrance point second secondNonNull := by
  rcases normProduct_isNonzeroSquare_of_isVertexBisector
      first second bisector firstNonNull secondNonNull notParallel
      isBisector with ⟨root, _rootNonzero, rootEquation⟩
  have rootEquationReversed :
      root ^ 2 = lineNorm first * lineNorm second := rootEquation.symm
  rcases vertex_bisector_classification first second root firstNonNull
      secondNonNull notParallel rootEquationReversed bisector isBisector with
    positiveEquivalent | negativeEquivalent
  · apply (equal_pointLineQuadrance_iff_on_vertexBisector first second root
      firstNonNull secondNonNull notParallel rootEquationReversed point).2
    left
    exact line_contains_of_equivalent positiveEquivalent point onBisector
  · apply (equal_pointLineQuadrance_iff_on_vertexBisector first second root
      firstNonNull secondNonNull notParallel rootEquationReversed point).2
    right
    exact line_contains_of_equivalent negativeEquivalent point onBisector

/-- Theorem 88 (Incenter).  `thirdSide` and `secondSide` meet at the first
vertex, `thirdSide` and `firstSide` at the second, and `secondSide` and
`firstSide` at the third.  The result constructs the common point and a third
bisector containing it. -/
theorem incenter
    [Nontrivial K] [DecidableEq K]
    (firstSide secondSide thirdSide : Line K)
    (firstSideNonNull : ¬ firstSide.IsNull)
    (secondSideNonNull : ¬ secondSide.IsNull)
    (thirdSideNonNull : ¬ thirdSide.IsNull)
    (firstVertexNonparallel : ¬ thirdSide.Parallel secondSide)
    (secondVertexNonparallel : ¬ thirdSide.Parallel firstSide)
    (thirdVertexNonparallel : ¬ secondSide.Parallel firstSide)
    (twoNonzero : (2 : K) ≠ 0)
    (firstBisector secondBisector : Line K)
    (isFirstBisector :
      IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel)
    (isSecondBisector :
      IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel) :
    ∃ bisectorsNonparallel : ¬ firstBisector.Parallel secondBisector,
      let center := lineIntersection firstBisector secondBisector
        bisectorsNonparallel
      firstBisector.Contains center ∧
        secondBisector.Contains center ∧
        ∃ thirdBisector : Line K,
          IsVertexBisector secondSide firstSide thirdBisector
              secondSideNonNull firstSideNonNull thirdVertexNonparallel ∧
            thirdBisector.Contains center := by
  rcases isFirstBisector with
    ⟨firstBisectorNonNull, firstBisectorContainsVertex,
      firstEqualSpreads⟩
  rcases isSecondBisector with
    ⟨secondBisectorNonNull, secondBisectorContainsVertex,
      secondEqualSpreads⟩
  have firstSidesNotEquivalent : ¬ thirdSide.Equivalent secondSide := by
    intro equivalent
    exact firstVertexNonparallel (line_parallel_of_equivalent equivalent)
  have secondSidesNotEquivalent : ¬ thirdSide.Equivalent firstSide := by
    intro equivalent
    exact secondVertexNonparallel (line_parallel_of_equivalent equivalent)
  let firstVertex := lineIntersection thirdSide secondSide
    firstVertexNonparallel
  let secondVertex := lineIntersection thirdSide firstSide
    secondVertexNonparallel
  have firstReflected :
      (reflectLine firstBisector thirdSide firstBisectorNonNull).Equivalent
        secondSide := by
    apply (spread_reflection firstBisector thirdSide secondSide firstVertex
      firstBisectorNonNull thirdSideNonNull secondSideNonNull
      firstBisectorContainsVertex
      (lineIntersection_on_first thirdSide secondSide firstVertexNonparallel)
      (lineIntersection_on_second thirdSide secondSide firstVertexNonparallel)
      firstSidesNotEquivalent).2
    exact firstEqualSpreads
  have secondReflected :
      (reflectLine secondBisector thirdSide secondBisectorNonNull).Equivalent
        firstSide := by
    apply (spread_reflection secondBisector thirdSide firstSide secondVertex
      secondBisectorNonNull thirdSideNonNull firstSideNonNull
      secondBisectorContainsVertex
      (lineIntersection_on_first thirdSide firstSide secondVertexNonparallel)
      (lineIntersection_on_second thirdSide firstSide secondVertexNonparallel)
      secondSidesNotEquivalent).2
    exact secondEqualSpreads
  have bisectorsNonparallel : ¬ firstBisector.Parallel secondBisector := by
    intro parallelBisectors
    have reflectedParallel := reflectLine_parallel_of_parallel_mirrors
      firstBisector secondBisector thirdSide firstBisectorNonNull
      secondBisectorNonNull parallelBisectors
    have secondToFirstReflected :
        secondSide.Parallel
          (reflectLine firstBisector thirdSide firstBisectorNonNull) :=
      Line.parallel_symm (line_parallel_of_equivalent firstReflected)
    have firstReflectedToSecondReflected :
        (reflectLine firstBisector thirdSide firstBisectorNonNull).Parallel
          (reflectLine secondBisector thirdSide secondBisectorNonNull) :=
      reflectedParallel
    have secondReflectedToFirst :
        (reflectLine secondBisector thirdSide secondBisectorNonNull).Parallel
          firstSide := line_parallel_of_equivalent secondReflected
    apply thirdVertexNonparallel
    exact line_parallel_trans
      (line_parallel_trans secondToFirstReflected
        firstReflectedToSecondReflected)
      secondReflectedToFirst
  refine ⟨bisectorsNonparallel, ?_⟩
  dsimp only
  let center := lineIntersection firstBisector secondBisector
    bisectorsNonparallel
  have centerOnFirst : firstBisector.Contains center :=
    lineIntersection_on_first firstBisector secondBisector
      bisectorsNonparallel
  have centerOnSecond : secondBisector.Contains center :=
    lineIntersection_on_second firstBisector secondBisector
      bisectorsNonparallel
  have firstBisectorAgain :
      IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel :=
    ⟨firstBisectorNonNull, firstBisectorContainsVertex, firstEqualSpreads⟩
  have secondBisectorAgain :
      IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel :=
    ⟨secondBisectorNonNull, secondBisectorContainsVertex, secondEqualSpreads⟩
  have equalThirdSecond :=
    equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel firstBisectorAgain center centerOnFirst
  have equalThirdFirst :=
    equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel secondBisectorAgain center centerOnSecond
  have equalSecondFirst :
      pointLineQuadrance center secondSide secondSideNonNull =
        pointLineQuadrance center firstSide firstSideNonNull :=
    equalThirdSecond.symm.trans equalThirdFirst
  rcases normProduct_isNonzeroSquare_of_isVertexBisector
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel firstBisectorAgain with
    ⟨firstRoot, _firstRootNonzero, firstRootEquation⟩
  rcases normProduct_isNonzeroSquare_of_isVertexBisector
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel secondBisectorAgain with
    ⟨secondRoot, _secondRootNonzero, secondRootEquation⟩
  let thirdRoot := firstRoot * secondRoot / lineNorm thirdSide
  have thirdSideNormCancel :
      lineNorm thirdSide * (lineNorm thirdSide)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel _ thirdSideNonNull
  have thirdRootEquation :
      thirdRoot ^ 2 = lineNorm secondSide * lineNorm firstSide := by
    unfold thirdRoot
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (firstRoot * secondRoot * (lineNorm thirdSide)⁻¹) ^ 2 =
          firstRoot ^ 2 * secondRoot ^ 2 *
            (lineNorm thirdSide)⁻¹ ^ 2 := by ring1
      _ = (lineNorm thirdSide * lineNorm secondSide) *
          (lineNorm thirdSide * lineNorm firstSide) *
            (lineNorm thirdSide)⁻¹ ^ 2 := by
              rw [← firstRootEquation, ← secondRootEquation]
      _ = lineNorm secondSide * lineNorm firstSide *
          (lineNorm thirdSide * (lineNorm thirdSide)⁻¹) ^ 2 := by ring1
      _ = lineNorm secondSide * lineNorm firstSide := by
        rw [thirdSideNormCancel]
        ring1
  have centerOnThirdCandidate :=
    (equal_pointLineQuadrance_iff_on_vertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      thirdRootEquation center).1 equalSecondFirst
  refine ⟨centerOnFirst, centerOnSecond, ?_⟩
  rcases centerOnThirdCandidate with centerOnPositive | centerOnNegative
  · let thirdBisector := positiveVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull thirdVertexNonparallel
    refine ⟨thirdBisector, ?_, centerOnPositive⟩
    exact positiveVertexBisector_isVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      twoNonzero thirdRootEquation
  · let thirdBisector := negativeVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull thirdVertexNonparallel
    refine ⟨thirdBisector, ?_, centerOnNegative⟩
    exact negativeVertexBisector_isVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      twoNonzero thirdRootEquation

end DivineProportions
