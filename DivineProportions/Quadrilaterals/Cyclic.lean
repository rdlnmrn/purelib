import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.Circumcenter
import DivineProportions.Circles.EqualProducts

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed quadrilateral: four distinct points, no three collinear.
The source's cyclic-rotation and reversal conventions are theorem invariances,
not an equality quotient on this executable record. -/
structure Quadrilateral (K : Type*) [RFAP.ExplicitField K] where
  first : Point K
  second : Point K
  third : Point K
  fourth : Point K
  firstSecondDistinct : first ≠ second
  firstThirdDistinct : first ≠ third
  firstFourthDistinct : first ≠ fourth
  secondThirdDistinct : second ≠ third
  secondFourthDistinct : second ≠ fourth
  thirdFourthDistinct : third ≠ fourth
  firstSecondThirdNoncollinear : ¬ Collinear first second third
  firstSecondFourthNoncollinear : ¬ Collinear first second fourth
  firstThirdFourthNoncollinear : ¬ Collinear first third fourth
  secondThirdFourthNoncollinear : ¬ Collinear second third fourth

namespace Quadrilateral

/-- A cyclic quadrilateral carries one explicit finite circle presentation
containing all four displayed points. -/
def IsCyclic (quadrilateral : Quadrilateral K) : Prop :=
  ∃ circle : Conic K, ∃ center : Point K, ∃ circleQuadrance : K,
    circle.IsCirclePresentation center circleQuadrance ∧
      circle.Contains quadrilateral.first ∧
      circle.Contains quadrilateral.second ∧
      circle.Contains quadrilateral.third ∧
      circle.Contains quadrilateral.fourth

/-- The three-by-three determinant used to expand the book's displayed
four-by-four determinant. -/
def determinantThree
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K) : K :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₃₂) -
    a₁₂ * (a₂₁ * a₃₃ - a₂₃ * a₃₁) +
    a₁₃ * (a₂₁ * a₃₂ - a₂₂ * a₃₁)

/-- The first coordinate in each row of the cyclicity determinant. -/
def circleRowNorm (point : Point K) : K := point.x ^ 2 + point.y ^ 2

/-- The source's determinant with rows `[xᵢ²+yᵢ², xᵢ, yᵢ, 1]`, expanded
along its first row. -/
def coordinateCircleDeterminant
    (first second third fourth : Point K) : K :=
  circleRowNorm first *
      determinantThree second.x second.y 1 third.x third.y 1
        fourth.x fourth.y 1 -
    first.x *
      determinantThree (circleRowNorm second) second.y 1
        (circleRowNorm third) third.y 1
        (circleRowNorm fourth) fourth.y 1 +
    first.y *
      determinantThree (circleRowNorm second) second.x 1
        (circleRowNorm third) third.x 1
        (circleRowNorm fourth) fourth.x 1 -
    determinantThree (circleRowNorm second) second.x second.y
      (circleRowNorm third) third.x third.y
      (circleRowNorm fourth) fourth.x fourth.y

/-- Translating the printed four-by-four determinant to the fourth point
gives the already useful quadrance/determinant expression from Chapter 16. -/
theorem coordinateCircleDeterminant_eq_fourPointCircleDeterminant
    (first second third fourth : Point K) :
    coordinateCircleDeterminant first second third fourth =
      Conic.fourPointCircleDeterminant first second third fourth := by
  unfold coordinateCircleDeterminant circleRowNorm determinantThree
    Conic.fourPointCircleDeterminant pointDeterminant quadrance
  ring1

/-- The four-point determinant expanded using quadrances from an arbitrary
displayed center.  This identity does not assume that any radii are equal. -/
theorem fourPointCircleDeterminant_center_formula
    (first second third fourth center : Point K) :
    Conic.fourPointCircleDeterminant first second third fourth =
      quadrance first center * pointDeterminant fourth second third -
        quadrance second center * pointDeterminant fourth first third +
        quadrance third center * pointDeterminant fourth first second -
        quadrance fourth center * pointDeterminant first second third := by
  unfold Conic.fourPointCircleDeterminant pointDeterminant quadrance
  ring1

/-- If the first three points have a common displayed radius, the four-point
determinant is their noncollinearity determinant times the fourth point's
circle-power. -/
theorem fourPointCircleDeterminant_eq_radius_difference
    (first second third fourth center : Point K) (circleQuadrance : K)
    (firstRadius : quadrance first center = circleQuadrance)
    (secondRadius : quadrance second center = circleQuadrance)
    (thirdRadius : quadrance third center = circleQuadrance) :
    Conic.fourPointCircleDeterminant first second third fourth =
      pointDeterminant first second third *
        (circleQuadrance - quadrance fourth center) := by
  rw [fourPointCircleDeterminant_center_formula, firstRadius, secondRadius,
    thirdRadius]
  unfold pointDeterminant
  ring1

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

/-- Forward direction of Theorem 109: four points on one displayed circle
make the printed coordinate determinant vanish. -/
theorem coordinateCircleDeterminant_eq_zero_of_isCyclic
    (quadrilateral : Quadrilateral K) (cyclic : quadrilateral.IsCyclic) :
    coordinateCircleDeterminant quadrilateral.first quadrilateral.second
      quadrilateral.third quadrilateral.fourth = 0 := by
  rcases cyclic with
    ⟨circle, center, circleQuadrance, presentation, firstOnCircle,
      secondOnCircle, thirdOnCircle, fourthOnCircle⟩
  rw [coordinateCircleDeterminant_eq_fourPointCircleDeterminant]
  exact Conic.fourPointCircleDeterminant_eq_zero circle center
    circleQuadrance presentation quadrilateral.first quadrilateral.second
    quadrilateral.third quadrilateral.fourth firstOnCircle secondOnCircle
    thirdOnCircle fourthOnCircle

/-- Converse direction of Theorem 109: the determinant equation constructs
the normalized circle through the first three vertices and proves that it also
contains the fourth. -/
theorem isCyclic_of_coordinateCircleDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilateral K) (twoNonzero : (2 : K) ≠ 0)
    (determinantZero :
      coordinateCircleDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third quadrilateral.fourth = 0) :
    quadrilateral.IsCyclic := by
  let center := circumcenterPoint quadrilateral.first quadrilateral.second
    quadrilateral.third quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct
      quadrilateral.firstSecondThirdNoncollinear
  let circleQuadrance := quadrance center quadrilateral.first
  rcases circumcenter quadrilateral.first quadrilateral.second
      quadrilateral.third quadrilateral.firstSecondDistinct
      quadrilateral.firstThirdDistinct quadrilateral.secondThirdDistinct
      quadrilateral.firstSecondThirdNoncollinear twoNonzero with
    ⟨_centerOnSecondThirdBisector, _centerOnFirstThirdBisector,
      _centerOnFirstSecondBisector, firstSecondRadius, secondThirdRadius⟩
  have firstRadius :
      quadrance quadrilateral.first center = circleQuadrance := by
    unfold circleQuadrance
    exact quadrance_symm quadrilateral.first center
  have secondRadius :
      quadrance quadrilateral.second center = circleQuadrance := by
    calc
      quadrance quadrilateral.second center =
          quadrance center quadrilateral.second :=
        quadrance_symm quadrilateral.second center
      _ = quadrance center quadrilateral.first := firstSecondRadius.symm
      _ = circleQuadrance := rfl
  have thirdRadius :
      quadrance quadrilateral.third center = circleQuadrance := by
    calc
      quadrance quadrilateral.third center =
          quadrance center quadrilateral.third :=
        quadrance_symm quadrilateral.third center
      _ = quadrance center quadrilateral.second := secondThirdRadius.symm
      _ = quadrance center quadrilateral.first := firstSecondRadius.symm
      _ = circleQuadrance := rfl
  have translatedDeterminantZero :
      Conic.fourPointCircleDeterminant quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth = 0 := by
    calc
      Conic.fourPointCircleDeterminant quadrilateral.first
          quadrilateral.second quadrilateral.third quadrilateral.fourth =
        coordinateCircleDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third quadrilateral.fourth :=
        (coordinateCircleDeterminant_eq_fourPointCircleDeterminant
          quadrilateral.first quadrilateral.second quadrilateral.third
          quadrilateral.fourth).symm
      _ = 0 := determinantZero
  have baseDeterminantNonzero :
      pointDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third ≠ 0 := by
    intro baseDeterminantZero
    exact quadrilateral.firstSecondThirdNoncollinear
      ((collinear_iff_pointDeterminant_eq_zero quadrilateral.first
        quadrilateral.second quadrilateral.third).2 baseDeterminantZero)
  have clearedFourthRadius :
      pointDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third *
        (circleQuadrance - quadrance quadrilateral.fourth center) = 0 := by
    calc
      pointDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third *
          (circleQuadrance - quadrance quadrilateral.fourth center) =
        Conic.fourPointCircleDeterminant quadrilateral.first
          quadrilateral.second quadrilateral.third quadrilateral.fourth :=
        (fourPointCircleDeterminant_eq_radius_difference
          quadrilateral.first quadrilateral.second quadrilateral.third
          quadrilateral.fourth center circleQuadrance firstRadius
          secondRadius thirdRadius).symm
      _ = 0 := translatedDeterminantZero
  have fourthDifferenceZero :
      circleQuadrance - quadrance quadrilateral.fourth center = 0 :=
    eq_zero_of_mul_eq_zero_left baseDeterminantNonzero clearedFourthRadius
  have fourthRadius :
      quadrance quadrilateral.fourth center = circleQuadrance := by
    calc
      quadrance quadrilateral.fourth center =
          circleQuadrance -
            (circleQuadrance - quadrance quadrilateral.fourth center) := by
        ring1
      _ = circleQuadrance := by rw [fourthDifferenceZero]; ring1
  let circle := Conic.circleConic center circleQuadrance
  have presentation :
      circle.IsCirclePresentation center circleQuadrance :=
    Conic.circleConic_isCirclePresentation center circleQuadrance
  refine ⟨circle, center, circleQuadrance, presentation, ?_, ?_, ?_, ?_⟩
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.first circleQuadrance presentation).2 firstRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.second circleQuadrance presentation).2 secondRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.third circleQuadrance presentation).2 thirdRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.fourth circleQuadrance presentation).2 fourthRadius

/-- Theorem 109 (Cyclic quadrilateral): a displayed quadrilateral is cyclic
exactly when the source's four-by-four coordinate determinant vanishes. -/
theorem cyclic_quadrilateral [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilateral K) (twoNonzero : (2 : K) ≠ 0) :
    quadrilateral.IsCyclic ↔
      coordinateCircleDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third quadrilateral.fourth = 0 := by
  constructor
  · exact coordinateCircleDeterminant_eq_zero_of_isCyclic quadrilateral
  · exact isCyclic_of_coordinateCircleDeterminant_eq_zero quadrilateral
      twoNonzero

end Quadrilateral

end DivineProportions
