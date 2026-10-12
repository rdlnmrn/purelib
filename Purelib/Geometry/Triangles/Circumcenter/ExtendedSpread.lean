module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Null
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Trigonometry.Spread
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane (Line)

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, §12.1: the Extended spread law

The book proves the result by introducing the three side midpoints and then
solving an auxiliary triangle.  Here the same finite content is exposed by a
stronger polynomial lemma: a triangle with a displayed common-quadrance center
satisfies `quadrea * circumquadrance = Q₁ * Q₂ * Q₃`.  Combining that identity
with Quadrea spread gives the final reciprocal, while the ordinary Spread law
gives the other two equalities.

No generic-position choice among the midpoints is needed, and all divisions
are guarded by explicit nonzero certificates.
-/

namespace Purelib.Geometry.Triangles.Circumcenter.ExtendedSpread

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Three radial dot products satisfying the Gram identity determine the circumquadrea product.

The identity is stated in independent scalar variables so normalization retains the dot products as scalar atoms.
-/
private theorem circumquadrea_of_gram_identity
    (q a b c : K) (gram : q ^ 3 + 2 * a * b * c - q * (a ^ 2 + b ^ 2 + c ^ 2) = 0) :
    QuadTriple.Basic.archimedesFunction (2 * (q - c)) (2 * (q - b)) (2 * (q - a)) * q =
      2 * (q - c) * (2 * (q - b)) * (2 * (q - a)) := by
  calc
    QuadTriple.Basic.archimedesFunction (2 * (q - c)) (2 * (q - b)) (2 * (q - a)) * q =
        2 * (q - c) * (2 * (q - b)) * (2 * (q - a)) +
          4 * (q ^ 3 + 2 * a * b * c - q * (a ^ 2 + b ^ 2 + c ^ 2)) := by
      unfold QuadTriple.Basic.archimedesFunction
      ring1
    _ = 2 * (q - c) * (2 * (q - b)) * (2 * (q - a)) := by
      rw [gram]
      ring1

/-- The finite polynomial identity behind the Extended spread law. It only asks for a displayed point having the same
quadrance `circumquadranceValue` from all three vertices. -/
theorem circumquadrea_identity
    (first second third center : Plane.Point K) (circumquadranceValue : K)
    (firstRadius : Quadrance.quadrance center first = circumquadranceValue)
    (secondRadius : Quadrance.quadrance center second = circumquadranceValue)
    (thirdRadius : Quadrance.quadrance center third = circumquadranceValue) :
    Quadrea.Basic.quadrea first second third * circumquadranceValue =
      Quadrance.quadrance second third * Quadrance.quadrance first third *
        Quadrance.quadrance first second := by
  let ax := first.x - center.x
  let ay := first.y - center.y
  let bx := second.x - center.x
  let bY := second.y - center.y
  let cx := third.x - center.x
  let cy := third.y - center.y
  let firstSecondDot := ax * bx + ay * bY
  let firstThirdDot := ax * cx + ay * cy
  let secondThirdDot := bx * cx + bY * cy
  have firstNorm : ax ^ 2 + ay ^ 2 = circumquadranceValue := by
    simpa only [Quadrance.quadrance, ax, ay] using firstRadius
  have secondNorm : bx ^ 2 + bY ^ 2 = circumquadranceValue := by
    simpa only [Quadrance.quadrance, bx, bY] using secondRadius
  have thirdNorm : cx ^ 2 + cy ^ 2 = circumquadranceValue := by
    simpa only [Quadrance.quadrance, cx, cy] using thirdRadius
  have gramIdentity :
      circumquadranceValue ^ 3 +
          2 * firstSecondDot * firstThirdDot * secondThirdDot -
          circumquadranceValue *
            (firstSecondDot ^ 2 + firstThirdDot ^ 2 +
              secondThirdDot ^ 2) = 0 := by
    calc
      circumquadranceValue ^ 3 +
            2 * firstSecondDot * firstThirdDot * secondThirdDot -
            circumquadranceValue *
              (firstSecondDot ^ 2 + firstThirdDot ^ 2 +
                secondThirdDot ^ 2) =
          (ax ^ 2 + ay ^ 2) * (bx ^ 2 + bY ^ 2) *
              (cx ^ 2 + cy ^ 2) +
            2 * firstSecondDot * firstThirdDot * secondThirdDot -
            (ax ^ 2 + ay ^ 2) * secondThirdDot ^ 2 -
            (bx ^ 2 + bY ^ 2) * firstThirdDot ^ 2 -
            (cx ^ 2 + cy ^ 2) * firstSecondDot ^ 2 := by
              rw [firstNorm, secondNorm, thirdNorm]
              ring1
      _ = 0 := by
        unfold firstSecondDot firstThirdDot secondThirdDot
        ring1
  have firstQuadrance :
      Quadrance.quadrance second third =
        2 * (circumquadranceValue - secondThirdDot) := by
    calc
      Quadrance.quadrance second third =
          (bx ^ 2 + bY ^ 2) + (cx ^ 2 + cy ^ 2) -
            2 * secondThirdDot := by
              unfold Quadrance.quadrance bx bY cx cy secondThirdDot
              ring1
      _ = 2 * (circumquadranceValue - secondThirdDot) := by
        rw [secondNorm, thirdNorm]
        ring1
  have secondQuadrance :
      Quadrance.quadrance first third =
        2 * (circumquadranceValue - firstThirdDot) := by
    calc
      Quadrance.quadrance first third =
          (ax ^ 2 + ay ^ 2) + (cx ^ 2 + cy ^ 2) -
            2 * firstThirdDot := by
              unfold Quadrance.quadrance ax ay cx cy firstThirdDot
              ring1
      _ = 2 * (circumquadranceValue - firstThirdDot) := by
        rw [firstNorm, thirdNorm]
        ring1
  have thirdQuadrance :
      Quadrance.quadrance first second =
        2 * (circumquadranceValue - firstSecondDot) := by
    calc
      Quadrance.quadrance first second =
          (ax ^ 2 + ay ^ 2) + (bx ^ 2 + bY ^ 2) -
            2 * firstSecondDot := by
              unfold Quadrance.quadrance ax ay bx bY firstSecondDot
              ring1
      _ = 2 * (circumquadranceValue - firstSecondDot) := by
        rw [firstNorm, secondNorm]
        ring1
  unfold Quadrea.Basic.quadrea
  rw [firstQuadrance, secondQuadrance, thirdQuadrance]
  exact circumquadrea_of_gram_identity
    circumquadranceValue firstSecondDot firstThirdDot secondThirdDot gramIdentity

/-- Theorem 82 (Extended spread law). The three spreads are taken at `first`, `second`, and `third`; their corresponding
quadrances are the opposite sides. `center` is a displayed circumcenter and its quadrance to `first` is the book's `K`.
-/
theorem extended_spread_law
    [Nontrivial K] [DecidableEq K]
    (first second third center : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNonNull :
      ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalFirstSecond :
      Quadrance.quadrance center first = Quadrance.quadrance center second)
    (equalSecondThird :
      Quadrance.quadrance center second = Quadrance.quadrance center third) :
    let firstSecondReversedNonNull :
        ¬ (Incidence.lineThrough second first firstSecondDistinct.symm).IsNull := by
      exact Line.Null.reversedLine_nonNull
        first second firstSecondDistinct firstSecondNonNull
    let firstThirdReversedNonNull :
        ¬ (Incidence.lineThrough third first firstThirdDistinct.symm).IsNull := by
      exact Line.Null.reversedLine_nonNull
        first third firstThirdDistinct firstThirdNonNull
    let secondThirdReversedNonNull :
        ¬ (Incidence.lineThrough third second secondThirdDistinct.symm).IsNull := by
      exact Line.Null.reversedLine_nonNull
        second third secondThirdDistinct secondThirdNonNull
    let s₁ := Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough first third firstThirdDistinct)
      firstSecondNonNull firstThirdNonNull
    let s₂ := Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
      (Incidence.lineThrough second third secondThirdDistinct)
      firstSecondReversedNonNull secondThirdNonNull
    let s₃ := Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
      (Incidence.lineThrough third second secondThirdDistinct.symm)
      firstThirdReversedNonNull secondThirdReversedNonNull
    let q₁ := Quadrance.quadrance second third
    let q₂ := Quadrance.quadrance first third
    let q₃ := Quadrance.quadrance first second
    let circumquadranceValue := Quadrance.quadrance center first
    s₁ / q₁ = s₂ / q₂ ∧
      s₂ / q₂ = s₃ / q₃ ∧
      s₃ / q₃ = 1 / (4 * circumquadranceValue) := by
  dsimp only
  let firstSecondReversedNonNull :
      ¬ (Incidence.lineThrough second first firstSecondDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first second firstSecondDistinct firstSecondNonNull
  let firstThirdReversedNonNull :
      ¬ (Incidence.lineThrough third first firstThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first third firstThirdDistinct firstThirdNonNull
  let secondThirdReversedNonNull :
      ¬ (Incidence.lineThrough third second secondThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      second third secondThirdDistinct secondThirdNonNull
  let s₁ := Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
    (Incidence.lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  let s₂ := Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
    (Incidence.lineThrough second third secondThirdDistinct)
    firstSecondReversedNonNull secondThirdNonNull
  let s₃ := Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
    (Incidence.lineThrough third second secondThirdDistinct.symm)
    firstThirdReversedNonNull secondThirdReversedNonNull
  let q₁ := Quadrance.quadrance second third
  let q₂ := Quadrance.quadrance first third
  let q₃ := Quadrance.quadrance first second
  let circumquadranceValue := Quadrance.quadrance center first
  have q₁Nonzero : q₁ ≠ 0 :=
    TriangleRatios.quadrance_ne_zero_of_line_nonNull second third secondThirdDistinct
      secondThirdNonNull
  have q₂Nonzero : q₂ ≠ 0 :=
    TriangleRatios.quadrance_ne_zero_of_line_nonNull first third firstThirdDistinct
      firstThirdNonNull
  have q₃Nonzero : q₃ ≠ 0 :=
    TriangleRatios.quadrance_ne_zero_of_line_nonNull first second firstSecondDistinct
      firstSecondNonNull
  have productNonzero : q₁ * q₂ * q₃ ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero
      (Algebra.Field.ExplicitField.mul_ne_zero q₁Nonzero q₂Nonzero) q₃Nonzero
  have circumIdentity :
      Quadrea.Basic.quadrea first second third * circumquadranceValue = q₁ * q₂ * q₃ := by
    apply circumquadrea_identity first second third center
      circumquadranceValue
    · exact rfl
    · exact equalFirstSecond.symm
    · exact (equalFirstSecond.trans equalSecondThird).symm
  have circumquadranceNonzero : circumquadranceValue ≠ 0 := by
    intro circumquadranceZero
    apply productNonzero
    calc
      q₁ * q₂ * q₃ =
          Quadrea.Basic.quadrea first second third * circumquadranceValue :=
            circumIdentity.symm
      _ = 0 := by rw [circumquadranceZero]; ring1
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have fourCircumquadranceNonzero :
      4 * circumquadranceValue ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero fourNonzero circumquadranceNonzero
  have spreadRatios := Trigonometry.Spread.spread_law first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull secondThirdNonNull twoNonzero
  change s₁ / q₁ = s₂ / q₂ ∧ s₂ / q₂ = s₃ / q₃ at spreadRatios
  have reverseSpreadAtThird := Spread.spread_reverse_both
    third first second firstThirdDistinct.symm secondThirdDistinct.symm
    firstThirdReversedNonNull secondThirdReversedNonNull
  have areaAtThird := Trigonometry.Spread.quadrea_spread first second third
    firstThirdDistinct secondThirdDistinct
    firstThirdNonNull secondThirdNonNull
  rw [← reverseSpreadAtThird] at areaAtThird
  change Quadrea.Basic.quadrea first second third = 4 * q₁ * q₂ * s₃ at areaAtThird
  have reciprocalCross : s₃ * (4 * circumquadranceValue) = 1 * q₃ := by
    have factorNonzero : q₁ * q₂ ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero q₁Nonzero q₂Nonzero
    apply ExplicitField.eq_of_mul_eq_mul_left factorNonzero
    calc
      (q₁ * q₂) * (s₃ * (4 * circumquadranceValue)) =
          (4 * q₁ * q₂ * s₃) * circumquadranceValue := by ring1
      _ = Quadrea.Basic.quadrea first second third * circumquadranceValue := by
        rw [← areaAtThird]
      _ = q₁ * q₂ * q₃ := circumIdentity
      _ = (q₁ * q₂) * (1 * q₃) := by ring1
  change s₁ / q₁ = s₂ / q₂ ∧
    s₂ / q₂ = s₃ / q₃ ∧ s₃ / q₃ = 1 / (4 * circumquadranceValue)
  refine ⟨spreadRatios.1, spreadRatios.2, ?_⟩
  exact Ratio.ratio_eq_of_cross_product q₃Nonzero
    fourCircumquadranceNonzero reciprocalCross

/-- The quotient chain of Theorem 82 can always be cleared back to the three finite identities `sᵢ(4K) = Qᵢ`. This is
the form used by the following reader exercises. -/
theorem extended_spread_law_cross_products
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (fourCircumquadranceNonzero : 4 * circumquadranceValue ≠ 0)
    (extendedRatios :
      s₁ / q₁ = s₂ / q₂ ∧
        s₂ / q₂ = s₃ / q₃ ∧
        s₃ / q₃ = 1 / (4 * circumquadranceValue)) :
    s₁ * (4 * circumquadranceValue) = q₁ ∧
      s₂ * (4 * circumquadranceValue) = q₂ ∧
      s₃ * (4 * circumquadranceValue) = q₃ := by
  have firstRatio : s₁ / q₁ = 1 / (4 * circumquadranceValue) :=
    extendedRatios.1.trans
      (extendedRatios.2.1.trans extendedRatios.2.2)
  have secondRatio : s₂ / q₂ = 1 / (4 * circumquadranceValue) :=
    extendedRatios.2.1.trans extendedRatios.2.2
  have firstCross := Ratio.cross_product_of_ratio_eq q₁Nonzero
    fourCircumquadranceNonzero firstRatio
  have secondCross := Ratio.cross_product_of_ratio_eq q₂Nonzero
    fourCircumquadranceNonzero secondRatio
  have thirdCross := Ratio.cross_product_of_ratio_eq q₃Nonzero
    fourCircumquadranceNonzero extendedRatios.2.2
  simpa only [one_mul] using And.intro firstCross
    (And.intro secondCross thirdCross)

/-- Exercise 12.2 before division: both expressions become equal after multiplication by the displayed circumquadrance.
-/
theorem exercise_12_2_cleared
    (q₁ q₂ q₃ s₁ s₂ s₃ area circumquadranceValue : K)
    (circumquadrea :
      area * circumquadranceValue = q₁ * q₂ * q₃)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    area * circumquadranceValue = q₁ * q₂ * q₃ ∧
      area * circumquadranceValue =
        64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := by
  constructor
  · exact circumquadrea
  · calc
      area * circumquadranceValue = q₁ * q₂ * q₃ := circumquadrea
      _ = (s₁ * (4 * circumquadranceValue)) *
          (s₂ * (4 * circumquadranceValue)) *
          (s₃ * (4 * circumquadranceValue)) := by
            rw [firstExtended, secondExtended, thirdExtended]
      _ = 64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := by ring1

/-- Exercise 12.2 in the book's exact quotient form: `A = Q₁Q₂Q₃/K = 64K²s₁s₂s₃`. -/
theorem exercise_12_2
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ area circumquadranceValue : K)
    (circumquadranceNonzero : circumquadranceValue ≠ 0)
    (circumquadrea :
      area * circumquadranceValue = q₁ * q₂ * q₃)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    area = (q₁ * q₂ * q₃) / circumquadranceValue ∧
      area = 64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃ := by
  have cleared := exercise_12_2_cleared q₁ q₂ q₃ s₁ s₂ s₃ area
    circumquadranceValue circumquadrea firstExtended secondExtended
    thirdExtended
  constructor
  · have ratio := Ratio.ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) circumquadranceNonzero
      (by simpa only [mul_one] using circumquadrea)
    simpa only [Purelib.Algebra.Field.ExplicitField.div_one] using ratio
  · apply ExplicitField.eq_of_mul_eq_mul_left circumquadranceNonzero
    calc
      circumquadranceValue * area =
          area * circumquadranceValue := by ring1
      _ = 64 * circumquadranceValue ^ 3 * s₁ * s₂ * s₃ := cleared.2
      _ = circumquadranceValue *
          (64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃) := by ring1

/-- The two- and three-spread sums multiplied by four times the circumquadrance equal the corresponding side-quadrance
sums.

The triangle is noncollinear, its sides are non-null and two is nonzero. -/
theorem exercise_12_3_cleared
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    (s₁ + s₂) * (4 * circumquadranceValue) = q₁ + q₂ ∧
      (s₁ + s₂ + s₃) * (4 * circumquadranceValue) =
        q₁ + q₂ + q₃ := by
  constructor
  · calc
      (s₁ + s₂) * (4 * circumquadranceValue) =
          s₁ * (4 * circumquadranceValue) +
            s₂ * (4 * circumquadranceValue) := by ring1
      _ = q₁ + q₂ := by rw [firstExtended, secondExtended]
  · calc
      (s₁ + s₂ + s₃) * (4 * circumquadranceValue) =
          s₁ * (4 * circumquadranceValue) +
            s₂ * (4 * circumquadranceValue) +
            s₃ * (4 * circumquadranceValue) := by ring1
      _ = q₁ + q₂ + q₃ := by
        rw [firstExtended, secondExtended, thirdExtended]

/-- The two- and three-spread sums are the corresponding side-quadrance sums divided by four times the circumquadrance.

The triangle is noncollinear, its sides are non-null and two is nonzero, so the common denominator is nonzero. -/
theorem exercise_12_3
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ s₁ s₂ s₃ circumquadranceValue : K)
    (fourCircumquadranceNonzero : 4 * circumquadranceValue ≠ 0)
    (firstExtended : s₁ * (4 * circumquadranceValue) = q₁)
    (secondExtended : s₂ * (4 * circumquadranceValue) = q₂)
    (thirdExtended : s₃ * (4 * circumquadranceValue) = q₃) :
    s₁ + s₂ = (q₁ + q₂) / (4 * circumquadranceValue) ∧
      s₁ + s₂ + s₃ =
        (q₁ + q₂ + q₃) / (4 * circumquadranceValue) := by
  have cleared := exercise_12_3_cleared q₁ q₂ q₃ s₁ s₂ s₃
    circumquadranceValue firstExtended secondExtended thirdExtended
  constructor
  · have ratio := Ratio.ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) fourCircumquadranceNonzero
      (by simpa only [mul_one] using cleared.1)
    simpa only [Purelib.Algebra.Field.ExplicitField.div_one] using ratio
  · have ratio := Ratio.ratio_eq_of_cross_product
      (one_ne_zero : (1 : K) ≠ 0) fourCircumquadranceNonzero
      (by simpa only [mul_one] using cleared.2)
    simpa only [Purelib.Algebra.Field.ExplicitField.div_one] using ratio

end Purelib.Geometry.Triangles.Circumcenter.ExtendedSpread

end
