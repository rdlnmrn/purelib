module
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Curves.Plane.Lemniscate.Basic
import Purelib.Curves.Plane.Lemniscate.Tangent.Conic
public import Purelib.Curves.Plane.Lemniscate.Tangent.Discriminant
import Purelib.Curves.Plane.Lemniscate.Tangent.Line
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Algebra.Field.Finite.Eleven
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Plane.Conic.QuadraticPart
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Geometry.Plane

@[expose] public section

/-!
# Divine Proportions, Examples 19.9--19.10

The radical data in Example 19.9 is expressed through explicit square-root
witnesses.  Example 19.10 is a closed `F₁₁` calculation.  Its printed
grammola quadrance is arithmetically incorrect: the displayed diagonal lines
give `K=1`, not `K=9`; both the countercheck and corrected identity are proved.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterNineteenLemniscate

open Purelib.Algebra

namespace ChapterNineteenLemniscateExamples

variable {K : Type*} [ExplicitField K]

/-- Expand the weighted squares 6(3x + 2y + 4)² + 10(x + 3y + 6)² into their six conic coefficients. -/
private theorem two_square_expansion (x y : K) :
    (3 * x + 2 * y + 4) ^ 2 * 6 +
        (1 * x + 3 * y + 6) ^ 2 * 10 =
      (6 * 3 ^ 2 + 10 * 1 ^ 2) * x ^ 2 +
        (6 * (2 * 3 * 2) + 10 * (2 * 1 * 3)) * x * y +
        (6 * 2 ^ 2 + 10 * 3 ^ 2) * y ^ 2 +
        (6 * (2 * 3 * 4) + 10 * (2 * 1 * 6)) * x +
        (6 * (2 * 2 * 4) + 10 * (2 * 3 * 6)) * y +
        (6 * 4 ^ 2 + 10 * 6 ^ 2) := by
  ring1

/-- Collect the scaled six-coefficient conic expression as five times its evaluation plus one. -/
private theorem scaled_conic_expansion (x y : K) :
    (5 * 4) * x ^ 2 + (5 * 0) * x * y +
        (5 * 3) * y ^ 2 + (5 * 0) * x +
        (5 * 1) * y + (5 * 3 + 1) =
      5 * (4 * x ^ 2 + 0 * x * y + 3 * y ^ 2 +
        0 * x + 1 * y + 3) + 1 := by
  ring1

namespace ExampleNineteenNine

/-- The source point `[sqrt(5)/4,sqrt(3)/4]`. -/
def point (rootFive rootThree : K) : Geometry.Plane.Point K :=
  ⟨rootFive / 4, rootThree / 4⟩

/-- The displayed parabolic tangent conic
`⟨1:2√15:15:-4√5:-4√3:3⟩`. -/
def displayedTangentConic [Nontrivial K]
    (rootFive rootThree : K) : Curves.Plane.Conic K where
  d := 1
  e := 2 * (rootFive * rootThree)
  f := 15
  a := -4 * rootFive
  b := -4 * rootThree
  c := 3
  quadratic_nonzero := Or.inl one_ne_zero

/-- Example 19.9's exact algebra.  The point is on both curves, and eight
times the source tangent-conic construction is exactly the printed
coefficient record. -/
theorem example_19_9 [Nontrivial K]
    (rootFive rootThree : K)
    (rootFiveSquared : rootFive ^ 2 = 5)
    (rootThreeSquared : rootThree ^ 2 = 3)
    (fourNonzero : (4 : K) ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) :
    let basePoint := point rootFive rootThree
    Curves.Plane.Lemniscate.Contains 1 basePoint ∧
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains basePoint ∧
      ∃ secondOrder : Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt 1 basePoint,
        let tangent := Curves.Plane.Lemniscate.Tangent.Conic.tangentConic 1 basePoint secondOrder
        let displayed := displayedTangentConic rootFive rootThree
        8 * tangent.d = displayed.d ∧
          8 * tangent.e = displayed.e ∧
          8 * tangent.f = displayed.f ∧
          8 * tangent.a = displayed.a ∧
          8 * tangent.b = displayed.b ∧
          8 * tangent.c = displayed.c ∧
          tangent.centerDiscriminant = 0 := by
  dsimp only
  let inverseFour : K := (4 : K)⁻¹
  have cancel : (4 : K) * inverseFour = 1 :=
    ExplicitField.mul_inv_cancel 4 fourNonzero
  have cancelSquare : (16 : K) * inverseFour ^ 2 = 1 := by
    calc
      (16 : K) * inverseFour ^ 2 = (4 * inverseFour) ^ 2 := by ring1
      _ = 1 := by rw [cancel]; ring1
  have cancelCube : (64 : K) * inverseFour ^ 3 = 1 := by
    calc
      (64 : K) * inverseFour ^ 3 = (4 * inverseFour) ^ 3 := by ring1
      _ = 1 := by rw [cancel]; ring1
  have scaledFiveSquare :
      (rootFive * inverseFour) ^ 2 = 5 * inverseFour ^ 2 := by
    calc
      (rootFive * inverseFour) ^ 2 =
          rootFive ^ 2 * inverseFour ^ 2 := by ring1
      _ = 5 * inverseFour ^ 2 := by rw [rootFiveSquared]
  have scaledThreeSquare :
      (rootThree * inverseFour) ^ 2 = 3 * inverseFour ^ 2 := by
    calc
      (rootThree * inverseFour) ^ 2 =
          rootThree ^ 2 * inverseFour ^ 2 := by ring1
      _ = 3 * inverseFour ^ 2 := by rw [rootThreeSquared]
  let basePoint := point rootFive rootThree
  have onLemniscate : Curves.Plane.Lemniscate.Contains 1 basePoint := by
    unfold Curves.Plane.Lemniscate.Contains Curves.Plane.Lemniscate.evaluate basePoint
      point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      ((rootFive * inverseFour) ^ 2 +
          (rootThree * inverseFour) ^ 2) ^ 2 -
        2 * 1 * ((rootFive * inverseFour) ^ 2 -
          (rootThree * inverseFour) ^ 2) = 0
    rw [scaledFiveSquare, scaledThreeSquare]
    simp only [mul_one]
    calc
      ((5 : K) * inverseFour ^ 2 + 3 * inverseFour ^ 2) ^ 2 -
          2 * (5 * inverseFour ^ 2 - 3 * inverseFour ^ 2) =
        4 * inverseFour ^ 2 *
          (16 * inverseFour ^ 2 - 1) := by ring1
      _ = 0 := by rw [cancelSquare]; ring1
  have discriminantZero :
      Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantValue 1 basePoint = 0 := by
    unfold Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantValue basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * ((rootFive * inverseFour) ^ 2 -
        (rootThree * inverseFour) ^ 2) - 1 = 0
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) * (5 * inverseFour ^ 2 - 3 * inverseFour ^ 2) - 1 =
          16 * inverseFour ^ 2 - 1 := by ring1
      _ = 0 := by rw [cancelSquare]; ring1
  have onDiscriminant :
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains basePoint :=
        by
    unfold Curves.Plane.Conic.Contains
    rw [Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic_evaluate]
    exact discriminantZero
  have tangentDScaled :
      8 * Curves.Plane.Lemniscate.Tangent.Conic.tangentD 1 basePoint = (1 : K) := by
    unfold Curves.Plane.Lemniscate.Tangent.Conic.tangentD basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * (3 * (rootFive * inverseFour) ^ 2 +
        (rootThree * inverseFour) ^ 2 - 1) = 1
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) *
          (3 * (5 * inverseFour ^ 2) + 3 * inverseFour ^ 2 - 1) =
        9 * (16 * inverseFour ^ 2) - 8 := by ring1
      _ = 1 := by rw [cancelSquare]; ring1
  have tangentDNonzero : Curves.Plane.Lemniscate.Tangent.Conic.tangentD 1 basePoint ≠ 0 := by
    intro tangentDZero
    have oneZero : (1 : K) = 0 := by
      calc
        (1 : K) = 8 * Curves.Plane.Lemniscate.Tangent.Conic.tangentD 1 basePoint :=
          tangentDScaled.symm
        _ = 0 := by rw [tangentDZero]; ring1
    exact one_ne_zero oneZero
  let secondOrder : Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt 1 basePoint :=
    Or.inl tangentDNonzero
  let tangent := Curves.Plane.Lemniscate.Tangent.Conic.tangentConic 1 basePoint secondOrder
  let displayed := displayedTangentConic rootFive rootThree
  have dEquation : 8 * tangent.d = displayed.d := by
    exact tangentDScaled
  have eEquation : 8 * tangent.e = displayed.e := by
    unfold tangent displayed Curves.Plane.Lemniscate.Tangent.Conic.tangentConic
      Curves.Plane.Lemniscate.Tangent.Conic.tangentE
      displayedTangentConic basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * (4 * (rootFive * inverseFour) *
        (rootThree * inverseFour)) = 2 * (rootFive * rootThree)
    calc
      (8 : K) * (4 * (rootFive * inverseFour) *
          (rootThree * inverseFour)) =
        2 * (rootFive * rootThree) *
          (16 * inverseFour ^ 2) := by ring1
      _ = 2 * (rootFive * rootThree) := by rw [cancelSquare]; ring1
  have fEquation : 8 * tangent.f = displayed.f := by
    unfold tangent displayed Curves.Plane.Lemniscate.Tangent.Conic.tangentConic
      Curves.Plane.Lemniscate.Tangent.Conic.tangentF
      displayedTangentConic basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * ((rootFive * inverseFour) ^ 2 +
        3 * (rootThree * inverseFour) ^ 2 + 1) = 15
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) *
          (5 * inverseFour ^ 2 + 3 * (3 * inverseFour ^ 2) + 1) =
        7 * (16 * inverseFour ^ 2) + 8 := by ring1
      _ = 15 := by rw [cancelSquare]; ring1
  have aEquation : 8 * tangent.a = displayed.a := by
    unfold tangent displayed Curves.Plane.Lemniscate.Tangent.Conic.tangentConic displayedTangentConic
      basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * (-4 * (rootFive * inverseFour) *
        ((rootFive * inverseFour) ^ 2 +
          (rootThree * inverseFour) ^ 2)) = -4 * rootFive
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) * (-4 * (rootFive * inverseFour) *
          (5 * inverseFour ^ 2 + 3 * inverseFour ^ 2)) =
        -4 * rootFive * (64 * inverseFour ^ 3) := by ring1
      _ = -4 * rootFive := by rw [cancelCube]; ring1
  have bEquation : 8 * tangent.b = displayed.b := by
    unfold tangent displayed Curves.Plane.Lemniscate.Tangent.Conic.tangentConic displayedTangentConic
      basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * (-4 * (rootThree * inverseFour) *
        ((rootFive * inverseFour) ^ 2 +
          (rootThree * inverseFour) ^ 2)) = -4 * rootThree
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) * (-4 * (rootThree * inverseFour) *
          (5 * inverseFour ^ 2 + 3 * inverseFour ^ 2)) =
        -4 * rootThree * (64 * inverseFour ^ 3) := by ring1
      _ = -4 * rootThree := by rw [cancelCube]; ring1
  have cEquation : 8 * tangent.c = displayed.c := by
    unfold tangent displayed Curves.Plane.Lemniscate.Tangent.Conic.tangentConic displayedTangentConic
      basePoint point
    simp only [ExplicitField.div_eq_mul_inv]
    change
      8 * (3 * 1 * ((rootFive * inverseFour) ^ 2 -
        (rootThree * inverseFour) ^ 2)) = 3
    rw [scaledFiveSquare, scaledThreeSquare]
    simp only [mul_one]
    calc
      (8 : K) * (3 * (5 * inverseFour ^ 2 - 3 * inverseFour ^ 2)) =
          3 * (16 * inverseFour ^ 2) := by ring1
      _ = 3 := by rw [cancelSquare]; exact mul_one 3
  have determinantZero : tangent.centerDiscriminant = 0 := by
    rw [Curves.Plane.Lemniscate.Tangent.Discriminant.tangentConic_discriminant_factor 1 basePoint
      onLemniscate]
    rw [discriminantZero]
    ring1
  exact ⟨onLemniscate, onDiscriminant, secondOrder,
    dEquation, eEquation, fEquation, aEquation, bEquation, cEquation,
    determinantZero⟩

end ExampleNineteenNine

namespace ExampleNineteenTen

open Purelib.Algebra.Field.Finite.Eleven

/-- The executable field with eleven elements used in the tangent computations. -/
abbrev F₁₁ := Finite.Eleven.Element

/-- The lemniscate point (1, 4) over the field with eleven elements. -/
def point14 : Geometry.Plane.Point F₁₁ := ⟨1, 4⟩
/-- The lemniscate point (1, −4) over the field with eleven elements. -/
def point1Neg4 : Geometry.Plane.Point F₁₁ := ⟨1, -4⟩
/-- The lemniscate point (−1, 4) over the field with eleven elements. -/
def pointNeg14 : Geometry.Plane.Point F₁₁ := ⟨-1, 4⟩
/-- The lemniscate point (−1, −4) over the field with eleven elements. -/
def pointNeg1Neg4 : Geometry.Plane.Point F₁₁ := ⟨-1, -4⟩
/-- The lemniscate point (0, 3) over the field with eleven elements. -/
def point03 : Geometry.Plane.Point F₁₁ := ⟨0, 3⟩

/-- The displayed tangent line at (1, 4), with coefficients (4, 7, 1). -/
def tangentLine14 : Geometry.Plane.Line F₁₁ where
  a := 4
  b := 7
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed tangent conic at (1, 4), with coefficients (3, 10, 1, 7, 6, 9). -/
def tangentConic14 : Curves.Plane.Conic F₁₁ where
  d := 3
  e := 10
  f := 1
  a := 7
  b := 6
  c := 9
  quadratic_nonzero := Or.inl (by decide)

/-- The displayed tangent line at (0, 3), with coefficients (0, 8, 9). -/
def tangentLine03 : Geometry.Plane.Line F₁₁ where
  a := 0
  b := 8
  c := 9
  direction_nonzero := Or.inr (by decide)

/-- The displayed tangent conic at (0, 3), with coefficients (4, 0, 3, 0, 1, 3). -/
def tangentConic03 : Curves.Plane.Conic F₁₁ where
  d := 4
  e := 0
  f := 3
  a := 0
  b := 1
  c := 3
  quadratic_nonzero := Or.inl (by decide)

/-- The directrix with coefficients (10, 5, 1) for the tangent parabola at (1, 4). -/
def directrix14 : Geometry.Plane.Line F₁₁ where
  a := 10
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The focus (9, 9) for the tangent parabola at (1, 4). -/
def focus14 : Geometry.Plane.Point F₁₁ := ⟨9, 9⟩

/-- The first displayed grammola diagonal at (0, 3), with coefficients (3, 2, 4). -/
def firstDiagonal03 : Geometry.Plane.Line F₁₁ where
  a := 3
  b := 2
  c := 4
  direction_nonzero := Or.inl (by decide)

/-- The second displayed grammola diagonal at (0, 3), with coefficients (1, 3, 6). -/
def secondDiagonal03 : Geometry.Plane.Line F₁₁ where
  a := 1
  b := 3
  c := 6
  direction_nonzero := Or.inl (by decide)

/-- Eight is nonzero over the field with eleven elements. -/
private theorem eightNonzero : (8 : F₁₁) ≠ 0 := by decide

/-- The lemniscate has a nonzero first-order tangent coefficient at (1, 4). -/
theorem firstOrder14 : Curves.Plane.Lemniscate.Tangent.Line.IsNonSingularAt 1 point14 := by
  unfold Curves.Plane.Lemniscate.Tangent.Line.IsNonSingularAt
    Curves.Plane.Lemniscate.Tangent.Line.tangentA
    Curves.Plane.Lemniscate.Tangent.Line.tangentB point14
  decide

/-- The lemniscate has a nonzero second-order tangent coefficient at (1, 4). -/
theorem secondOrder14 : Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt 1 point14 := by
  unfold Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt
    Curves.Plane.Lemniscate.Tangent.Conic.tangentD
    Curves.Plane.Lemniscate.Tangent.Conic.tangentE Curves.Plane.Lemniscate.Tangent.Conic.tangentF
      point14
  decide

/-- The lemniscate has a nonzero first-order tangent coefficient at (0, 3). -/
theorem firstOrder03 : Curves.Plane.Lemniscate.Tangent.Line.IsNonSingularAt 1 point03 := by
  unfold Curves.Plane.Lemniscate.Tangent.Line.IsNonSingularAt
    Curves.Plane.Lemniscate.Tangent.Line.tangentA
    Curves.Plane.Lemniscate.Tangent.Line.tangentB point03
  decide

/-- The lemniscate has a nonzero second-order tangent coefficient at (0, 3). -/
theorem secondOrder03 : Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt 1 point03 := by
  unfold Curves.Plane.Lemniscate.Tangent.Conic.IsSecondOrderNonSingularAt
    Curves.Plane.Lemniscate.Tangent.Conic.tangentD
    Curves.Plane.Lemniscate.Tangent.Conic.tangentE Curves.Plane.Lemniscate.Tangent.Conic.tangentF
      point03
  decide

/-- The four intersections `[+-1,+-4]` printed in Figure 19.11. -/
theorem displayed_intersections :
    let eightNonzero : (8 : F₁₁) ≠ 0 := by decide
    Curves.Plane.Lemniscate.Contains 1 point14 ∧
      Curves.Plane.Lemniscate.Contains 1 point1Neg4 ∧
      Curves.Plane.Lemniscate.Contains 1 pointNeg14 ∧
      Curves.Plane.Lemniscate.Contains 1 pointNeg1Neg4 ∧
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains point14 ∧
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains point1Neg4 ∧
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains pointNeg14 ∧
      (Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic 1 eightNonzero).Contains
        pointNeg1Neg4 := by
  dsimp only
  unfold Curves.Plane.Lemniscate.Contains Curves.Plane.Lemniscate.evaluate
    Curves.Plane.Conic.Contains
    Curves.Plane.Lemniscate.Tangent.Discriminant.discriminantConic Curves.Plane.Conic.evaluate
      point14 point1Neg4
    pointNeg14 pointNeg1Neg4
  decide

/-- At `[1,4]` the construction gives the printed line up to scale `4`, and
the printed conic up to scale `6`. -/
theorem tangent_data_at_14 :
    (Curves.Plane.Lemniscate.Tangent.Line.tangentLine 1 point14 firstOrder14).Equivalent tangentLine14 ∧
      let tangent := Curves.Plane.Lemniscate.Tangent.Conic.tangentConic 1 point14 secondOrder14
      tangent.d = 6 * tangentConic14.d ∧
        tangent.e = 6 * tangentConic14.e ∧
        tangent.f = 6 * tangentConic14.f ∧
        tangent.a = 6 * tangentConic14.a ∧
        tangent.b = 6 * tangentConic14.b ∧
        tangent.c = 6 * tangentConic14.c := by
  unfold Geometry.Plane.Line.Equivalent Curves.Plane.Lemniscate.Tangent.Line.tangentLine
    Curves.Plane.Lemniscate.Tangent.Line.tangentA
    Curves.Plane.Lemniscate.Tangent.Line.tangentB tangentLine14
  dsimp only
  constructor
  · exact ⟨by decide, by decide, by decide⟩
  · unfold Curves.Plane.Lemniscate.Tangent.Conic.tangentConic
      Curves.Plane.Lemniscate.Tangent.Conic.tangentD
      Curves.Plane.Lemniscate.Tangent.Conic.tangentE
        Curves.Plane.Lemniscate.Tangent.Conic.tangentF tangentConic14 point14
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The directrix and focus printed for the tangent conic at `[1,4]` give an
exact focus/directrix presentation. -/
theorem tangentConic14_parabola :
    tangentConic14.IsParabolaPresentation focus14 directrix14 := by
  refine ⟨
    { directrixNonNull := ?_
      focusNotOnDirectrix := ?_
      scale := 1
      scaleNonzero := by decide
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  · unfold Geometry.Plane.Line.IsNull directrix14
    decide
  · unfold Geometry.Plane.Line.Contains focus14 directrix14
    decide
  all_goals dsimp only [tangentConic14, directrix14, focus14, Line.Basic.lineNorm]
  all_goals decide

/-- At `[0,3]` the source construction gives the displayed line and twice
the displayed tangent conic. -/
theorem tangent_data_at_03 :
    (Curves.Plane.Lemniscate.Tangent.Line.tangentLine 1 point03 firstOrder03).Equivalent tangentLine03 ∧
      let tangent := Curves.Plane.Lemniscate.Tangent.Conic.tangentConic 1 point03 secondOrder03
      tangent.d = 2 * tangentConic03.d ∧
        tangent.e = 2 * tangentConic03.e ∧
        tangent.f = 2 * tangentConic03.f ∧
        tangent.a = 2 * tangentConic03.a ∧
        tangent.b = 2 * tangentConic03.b ∧
        tangent.c = 2 * tangentConic03.c := by
  unfold Geometry.Plane.Line.Equivalent Curves.Plane.Lemniscate.Tangent.Line.tangentLine
    Curves.Plane.Lemniscate.Tangent.Line.tangentA
    Curves.Plane.Lemniscate.Tangent.Line.tangentB tangentLine03
  dsimp only
  constructor
  · exact ⟨by decide, by decide, by decide⟩
  · unfold Curves.Plane.Lemniscate.Tangent.Conic.tangentConic
      Curves.Plane.Lemniscate.Tangent.Conic.tangentD
      Curves.Plane.Lemniscate.Tangent.Conic.tangentE
        Curves.Plane.Lemniscate.Tangent.Conic.tangentF tangentConic03 point03
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The first displayed grammola diagonal has nonzero norm. -/
private theorem firstDiagonalNonNull : ¬ firstDiagonal03.IsNull := by
  unfold Geometry.Plane.Line.IsNull firstDiagonal03
  decide

/-- The second displayed grammola diagonal has nonzero norm. -/
private theorem secondDiagonalNonNull : ¬ secondDiagonal03.IsNull := by
  unfold Geometry.Plane.Line.IsNull secondDiagonal03
  decide

/-- Sum of quadrances to the two diagonal lines printed in Example 19.10. -/
def grammolaQuadranceSum (candidate : Geometry.Plane.Point F₁₁) : F₁₁ :=
  let firstDiagonalNonNull : ¬ firstDiagonal03.IsNull := by
    unfold Geometry.Plane.Line.IsNull firstDiagonal03
    decide
  let secondDiagonalNonNull : ¬ secondDiagonal03.IsNull := by
    unfold Geometry.Plane.Line.IsNull secondDiagonal03
    decide
  Line.Quadrance.pointLineQuadrance candidate firstDiagonal03 firstDiagonalNonNull +
    Line.Quadrance.pointLineQuadrance candidate secondDiagonal03 secondDiagonalNonNull

/-- The sum of quadrances to the two displayed diagonals equals five times the tangent-conic evaluation plus one.

The exact characteristic-eleven identity determines the corrected associated quadrance of the grammola. -/
private theorem grammola_polynomial_identity (candidate : Geometry.Plane.Point F₁₁) :
    grammolaQuadranceSum candidate =
      5 * tangentConic03.evaluate candidate + 1 := by
  have firstNorm : Line.Basic.lineNorm firstDiagonal03 = (2 : F₁₁) := by
    unfold Line.Basic.lineNorm firstDiagonal03
    decide
  have secondNorm : Line.Basic.lineNorm secondDiagonal03 = (10 : F₁₁) := by
    unfold Line.Basic.lineNorm secondDiagonal03
    decide
  have inverseTwo : (2 : F₁₁)⁻¹ = 6 := by decide
  have inverseTen : (10 : F₁₁)⁻¹ = 10 := by decide
  have dCoefficient :
      (6 : F₁₁) * 3 ^ 2 + 10 * 1 ^ 2 = 5 * 4 := by decide
  have eCoefficient :
      (6 : F₁₁) * (2 * 3 * 2) + 10 * (2 * 1 * 3) = 5 * 0 := by
    decide
  have fCoefficient :
      (6 : F₁₁) * 2 ^ 2 + 10 * 3 ^ 2 = 5 * 3 := by decide
  have aCoefficient :
      (6 : F₁₁) * (2 * 3 * 4) + 10 * (2 * 1 * 6) = 5 * 0 := by
    decide
  have bCoefficient :
      (6 : F₁₁) * (2 * 2 * 4) + 10 * (2 * 3 * 6) = 5 * 1 := by
    decide
  have cCoefficient :
      (6 : F₁₁) * 4 ^ 2 + 10 * 6 ^ 2 = 5 * 3 + 1 := by decide
  unfold grammolaQuadranceSum
  dsimp only
  rw [Line.Quadrance.pointLineQuadrance_formula, Line.Quadrance.pointLineQuadrance_formula,
    firstNorm, secondNorm]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [inverseTwo, inverseTen]
  dsimp only [firstDiagonal03, secondDiagonal03, tangentConic03]
  unfold Curves.Plane.Conic.evaluate
  calc
    (3 * candidate.x + 2 * candidate.y + 4) ^ 2 * 6 +
          (1 * candidate.x + 3 * candidate.y + 6) ^ 2 * 10 =
        (6 * 3 ^ 2 + 10 * 1 ^ 2) * candidate.x ^ 2 +
          (6 * (2 * 3 * 2) + 10 * (2 * 1 * 3)) *
            candidate.x * candidate.y +
          (6 * 2 ^ 2 + 10 * 3 ^ 2) * candidate.y ^ 2 +
          (6 * (2 * 3 * 4) + 10 * (2 * 1 * 6)) * candidate.x +
          (6 * (2 * 2 * 4) + 10 * (2 * 3 * 6)) * candidate.y +
          (6 * 4 ^ 2 + 10 * 6 ^ 2) :=
      two_square_expansion candidate.x candidate.y
    _ = (5 * 4) * candidate.x ^ 2 +
          (5 * 0) * candidate.x * candidate.y +
          (5 * 3) * candidate.y ^ 2 +
          (5 * 0) * candidate.x + (5 * 1) * candidate.y + (5 * 3 + 1) := by
      rw [dCoefficient, eCoefficient, fCoefficient, aCoefficient,
        bCoefficient, cCoefficient]
    _ = 5 *
        (4 * candidate.x ^ 2 + 0 * candidate.x * candidate.y +
          3 * candidate.y ^ 2 + 0 * candidate.x +
          1 * candidate.y + 3) + 1 :=
      scaled_conic_expansion candidate.x candidate.y

/-- Corrected grammola statement: the printed conic is exactly the locus
where the sum of quadrances to the two printed diagonals is `1`. -/
theorem tangentConic03_grammola_corrected (candidate : Geometry.Plane.Point F₁₁) :
    tangentConic03.Contains candidate ↔ grammolaQuadranceSum candidate = 1 := by
  have identity := grammola_polynomial_identity candidate
  unfold Curves.Plane.Conic.Contains
  constructor
  · intro onConic
    calc
      grammolaQuadranceSum candidate =
          5 * tangentConic03.evaluate candidate + 1 := identity
      _ = 1 := by rw [onConic, mul_zero]; exact zero_add 1
  · intro quadranceEquation
    have productWithOne :
        0 + 1 = 5 * tangentConic03.evaluate candidate + 1 := by
      calc
        0 + 1 = 1 := zero_add 1
        _ = grammolaQuadranceSum candidate := quadranceEquation.symm
        _ = 5 * tangentConic03.evaluate candidate + 1 := identity
    have productZero : 5 * tangentConic03.evaluate candidate = 0 :=
      (add_right_cancel productWithOne).symm
    by_cases evaluationZero : tangentConic03.evaluate candidate = 0
    · exact evaluationZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero (by decide : (5 : F₁₁) ≠ 0)
          evaluationZero) productZero)

/-- The source's `K=9` is false already at its base point: the point lies on
the tangent conic, while its quadrance sum is `1`, not `9`. -/
theorem printed_grammola_quadrance_countercheck :
    tangentConic03.Contains point03 ∧
      grammolaQuadranceSum point03 = 1 ∧
      grammolaQuadranceSum point03 ≠ 9 := by
  have onConic : tangentConic03.Contains point03 := by
    unfold Curves.Plane.Conic.Contains tangentConic03 Curves.Plane.Conic.evaluate point03
    decide
  have sumOne := (tangentConic03_grammola_corrected point03).1 onConic
  exact ⟨onConic, sumOne, by rw [sumOne]; decide⟩

/-- Example 19.10, with its valid data and corrected grammola constant. -/
theorem example_19_10 :
    Curves.Plane.Lemniscate.Contains 1 point14 ∧
      (Curves.Plane.Lemniscate.Tangent.Line.tangentLine 1 point14 firstOrder14).Equivalent tangentLine14 ∧
      tangentConic14.IsParabolaPresentation focus14 directrix14 ∧
      Curves.Plane.Lemniscate.Contains 1 point03 ∧
      (Curves.Plane.Lemniscate.Tangent.Line.tangentLine 1 point03 firstOrder03).Equivalent tangentLine03 ∧
      tangentConic03.Contains point03 ∧
      grammolaQuadranceSum point03 = 1 ∧
      grammolaQuadranceSum point03 ≠ 9 := by
  have point14On : Curves.Plane.Lemniscate.Contains 1 point14 := displayed_intersections.1
  have point03On : Curves.Plane.Lemniscate.Contains 1 point03 := by
    unfold Curves.Plane.Lemniscate.Contains Curves.Plane.Lemniscate.evaluate point03
    decide
  exact ⟨point14On, tangent_data_at_14.1, tangentConic14_parabola,
    point03On, tangent_data_at_03.1,
    printed_grammola_quadrance_countercheck.1,
    printed_grammola_quadrance_countercheck.2.1,
    printed_grammola_quadrance_countercheck.2.2⟩

end ExampleNineteenTen

end ChapterNineteenLemniscateExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterNineteenLemniscate
