import DivineProportions.Curves.Lemniscate
import DivineProportions.Algebra.FieldEleven

/-!
# Divine Proportions, Examples 19.9--19.10

The radical data in Example 19.9 is expressed through explicit square-root
witnesses.  Example 19.10 is a closed `F₁₁` calculation.  Its printed
grammola quadrance is arithmetically incorrect: the displayed diagonal lines
give `K=1`, not `K=9`; both the countercheck and corrected identity are proved.
-/

namespace DivineProportions

namespace ChapterNineteenLemniscateExamples

variable {K : Type*} [RFAP.ExplicitField K]

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

private theorem scaled_conic_expansion (x y : K) :
    (5 * 4) * x ^ 2 + (5 * 0) * x * y +
        (5 * 3) * y ^ 2 + (5 * 0) * x +
        (5 * 1) * y + (5 * 3 + 1) =
      5 * (4 * x ^ 2 + 0 * x * y + 3 * y ^ 2 +
        0 * x + 1 * y + 3) + 1 := by
  ring1

namespace ExampleNineteenNine

/-- The source point `[sqrt(5)/4,sqrt(3)/4]`. -/
def point (rootFive rootThree : K) : Point K :=
  ⟨rootFive / 4, rootThree / 4⟩

/-- The displayed parabolic tangent conic
`⟨1:2√15:15:-4√5:-4√3:3⟩`. -/
def displayedTangentConic [Nontrivial K]
    (rootFive rootThree : K) : Conic K where
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
    Lemniscate.Contains 1 basePoint ∧
      (Lemniscate.discriminantConic 1 eightNonzero).Contains basePoint ∧
      ∃ secondOrder : Lemniscate.IsSecondOrderNonSingularAt 1 basePoint,
        let tangent := Lemniscate.tangentConic 1 basePoint secondOrder
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
    RFAP.ExplicitField.mul_inv_cancel 4 fourNonzero
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
  have onLemniscate : Lemniscate.Contains 1 basePoint := by
    unfold Lemniscate.Contains Lemniscate.evaluate basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
      Lemniscate.discriminantValue 1 basePoint = 0 := by
    unfold Lemniscate.discriminantValue basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    change
      8 * ((rootFive * inverseFour) ^ 2 -
        (rootThree * inverseFour) ^ 2) - 1 = 0
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) * (5 * inverseFour ^ 2 - 3 * inverseFour ^ 2) - 1 =
          16 * inverseFour ^ 2 - 1 := by ring1
      _ = 0 := by rw [cancelSquare]; ring1
  have onDiscriminant :
      (Lemniscate.discriminantConic 1 eightNonzero).Contains basePoint := by
    unfold Conic.Contains
    rw [Lemniscate.discriminantConic_evaluate]
    exact discriminantZero
  have tangentDScaled :
      8 * Lemniscate.tangentD 1 basePoint = (1 : K) := by
    unfold Lemniscate.tangentD basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    change
      8 * (3 * (rootFive * inverseFour) ^ 2 +
        (rootThree * inverseFour) ^ 2 - 1) = 1
    rw [scaledFiveSquare, scaledThreeSquare]
    calc
      (8 : K) *
          (3 * (5 * inverseFour ^ 2) + 3 * inverseFour ^ 2 - 1) =
        9 * (16 * inverseFour ^ 2) - 8 := by ring1
      _ = 1 := by rw [cancelSquare]; ring1
  have tangentDNonzero : Lemniscate.tangentD 1 basePoint ≠ 0 := by
    intro tangentDZero
    have oneZero : (1 : K) = 0 := by
      calc
        (1 : K) = 8 * Lemniscate.tangentD 1 basePoint :=
          tangentDScaled.symm
        _ = 0 := by rw [tangentDZero]; ring1
    exact one_ne_zero oneZero
  let secondOrder : Lemniscate.IsSecondOrderNonSingularAt 1 basePoint :=
    Or.inl tangentDNonzero
  let tangent := Lemniscate.tangentConic 1 basePoint secondOrder
  let displayed := displayedTangentConic rootFive rootThree
  have dEquation : 8 * tangent.d = displayed.d := by
    exact tangentDScaled
  have eEquation : 8 * tangent.e = displayed.e := by
    unfold tangent displayed Lemniscate.tangentConic Lemniscate.tangentE
      displayedTangentConic basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
    unfold tangent displayed Lemniscate.tangentConic Lemniscate.tangentF
      displayedTangentConic basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
    unfold tangent displayed Lemniscate.tangentConic displayedTangentConic
      basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
    unfold tangent displayed Lemniscate.tangentConic displayedTangentConic
      basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
    unfold tangent displayed Lemniscate.tangentConic displayedTangentConic
      basePoint point
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
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
    rw [Lemniscate.tangentConic_discriminant_factor 1 basePoint onLemniscate]
    rw [discriminantZero]
    ring1
  exact ⟨onLemniscate, onDiscriminant, secondOrder,
    dEquation, eEquation, fEquation, aEquation, bEquation, cEquation,
    determinantZero⟩

end ExampleNineteenNine

namespace ExampleNineteenTen

open FieldEleven

abbrev F₁₁ := FieldEleven.Element

def point14 : Point F₁₁ := ⟨1, 4⟩
def point1Neg4 : Point F₁₁ := ⟨1, -4⟩
def pointNeg14 : Point F₁₁ := ⟨-1, 4⟩
def pointNeg1Neg4 : Point F₁₁ := ⟨-1, -4⟩
def point03 : Point F₁₁ := ⟨0, 3⟩

def tangentLine14 : Line F₁₁ where
  a := 4
  b := 7
  c := 1
  direction_nonzero := Or.inl (by decide)

def tangentConic14 : Conic F₁₁ where
  d := 3
  e := 10
  f := 1
  a := 7
  b := 6
  c := 9
  quadratic_nonzero := Or.inl (by decide)

def tangentLine03 : Line F₁₁ where
  a := 0
  b := 8
  c := 9
  direction_nonzero := Or.inr (by decide)

def tangentConic03 : Conic F₁₁ where
  d := 4
  e := 0
  f := 3
  a := 0
  b := 1
  c := 3
  quadratic_nonzero := Or.inl (by decide)

def directrix14 : Line F₁₁ where
  a := 10
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

def focus14 : Point F₁₁ := ⟨9, 9⟩

def firstDiagonal03 : Line F₁₁ where
  a := 3
  b := 2
  c := 4
  direction_nonzero := Or.inl (by decide)

def secondDiagonal03 : Line F₁₁ where
  a := 1
  b := 3
  c := 6
  direction_nonzero := Or.inl (by decide)

private theorem eightNonzero : (8 : F₁₁) ≠ 0 := by decide

theorem firstOrder14 : Lemniscate.IsNonSingularAt 1 point14 := by
  unfold Lemniscate.IsNonSingularAt Lemniscate.tangentA
    Lemniscate.tangentB point14
  decide

theorem secondOrder14 : Lemniscate.IsSecondOrderNonSingularAt 1 point14 := by
  unfold Lemniscate.IsSecondOrderNonSingularAt Lemniscate.tangentD
    Lemniscate.tangentE Lemniscate.tangentF point14
  decide

theorem firstOrder03 : Lemniscate.IsNonSingularAt 1 point03 := by
  unfold Lemniscate.IsNonSingularAt Lemniscate.tangentA
    Lemniscate.tangentB point03
  decide

theorem secondOrder03 : Lemniscate.IsSecondOrderNonSingularAt 1 point03 := by
  unfold Lemniscate.IsSecondOrderNonSingularAt Lemniscate.tangentD
    Lemniscate.tangentE Lemniscate.tangentF point03
  decide

/-- The four intersections `[+-1,+-4]` printed in Figure 19.11. -/
theorem displayed_intersections :
    Lemniscate.Contains 1 point14 ∧
      Lemniscate.Contains 1 point1Neg4 ∧
      Lemniscate.Contains 1 pointNeg14 ∧
      Lemniscate.Contains 1 pointNeg1Neg4 ∧
      (Lemniscate.discriminantConic 1 eightNonzero).Contains point14 ∧
      (Lemniscate.discriminantConic 1 eightNonzero).Contains point1Neg4 ∧
      (Lemniscate.discriminantConic 1 eightNonzero).Contains pointNeg14 ∧
      (Lemniscate.discriminantConic 1 eightNonzero).Contains
        pointNeg1Neg4 := by
  unfold Lemniscate.Contains Lemniscate.evaluate Conic.Contains
    Lemniscate.discriminantConic Conic.evaluate point14 point1Neg4
    pointNeg14 pointNeg1Neg4
  decide

/-- At `[1,4]` the construction gives the printed line up to scale `4`, and
the printed conic up to scale `6`. -/
theorem tangent_data_at_14 :
    (Lemniscate.tangentLine 1 point14 firstOrder14).Equivalent tangentLine14 ∧
      let tangent := Lemniscate.tangentConic 1 point14 secondOrder14
      tangent.d = 6 * tangentConic14.d ∧
        tangent.e = 6 * tangentConic14.e ∧
        tangent.f = 6 * tangentConic14.f ∧
        tangent.a = 6 * tangentConic14.a ∧
        tangent.b = 6 * tangentConic14.b ∧
        tangent.c = 6 * tangentConic14.c := by
  unfold Line.Equivalent Lemniscate.tangentLine Lemniscate.tangentA
    Lemniscate.tangentB tangentLine14
  dsimp only
  constructor
  · exact ⟨by decide, by decide, by decide⟩
  · unfold Lemniscate.tangentConic Lemniscate.tangentD
      Lemniscate.tangentE Lemniscate.tangentF tangentConic14 point14
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
  · unfold Line.IsNull directrix14
    decide
  · unfold Line.Contains focus14 directrix14
    decide
  all_goals dsimp only [tangentConic14, directrix14, focus14, lineNorm]
  all_goals decide

/-- At `[0,3]` the source construction gives the displayed line and twice
the displayed tangent conic. -/
theorem tangent_data_at_03 :
    (Lemniscate.tangentLine 1 point03 firstOrder03).Equivalent tangentLine03 ∧
      let tangent := Lemniscate.tangentConic 1 point03 secondOrder03
      tangent.d = 2 * tangentConic03.d ∧
        tangent.e = 2 * tangentConic03.e ∧
        tangent.f = 2 * tangentConic03.f ∧
        tangent.a = 2 * tangentConic03.a ∧
        tangent.b = 2 * tangentConic03.b ∧
        tangent.c = 2 * tangentConic03.c := by
  unfold Line.Equivalent Lemniscate.tangentLine Lemniscate.tangentA
    Lemniscate.tangentB tangentLine03
  dsimp only
  constructor
  · exact ⟨by decide, by decide, by decide⟩
  · unfold Lemniscate.tangentConic Lemniscate.tangentD
      Lemniscate.tangentE Lemniscate.tangentF tangentConic03 point03
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

private theorem firstDiagonalNonNull : ¬ firstDiagonal03.IsNull := by
  unfold Line.IsNull firstDiagonal03
  decide

private theorem secondDiagonalNonNull : ¬ secondDiagonal03.IsNull := by
  unfold Line.IsNull secondDiagonal03
  decide

/-- Sum of quadrances to the two diagonal lines printed in Example 19.10. -/
def grammolaQuadranceSum (candidate : Point F₁₁) : F₁₁ :=
  pointLineQuadrance candidate firstDiagonal03 firstDiagonalNonNull +
    pointLineQuadrance candidate secondDiagonal03 secondDiagonalNonNull

private theorem grammola_polynomial_identity (candidate : Point F₁₁) :
    grammolaQuadranceSum candidate =
      5 * tangentConic03.evaluate candidate + 1 := by
  have firstNorm : lineNorm firstDiagonal03 = (2 : F₁₁) := by
    unfold lineNorm firstDiagonal03
    decide
  have secondNorm : lineNorm secondDiagonal03 = (10 : F₁₁) := by
    unfold lineNorm secondDiagonal03
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
  rw [pointLineQuadrance_formula, pointLineQuadrance_formula,
    firstNorm, secondNorm]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [inverseTwo, inverseTen]
  dsimp only [firstDiagonal03, secondDiagonal03, tangentConic03]
  unfold Conic.evaluate
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
theorem tangentConic03_grammola_corrected (candidate : Point F₁₁) :
    tangentConic03.Contains candidate ↔ grammolaQuadranceSum candidate = 1 := by
  have identity := grammola_polynomial_identity candidate
  unfold Conic.Contains
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
        ((RFAP.ExplicitField.mul_ne_zero (by decide : (5 : F₁₁) ≠ 0)
          evaluationZero) productZero)

/-- The source's `K=9` is false already at its base point: the point lies on
the tangent conic, while its quadrance sum is `1`, not `9`. -/
theorem printed_grammola_quadrance_countercheck :
    tangentConic03.Contains point03 ∧
      grammolaQuadranceSum point03 = 1 ∧
      grammolaQuadranceSum point03 ≠ 9 := by
  have onConic : tangentConic03.Contains point03 := by
    unfold Conic.Contains tangentConic03 Conic.evaluate point03
    decide
  have sumOne := (tangentConic03_grammola_corrected point03).1 onConic
  exact ⟨onConic, sumOne, by rw [sumOne]; decide⟩

/-- Example 19.10, with its valid data and corrected grammola constant. -/
theorem example_19_10 :
    Lemniscate.Contains 1 point14 ∧
      (Lemniscate.tangentLine 1 point14 firstOrder14).Equivalent tangentLine14 ∧
      tangentConic14.IsParabolaPresentation focus14 directrix14 ∧
      Lemniscate.Contains 1 point03 ∧
      (Lemniscate.tangentLine 1 point03 firstOrder03).Equivalent tangentLine03 ∧
      tangentConic03.Contains point03 ∧
      grammolaQuadranceSum point03 = 1 ∧
      grammolaQuadranceSum point03 ≠ 9 := by
  have point14On : Lemniscate.Contains 1 point14 := displayed_intersections.1
  have point03On : Lemniscate.Contains 1 point03 := by
    unfold Lemniscate.Contains Lemniscate.evaluate point03
    decide
  exact ⟨point14On, tangent_data_at_14.1, tangentConic14_parabola,
    point03On, tangent_data_at_03.1,
    printed_grammola_quadrance_countercheck.1,
    printed_grammola_quadrance_countercheck.2.1,
    printed_grammola_quadrance_countercheck.2.2⟩

end ExampleNineteenTen

end ChapterNineteenLemniscateExamples

end DivineProportions
