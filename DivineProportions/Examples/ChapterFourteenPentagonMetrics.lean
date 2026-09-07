import DivineProportions.Examples.ChapterFourteenPolygons
import DivineProportions.Proportions.Median
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

namespace DivineProportions.ChapterFourteenExamples.ExercisesFourteenThreeFour

variable {K : Type*} [RFAP.ExplicitField K]

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

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply eq_of_mul_eq_mul_right factorNonzero
  calc
    left * factor = factor * left := by ring1
    _ = factor * right := productsEqual
    _ = right * factor := by ring1

/-- The smaller displayed nonzero root `(5-r)/8`. -/
def alpha (root : K) : K := (5 - root) / 8

/-- The larger displayed nonzero root `(5+r)/8`. -/
def beta (root : K) : K := (5 + root) / 8

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

private theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

private theorem sixteen_ne_zero (twoNonzero : (2 : K) ≠ 0) : (16 : K) ≠ 0 := by
  rw [show (16 : K) = 4 * 4 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
    (four_ne_zero twoNonzero)

private theorem alpha_mul_eight (root : K) (twoNonzero : (2 : K) ≠ 0) :
    alpha root * 8 = 5 - root := by
  exact RFAP.ExplicitField.div_mul_cancel _ (eight_ne_zero twoNonzero)

private theorem beta_mul_eight (root : K) (twoNonzero : (2 : K) ≠ 0) :
    beta root * 8 = 5 + root := by
  exact RFAP.ExplicitField.div_mul_cancel _ (eight_ne_zero twoNonzero)

private theorem five_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) : (5 : K) ≠ 0 := by
  intro fiveZero
  have squareZero : root * root = 0 := by
    calc
      root * root = root ^ 2 := by ring1
      _ = 5 := rootSquare
      _ = 0 := fiveZero
  by_cases rootZero : root = 0
  · exact rootNonzero rootZero
  · exact (RFAP.ExplicitField.mul_ne_zero rootZero rootZero) squareZero

/-- A nonzero square root of five makes the displayed `alpha` nonzero. -/
theorem alpha_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0) :
    alpha root ≠ 0 := by
  intro alphaZero
  have rootFive : root = 5 := by
    have differenceZero : (5 : K) - root = 0 := by
      calc
        (5 : K) - root = alpha root * 8 :=
          (alpha_mul_eight root twoNonzero).symm
        _ = 0 := by rw [alphaZero]; ring1
    exact sub_eq_zero.mp differenceZero |>.symm
  have twentyZero : (20 : K) = 0 := by
    calc
      (20 : K) = root ^ 2 - 5 := by rw [rootFive]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have twentyNonzero : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 4 * 5 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
      (five_ne_zero root rootNonzero rootSquare)
  exact twentyNonzero twentyZero

/-- A nonzero square root of five makes the displayed `beta` nonzero. -/
theorem beta_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0) :
    beta root ≠ 0 := by
  intro betaZero
  have rootNegativeFive : root = -5 := by
    have sumZero : (5 : K) + root = 0 := by
      calc
        (5 : K) + root = beta root * 8 :=
          (beta_mul_eight root twoNonzero).symm
        _ = 0 := by rw [betaZero]; ring1
    apply eq_neg_of_add_eq_zero_left
    calc
      root + 5 = 5 + root := by ring1
      _ = 0 := sumZero
  have twentyZero : (20 : K) = 0 := by
    calc
      (20 : K) = root ^ 2 - 5 := by rw [rootNegativeFive]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have twentyNonzero : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 4 * 5 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
      (five_ne_zero root rootNonzero rootSquare)
  exact twentyNonzero twentyZero

/-- `alpha` annihilates the nontrivial quadratic factor of `S₅`. -/
theorem factor_alpha (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 - 20 * alpha root + 16 * alpha root ^ 2 = 0 := by
  apply eq_of_mul_eq_mul_right (four_ne_zero twoNonzero)
  calc
    (5 - 20 * alpha root + 16 * alpha root ^ 2) * 4 =
        20 - 10 * (alpha root * 8) + (alpha root * 8) ^ 2 := by ring1
    _ = 20 - 10 * (5 - root) + (5 - root) ^ 2 := by
      rw [alpha_mul_eight root twoNonzero]
    _ = root ^ 2 - 5 := by ring1
    _ = 0 := by rw [rootSquare]; ring1
    _ = 0 * 4 := by ring1

/-- `beta` annihilates the nontrivial quadratic factor of `S₅`. -/
theorem factor_beta (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 - 20 * beta root + 16 * beta root ^ 2 = 0 := by
  apply eq_of_mul_eq_mul_right (four_ne_zero twoNonzero)
  calc
    (5 - 20 * beta root + 16 * beta root ^ 2) * 4 =
        20 - 10 * (beta root * 8) + (beta root * 8) ^ 2 := by ring1
    _ = 20 - 10 * (5 + root) + (5 + root) ^ 2 := by
      rw [beta_mul_eight root twoNonzero]
    _ = root ^ 2 - 5 := by ring1
    _ = 0 := by rw [rootSquare]; ring1
    _ = 0 * 4 := by ring1

/-- The order-five identity `β=4α(1-α)`. -/
theorem beta_logistic_alpha (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    beta root = 4 * alpha root * (1 - alpha root) := by
  apply eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * beta root = 2 * (beta root * 8) := by ring1
    _ = 2 * (5 + root) := by rw [beta_mul_eight root twoNonzero]
    _ = 8 * (5 - root) - (5 - root) ^ 2 := by
      apply sub_eq_zero.mp
      calc
        2 * (5 + root) - (8 * (5 - root) - (5 - root) ^ 2) =
            root ^ 2 - 5 := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = 8 * (alpha root * 8) - (alpha root * 8) ^ 2 := by
      rw [alpha_mul_eight root twoNonzero]
    _ = 16 * (4 * alpha root * (1 - alpha root)) := by ring1

/-- The symmetric order-five identity `α=4β(1-β)`. -/
theorem alpha_logistic_beta (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    alpha root = 4 * beta root * (1 - beta root) := by
  apply eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * alpha root = 2 * (alpha root * 8) := by ring1
    _ = 2 * (5 - root) := by rw [alpha_mul_eight root twoNonzero]
    _ = 8 * (5 + root) - (5 + root) ^ 2 := by
      apply sub_eq_zero.mp
      calc
        2 * (5 - root) - (8 * (5 + root) - (5 + root) ^ 2) =
            root ^ 2 - 5 := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = 8 * (beta root * 8) - (beta root * 8) ^ 2 := by
      rw [beta_mul_eight root twoNonzero]
    _ = 16 * (4 * beta root * (1 - beta root)) := by ring1

/-- Every zero of the quadratic factor is one of the two displayed values.
The difference-of-squares product is split by decidable equality, without a
global root-selection argument. -/
theorem factor_root_classification [DecidableEq K]
    (root value : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0)
    (factorZero : 5 - 20 * value + 16 * value ^ 2 = 0) :
    value = alpha root ∨ value = beta root := by
  let transformed := 8 * value - 5
  have transformedSquare : transformed ^ 2 = 5 := by
    calc
      transformed ^ 2 = 5 +
          4 * (5 - 20 * value + 16 * value ^ 2) := by
        unfold transformed
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have productZero : (transformed - root) * (transformed + root) = 0 := by
    calc
      (transformed - root) * (transformed + root) =
          transformed ^ 2 - root ^ 2 := by ring1
      _ = 0 := by rw [transformedSquare, rootSquare]; ring1
  by_cases firstZero : transformed - root = 0
  · right
    apply eq_of_mul_eq_mul_right (eight_ne_zero twoNonzero)
    calc
      value * 8 = 5 + root := by
        have transformedRoot : transformed = root := sub_eq_zero.mp firstZero
        calc
          value * 8 = transformed + 5 := by ring1
          _ = 5 + root := by rw [transformedRoot]; ring1
      _ = beta root * 8 := (beta_mul_eight root twoNonzero).symm
  · left
    have secondZero : transformed + root = 0 := by
      by_cases secondZero : transformed + root = 0
      · exact secondZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstZero secondZero) productZero)
    apply eq_of_mul_eq_mul_right (eight_ne_zero twoNonzero)
    calc
      value * 8 = 5 - root := by
        have transformedNegativeRoot : transformed = -root :=
          eq_neg_of_add_eq_zero_left secondZero
        calc
          value * 8 = transformed + 5 := by ring1
          _ = 5 - root := by rw [transformedNegativeRoot]; ring1
      _ = alpha root * 8 := (alpha_mul_eight root twoNonzero).symm

/-- Exercise 14.3's root claim: `alpha` and `beta` are roots of `S₅`, and
they exhaust all its requested nonzero roots. -/
theorem nontrivial_zeroes [DecidableEq K]
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    spreadPolynomial 5 (alpha root) = 0 ∧
      spreadPolynomial 5 (beta root) = 0 ∧
      ∀ value : K, value ≠ 0 → spreadPolynomial 5 value = 0 →
        value = alpha root ∨ value = beta root := by
  constructor
  · rw [spreadPolynomial_five_formula,
      factor_alpha root rootSquare twoNonzero]
    ring1
  constructor
  · rw [spreadPolynomial_five_formula,
      factor_beta root rootSquare twoNonzero]
    ring1
  · intro value valueNonzero polynomialZero
    rw [spreadPolynomial_five_formula] at polynomialZero
    have factorSquareZero : (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
      by_cases factorSquareZero :
          (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
      · exact factorSquareZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero valueNonzero factorSquareZero)
            polynomialZero)
    have factorZero : 5 - 20 * value + 16 * value ^ 2 = 0 := by
      by_cases factorZero : 5 - 20 * value + 16 * value ^ 2 = 0
      · exact factorZero
      · have factorSquareNonzero :
            (5 - 20 * value + 16 * value ^ 2) *
                (5 - 20 * value + 16 * value ^ 2) ≠ 0 :=
          RFAP.ExplicitField.mul_ne_zero factorZero factorZero
        apply False.elim
        apply factorSquareNonzero
        simpa only [pow_two] using factorSquareZero
    exact factor_root_classification root value rootSquare twoNonzero factorZero

private theorem metricScalars (a b q r d : K)
    (aNonzero : a ≠ 0) (bNonzero : b ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (betaValue : b = 4 * a * (1 - a))
    (sideValue : r = 4 * a * q)
    (diagonalValue : d = 16 * a * (1 - a) * q) :
    q = (1 - a) * r / b ∧
      q = r / (4 * a) ∧
      (2 * (q + q) - r) / 4 = (1 - a) * r / (4 * a) ∧
      d / 4 = (1 - a) * r ∧
      d = 4 * (1 - a) * r ∧
      d = b * r / a := by
  have fourNonzero := four_ne_zero twoNonzero
  have fourANonzero : (4 : K) * a ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero aNonzero
  have radiusFirst : q = (1 - a) * r / b := by
    apply eq_of_mul_eq_mul_right bNonzero
    calc
      q * b = q * (4 * a * (1 - a)) := by rw [betaValue]
      _ = (1 - a) * r := by rw [sideValue]; ring1
      _ = ((1 - a) * r / b) * b :=
        (RFAP.ExplicitField.div_mul_cancel _ bNonzero).symm
  have radiusSecond : q = r / (4 * a) := by
    apply eq_of_mul_eq_mul_right fourANonzero
    calc
      q * (4 * a) = r := by rw [sideValue]; ring1
      _ = (r / (4 * a)) * (4 * a) :=
        (RFAP.ExplicitField.div_mul_cancel _ fourANonzero).symm
  have midpointValue :
      (2 * (q + q) - r) / 4 = (1 - a) * r / (4 * a) := by
    apply eq_of_mul_eq_mul_right
      (RFAP.ExplicitField.mul_ne_zero fourNonzero fourANonzero)
    calc
      ((2 * (q + q) - r) / 4) * (4 * (4 * a)) =
          (((2 * (q + q) - r) / 4) * 4) * (4 * a) := by ring1
      _ = (2 * (q + q) - r) * (4 * a) := by
        rw [RFAP.ExplicitField.div_mul_cancel _ fourNonzero]
      _ = ((1 - a) * r) * 4 := by rw [sideValue]; ring1
      _ = (((1 - a) * r / (4 * a)) * (4 * a)) * 4 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ fourANonzero]
      _ = ((1 - a) * r / (4 * a)) * (4 * (4 * a)) := by ring1
  have diagonalSide : d = 4 * (1 - a) * r := by
    rw [diagonalValue, sideValue]
    ring1
  have halfDiagonal : d / 4 = (1 - a) * r := by
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      (d / 4) * 4 = d :=
        RFAP.ExplicitField.div_mul_cancel _ fourNonzero
      _ = 4 * (1 - a) * r := diagonalSide
      _ = ((1 - a) * r) * 4 := by ring1
  have diagonalRatio : d = b * r / a := by
    apply eq_of_mul_eq_mul_right aNonzero
    calc
      d * a = (4 * (1 - a) * r) * a := by rw [diagonalSide]
      _ = b * r := by rw [betaValue]; ring1
      _ = (b * r / a) * a :=
        (RFAP.ExplicitField.div_mul_cancel _ aNonzero).symm
  exact ⟨radiusFirst, radiusSecond, midpointValue, halfDiagonal,
    diagonalSide, diagonalRatio⟩

variable [Nontrivial K] [DecidableEq K]

/-- Figure 14.4 as finite data.  The corner configuration is labelled
`first=B`, `second=A`, `third=E`, and `center=P`.  Its last field is the
radial spread `s(PB,PE)=alpha` used in Exercise 14.4. -/
structure Figure (root : K) where
  corner : PolygonTriangleConfiguration K (alpha root)
  radialDiagonalSpread :
    spread
        (lineThrough corner.center corner.first corner.centerFirstDistinct)
        (lineThrough corner.center corner.third corner.centerThirdDistinct)
        corner.centerFirstNonNull corner.centerThirdNonNull = alpha root

namespace Figure

/-- The common side quadrance `R=Q(A,B)`. -/
def sideQuadrance (figure : Figure (K := K) root) : K :=
  quadrance figure.corner.second figure.corner.first

/-- The point `M`, the midpoint of the side `AB`. -/
def firstMidpoint (figure : Figure (K := K) root) : Point K :=
  midpoint figure.corner.second figure.corner.first

/-- The point `F`, the midpoint of the diagonal `BE`. -/
def diagonalMidpoint (figure : Figure (K := K) root) : Point K :=
  midpoint figure.corner.first figure.corner.third

/-- The adjacent radial spread `s(PA,PB)`. -/
def adjacentRadialSpread (figure : Figure (K := K) root) : K :=
  spread
    (lineThrough figure.corner.center figure.corner.second
      figure.corner.centerSecondDistinct)
    (lineThrough figure.corner.center figure.corner.first
      figure.corner.centerFirstDistinct)
    figure.corner.centerSecondNonNull figure.corner.centerFirstNonNull

/-- The diagonal radial spread `s(PB,PE)`. -/
def diagonalRadialSpread (figure : Figure (K := K) root) : K :=
  spread
    (lineThrough figure.corner.center figure.corner.first
      figure.corner.centerFirstDistinct)
    (lineThrough figure.corner.center figure.corner.third
      figure.corner.centerThirdDistinct)
    figure.corner.centerFirstNonNull figure.corner.centerThirdNonNull

/-- Exercise 14.3's six Figure 14.4 quadrance equalities.  The first two are
the two printed forms of `Q(P,A)`; the next two concern `M` and `F`; the last
two are the two printed forms of `Q(B,E)`. -/
theorem exercise_14_3 (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    quadrance figure.corner.center figure.corner.second =
        (1 - alpha root) * figure.sideQuadrance / beta root ∧
      quadrance figure.corner.center figure.corner.second =
        figure.sideQuadrance / (4 * alpha root) ∧
      quadrance figure.corner.center figure.firstMidpoint =
        (1 - alpha root) * figure.sideQuadrance / (4 * alpha root) ∧
      quadrance figure.corner.first figure.diagonalMidpoint =
        (1 - alpha root) * figure.sideQuadrance ∧
      quadrance figure.corner.first figure.corner.third =
        4 * (1 - alpha root) * figure.sideQuadrance ∧
      quadrance figure.corner.first figure.corner.third =
        beta root * figure.sideQuadrance / alpha root := by
  have aNonzero := alpha_ne_zero root rootNonzero rootSquare twoNonzero
  have bNonzero := beta_ne_zero root rootNonzero rootSquare twoNonzero
  rcases polygon_triangle (alpha root) aNonzero twoNonzero figure.corner with
    ⟨firstSide, _secondSide, diagonal, _firstSpread, _thirdSpread,
      _apexSpread⟩
  let q := quadrance figure.corner.center figure.corner.second
  let r := figure.sideQuadrance
  let d := quadrance figure.corner.first figure.corner.third
  have sideValue : r = 4 * alpha root * q := by
    unfold r q sideQuadrance
    calc
      quadrance figure.corner.second figure.corner.first =
          quadrance figure.corner.first figure.corner.second :=
        quadrance_symm _ _
      _ = 4 * alpha root *
          quadrance figure.corner.center figure.corner.first := firstSide
      _ = 4 * alpha root *
          quadrance figure.corner.center figure.corner.second := by
        rw [figure.corner.secondRadius]
  have diagonalValue : d = 16 * alpha root * (1 - alpha root) * q := by
    unfold d q
    calc
      quadrance figure.corner.first figure.corner.third =
          16 * alpha root * (1 - alpha root) *
            quadrance figure.corner.center figure.corner.first := diagonal
      _ = 16 * alpha root * (1 - alpha root) *
          quadrance figure.corner.center figure.corner.second := by
        rw [figure.corner.secondRadius]
  rcases metricScalars (alpha root) (beta root) q r d aNonzero bNonzero
      twoNonzero (beta_logistic_alpha root rootSquare twoNonzero)
      sideValue diagonalValue with
    ⟨radiusFirst, radiusSecond, midpointScalar, halfDiagonal,
      diagonalSide, diagonalRatio⟩
  have midpointValue :
      quadrance figure.corner.center figure.firstMidpoint =
        (1 - alpha root) * r / (4 * alpha root) := by
    unfold firstMidpoint
    rw [median_quadrance _ _ _ twoNonzero]
    change (2 *
      (quadrance figure.corner.center figure.corner.first +
        quadrance figure.corner.center figure.corner.second) - r) / 4 = _
    rw [← figure.corner.secondRadius]
    exact midpointScalar
  have diagonalMidpointValue :
      quadrance figure.corner.first figure.diagonalMidpoint =
        (1 - alpha root) * r := by
    unfold diagonalMidpoint
    calc
      quadrance figure.corner.first
          (midpoint figure.corner.first figure.corner.third) =
        quadrance (midpoint figure.corner.first figure.corner.third)
          figure.corner.first := quadrance_symm _ _
      _ = d / 4 := midpoint_quadrance _ _ twoNonzero
      _ = (1 - alpha root) * r := halfDiagonal
  exact ⟨radiusFirst, radiusSecond, midpointValue,
    diagonalMidpointValue, diagonalSide, diagonalRatio⟩

omit [Nontrivial K] in
/-- The adjacent radial spread in Figure 14.4 is `beta`. -/
theorem adjacentRadialSpread_eq_beta (root : K)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    figure.adjacentRadialSpread = beta root := by
  unfold adjacentRadialSpread
  calc
    spread
        (lineThrough figure.corner.center figure.corner.second
          figure.corner.centerSecondDistinct)
        (lineThrough figure.corner.center figure.corner.first
          figure.corner.centerFirstDistinct)
        figure.corner.centerSecondNonNull figure.corner.centerFirstNonNull =
      spread
        (lineThrough figure.corner.center figure.corner.first
          figure.corner.centerFirstDistinct)
        (lineThrough figure.corner.center figure.corner.second
          figure.corner.centerSecondDistinct)
        figure.corner.centerFirstNonNull figure.corner.centerSecondNonNull :=
      spread_symm _ _ _ _
    _ = 4 * alpha root * (1 - alpha root) :=
      figure.corner.doubleRadialSpread
    _ = beta root :=
      (beta_logistic_alpha root rootSquare twoNonzero).symm

omit [Nontrivial K] in
/-- The supplied diagonal radial spread is exactly `alpha`. -/
theorem diagonalRadialSpread_eq_alpha (figure : Figure (K := K) root) :
    figure.diagonalRadialSpread = alpha root := by
  exact figure.radialDiagonalSpread

/-- Exercise 14.4: `beta:alpha` is both the displayed spread proportion and
the diagonal-to-side quadrance proportion. -/
theorem exercise_14_4 (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0)
    (figure : Figure (K := K) root) :
    beta root / alpha root =
        figure.adjacentRadialSpread / figure.diagonalRadialSpread ∧
      beta root / alpha root =
        quadrance figure.corner.first figure.corner.third /
          figure.sideQuadrance := by
  have aNonzero := alpha_ne_zero root rootNonzero rootSquare twoNonzero
  have metric := exercise_14_3 root rootNonzero rootSquare twoNonzero figure
  have diagonalRatio := metric.2.2.2.2.2
  have sideNonzero : figure.sideQuadrance ≠ 0 := by
    intro sideZero
    apply figure.corner.firstSecondNonNull
    change lineNorm
      (lineThrough figure.corner.first figure.corner.second
        figure.corner.firstSecondDistinct) = 0
    rw [lineThrough_norm_eq_quadrance]
    calc
      quadrance figure.corner.first figure.corner.second =
          quadrance figure.corner.second figure.corner.first :=
        quadrance_symm _ _
      _ = figure.sideQuadrance := rfl
      _ = 0 := sideZero
  constructor
  · rw [adjacentRadialSpread_eq_beta root rootSquare twoNonzero figure,
      diagonalRadialSpread_eq_alpha figure]
  · apply eq_of_mul_eq_mul_right sideNonzero
    calc
      (beta root / alpha root) * figure.sideQuadrance =
          beta root * figure.sideQuadrance / alpha root := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
      _ = quadrance figure.corner.first figure.corner.third :=
        diagonalRatio.symm
      _ = (quadrance figure.corner.first figure.corner.third /
          figure.sideQuadrance) * figure.sideQuadrance :=
        (RFAP.ExplicitField.div_mul_cancel _ sideNonzero).symm

end Figure

namespace Decimal

/-- The project-owned exact constructive rational field. -/
abbrev Rational := RFAP.ConstructiveFraction.Rational

private def displayedFraction (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : Rational :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, (denominator : Int), Int.natCast_pos.mpr positive⟩

/-- The nontrivial quadratic factor `5-20s+16s²`. -/
def quadratic (value : Rational) : Rational :=
  5 - 20 * value + 16 * value ^ 2

/-- Lower endpoint `0.345491` of the printed alpha bracket. -/
def alphaLower : Rational := displayedFraction 345491 1000000 (by decide)

/-- Upper endpoint `0.345492` of the printed alpha bracket. -/
def alphaUpper : Rational := displayedFraction 345492 1000000 (by decide)

/-- Lower endpoint `0.904508` of the printed beta bracket. -/
def betaLower : Rational := displayedFraction 904508 1000000 (by decide)

/-- Upper endpoint `0.904509` of the printed beta bracket. -/
def betaUpper : Rational := displayedFraction 904509 1000000 (by decide)

/-- Exact finite sign-change evidence for `α≈0.345491...`. -/
theorem alphaBracket :
    alphaLower < alphaUpper ∧
      0 < quadratic alphaLower ∧ quadratic alphaUpper < 0 := by
  decide

/-- Exact finite sign-change evidence for `β≈0.904508...`. -/
theorem betaBracket :
    betaLower < betaUpper ∧
      quadratic betaLower < 0 ∧ 0 < quadratic betaUpper := by
  decide

end Decimal

end DivineProportions.ChapterFourteenExamples.ExercisesFourteenThreeFour
