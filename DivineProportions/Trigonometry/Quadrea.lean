import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.Quadrance
import DivineProportions.Algebra.QuadraticCompatibility

/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The symmetric quadrea of three points. -/
def quadrea (first second third : Point K) : K :=
  archimedesFunction
    (quadrance second third)
    (quadrance first third)
    (quadrance first second)

/-- Theorem 26 (Quadrea): quadrea is four times the square of the coordinate
determinant. -/
theorem quadrea_coordinate_formula (first second third : Point K) :
    quadrea first second third =
      4 * pointDeterminant first second third ^ 2 :=
  archimedes_quadrance_identity first second third

/-- The nonzero clause of Theorem 26: outside characteristic two, nonzero
quadrea is exactly noncollinearity. -/
theorem quadrea_ne_zero_iff_not_collinear [Nontrivial K] [DecidableEq K]
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrea first second third ≠ 0 ↔ ¬ Collinear first second third := by
  exact not_congr (triple_quad_formula first second third twoNonzero)

/-- Theorem 27 (Right quadrea): the quadrea of a Pythagorean triple is four
times the product of the two perpendicular quadrances. -/
theorem right_quadrea (q₁ q₂ q₃ : K) (pythagoras : q₁ + q₂ = q₃) :
    archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ := by
  unfold archimedesFunction
  rw [← pythagoras]
  ring1

/-- The geometric form of Theorem 27. -/
theorem right_triangle_quadrea [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (perpendicular :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct)) :
    quadrea first second third =
      4 * quadrance second third * quadrance first third := by
  apply right_quadrea
  exact (pythagoras_iff_perpendicular first second third
    firstThirdDistinct secondThirdDistinct twoNonzero).2 perpendicular

/-- A scalar displayed as a sum of two squares. -/
def IsSumOfTwoSquares (value : K) : Prop :=
  ∃ first second : K, first ^ 2 + second ^ 2 = value

/-- A scalar displayed as the square of a nonzero field element. -/
def IsNonzeroSquare (value : K) : Prop :=
  ∃ root : K, root ≠ 0 ∧ value = root ^ 2

/-- A displayed noncollinear triangle with the three prescribed quadrances,
using the book's convention `q₁ = Q(A₂,A₃)`, and cyclically. -/
def HasTriangleQuadrances (q₁ q₂ q₃ : K) : Prop :=
  ∃ first second third : Point K,
    ¬ Collinear first second third ∧
      quadrance second third = q₁ ∧
      quadrance first third = q₂ ∧
      quadrance first second = q₃

private theorem not_collinear_swap_first_second
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear second first third := by
  intro swapped
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    (collinear_iff_pointDeterminant_eq_zero second first third).1 swapped
  calc
    pointDeterminant first second third =
        -pointDeterminant second first third := by
          unfold pointDeterminant
          ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

private theorem not_collinear_swap_second_third
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear first third second := by
  intro swapped
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    (collinear_iff_pointDeterminant_eq_zero first third second).1 swapped
  calc
    pointDeterminant first second third =
        -pointDeterminant first third second := by
          unfold pointDeterminant
          ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

private theorem construct_triangle_when_q₂_nonzero
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ a b root : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₂Nonzero : q₂ ≠ 0)
    (q₂Squares : a ^ 2 + b ^ 2 = q₂)
    (rootNonzero : root ≠ 0)
    (rootEquation : archimedesFunction q₁ q₂ q₃ = root ^ 2) :
    HasTriangleQuadrances q₁ q₂ q₃ := by
  let r : K := q₁ + q₂ - q₃
  let denominator : K := 2 * q₂
  let xNumerator : K := a * r - b * root
  let yNumerator : K := b * r + a * root
  let first : Point K := ⟨a, b⟩
  let second : Point K :=
    ⟨xNumerator / denominator, yNumerator / denominator⟩
  let third : Point K := ⟨0, 0⟩
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have rootSquared : root ^ 2 = 4 * q₁ * q₂ - r ^ 2 := by
    calc
      root ^ 2 = archimedesFunction q₁ q₂ q₃ := rootEquation.symm
      _ = 4 * q₁ * q₂ - r ^ 2 := by
        unfold archimedesFunction r
        ring1
  have numeratorNorm : xNumerator ^ 2 + yNumerator ^ 2 =
      4 * q₁ * q₂ ^ 2 := by
    calc
      xNumerator ^ 2 + yNumerator ^ 2 =
          (a ^ 2 + b ^ 2) * (r ^ 2 + root ^ 2) := by
            unfold xNumerator yNumerator
            ring1
      _ = q₂ * (r ^ 2 + root ^ 2) := by rw [q₂Squares]
      _ = 4 * q₁ * q₂ ^ 2 := by rw [rootSquared]; ring1
  have secondThirdQuadrance : quadrance second third = q₁ := by
    unfold quadrance second third
    simp only [zero_sub]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-(xNumerator * denominator⁻¹)) ^ 2 +
          (-(yNumerator * denominator⁻¹)) ^ 2 =
        (xNumerator ^ 2 + yNumerator ^ 2) * denominator⁻¹ ^ 2 := by ring1
      _ = 4 * q₁ * q₂ ^ 2 * denominator⁻¹ ^ 2 := by
        rw [numeratorNorm]
      _ = q₁ * (denominator * denominator⁻¹) ^ 2 := by
        unfold denominator
        ring1
      _ = q₁ := by rw [denominatorCancel]; ring1
  have firstThirdQuadrance : quadrance first third = q₂ := by
    unfold quadrance first third
    simp only [zero_sub]
    calc
      (-a) ^ 2 + (-b) ^ 2 = a ^ 2 + b ^ 2 := by ring1
      _ = q₂ := q₂Squares
  have xDifference :
      xNumerator / denominator - a =
        (xNumerator - a * denominator) * denominator⁻¹ := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      xNumerator * denominator⁻¹ - a =
          xNumerator * denominator⁻¹ -
            a * (denominator * denominator⁻¹) := by
              rw [denominatorCancel]
              ring1
      _ = (xNumerator - a * denominator) * denominator⁻¹ := by ring1
  have yDifference :
      yNumerator / denominator - b =
        (yNumerator - b * denominator) * denominator⁻¹ := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      yNumerator * denominator⁻¹ - b =
          yNumerator * denominator⁻¹ -
            b * (denominator * denominator⁻¹) := by
              rw [denominatorCancel]
              ring1
      _ = (yNumerator - b * denominator) * denominator⁻¹ := by ring1
  have differenceNumeratorNorm :
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        q₃ * denominator ^ 2 := by
    calc
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        (a ^ 2 + b ^ 2) * ((r - 2 * q₂) ^ 2 + root ^ 2) := by
          unfold xNumerator yNumerator denominator
          ring1
      _ = q₂ * ((r - 2 * q₂) ^ 2 + root ^ 2) := by rw [q₂Squares]
      _ = q₃ * denominator ^ 2 := by
        rw [rootSquared]
        unfold r denominator
        ring1
  have firstSecondQuadrance : quadrance first second = q₃ := by
    unfold quadrance first second
    change
      (xNumerator / denominator - a) ^ 2 +
          (yNumerator / denominator - b) ^ 2 = q₃
    rw [xDifference, yDifference]
    calc
      ((xNumerator - a * denominator) * denominator⁻¹) ^ 2 +
          ((yNumerator - b * denominator) * denominator⁻¹) ^ 2 =
        ((xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2) * denominator⁻¹ ^ 2 := by
            ring1
      _ = q₃ * denominator ^ 2 * denominator⁻¹ ^ 2 := by
        rw [differenceNumeratorNorm]
      _ = q₃ * (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = q₃ := by rw [denominatorCancel]; ring1
  have constructedQuadrea : quadrea first second third = root ^ 2 := by
    unfold quadrea
    rw [secondThirdQuadrance, firstThirdQuadrance, firstSecondQuadrance]
    exact rootEquation
  have rootSquareNonzero : root ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero rootNonzero rootNonzero
  have notCollinear : ¬ Collinear first second third :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).1
      (by rw [constructedQuadrea]; exact rootSquareNonzero)
  exact ⟨first, second, third, notCollinear,
    secondThirdQuadrance, firstThirdQuadrance, firstSecondQuadrance⟩

/-- Theorem 28 (Triangle quadrea), with all constructive witnesses exposed.
The disjunction is the finite content of “not all zero”; each sum-of-squares
and square assertion carries its actual witness. -/
theorem triangle_quadrea [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ : K) (twoNonzero : (2 : K) ≠ 0) :
    HasTriangleQuadrances q₁ q₂ q₃ ↔
      (q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0) ∧
      IsSumOfTwoSquares q₁ ∧ IsSumOfTwoSquares q₂ ∧
      IsSumOfTwoSquares q₃ ∧
      IsNonzeroSquare (archimedesFunction q₁ q₂ q₃) := by
  constructor
  · rintro ⟨first, second, third, notCollinear,
      firstQuadrance, secondQuadrance, thirdQuadrance⟩
    have someNonzero : q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0 := by
      by_cases q₁Nonzero : q₁ ≠ 0
      · exact Or.inl q₁Nonzero
      · by_cases q₂Nonzero : q₂ ≠ 0
        · exact Or.inr (Or.inl q₂Nonzero)
        · right
          right
          intro q₃Zero
          apply notCollinear
          apply (triple_quad_formula first second third twoNonzero).1
          rw [firstQuadrance, secondQuadrance, thirdQuadrance]
          have q₁Zero : q₁ = 0 := by
            by_cases equality : q₁ = 0
            · exact equality
            · exact False.elim (q₁Nonzero equality)
          have q₂Zero : q₂ = 0 := by
            by_cases equality : q₂ = 0
            · exact equality
            · exact False.elim (q₂Nonzero equality)
          rw [q₁Zero, q₂Zero, q₃Zero]
          unfold archimedesFunction
          ring1
    have q₁Squares : IsSumOfTwoSquares q₁ := by
      refine ⟨third.x - second.x, third.y - second.y, ?_⟩
      exact firstQuadrance
    have q₂Squares : IsSumOfTwoSquares q₂ := by
      refine ⟨third.x - first.x, third.y - first.y, ?_⟩
      exact secondQuadrance
    have q₃Squares : IsSumOfTwoSquares q₃ := by
      refine ⟨second.x - first.x, second.y - first.y, ?_⟩
      exact thirdQuadrance
    have determinantNonzero : pointDeterminant first second third ≠ 0 := by
      intro determinantZero
      exact notCollinear
        ((collinear_iff_pointDeterminant_eq_zero first second third).2
          determinantZero)
    have twiceDeterminantNonzero :
        (2 : K) * pointDeterminant first second third ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero determinantNonzero
    have quadreaSquare : IsNonzeroSquare
        (archimedesFunction q₁ q₂ q₃) := by
      refine ⟨2 * pointDeterminant first second third,
        twiceDeterminantNonzero, ?_⟩
      calc
        archimedesFunction q₁ q₂ q₃ =
            quadrea first second third := by
              unfold quadrea
              rw [firstQuadrance, secondQuadrance, thirdQuadrance]
        _ = 4 * pointDeterminant first second third ^ 2 :=
          quadrea_coordinate_formula first second third
        _ = (2 * pointDeterminant first second third) ^ 2 := by ring1
    exact ⟨someNonzero, q₁Squares, q₂Squares, q₃Squares,
      quadreaSquare⟩
  · rintro ⟨someNonzero, q₁Squares, q₂Squares, q₃Squares,
      root, rootNonzero, rootEquation⟩
    rcases q₁Squares with ⟨a₁, b₁, q₁Equation⟩
    rcases q₂Squares with ⟨a₂, b₂, q₂Equation⟩
    rcases q₃Squares with ⟨a₃, b₃, q₃Equation⟩
    rcases someNonzero with q₁Nonzero | q₂Nonzero | q₃Nonzero
    · have permutedRoot :
          archimedesFunction q₂ q₁ q₃ = root ^ 2 := by
        calc
          archimedesFunction q₂ q₁ q₃ =
              archimedesFunction q₁ q₂ q₃ := by
                unfold archimedesFunction
                ring1
          _ = root ^ 2 := rootEquation
      rcases construct_triangle_when_q₂_nonzero
        q₂ q₁ q₃ a₁ b₁ root twoNonzero q₁Nonzero
        q₁Equation rootNonzero permutedRoot with
        ⟨first, second, third, notCollinear,
          firstQuadrance, secondQuadrance, thirdQuadrance⟩
      exact ⟨second, first, third,
        not_collinear_swap_first_second notCollinear,
        secondQuadrance, firstQuadrance,
        (quadrance_symm second first).trans thirdQuadrance⟩
    · exact construct_triangle_when_q₂_nonzero
        q₁ q₂ q₃ a₂ b₂ root twoNonzero q₂Nonzero
        q₂Equation rootNonzero rootEquation
    · have permutedRoot :
          archimedesFunction q₁ q₃ q₂ = root ^ 2 := by
        calc
          archimedesFunction q₁ q₃ q₂ =
              archimedesFunction q₁ q₂ q₃ := by
                unfold archimedesFunction
                ring1
          _ = root ^ 2 := rootEquation
      rcases construct_triangle_when_q₂_nonzero
        q₁ q₃ q₂ a₃ b₃ root twoNonzero q₃Nonzero
        q₃Equation rootNonzero permutedRoot with
        ⟨first, second, third, notCollinear,
          firstQuadrance, secondQuadrance, thirdQuadrance⟩
      exact ⟨first, third, second,
        not_collinear_swap_second_third notCollinear,
        (quadrance_symm third second).trans firstQuadrance,
        thirdQuadrance, secondQuadrance⟩

/-- Theorem 29 (Archimedes' formula), as a universal polynomial identity. -/
theorem archimedes_formula (d₁ d₂ d₃ : K) :
    archimedesFunction (d₁ ^ 2) (d₂ ^ 2) (d₃ ^ 2) =
      (d₁ + d₂ + d₃) * (d₁ + d₂ - d₃) *
        (d₂ + d₃ - d₁) * (d₃ + d₁ - d₂) := by
  unfold archimedesFunction
  ring1

/-- A triple of scalars satisfying Archimedes' polynomial. -/
def QuadTriple (a b c : K) : Prop := archimedesFunction a b c = 0

/-- The centered-square form of the quad-triple relation. -/
theorem quadTriple_iff_centered_square (a b x : K) :
    QuadTriple a b x ↔ (x - (a + b)) ^ 2 = 4 * a * b := by
  have identity : archimedesFunction a b x =
      4 * a * b - (x - (a + b)) ^ 2 := by
    unfold archimedesFunction
    ring1
  unfold QuadTriple
  rw [identity]
  constructor <;> intro equation
  · calc
      (x - (a + b)) ^ 2 =
          4 * a * b - (4 * a * b - (x - (a + b)) ^ 2) := by ring1
      _ = 4 * a * b := by rw [equation]; ring1
  · rw [equation]
    ring1

/-- The symmetric polynomial in the Quadruple quad formula. -/
def quadrupleQuadFunction (a b c d : K) : K :=
  ((a + b + c + d) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 -
    64 * a * b * c * d

/-- Theorem 30 (Two quad triples), polynomial clause. -/
theorem two_quad_triples
    (a b c d x : K) (first : QuadTriple a b x)
    (second : QuadTriple c d x) :
    quadrupleQuadFunction a b c d = 0 := by
  have compatible : QuadraticsCompatible (a + b) (4 * a * b)
      (c + d) (4 * c * d) :=
    ⟨x, (quadTriple_iff_centered_square a b x).1 first,
      (quadTriple_iff_centered_square c d x).1 second⟩
  have compatibilityIdentity :=
    quadraticCompatibilityIdentity_of_compatible compatible
  unfold quadraticCompatibilityIdentity at compatibilityIdentity
  unfold quadrupleQuadFunction
  calc
    ((a + b + c + d) ^ 2 -
          2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 -
        64 * a * b * c * d =
      (((a + b - (c + d)) ^ 2 -
          (4 * a * b + 4 * c * d)) ^ 2) -
        4 * (4 * a * b) * (4 * c * d) := by ring1
    _ = 0 := by rw [compatibilityIdentity]; ring1

private theorem sub_ne_zero_of_ne {a b : K} (different : a ≠ b) :
    a - b ≠ 0 := by
  intro differenceZero
  apply different
  calc
    a = (a - b) + b := by ring1
    _ = 0 + b := by rw [differenceZero]
    _ = b := zero_add b

/-- Theorem 30, common-value clause.  Its sole denominator is displayed as a
nonzero hypothesis. -/
theorem two_quad_triples_common_value
    (a b c d x : K) (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : a + b ≠ c + d)
    (first : QuadTriple a b x) (second : QuadTriple c d x) :
    x = ((a - b) ^ 2 - (c - d) ^ 2) /
      (2 * (a + b - c - d)) := by
  have differenceNonzero : a + b - c - d ≠ 0 := by
    have centreDifference : a + b - (c + d) ≠ 0 :=
      sub_ne_zero_of_ne centresDistinct
    intro differenceZero
    apply centreDifference
    calc
      a + b - (c + d) = a + b - c - d := by ring1
      _ = 0 := differenceZero
  have denominatorNonzero : (2 : K) * (a + b - c - d) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel :
      (2 * (a + b - c - d)) * (2 * (a + b - c - d))⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  have firstEquation := (quadTriple_iff_centered_square a b x).1 first
  have secondEquation := (quadTriple_iff_centered_square c d x).1 second
  have cleared :
      2 * (a + b - c - d) * x =
        (a - b) ^ 2 - (c - d) ^ 2 := by
    calc
      2 * (a + b - c - d) * x =
          (a + b) ^ 2 - (c + d) ^ 2 -
            (x - (a + b)) ^ 2 + (x - (c + d)) ^ 2 := by ring1
      _ = (a + b) ^ 2 - (c + d) ^ 2 -
          4 * a * b + 4 * c * d := by rw [firstEquation, secondEquation]
      _ = (a - b) ^ 2 - (c - d) ^ 2 := by ring1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    x = x * ((2 * (a + b - c - d)) *
        (2 * (a + b - c - d))⁻¹) := by
          rw [denominatorCancel, mul_one]
    _ = (2 * (a + b - c - d) * x) *
        (2 * (a + b - c - d))⁻¹ := by ring1
    _ = ((a - b) ^ 2 - (c - d) ^ 2) *
        (2 * (a + b - c - d))⁻¹ := by rw [cleared]

/-- Four points are collinear when one displayed line contains all four. -/
def FourCollinear (first second third fourth : Point K) : Prop :=
  ∃ line : Line K,
    line.Contains first ∧ line.Contains second ∧
      line.Contains third ∧ line.Contains fourth

/-- Theorem 31 (Quadruple quad formula), including both conditional diagonal
formulas from the source. -/
theorem quadruple_quad_formula [Nontrivial K] [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (collinear : FourCollinear first second third fourth) :
    quadrupleQuadFunction
        (quadrance first second) (quadrance second third)
        (quadrance third fourth) (quadrance first fourth) = 0 ∧
      (quadrance first second + quadrance second third ≠
          quadrance third fourth + quadrance first fourth →
        quadrance first third =
          ((quadrance first second - quadrance second third) ^ 2 -
            (quadrance third fourth - quadrance first fourth) ^ 2) /
          (2 * (quadrance first second + quadrance second third -
            quadrance third fourth - quadrance first fourth))) ∧
      (quadrance second third + quadrance third fourth ≠
          quadrance first second + quadrance first fourth →
        quadrance second fourth =
          ((quadrance second third - quadrance third fourth) ^ 2 -
            (quadrance first second - quadrance first fourth) ^ 2) /
          (2 * (quadrance second third + quadrance third fourth -
            quadrance first second - quadrance first fourth))) := by
  rcases collinear with
    ⟨line, containsFirst, containsSecond, containsThird, containsFourth⟩
  have collinear123 : Collinear first second third :=
    ⟨line, containsFirst, containsSecond, containsThird⟩
  have collinear134 : Collinear first third fourth :=
    ⟨line, containsFirst, containsThird, containsFourth⟩
  have collinear234 : Collinear second third fourth :=
    ⟨line, containsSecond, containsThird, containsFourth⟩
  have collinear241 : Collinear second fourth first :=
    ⟨line, containsSecond, containsFourth, containsFirst⟩
  have triple123Raw :=
    (triple_quad_formula first second third twoNonzero).2 collinear123
  have triple134 : QuadTriple
      (quadrance third fourth) (quadrance first fourth)
      (quadrance first third) :=
    (triple_quad_formula first third fourth twoNonzero).2 collinear134
  have triple123 : QuadTriple
      (quadrance first second) (quadrance second third)
      (quadrance first third) := by
    unfold QuadTriple
    calc
      archimedesFunction
          (quadrance first second) (quadrance second third)
          (quadrance first third) =
        archimedesFunction
          (quadrance second third) (quadrance first third)
          (quadrance first second) := by
            unfold archimedesFunction
            ring1
      _ = 0 := triple123Raw
  have triple234Raw :=
    (triple_quad_formula second third fourth twoNonzero).2 collinear234
  have triple234 : QuadTriple
      (quadrance second third) (quadrance third fourth)
      (quadrance second fourth) := by
    unfold QuadTriple
    calc
      archimedesFunction
          (quadrance second third) (quadrance third fourth)
          (quadrance second fourth) =
        archimedesFunction
          (quadrance third fourth) (quadrance second fourth)
          (quadrance second third) := by
            unfold archimedesFunction
            ring1
      _ = 0 := triple234Raw
  have triple241 : QuadTriple
      (quadrance first second) (quadrance first fourth)
      (quadrance second fourth) := by
    have raw :=
      (triple_quad_formula second fourth first twoNonzero).2 collinear241
    unfold QuadTriple
    calc
      archimedesFunction
          (quadrance first second) (quadrance first fourth)
          (quadrance second fourth) =
        archimedesFunction
          (quadrance second first) (quadrance fourth first)
          (quadrance second fourth) := by
            rw [quadrance_symm first fourth, quadrance_symm first second]
      _ =
        archimedesFunction
          (quadrance fourth first) (quadrance second first)
          (quadrance second fourth) := by
            unfold archimedesFunction
            ring1
      _ = 0 := raw
  refine ⟨two_quad_triples _ _ _ _ _ triple123 triple134, ?_, ?_⟩
  · intro denominatorNonzero
    exact two_quad_triples_common_value _ _ _ _ _ twoNonzero
      denominatorNonzero triple123 triple134
  · intro denominatorNonzero
    exact two_quad_triples_common_value _ _ _ _ _ twoNonzero
      denominatorNonzero triple234 triple241

/-- Theorem 32 (Brahmagupta's identity), as the exact eight-factor
polynomial identity in the source. -/
theorem brahmagupta_identity (d₁₂ d₂₃ d₃₄ d₁₄ : K) :
    quadrupleQuadFunction
        (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₁₄ ^ 2) =
      (d₁₂ - d₁₄ + d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ + d₂₃ - d₃₄) *
      (d₁₄ - d₁₂ + d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ - d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ + d₂₃ + d₃₄) *
      (d₁₂ - d₁₄ - d₂₃ + d₃₄) *
      (d₁₂ - d₁₄ + d₂₃ - d₃₄) *
      (d₂₃ - d₁₄ - d₁₂ + d₃₄) := by
  unfold quadrupleQuadFunction
  ring1

end DivineProportions
