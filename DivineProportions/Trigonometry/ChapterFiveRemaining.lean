import DivineProportions.Trigonometry.QuadTripleExercises

/-!
# Divine Proportions, remaining Chapter 5 exercises

Exercise 5.3 is false with the source's definition of a triangle: the
nonzero quadrances `1,1,4` have zero quadrea, hence cannot belong to three
noncollinear points.  The corrected theorem below isolates the exact missing
condition.  In a field carrying an explicit square root of `-1`, every scalar
is constructively a sum of two squares, so Theorem 28 reduces triangle
existence to an explicit nonzero square witness for the quadrea.

Exercise 5.17 is retained through the finite construction responsible for its
factor `2`: a chosen base vector and either sign of a nonzero quadrea root give
two distinct completion points with the requested quadrances.  The remaining
`p²` translation and `p±1` nonzero-circle factors are recorded as finite
counting data rather than by enumerating an entire field carrier.

Exercise 5.19 is answered by a recursive, fuel-indexed finite quad relation.
For five entries it introduces the two diagonals of a fan triangulation; for
any requested finite number of entries it repeatedly combines two adjacent
signed lengths.  There is no infinite sequence or completed polygon.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- In a field with an explicit imaginary unit, every scalar has a displayed
sum-of-two-squares representation. -/
theorem isSumOfTwoSquares_of_squareRootNegativeOne
    (value imaginary : K) (twoNonzero : (2 : K) ≠ 0)
    (imaginarySquare : imaginary ^ 2 = -1) :
    IsSumOfTwoSquares value := by
  let first := (value + 1) / 2
  let second := imaginary * (value - 1) / 2
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  refine ⟨first, second, ?_⟩
  unfold first second
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((value + 1) * (2 : K)⁻¹) ^ 2 +
          (imaginary * (value - 1) * (2 : K)⁻¹) ^ 2 =
        ((value + 1) ^ 2 + imaginary ^ 2 * (value - 1) ^ 2) *
          (2 : K)⁻¹ ^ 2 := by ring1
    _ = 4 * value * (2 : K)⁻¹ ^ 2 := by
      rw [imaginarySquare]
      ring1
    _ = value * ((2 : K) * (2 : K)⁻¹) ^ 2 := by ring1
    _ = value := by rw [twoCancel]; ring1

/-- Corrected Exercise 5.3.  Once an imaginary unit is supplied, the only
remaining constructive obstruction is exactly the source's Theorem 28
condition that the quadrea be a nonzero square. -/
theorem exercise_5_3_corrected
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ imaginary : K) (twoNonzero : (2 : K) ≠ 0)
    (someNonzero : q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0)
    (imaginarySquare : imaginary ^ 2 = -1) :
    HasTriangleQuadrances q₁ q₂ q₃ ↔
      IsNonzeroSquare (archimedesFunction q₁ q₂ q₃) := by
  constructor
  · intro triangle
    exact ((triangle_quadrea q₁ q₂ q₃ twoNonzero).1 triangle).2.2.2.2
  · intro areaSquare
    apply (triangle_quadrea q₁ q₂ q₃ twoNonzero).2
    exact ⟨someNonzero,
      isSumOfTwoSquares_of_squareRootNegativeOne q₁ imaginary twoNonzero
        imaginarySquare,
      isSumOfTwoSquares_of_squareRootNegativeOne q₂ imaginary twoNonzero
        imaginarySquare,
      isSumOfTwoSquares_of_squareRootNegativeOne q₃ imaginary twoNonzero
        imaginarySquare,
      areaSquare⟩

/-- Exercise 5.3 is false as printed: `1,1,4` are not all zero, but their
quadrea vanishes, so they cannot be the quadrances of a noncollinear triangle
over any constructive field of characteristic different from two. -/
theorem exercise_5_3_printed_counterexample
    [Nontrivial K] [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) :
    ¬ HasTriangleQuadrances (1 : K) 1 4 := by
  intro triangle
  have areaSquare :=
    ((triangle_quadrea (1 : K) 1 4 twoNonzero).1 triangle).2.2.2.2
  rcases areaSquare with ⟨root, rootNonzero, rootEquation⟩
  have areaZero : archimedesFunction (1 : K) 1 4 = 0 := by
    unfold archimedesFunction
    ring1
  have rootSquareZero : root ^ 2 = 0 := by
    calc
      root ^ 2 = archimedesFunction (1 : K) 1 4 := rootEquation.symm
      _ = 0 := areaZero
  have rootProductZero : root * root = 0 := by
    calc
      root * root = root ^ 2 := by ring1
      _ = 0 := rootSquareZero
  exact (RFAP.ExplicitField.mul_ne_zero rootNonzero rootNonzero)
    rootProductZero

namespace ExerciseFiveSeventeen

/-- The source's completion point for a base vector `[a,b]`, with the chosen
sign of the quadrea root retained in `areaRoot`. -/
def completionPoint
    (q₁ q₂ q₃ areaRoot a b : K) : Point K :=
  let radial := q₁ + q₂ - q₃
  let denominator := 2 * q₂
  ⟨(a * radial - b * areaRoot) / denominator,
    (b * radial + a * areaRoot) / denominator⟩

/-- The completion formula has the two requested quadrances; the chosen base
vector has quadrance `q₂` from the origin. -/
theorem completionPoint_quadrances
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂)
    (areaEquation :
      archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2) :
    let origin : Point K := ⟨0, 0⟩
    let base : Point K := ⟨a, b⟩
    let completion := completionPoint q₁ q₂ q₃ areaRoot a b
    quadrance completion origin = q₁ ∧
      quadrance base origin = q₂ ∧
      quadrance base completion = q₃ := by
  let radial := q₁ + q₂ - q₃
  let denominator := 2 * q₂
  let xNumerator := a * radial - b * areaRoot
  let yNumerator := b * radial + a * areaRoot
  let origin : Point K := ⟨0, 0⟩
  let base : Point K := ⟨a, b⟩
  let completion := completionPoint q₁ q₂ q₃ areaRoot a b
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have areaRootSquared : areaRoot ^ 2 = 4 * q₁ * q₂ - radial ^ 2 := by
    calc
      areaRoot ^ 2 = archimedesFunction q₁ q₂ q₃ := areaEquation.symm
      _ = 4 * q₁ * q₂ - radial ^ 2 := by
        unfold archimedesFunction radial
        ring1
  have numeratorNorm :
      xNumerator ^ 2 + yNumerator ^ 2 = 4 * q₁ * q₂ ^ 2 := by
    calc
      xNumerator ^ 2 + yNumerator ^ 2 =
          (a ^ 2 + b ^ 2) * (radial ^ 2 + areaRoot ^ 2) := by
        unfold xNumerator yNumerator
        ring1
      _ = q₂ * (radial ^ 2 + areaRoot ^ 2) := by rw [baseNorm]
      _ = 4 * q₁ * q₂ ^ 2 := by rw [areaRootSquared]; ring1
  have completionOrigin : quadrance completion origin = q₁ := by
    unfold quadrance completion completionPoint origin
    simp only [zero_sub, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-((a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹)) ^ 2 +
          (-((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹)) ^ 2 =
        (xNumerator ^ 2 + yNumerator ^ 2) * denominator⁻¹ ^ 2 := by
          unfold xNumerator yNumerator denominator radial
          ring1
      _ = 4 * q₁ * q₂ ^ 2 * denominator⁻¹ ^ 2 := by
        rw [numeratorNorm]
      _ = q₁ * (denominator * denominator⁻¹) ^ 2 := by
        unfold denominator
        ring1
      _ = q₁ := by rw [denominatorCancel]; ring1
  have baseOrigin : quadrance base origin = q₂ := by
    unfold quadrance base origin
    simp only [zero_sub]
    calc
      (-a) ^ 2 + (-b) ^ 2 = a ^ 2 + b ^ 2 := by ring1
      _ = q₂ := baseNorm
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
  have differenceNorm :
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        q₃ * denominator ^ 2 := by
    calc
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        (a ^ 2 + b ^ 2) *
          ((radial - 2 * q₂) ^ 2 + areaRoot ^ 2) := by
        unfold xNumerator yNumerator denominator
        ring1
      _ = q₂ * ((radial - 2 * q₂) ^ 2 + areaRoot ^ 2) := by
        rw [baseNorm]
      _ = q₃ * denominator ^ 2 := by
        rw [areaRootSquared]
        unfold radial denominator
        ring1
  have baseCompletion : quadrance base completion = q₃ := by
    unfold quadrance base completion completionPoint
    change
      (xNumerator / denominator - a) ^ 2 +
          (yNumerator / denominator - b) ^ 2 = q₃
    rw [xDifference, yDifference]
    calc
      ((xNumerator - a * denominator) * denominator⁻¹) ^ 2 +
          ((yNumerator - b * denominator) * denominator⁻¹) ^ 2 =
        ((xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2) *
            denominator⁻¹ ^ 2 := by ring1
      _ = q₃ * denominator ^ 2 * denominator⁻¹ ^ 2 := by
        rw [differenceNorm]
      _ = q₃ * (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = q₃ := by rw [denominatorCancel]; ring1
  exact ⟨completionOrigin, baseOrigin, baseCompletion⟩

/-- The determinant of the base, completion, and origin, with the common
denominator left cleared, is `q₂ * areaRoot`. -/
theorem completionPoint_determinant_cleared
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    pointDeterminant (⟨a, b⟩ : Point K)
        (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
        (2 * q₂) =
      q₂ * areaRoot := by
  have denominatorNonzero : (2 : K) * q₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancelLeft :
      ((2 : K) * q₂)⁻¹ * (2 * q₂) = 1 := by
    calc
      ((2 : K) * q₂)⁻¹ * (2 * q₂) =
          (2 * q₂) * ((2 : K) * q₂)⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold pointDeterminant completionPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (a * ((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹) -
          a * 0 +
          (a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹ * 0 -
          0 * ((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹) +
          0 * b -
          (a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹ * b) *
            (2 * q₂) =
        (a ^ 2 + b ^ 2) * areaRoot *
          (((2 : K) * q₂)⁻¹ * (2 * q₂)) := by ring1
    _ = q₂ * areaRoot := by
      rw [baseNorm, denominatorCancelLeft]
      ring1

/-- A nonzero selected quadrea root makes the completion genuinely
two-dimensional.  This is the noncollinearity certificate needed for the
source's use of the word “triangle”. -/
theorem completionPoint_not_collinear
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    ¬ Collinear (⟨a, b⟩ : Point K)
      (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ := by
  intro collinear
  have determinantZero :=
    (collinear_iff_pointDeterminant_eq_zero
      (⟨a, b⟩ : Point K)
      (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩).1 collinear
  have clearedZero :
      pointDeterminant (⟨a, b⟩ : Point K)
          (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
          (2 * q₂) = 0 := by
    rw [determinantZero]
    ring1
  have clearedValue := completionPoint_determinant_cleared
    q₁ q₂ q₃ areaRoot a b twoNonzero q₂Nonzero baseNorm
  have productZero : q₂ * areaRoot = 0 := by
    calc
      q₂ * areaRoot =
          pointDeterminant (⟨a, b⟩ : Point K)
              (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
              (2 * q₂) := clearedValue.symm
      _ = 0 := clearedZero
  exact (RFAP.ExplicitField.mul_ne_zero q₂Nonzero areaRootNonzero)
    productZero

/-- The two signs of a nonzero area root give two genuinely distinct
completion points. -/
theorem completionPoint_signs_distinct
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    completionPoint q₁ q₂ q₃ areaRoot a b ≠
      completionPoint q₁ q₂ q₃ (-areaRoot) a b := by
  intro completionsEqual
  let base : Point K := ⟨a, b⟩
  let origin : Point K := ⟨0, 0⟩
  have determinantsEqual := congrArg
    (fun point => pointDeterminant base point origin * (2 * q₂))
    completionsEqual
  have positiveDeterminant := completionPoint_determinant_cleared
    q₁ q₂ q₃ areaRoot a b twoNonzero q₂Nonzero baseNorm
  have negativeDeterminant := completionPoint_determinant_cleared
    q₁ q₂ q₃ (-areaRoot) a b twoNonzero q₂Nonzero baseNorm
  have productsEqual : q₂ * areaRoot = q₂ * (-areaRoot) := by
    calc
      q₂ * areaRoot =
          pointDeterminant base
              (completionPoint q₁ q₂ q₃ areaRoot a b) origin *
            (2 * q₂) := positiveDeterminant.symm
      _ = pointDeterminant base
              (completionPoint q₁ q₂ q₃ (-areaRoot) a b) origin *
            (2 * q₂) := determinantsEqual
      _ = q₂ * (-areaRoot) := negativeDeterminant
  have productZero : q₂ * (2 * areaRoot) = 0 := by
    calc
      q₂ * (2 * areaRoot) =
          q₂ * areaRoot - q₂ * (-areaRoot) := by ring1
      _ = 0 := by rw [productsEqual]; ring1
  exact (RFAP.ExplicitField.mul_ne_zero q₂Nonzero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero areaRootNonzero)) productZero

/-- Exercise 5.17's constructive factor two: both signs of the supplied
nonzero quadrea root produce the requested quadrances, and the resulting
completion points differ. -/
theorem exercise_5_17_two_completions
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂)
    (areaEquation :
      archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2) :
    let origin : Point K := ⟨0, 0⟩
    let base : Point K := ⟨a, b⟩
    let positive := completionPoint q₁ q₂ q₃ areaRoot a b
    let negative := completionPoint q₁ q₂ q₃ (-areaRoot) a b
    quadrance positive origin = q₁ ∧
      quadrance base origin = q₂ ∧
      quadrance base positive = q₃ ∧
      ¬ Collinear base positive origin ∧
      quadrance negative origin = q₁ ∧
      quadrance base negative = q₃ ∧
      ¬ Collinear base negative origin ∧
      positive ≠ negative := by
  have positive := completionPoint_quadrances q₁ q₂ q₃ areaRoot a b
    twoNonzero q₂Nonzero baseNorm areaEquation
  have negativeAreaEquation :
      archimedesFunction q₁ q₂ q₃ = (-areaRoot) ^ 2 := by
    calc
      archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2 := areaEquation
      _ = (-areaRoot) ^ 2 := by ring1
  have negative := completionPoint_quadrances q₁ q₂ q₃ (-areaRoot) a b
    twoNonzero q₂Nonzero baseNorm negativeAreaEquation
  exact ⟨positive.1, positive.2.1, positive.2.2,
    completionPoint_not_collinear q₁ q₂ q₃ areaRoot a b twoNonzero
      q₂Nonzero areaRootNonzero baseNorm,
    negative.1, negative.2.2,
    completionPoint_not_collinear q₁ q₂ q₃ (-areaRoot) a b twoNonzero
      q₂Nonzero (neg_ne_zero.mpr areaRootNonzero) baseNorm,
    completionPoint_signs_distinct q₁ q₂ q₃ areaRoot a b twoNonzero
      q₂Nonzero areaRootNonzero baseNorm⟩

/-- The `p=4l+3` count printed in Exercise 5.17. -/
def countFourMulAddThree (p : Nat) : Nat := 2 * p ^ 2 * (p + 1)

/-- The `p=4l+1` count printed in Exercise 5.17. -/
def countFourMulAddOne (p : Nat) : Nat := 2 * p ^ 2 * (p - 1)

/-- Finite bookkeeping for the `4l+3` branch: two completions times `p²`
translations times `p+1` base vectors. -/
theorem count_four_mul_add_three_from_factors
    (p translations baseVectors completions total : Nat)
    (translationCount : translations = p ^ 2)
    (baseVectorCount : baseVectors = p + 1)
    (completionCount : completions = 2)
    (factorization : total = completions * translations * baseVectors) :
    total = countFourMulAddThree p := by
  rw [factorization, translationCount, baseVectorCount, completionCount]
  rfl

/-- Finite bookkeeping for the `4l+1` branch. -/
theorem count_four_mul_add_one_from_factors
    (p translations baseVectors completions total : Nat)
    (translationCount : translations = p ^ 2)
    (baseVectorCount : baseVectors = p - 1)
    (completionCount : completions = 2)
    (factorization : total = completions * translations * baseVectors) :
    total = countFourMulAddOne p := by
  rw [factorization, translationCount, baseVectorCount, completionCount]
  rfl

end ExerciseFiveSeventeen

namespace ExerciseFiveNineteen

/-- A finite scalar sum, defined by primitive recursion on the supplied list. -/
def finiteScalarSum : List K → K
  | [] => 0
  | head :: tail => head + finiteScalarSum tail

@[simp] theorem finiteScalarSum_nil : finiteScalarSum ([] : List K) = 0 := rfl

@[simp] theorem finiteScalarSum_cons (head : K) (tail : List K) :
    finiteScalarSum (head :: tail) = head + finiteScalarSum tail := rfl

/-- The recursive finite `n`-tuple quad relation.  Fuel zero expects a quad
triple.  Each successor step combines the first two entries through a new
diagonal and recurses on a list shorter by one. -/
def FiniteQuadRelation : Nat → List K → Prop
  | 0, [first, second, third] => QuadTriple first second third
  | 0, _ => False
  | fuel + 1, first :: second :: tail =>
      ∃ diagonal : K,
        QuadTriple first second diagonal ∧
          FiniteQuadRelation fuel (diagonal :: tail)
  | _ + 1, _ => False

/-- The quintuple relation written without recursion: two finite diagonal
witnesses split the five entries into three quad triples. -/
def QuintupleQuadRelation
    (q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ : K) : Prop :=
  ∃ q₁₃ q₁₄ : K,
    QuadTriple q₁₂ q₂₃ q₁₃ ∧
      QuadTriple q₁₃ q₃₄ q₁₄ ∧
      QuadTriple q₁₄ q₄₅ q₁₅

theorem finiteQuadRelation_two_iff_quintuple
    (q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ : K) :
    FiniteQuadRelation 2 [q₁₂, q₂₃, q₃₄, q₄₅, q₁₅] ↔
      QuintupleQuadRelation q₁₂ q₂₃ q₃₄ q₄₅ q₁₅ := by
  change
    (∃ q₁₃,
      QuadTriple q₁₂ q₂₃ q₁₃ ∧
        ∃ q₁₄,
          QuadTriple q₁₃ q₃₄ q₁₄ ∧
            QuadTriple q₁₄ q₄₅ q₁₅) ↔
      ∃ q₁₃ q₁₄,
        QuadTriple q₁₂ q₂₃ q₁₃ ∧
          QuadTriple q₁₃ q₃₄ q₁₄ ∧
            QuadTriple q₁₄ q₄₅ q₁₅
  constructor
  · rintro ⟨q₁₃, firstRelation, q₁₄, secondRelation, thirdRelation⟩
    exact ⟨q₁₃, q₁₄, firstRelation, secondRelation, thirdRelation⟩
  · rintro ⟨q₁₃, q₁₄, firstRelation, secondRelation, thirdRelation⟩
    exact ⟨q₁₃, firstRelation, q₁₄, secondRelation, thirdRelation⟩

/-- Squared increments of any explicitly closed finite one-dimensional chain
satisfy the corresponding recursive quad relation. -/
theorem finiteQuadRelation_of_closed_steps
    (first second third : K) (tail : List K)
    (closed : finiteScalarSum (first :: second :: third :: tail) = 0) :
    FiniteQuadRelation tail.length
      (List.map (fun step => step ^ 2)
        (first :: second :: third :: tail)) := by
  induction tail generalizing first second third with
  | nil =>
      simp only [List.length_nil, List.map, FiniteQuadRelation]
      apply exercise_5_8 first second third
      right
      right
      left
      have sumZero : first + second + third = 0 := by
        calc
          first + second + third =
              finiteScalarSum (first :: second :: third :: []) := by
            simp only [finiteScalarSum_cons, finiteScalarSum_nil, add_zero]
            ring1
          _ = 0 := closed
      exact eq_neg_of_add_eq_zero_left sumZero
  | cons fourth rest inductionHypothesis =>
      simp only [List.length_cons, List.map, FiniteQuadRelation]
      refine ⟨(first + second) ^ 2, ?_, ?_⟩
      · exact exercise_5_8 first second (first + second) (Or.inl rfl)
      · apply inductionHypothesis (first := first + second)
          (second := third) (third := fourth)
        calc
          finiteScalarSum ((first + second) :: third :: fourth :: rest) =
              finiteScalarSum (first :: second :: third :: fourth :: rest) := by
            simp only [finiteScalarSum_cons]
            ring1
          _ = 0 := closed

/-- Exercise 5.19, quintuple case.  Five signed one-dimensional increments
which close up give the two requested diagonal witnesses and hence three
successive quad triples. -/
theorem exercise_5_19_quintuple
    (d₁₂ d₂₃ d₃₄ d₄₅ d₁₅ : K)
    (closed : d₁₂ + d₂₃ + d₃₄ + d₄₅ + d₁₅ = 0) :
    QuintupleQuadRelation
      (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₄₅ ^ 2) (d₁₅ ^ 2) := by
  apply (finiteQuadRelation_two_iff_quintuple
    (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₄₅ ^ 2) (d₁₅ ^ 2)).1
  apply finiteQuadRelation_of_closed_steps d₁₂ d₂₃ d₃₄ [d₄₅, d₁₅]
  calc
    finiteScalarSum (d₁₂ :: d₂₃ :: d₃₄ :: [d₄₅, d₁₅]) =
        d₁₂ + d₂₃ + d₃₄ + d₄₅ + d₁₅ := by
      simp only [finiteScalarSum_cons, finiteScalarSum_nil, add_zero]
      ring1
    _ = 0 := closed

/-- Exercise 5.19, general finite case.  The caller requests exactly the
finite tail to be combined; the theorem performs that many recursive steps. -/
theorem exercise_5_19_general
    (first second third : K) (tail : List K)
    (closed : finiteScalarSum (first :: second :: third :: tail) = 0) :
    FiniteQuadRelation tail.length
      (List.map (fun step => step ^ 2)
        (first :: second :: third :: tail)) :=
  finiteQuadRelation_of_closed_steps first second third tail closed

end ExerciseFiveNineteen

end DivineProportions
