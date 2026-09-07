import DivineProportions.Quadrilaterals.FourPoint
import DivineProportions.Plane.Reflection
import DivineProportions.Trigonometry.TripleSpread

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace DivineProportions
namespace ResectionApplications

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

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-! ## Problem 24: Snellius--Pothenot resection -/

def resectionCenterNumerator
    (q₁ q₂ q₃ r₁ r₂ r₃ : K) : K :=
  (q₁ + q₂ + q₃) * (r₁ + r₂ + r₃) -
    2 * (q₁ * r₁ + q₂ * r₂ + q₃ * r₃)

def resectionCenteredRoot
    (q₁ q₂ q₃ r₁ r₂ r₃ R₃ : K) : K :=
  2 * r₃ * R₃ - resectionCenterNumerator q₁ q₂ q₃ r₁ r₂ r₃

/-- The general centered resection quadratic with every denominator cleared:
`(R₃-C)²=D` becomes
`(2r₃R₃-Cnum)²=4r₃r₁r₂ A(Q₁,Q₂,Q₃)`. -/
theorem problem_24_cleared [DecidableEq K]
    (q₁ q₂ q₃ r₁ r₂ r₃ R₁ R₂ R₃ : K)
    (q₃Nonzero : q₃ ≠ 0) (r₃Nonzero : r₃ ≠ 0)
    (spreadTriple : SpreadTriple r₁ r₂ r₃)
    (firstSpreadLaw : r₃ * R₁ = r₂ * q₃)
    (secondSpreadLaw : r₃ * R₂ = r₁ * q₃)
    (fourPointRelation :
      Quadrilateral.eulerFunction q₁ q₂ q₃ R₁ R₂ R₃ = 0) :
    resectionCenteredRoot q₁ q₂ q₃ r₁ r₂ r₃ R₃ ^ 2 =
      4 * r₃ * r₁ * r₂ * archimedesFunction q₁ q₂ q₃ := by
  let fourPointNumerator :=
    Quadrilateral.fourPointQuadraticNumerator q₁ q₂ q₃ R₁ R₂ R₃
  let centerNumerator := resectionCenterNumerator q₁ q₂ q₃ r₁ r₂ r₃
  let centeredRoot := 2 * r₃ * R₃ - centerNumerator
  have numeratorEquation :
      fourPointNumerator ^ 2 =
        archimedesFunction q₁ q₂ q₃ *
          archimedesFunction R₁ R₂ q₃ := by
    have identity := Quadrilateral.fourPoint_quadratic_identity
      q₁ q₂ q₃ R₁ R₂ R₃
    unfold fourPointNumerator
    apply sub_eq_zero.mp
    calc
      Quadrilateral.fourPointQuadraticNumerator q₁ q₂ q₃ R₁ R₂ R₃ ^ 2 -
          archimedesFunction q₁ q₂ q₃ *
            archimedesFunction R₁ R₂ q₃ =
        -2 * q₃ *
          Quadrilateral.eulerFunction q₁ q₂ q₃ R₁ R₂ R₃ :=
            identity
      _ = 0 := by rw [fourPointRelation]; ring1
  have numeratorCenterRelation :
      r₃ * fourPointNumerator = q₃ * centeredRoot := by
    unfold fourPointNumerator centeredRoot centerNumerator
      Quadrilateral.fourPointQuadraticNumerator resectionCenterNumerator
    calc
      r₃ *
          (q₃ * (2 * R₃ - R₁ - R₂ + q₃ - q₁ - q₂) +
            (q₁ - q₂) * (R₂ - R₁)) =
        q₃ *
            (2 * r₃ * R₃ - r₃ * R₁ - r₃ * R₂ +
              r₃ * q₃ - r₃ * q₁ - r₃ * q₂) +
          (q₁ - q₂) * (r₃ * R₂ - r₃ * R₁) := by ring1
      _ = q₃ *
            (2 * r₃ * R₃ - r₂ * q₃ - r₁ * q₃ +
              r₃ * q₃ - r₃ * q₁ - r₃ * q₂) +
          (q₁ - q₂) * (r₁ * q₃ - r₂ * q₃) := by
            rw [firstSpreadLaw, secondSpreadLaw]
      _ = q₃ *
          (2 * r₃ * R₃ -
            ((q₁ + q₂ + q₃) * (r₁ + r₂ + r₃) -
              2 * (q₁ * r₁ + q₂ * r₂ + q₃ * r₃))) := by ring1
  have scaledArchimedes :
      r₃ ^ 2 * archimedesFunction R₁ R₂ q₃ =
        q₃ ^ 2 * archimedesFunction r₂ r₁ r₃ := by
    calc
      r₃ ^ 2 * archimedesFunction R₁ R₂ q₃ =
          archimedesFunction (r₃ * R₁) (r₃ * R₂) (r₃ * q₃) := by
            unfold archimedesFunction
            ring1
      _ = archimedesFunction (r₂ * q₃) (r₁ * q₃) (r₃ * q₃) := by
            rw [firstSpreadLaw, secondSpreadLaw]
      _ = q₃ ^ 2 * archimedesFunction r₂ r₁ r₃ := by
            unfold archimedesFunction
            ring1
  have spreadArchimedes :
      archimedesFunction r₂ r₁ r₃ = 4 * r₁ * r₂ * r₃ := by
    unfold SpreadTriple tripleSpreadFunction at spreadTriple
    unfold archimedesFunction
    calc
      (r₂ + r₁ + r₃) ^ 2 -
          2 * (r₂ ^ 2 + r₁ ^ 2 + r₃ ^ 2) =
        ((r₁ + r₂ + r₃) ^ 2 -
          2 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) -
          4 * r₁ * r₂ * r₃) +
            4 * r₁ * r₂ * r₃ := by ring1
      _ = 4 * r₁ * r₂ * r₃ := by rw [spreadTriple]; ring1
  have r₃Archimedes :
      r₃ * archimedesFunction R₁ R₂ q₃ =
        4 * q₃ ^ 2 * r₁ * r₂ := by
    apply eq_of_mul_eq_mul_right r₃Nonzero
    calc
      (r₃ * archimedesFunction R₁ R₂ q₃) * r₃ =
          r₃ ^ 2 * archimedesFunction R₁ R₂ q₃ := by ring1
      _ = q₃ ^ 2 * archimedesFunction r₂ r₁ r₃ := scaledArchimedes
      _ = (4 * q₃ ^ 2 * r₁ * r₂) * r₃ := by
        rw [spreadArchimedes]
        ring1
  have q₃SquareNonzero : q₃ ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero q₃Nonzero q₃Nonzero
  have scaledCenteredEquation :
      q₃ ^ 2 * centeredRoot ^ 2 =
        q₃ ^ 2 *
          (4 * r₃ * r₁ * r₂ * archimedesFunction q₁ q₂ q₃) := by
    calc
      q₃ ^ 2 * centeredRoot ^ 2 =
          (q₃ * centeredRoot) ^ 2 := by ring1
      _ = (r₃ * fourPointNumerator) ^ 2 := by rw [numeratorCenterRelation]
      _ = r₃ ^ 2 * fourPointNumerator ^ 2 := by ring1
      _ = r₃ ^ 2 *
          (archimedesFunction q₁ q₂ q₃ *
            archimedesFunction R₁ R₂ q₃) := by rw [numeratorEquation]
      _ = r₃ * archimedesFunction q₁ q₂ q₃ *
          (r₃ * archimedesFunction R₁ R₂ q₃) := by ring1
      _ = q₃ ^ 2 *
          (4 * r₃ * r₁ * r₂ *
            archimedesFunction q₁ q₂ q₃) := by
              rw [r₃Archimedes]
              ring1
  apply eq_of_mul_eq_mul_right q₃SquareNonzero
  calc
    centeredRoot ^ 2 * q₃ ^ 2 =
        q₃ ^ 2 * centeredRoot ^ 2 := by ring1
    _ = q₃ ^ 2 *
        (4 * r₃ * r₁ * r₂ *
          archimedesFunction q₁ q₂ q₃) := scaledCenteredEquation
    _ = (4 * r₃ * r₁ * r₂ *
          archimedesFunction q₁ q₂ q₃) * q₃ ^ 2 := by ring1

def resectionCrossSpreadNumerator
    (first third opposite : K) : K :=
  4 * first * third - (first + third - opposite) ^ 2

/-- The remainder of Problem 24: the two Cross-law numerators and final
Spread-law equations determining `P₁,P₂`. -/
theorem problem_24_finish
    (q₁ q₂ r₁ r₂ R₁ R₂ R₃ v₁ v₂ P₁ P₂ : K)
    (firstCross :
      v₁ * (4 * R₁ * R₃) =
        resectionCrossSpreadNumerator R₁ R₃ q₂)
    (secondCross :
      v₂ * (4 * R₂ * R₃) =
        resectionCrossSpreadNumerator R₂ R₃ q₁)
    (firstSpreadLaw : r₂ * P₁ = v₁ * R₁)
    (secondSpreadLaw : r₁ * P₂ = v₂ * R₂) :
    v₁ * (4 * R₁ * R₃) =
        resectionCrossSpreadNumerator R₁ R₃ q₂ ∧
      v₂ * (4 * R₂ * R₃) =
        resectionCrossSpreadNumerator R₂ R₃ q₁ ∧
      r₂ * P₁ = v₁ * R₁ ∧
      r₁ * P₂ = v₂ * R₂ :=
  ⟨firstCross, secondCross, firstSpreadLaw, secondSpreadLaw⟩

/-! ## Example 25.1 -/

def clearedCrossSpread
    (commonDenominator firstNumerator thirdNumerator opposite
      spreadNumerator spreadDenominator : K) : K :=
  spreadDenominator *
      (4 * firstNumerator * thirdNumerator -
        (firstNumerator + thirdNumerator - opposite * commonDenominator) ^ 2) -
    spreadNumerator * (4 * firstNumerator * thirdNumerator)

/-- All large exact arithmetic in Example 25.1, including both resection
solutions and the selected original point. -/
theorem example_25_1_certificates :
    (33320 : K) * 925 * 169 = 6253 * 196 * 17 * 250 ∧
    (34425 : K) * 370 * 169 = 6253 * 81 * 17 * 250 ∧
    ((13456 : K) - 46216) ^ 2 = (2520 * 13) ^ 2 ∧
    ((78976 : K) - 46216) ^ 2 = (2520 * 13) ^ 2 ∧
    clearedCrossSpread (6253 : K) 33320 13456 8 169 170 = 0 ∧
    clearedCrossSpread (6253 : K) 34425 13456 13 169 425 = 0 ∧
    (169 : K) * 17 * 250 = 25 * 170 * 169 ∧
    (169 : K) * 17 * 250 = 10 * 425 * 169 ∧
    clearedCrossSpread (6253 : K) 33320 78976 8 33124 52445 = 0 ∧
    clearedCrossSpread (6253 : K) 34425 78976 13 474721 524450 = 0 ∧
    33124 * 17 * 250 * 617 = 9800 * 52445 * 169 ∧
    474721 * 17 * 250 * 617 = 14045 * 524450 * 169 := by
  unfold clearedCrossSpread
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-! ## Exercise 25.2: a direct finite-candidate solution -/

/-- The numerator of the spread between the two displayed rays based at
`base`, without constructing line quotients or dividing by their norms. -/
def sectorSpreadNumerator
    (base first second : Point K) : K :=
  ((first.x - base.x) * (second.y - base.y) -
      (first.y - base.y) * (second.x - base.x)) ^ 2

/-- A denominator-cleared check that a displayed sector has spread
`numerator/denominator`. -/
def MatchesSectorSpread
    (base first second : Point K) (numerator denominator : K) : Prop :=
  denominator * sectorSpreadNumerator base first second =
    numerator * quadrance base first * quadrance base second

/-- A point matches all three measured resection spreads directly.  This is
the coordinate alternative requested by Exercise 25.2 and contains no Euler
or Four-point polynomial. -/
def MatchesResectionReadings
    (a₁ a₂ a₃ candidate : Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) : Prop :=
  quadrance candidate a₁ ≠ 0 ∧
    quadrance candidate a₂ ≠ 0 ∧
    quadrance candidate a₃ ≠ 0 ∧
    MatchesSectorSpread candidate a₂ a₃
      r₁Numerator r₁Denominator ∧
    MatchesSectorSpread candidate a₁ a₃
      r₂Numerator r₂Denominator ∧
    MatchesSectorSpread candidate a₁ a₂
      r₃Numerator r₃Denominator

instance matchesResectionReadingsDecidable [DecidableEq K]
    (a₁ a₂ a₃ candidate : Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) :
    Decidable (MatchesResectionReadings a₁ a₂ a₃ candidate
      r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator) := by
  unfold MatchesResectionReadings MatchesSectorSpread
  infer_instance

/-- An executable alternative resection solver on any explicitly supplied
finite search region. -/
def finiteResectionSolutions [DecidableEq K]
    (candidates : List (Point K))
    (a₁ a₂ a₃ : Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) : List (Point K) :=
  candidates.filter fun candidate => decide
    (MatchesResectionReadings a₁ a₂ a₃ candidate
      r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator)

/-- Exercise 25.2: the direct finite solver returns all and only candidates
whose three cleared coordinate-spread equations match the readings. -/
theorem exercise_25_2 [DecidableEq K]
    (candidates : List (Point K))
    (a₁ a₂ a₃ candidate : Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) :
    candidate ∈ finiteResectionSolutions candidates a₁ a₂ a₃
        r₁Numerator r₁Denominator
        r₂Numerator r₂Denominator
        r₃Numerator r₃Denominator ↔
      candidate ∈ candidates ∧
        MatchesResectionReadings a₁ a₂ a₃ candidate
          r₁Numerator r₁Denominator
          r₂Numerator r₂Denominator
          r₃Numerator r₃Denominator := by
  simp only [finiteResectionSolutions, List.mem_filter, decide_eq_true_eq]

/-- The original point in Example 25.1 passes the alternative solver's three
direct tests. -/
theorem example_25_1_direct_reading_certificates :
    MatchesSectorSpread
        (⟨4, 5⟩ : Point K) ⟨5, 2⟩ ⟨3, -1⟩ 81 370 ∧
      MatchesSectorSpread
        (⟨4, 5⟩ : Point K) ⟨1, 1⟩ ⟨3, -1⟩ 196 925 ∧
      MatchesSectorSpread
        (⟨4, 5⟩ : Point K) ⟨1, 1⟩ ⟨5, 2⟩ 169 250 := by
  unfold MatchesSectorSpread sectorSpreadNumerator quadrance
  constructor
  · ring1
  constructor <;> ring1

/-! ## The reflected-circle correspondence after Example 25.1 -/

/-- The finite data needed to construct the three reflections in the sides
of a non-null reference triangle. -/
structure ReflectionTriangleData (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] where
  first : Point K
  second : Point K
  third : Point K
  base : Point K
  firstSecondDistinct : first ≠ second
  firstThirdDistinct : first ≠ third
  secondThirdDistinct : second ≠ third
  firstSecondNonNull :
    ¬ (lineThrough first second firstSecondDistinct).IsNull
  firstThirdNonNull :
    ¬ (lineThrough first third firstThirdDistinct).IsNull
  secondThirdNonNull :
    ¬ (lineThrough second third secondThirdDistinct).IsNull

namespace ReflectionTriangleData

def reflectedInSecondThird [DecidableEq K]
    (data : ReflectionTriangleData K) : Point K :=
  reflectPoint
    (lineThrough data.second data.third data.secondThirdDistinct)
    data.secondThirdNonNull data.base

def reflectedInFirstThird [DecidableEq K]
    (data : ReflectionTriangleData K) : Point K :=
  reflectPoint
    (lineThrough data.first data.third data.firstThirdDistinct)
    data.firstThirdNonNull data.base

def reflectedInFirstSecond [DecidableEq K]
    (data : ReflectionTriangleData K) : Point K :=
  reflectPoint
    (lineThrough data.first data.second data.firstSecondDistinct)
    data.firstSecondNonNull data.base

/-- A candidate lies on all three reflected circumcircles in the exact
determinant sense used by Theorem 109. -/
def IsCommonReflectedCirclePoint [DecidableEq K]
    (data : ReflectionTriangleData K) (candidate : Point K) : Prop :=
  Quadrilateral.coordinateCircleDeterminant
      data.second data.third data.reflectedInSecondThird candidate = 0 ∧
    Quadrilateral.coordinateCircleDeterminant
      data.first data.third data.reflectedInFirstThird candidate = 0 ∧
    Quadrilateral.coordinateCircleDeterminant
      data.first data.second data.reflectedInFirstSecond candidate = 0

instance isCommonReflectedCirclePointDecidable [DecidableEq K]
    (data : ReflectionTriangleData K) (candidate : Point K) :
    Decidable (data.IsCommonReflectedCirclePoint candidate) := by
  unfold IsCommonReflectedCirclePoint
  infer_instance

/-- The constructive finite version of the common-point construction cited
after Example 25.1: inspect an explicit finite region and retain precisely
the common reflected-circle points. -/
def finiteCommonReflectedCirclePoints [DecidableEq K]
    (data : ReflectionTriangleData K) (candidates : List (Point K)) :
    List (Point K) :=
  candidates.filter fun candidate => decide
    (data.IsCommonReflectedCirclePoint candidate)

theorem mem_finiteCommonReflectedCirclePoints [DecidableEq K]
    (data : ReflectionTriangleData K) (candidates : List (Point K))
    (candidate : Point K) :
    candidate ∈ data.finiteCommonReflectedCirclePoints candidates ↔
      candidate ∈ candidates ∧ data.IsCommonReflectedCirclePoint candidate := by
  simp only [finiteCommonReflectedCirclePoints, List.mem_filter,
    decide_eq_true_eq]

/-- A singleton result is an exact uniqueness certificate on the supplied
finite search region. -/
theorem common_reflected_circle_point_unique_in_finite_region
    [DecidableEq K]
    (data : ReflectionTriangleData K) (candidates : List (Point K))
    (common candidate : Point K)
    (singleton : data.finiteCommonReflectedCirclePoints candidates = [common])
    (candidateMember : candidate ∈ candidates)
    (candidateCommon : data.IsCommonReflectedCirclePoint candidate) :
    candidate = common := by
  have retained :
      candidate ∈ data.finiteCommonReflectedCirclePoints candidates :=
    (data.mem_finiteCommonReflectedCirclePoints candidates candidate).2
      ⟨candidateMember, candidateCommon⟩
  rw [singleton] at retained
  simpa only [List.mem_singleton] using retained

end ReflectionTriangleData

/-- The orthocenter of the normalized triangle with vertices
`(u,v),(0,0),(d,0)`. -/
def normalizedOrthocenter (u v d : K) : Point K :=
  ⟨u, u * (d - u) / v⟩

/-- Reflection in the normalized side joining `(0,0)` and `(d,0)`. -/
def normalizedSideReflection (x y : K) : Point K := ⟨x, -y⟩

/-- The source's many-to-one observation, in a finite coordinate normal
form: if `B` is on the reference circumcircle, reflecting `B` in the
horizontal side produces a point whose side-circle contains the orthocenter.
Cyclic relabelling gives the same statement for the other two sides. -/
theorem circumcircle_reflection_collapses_to_orthocenter_normalized
    (u v d x y : K) (vNonzero : v ≠ 0) (dNonzero : d ≠ 0)
    (baseCyclic :
      Quadrilateral.coordinateCircleDeterminant
        ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩ = 0) :
    Quadrilateral.coordinateCircleDeterminant
      ⟨0, 0⟩ ⟨d, 0⟩ (normalizedSideReflection x y)
        (normalizedOrthocenter u v d) = 0 := by
  let t := u * (d - u)
  let w := t / v
  let f := x ^ 2 + y ^ 2 - d * x
  let circleResidual := v * f + (t - v ^ 2) * y
  have expandedBase :
      Quadrilateral.coordinateCircleDeterminant
          ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩ =
        -d * circleResidual := by
    unfold Quadrilateral.coordinateCircleDeterminant
      Quadrilateral.circleRowNorm Quadrilateral.determinantThree
      circleResidual f t
    ring1
  have scaledResidualZero : d * circleResidual = 0 := by
    calc
      d * circleResidual =
          -(Quadrilateral.coordinateCircleDeterminant
            ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩) := by
              rw [expandedBase]
              ring1
      _ = 0 := by rw [baseCyclic]; ring1
  have residualZero : circleResidual = 0 :=
    eq_zero_of_mul_eq_zero_left dNonzero scaledResidualZero
  have heightCleared : w * v = t := by
    unfold w
    exact RFAP.ExplicitField.div_mul_cancel t vNonzero
  let reflectedResidual :=
    f * w + y * (u ^ 2 + w ^ 2 - d * u)
  have residualIdentity :
      v ^ 2 * reflectedResidual = t * circleResidual := by
    calc
      v ^ 2 * reflectedResidual =
          f * (w * v) * v + y * (w * v) ^ 2 -
            y * t * v ^ 2 := by
              unfold reflectedResidual t
              ring1
      _ = f * t * v + y * t ^ 2 - y * t * v ^ 2 := by
            rw [heightCleared]
      _ = t * circleResidual := by
            unfold circleResidual
            ring1
  have vSquareNonzero : v ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero vNonzero vNonzero
  have reflectedResidualZero : reflectedResidual = 0 := by
    apply eq_zero_of_mul_eq_zero_left vSquareNonzero
    calc
      v ^ 2 * reflectedResidual = t * circleResidual := residualIdentity
      _ = 0 := by rw [residualZero]; ring1
  change
    Quadrilateral.coordinateCircleDeterminant
      ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, -y⟩ ⟨u, u * (d - u) / v⟩ = 0
  have orthocenterY : u * (d - u) / v = w := by rfl
  rw [orthocenterY]
  calc
    Quadrilateral.coordinateCircleDeterminant
        ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, -y⟩ ⟨u, w⟩ =
      d * reflectedResidual := by
        unfold Quadrilateral.coordinateCircleDeterminant
          Quadrilateral.circleRowNorm Quadrilateral.determinantThree
          reflectedResidual f
        ring1
    _ = 0 := by rw [reflectedResidualZero]; ring1

/-! ## Problem 25: Hansen's problem -/

def clearedSpreadTriple
    (denominator first second third : K) : K :=
  denominator *
      ((first + second + third) ^ 2 -
        2 * (first ^ 2 + second ^ 2 + third ^ 2)) -
    4 * first * second * third

/-- Exercise 25.1's Triangle-spread-rule selection.  For the lower root the
two sectors at Collins' point are obtuse; for the upper root both would be
acute.  The four comparisons are written as exact common-denominator
integer tests, so the choice does not depend on a numerical approximation. -/
theorem exercise_25_1_triangle_rule_selection :
    clearedSpreadTriple (6290 : K) 1682 4165 6253 = 0 ∧
      clearedSpreadTriple (204425 : K) 13456 34425 81289 = 0 ∧
      clearedSpreadTriple (1940465 : K) 1934912 816340 1225588 = 0 ∧
      clearedSpreadTriple (252260450 : K)
        221843584 96699825 228340801 = 0 ∧
      (1682 + 4165 : Nat) ≤ 6253 ∧
      (13456 + 34425 : Nat) ≤ 81289 ∧
      ¬ (1934912 + 816340 : Nat) ≤ 1225588 ∧
      ¬ (221843584 + 96699825 : Nat) ≤ 228340801 := by
  unfold clearedSpreadTriple
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  decide

def clearedTwoSpreadTriplesValue
    (denominator first second third fourth
      outputNumerator outputDenominator : K) : K :=
  outputDenominator * ((first - second) ^ 2 - (third - fourth) ^ 2) -
    outputNumerator * 2 *
      (denominator * (first + second - third - fourth) -
        2 * first * second + 2 * third * fourth)

/-- The three Triangle-spread and two Two-spread-triples calculations in
Problem 25, all on their least convenient common denominators. -/
theorem problem_25_spread_certificates :
    clearedSpreadTriple (4250 : K) 3610 2873 3025 = 0 ∧
    clearedSpreadTriple (6970 : K) 4410 2057 6929 = 0 ∧
    clearedSpreadTriple (10250 : K) 6929 3025 10240 = 0 ∧
    clearedTwoSpreadTriplesValue (34850 : K)
      34816 29602 24805 10285 121 697 = 0 ∧
    clearedTwoSpreadTriplesValue (174250 : K)
      174080 110250 117793 173225 169 425 = 0 := by
  unfold clearedSpreadTriple clearedTwoSpreadTriplesValue
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The Alternate-spreads ratio and square witness used by the Spread-from-
ratio theorem in Problem 25. -/
theorem problem_25_ratio_certificates :
    (441 * 169 * 121 * 425 * 410 * 425 * 14801 : K) =
      11025 * (697 * 250 * 697) * (169 * 121 * 361) ∧
    11025 * 1 * 606841 = 441 * 14801 * 1025 ∧
    606841 = 779 ^ 2 ∧
    441 = 21 ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

def spreadFromRatioCandidateCertificate
    (xNumerator xDenominator yNumerator yDenominator sign : Int) : Prop :=
  14801 * xNumerator * yDenominator =
      11025 * yNumerator * xDenominator ∧
    yNumerator *
        (11025 * 779 + 14801 * 779 + sign * 42 * 14801) * 1025 =
      1024 * yDenominator * 14801 * 779

/-- Both exact `[x,y]` candidates printed in Problem 25. -/
theorem problem_25_spread_candidates :
    spreadFromRatioCandidateCertificate 441 1066 361 650 1 ∧
      spreadFromRatioCandidateCertificate
        112896 256537 92416 156425 (-1) := by
  unfold spreadFromRatioCandidateCertificate
  decide

/-- The general denominator-cleared pair of equations used by the Spread
from ratio theorem.  `sign=1` selects the `+2r` denominator and `sign=-1`
selects the other finite candidate. -/
def clearedSpreadFromRatioCandidate
    (aNumerator aDenominator spreadNumerator spreadDenominator
      rootNumerator rootDenominator
      xNumerator xDenominator yNumerator yDenominator sign : Int) : Prop :=
  aDenominator * xNumerator * yDenominator =
      aNumerator * yNumerator * xDenominator ∧
    yNumerator * spreadDenominator *
        (aNumerator * rootDenominator +
          aDenominator * rootDenominator +
          sign * 2 * rootNumerator * aDenominator) =
      yDenominator * spreadNumerator * aDenominator * rootDenominator

/-- The selected first candidate gives the four required quadrances
`Q(A,D)=17`, `Q(B,C)=17`, `Q(A,C)=41`, `Q(B,D)=25`; the last four equations
also check the source's coordinates directly. -/
theorem problem_25_final_quadrances :
    (361 * 650 * 17 : Int) = 361 * 425 * 26 ∧
    (441 * 1066 * 17 : Int) = 441 * 697 * 26 ∧
    (121 * 170 * 41 : Int) = 121 * 410 * 17 ∧
    (169 * 170 * 25 : Int) = 169 * 250 * 17 ∧
    ((1 : Int) ^ 2 + 5 ^ 2 = 26) ∧
    ((5 : Int) ^ 2 + 4 ^ 2 = 41) ∧
    (((5 : Int) - 1) ^ 2 + (4 - 5) ^ 2 = 17) ∧
    ((4 : Int) ^ 2 + 1 ^ 2 = 17) ∧
    (((4 : Int) - 1) ^ 2 + (1 - 5) ^ 2 = 25) := by
  decide

/-! ## Exercise 25.3 -/

/-- The three Triangle-spread calculations in Exercise 25.3.  The first two
recover the two missing measured spreads `2809/10730` and `784/2465`; the
third gives the crossing spread `1089/1258`. -/
theorem exercise_25_3_triangle_spread_certificates :
    clearedSpreadTriple (10730 : K) 2809 3712 9065 = 0 ∧
      clearedSpreadTriple (4930 : K) 1568 1421 4165 = 0 ∧
      clearedSpreadTriple (6290 : K) 1813 2176 5445 = 0 := by
  unfold clearedSpreadTriple
  constructor
  · ring1
  constructor <;> ring1

/-- The two Two-spread-triples evaluations in Exercise 25.3.  All four
inputs use the common denominator `182410`. -/
theorem exercise_25_3_two_spread_certificates :
    clearedTwoSpreadTriplesValue (182410 : K)
        157905 47753 154105 52577 2401 2465 = 0 ∧
      clearedTwoSpreadTriplesValue (182410 : K)
        157905 58016 63104 154105 10201 10730 = 0 := by
  unfold clearedTwoSpreadTriplesValue
  constructor <;> ring1

/-- The Alternate-spreads ratio and its exact square witness for Exercise
25.3. -/
theorem exercise_25_3_ratio_certificates :
    ((784 * 64 * 2401) * (10730 * 170 * 10730) * 487128353 : K) =
        727752704 * (2465 * 185 * 2465) * (10201 * 49 * 2809) ∧
      (727752704 * 169 * 8281182001 : K) =
        1662029824 * 487128353 * 1258 ∧
      (1662029824 : K) = 40768 ^ 2 ∧
      (8281182001 : K) = 91001 ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- Exercise 25.3's printed `x` and `y` are exactly the `+2r` solution of
the derived Spread-from-ratio equations, and both are proper positive
spreads. -/
theorem exercise_25_3_answer_certificates :
    clearedSpreadFromRatioCandidate
        727752704 487128353 1089 1258 40768 91001
        9834496 25778545 28654609 112212490 1 ∧
      0 < 9834496 ∧ 9834496 < 25778545 ∧
      0 < 28654609 ∧ 28654609 < 112212490 := by
  unfold clearedSpreadFromRatioCandidate
  decide

end ResectionApplications
end DivineProportions
