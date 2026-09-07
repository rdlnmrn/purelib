import DivineProportions.Examples.ChapterFourteenPentagonMetrics
import DivineProportions.Space.Metric

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace DivineProportions
namespace PlatonicSolids

open Vector3

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

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-! ## A common isosceles-spread certificate -/

/-- Suppose the base quadrance is `baseNumerator/baseDenominator` and each
equal quadrance is `radiusNumerator/radiusDenominator`.  This is exactly the
cross-multiplied assertion that the isosceles vertex spread is
`spreadNumerator/spreadDenominator`. -/
def ClearedIsoscelesSpread
    (baseNumerator baseDenominator radiusNumerator radiusDenominator
      spreadNumerator spreadDenominator : K) : Prop :=
  spreadDenominator * baseNumerator * radiusDenominator *
      (4 * radiusNumerator * baseDenominator -
        baseNumerator * radiusDenominator) =
    spreadNumerator * 4 * radiusNumerator ^ 2 * baseDenominator ^ 2

/-- The corresponding endpoint spread `1-base/(4 radius)`, again with all
denominators cleared. -/
def ClearedIsoscelesEndpointSpread
    (baseNumerator baseDenominator radiusNumerator radiusDenominator
      spreadNumerator spreadDenominator : K) : Prop :=
  spreadDenominator *
      (4 * radiusNumerator * baseDenominator -
        baseNumerator * radiusDenominator) =
    spreadNumerator * 4 * radiusNumerator * baseDenominator

/-- The regular tetrahedron's face spread is `8/9`. -/
theorem tetrahedron_face_spread_cleared (Q : K) :
    ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 := by
  unfold ClearedIsoscelesSpread
  ring1

/-- The cube has perpendicular faces, while its opposite center rays have
the tetrahedral spread `8/9`. -/
theorem cube_face_and_center_spreads_cleared (Q : K) :
    (1 : K) = 1 ∧
      ClearedIsoscelesEndpointSpread (2 * Q) 1 (3 * Q) 4 1 3 ∧
      ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 := by
  constructor
  · rfl
  constructor
  · unfold ClearedIsoscelesEndpointSpread
    ring1
  unfold ClearedIsoscelesSpread
  ring1

/-- The three Pythagorean quadrance steps in the cube section.  `quarter` is
the common value `Q/4`; the conclusions are the cleared forms of `Q/2`,
`3Q/4`, and `2Q`. -/
theorem cube_quadrance_chain_cleared
    (quarter Q : K) (quarterValue : 4 * quarter = Q) :
    2 * (2 * quarter) = Q ∧
      4 * (3 * quarter) = 3 * Q ∧
      8 * quarter = 2 * Q := by
  constructor
  · calc
      2 * (2 * quarter) = 4 * quarter := by ring1
      _ = Q := quarterValue
  constructor
  · calc
      4 * (3 * quarter) = 3 * (4 * quarter) := by ring1
      _ = 3 * Q := by rw [quarterValue]
  · calc
      8 * quarter = 2 * (4 * quarter) := by ring1
      _ = 2 * Q := by rw [quarterValue]

/-- The octahedron has the same numerical face spread as the tetrahedron,
with base quadrance `2Q` and equal midpoint quadrances `3Q/4`. -/
theorem octahedron_face_spread_cleared (Q : K) :
    ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 := by
  unfold ClearedIsoscelesSpread
  ring1

/-- The closed integer comparisons distinguishing the acute tetrahedral and
obtuse octahedral sectors. -/
theorem tetrahedron_octahedron_sector_types :
    (2 : Nat) < 3 ∧ (3 : Nat) < 4 := by
  decide

/-! ## Exercise 26.1: centroid and center -/

def tripleSum (first second third : Vector3 K) : Vector3 K :=
  add (add first second) third

/-- Displacement from one tetrahedron vertex to the centroid of its opposite
face, expressed in its three outgoing edge vectors. -/
def oppositeFaceCentroidDisplacement
    (first second third : Vector3 K) : Vector3 K :=
  scale ((1 : K) / 3) (tripleSum first second third)

/-- Displacement from one tetrahedron vertex to the tetrahedron center. -/
def tetrahedronCenterDisplacement
    (first second third : Vector3 K) : Vector3 K :=
  scale ((1 : K) / 4) (tripleSum first second third)

/-- Three equal outgoing edges whose pairwise endpoint distances are also
`Q` have triple-sum quadrance `6Q`. -/
theorem regular_tetrahedron_triple_sum_quadrance
    (first second third : Vector3 K) (Q : K)
    (firstQuadrance : Vector3.quadrance first = Q)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = Q)
    (firstSecondDot : 2 * dot first second = Q)
    (firstThirdDot : 2 * dot first third = Q)
    (secondThirdDot : 2 * dot second third = Q) :
    Vector3.quadrance (tripleSum first second third) = 6 * Q := by
  unfold tripleSum
  calc
    Vector3.quadrance (add (add first second) third) =
        Vector3.quadrance first + Vector3.quadrance second +
          Vector3.quadrance third +
          2 * dot first second + 2 * dot first third +
          2 * dot second third := by
            rw [quadrance_add, quadrance_add, dot_add_left]
            ring1
    _ = 6 * Q := by
      rw [firstQuadrance, secondQuadrance, thirdQuadrance,
        firstSecondDot, firstThirdDot, secondThirdDot]
      ring1

/-- Exercise 26.1.  The two displayed quotient formulas are kept in their
stronger cleared forms `3Q(A,G)=2Q` and `8Q(A,P)=3Q`. -/
theorem exercise_26_1
    (first second third : Vector3 K) (Q : K)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (firstQuadrance : Vector3.quadrance first = Q)
    (secondQuadrance : Vector3.quadrance second = Q)
    (thirdQuadrance : Vector3.quadrance third = Q)
    (firstSecondDot : 2 * dot first second = Q)
    (firstThirdDot : 2 * dot first third = Q)
    (secondThirdDot : 2 * dot second third = Q) :
    3 * Vector3.quadrance
        (oppositeFaceCentroidDisplacement first second third) =
        2 * Q ∧
      8 * Vector3.quadrance
        (tetrahedronCenterDisplacement first second third) =
        3 * Q := by
  have sumQuadrance := regular_tetrahedron_triple_sum_quadrance
    first second third Q firstQuadrance secondQuadrance thirdQuadrance
    firstSecondDot firstThirdDot secondThirdDot
  have oneThirdCancel : ((1 : K) / 3) * 3 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 threeNonzero
  have fourNonzero := four_ne_zero twoNonzero
  have oneFourthCancel : ((1 : K) / 4) * 4 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 fourNonzero
  constructor
  · unfold oppositeFaceCentroidDisplacement
    rw [quadrance_scale, sumQuadrance]
    calc
      3 * (((1 : K) / 3) ^ 2 * (6 * Q)) =
          2 * ((((1 : K) / 3) * 3) ^ 2) * Q := by ring1
      _ = 2 * Q := by rw [oneThirdCancel]; ring1
  · unfold tetrahedronCenterDisplacement
    rw [quadrance_scale, sumQuadrance]
    calc
      8 * (((1 : K) / 4) ^ 2 * (6 * Q)) =
          3 * ((((1 : K) / 4) * 4) ^ 2) * Q := by ring1
      _ = 3 * Q := by rw [oneFourthCancel]; ring1

/-- Exercise 26.2 and the cube calculation use the identical cleared
isosceles certificate, so the center-ray spread equals the face spread. -/
theorem exercise_26_2 (Q : K) :
    ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 ∧
      ClearedIsoscelesSpread Q 1 (3 * Q) 8 8 9 := by
  exact ⟨tetrahedron_face_spread_cleared Q,
    by unfold ClearedIsoscelesSpread; ring1⟩

/-! ## Exercise 26.3: five around an edge, but not six -/

/-- `8/9` lies below the larger order-five zero (the quadratic factor is
negative there), but above the order-six threshold `3/4`.  These are the
exact finite comparisons used in Exercise 26.3. -/
theorem exercise_26_3 :
    (405 - 20 * 8 * 9 + 16 * 8 ^ 2 : Int) = -11 ∧
      (405 - 20 * 8 * 9 + 16 * 8 ^ 2 : Int) < 0 ∧
      (3 * 9 : Nat) < 8 * 4 := by
  decide

/-! ## Icosahedron and dodecahedron -/

namespace Golden

abbrev alpha (root : K) : K :=
  ChapterFourteenExamples.ExercisesFourteenThreeFour.alpha root

abbrev beta (root : K) : K :=
  ChapterFourteenExamples.ExercisesFourteenThreeFour.beta root

private theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

private theorem sixtyFour_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (64 : K) ≠ 0 := by
  rw [show (64 : K) = 2 * 2 * 2 * 2 * 2 * 2 by ring1]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
          twoNonzero) twoNonzero) twoNonzero) twoNonzero

/-- The golden identity used to simplify the icosahedral face spread. -/
theorem beta_mul_three_alpha_sub_beta_eq_alpha_square
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    beta root * (3 * alpha root - beta root) = alpha root ^ 2 := by
  have eightNonzero := eight_ne_zero twoNonzero
  have alphaEight : alpha root * 8 = 5 - root :=
    RFAP.ExplicitField.div_mul_cancel _ eightNonzero
  have betaEight : beta root * 8 = 5 + root :=
    RFAP.ExplicitField.div_mul_cancel _ eightNonzero
  apply eq_of_mul_eq_mul_right (sixtyFour_ne_zero twoNonzero)
  calc
    (beta root * (3 * alpha root - beta root)) * 64 =
        (beta root * 8) *
          (3 * (alpha root * 8) - beta root * 8) := by ring1
    _ = (5 + root) * (3 * (5 - root) - (5 + root)) := by
      rw [alphaEight, betaEight]
    _ = (5 - root) ^ 2 := by
      apply sub_eq_zero.mp
      calc
        (5 + root) * (3 * (5 - root) - (5 + root)) -
            (5 - root) ^ 2 = -5 * (root ^ 2 - 5) := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = alpha root ^ 2 * 64 := by rw [← alphaEight]; ring1

/-- The golden identity used to simplify the dodecahedral face spread. -/
theorem five_mul_four_alpha_sub_one_eq_sixteen_alpha_square
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 * (4 * alpha root - 1) = 16 * alpha root ^ 2 := by
  have factor :=
    ChapterFourteenExamples.ExercisesFourteenThreeFour.factor_alpha
      root rootSquare twoNonzero
  apply sub_eq_zero.mp
  calc
    5 * (4 * alpha root - 1) - 16 * alpha root ^ 2 =
        -(5 - 20 * alpha root + 16 * alpha root ^ 2) := by ring1
    _ = 0 := by rw [factor]; ring1

end Golden

/-- The icosahedral face-spread simplification to `4/9`, with the pentagon
diagonal `βQ/α` and midpoint quadrance `3Q/4`. -/
theorem icosahedron_face_spread_cleared
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    ClearedIsoscelesSpread
      (Golden.beta root * Q) (Golden.alpha root) (3 * Q) 4 4 9 := by
  have golden := Golden.beta_mul_three_alpha_sub_beta_eq_alpha_square
    root rootSquare twoNonzero
  apply sub_eq_zero.mp
  calc
    9 * (Golden.beta root * Q) * 4 *
          (4 * (3 * Q) * Golden.alpha root -
            Golden.beta root * Q * 4) -
        4 * 4 * (3 * Q) ^ 2 * Golden.alpha root ^ 2 =
      144 * Q ^ 2 *
        (Golden.beta root *
            (3 * Golden.alpha root - Golden.beta root) -
          Golden.alpha root ^ 2) := by ring1
    _ = 0 := by rw [golden]; ring1

/-- The dodecahedral face-spread simplification to `4/5`. -/
theorem dodecahedron_face_spread_cleared
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    ClearedIsoscelesSpread
      (Golden.beta root * Q) (Golden.alpha root)
      (Golden.beta root * Q) 1 4 5 := by
  have golden := Golden.five_mul_four_alpha_sub_one_eq_sixteen_alpha_square
    root rootSquare twoNonzero
  apply sub_eq_zero.mp
  calc
    5 * (Golden.beta root * Q) * 1 *
          (4 * (Golden.beta root * Q) * Golden.alpha root -
            Golden.beta root * Q * 1) -
        4 * 4 * (Golden.beta root * Q) ^ 2 *
          Golden.alpha root ^ 2 =
      Golden.beta root ^ 2 * Q ^ 2 *
        (5 * (4 * Golden.alpha root - 1) -
          16 * Golden.alpha root ^ 2) := by ring1
    _ = 0 := by rw [golden]; ring1

/-! ## Exercise 26.4: an explicit finite icosahedron -/

/-- A uniformly scaled standard icosahedron neighborhood.  Scaling by four
removes every `/2` from the usual golden-ratio coordinates. -/
def icosahedronV (root : K) : Point3 K := ⟨0, 4, 2 * (1 + root)⟩
def icosahedronA (root : K) : Point3 K := ⟨4, 2 * (1 + root), 0⟩
def icosahedronD (root : K) : Point3 K := ⟨0, -4, 2 * (1 + root)⟩
def icosahedronE (root : K) : Point3 K := ⟨2 * (1 + root), 0, 4⟩
def icosahedronG (root : K) : Point3 K := ⟨-4, -2 * (1 + root), 0⟩

/-- The midpoint of `VE`, written directly in the scaled coordinates. -/
def icosahedronM (root : K) : Point3 K := ⟨1 + root, 2, 3 + root⟩

/-- The displayed point `M` really is the midpoint of `VE`, in cleared
coordinate form. -/
theorem icosahedronM_midpoint_cleared (root : K) :
    add (icosahedronV root) (icosahedronE root) =
      scale 2 (icosahedronM root) := by
  unfold icosahedronV icosahedronE icosahedronM add scale
  congr 1 <;> ring1

/-- All metric and dot-product calculations needed for Exercise 26.4. -/
theorem exercise_26_4_metric_certificates
    (root : K) (rootSquare : root ^ 2 = 5) :
    Vector3.quadrance (sub (icosahedronD root) (icosahedronM root)) = 48 ∧
      Vector3.quadrance (sub (icosahedronA root) (icosahedronM root)) = 48 ∧
      Vector3.quadrance (sub (icosahedronG root) (icosahedronM root)) =
        80 + 32 * root ∧
      dot (sub (icosahedronD root) (icosahedronM root))
          (sub (icosahedronG root) (icosahedronM root)) =
        32 + 16 * root ∧
      dot (sub (icosahedronA root) (icosahedronM root))
          (sub (icosahedronG root) (icosahedronM root)) = -16 ∧
      Vector3.quadrance (sub (icosahedronA root) (icosahedronG root)) =
        32 * (5 + root) := by
  dsimp [icosahedronA, icosahedronD, icosahedronG, icosahedronM,
    Vector3.quadrance, Vector3.dot, Vector3.sub]
  constructor
  · apply sub_eq_zero.mp
    calc
      _ = 2 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · apply sub_eq_zero.mp
    calc
      _ = 6 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · apply sub_eq_zero.mp
    calc
      _ = 6 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  constructor
  · ring1
  constructor
  · apply sub_eq_zero.mp
    calc
      _ = -2 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1
  · apply sub_eq_zero.mp
    calc
      _ = 16 * (root ^ 2 - 5) := by ring1
      _ = 0 := by rw [rootSquare]; ring1

private theorem directionSpread_residual_formula
    (first second : Vector3 K)
    (firstNonzero : Vector3.quadrance first ≠ 0)
    (secondNonzero : Vector3.quadrance second ≠ 0) :
    directionSpread first second firstNonzero secondNonzero =
      (Vector3.quadrance first * Vector3.quadrance second -
          dot first second ^ 2) /
        (Vector3.quadrance first * Vector3.quadrance second) := by
  have denominatorNonzero :
      Vector3.quadrance first * Vector3.quadrance second ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonzero secondNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  unfold directionSpread
  have leftCancel := RFAP.ExplicitField.div_mul_cancel
    (dot first second ^ 2) denominatorNonzero
  have rightCancel := RFAP.ExplicitField.div_mul_cancel
    (Vector3.quadrance first * Vector3.quadrance second - dot first second ^ 2)
      denominatorNonzero
  calc
    (1 - dot first second ^ 2 /
          (Vector3.quadrance first * Vector3.quadrance second)) *
        (Vector3.quadrance first * Vector3.quadrance second) =
      Vector3.quadrance first * Vector3.quadrance second -
        (dot first second ^ 2 /
          (Vector3.quadrance first * Vector3.quadrance second)) *
          (Vector3.quadrance first * Vector3.quadrance second) := by ring1
    _ = Vector3.quadrance first * Vector3.quadrance second -
        dot first second ^ 2 := by
      rw [leftCancel]
    _ = ((Vector3.quadrance first * Vector3.quadrance second -
          dot first second ^ 2) /
          (Vector3.quadrance first * Vector3.quadrance second)) *
        (Vector3.quadrance first * Vector3.quadrance second) :=
      rightCancel.symm

/-- Exercise 26.4's two exact spreads and final long quadrance.  Nonzero
hypotheses name precisely the denominators used in the printed fractions. -/
theorem exercise_26_4
    (root : K) (rootSquare : root ^ 2 = 5)
    (fortyEightNonzero : (48 : K) ≠ 0)
    (longMetricNonzero : (80 : K) + 32 * root ≠ 0)
    (fifteenNonzero : (15 : K) ≠ 0) :
    directionSpread
        (sub (icosahedronD root) (icosahedronM root))
        (sub (icosahedronG root) (icosahedronM root))
        (by
          rw [(exercise_26_4_metric_certificates root rootSquare).1]
          exact fortyEightNonzero)
        (by
          rw [(exercise_26_4_metric_certificates root rootSquare).2.2.1]
          exact longMetricNonzero) =
      (10 - 2 * root) / 15 ∧
    directionSpread
        (sub (icosahedronA root) (icosahedronM root))
        (sub (icosahedronG root) (icosahedronM root))
        (by
          rw [(exercise_26_4_metric_certificates root rootSquare).2.1]
          exact fortyEightNonzero)
        (by
          rw [(exercise_26_4_metric_certificates root rootSquare).2.2.1]
          exact longMetricNonzero) =
      (10 + 2 * root) / 15 ∧
    Vector3.quadrance (sub (icosahedronA root) (icosahedronG root)) =
      32 * (5 + root) := by
  let metrics := exercise_26_4_metric_certificates root rootSquare
  have denominatorNonzero :
      (48 : K) * (80 + 32 * root) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fortyEightNonzero longMetricNonzero
  constructor
  · rw [directionSpread_residual_formula]
    rw [metrics.1, metrics.2.2.1, metrics.2.2.2.1]
    apply eq_of_mul_eq_mul_right
      (RFAP.ExplicitField.mul_ne_zero denominatorNonzero fifteenNonzero)
    have leftCancel := RFAP.ExplicitField.div_mul_cancel
      (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2)
      denominatorNonzero
    have rightCancel := RFAP.ExplicitField.div_mul_cancel
      (10 - 2 * root) fifteenNonzero
    calc
      ((48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) /
          (48 * (80 + 32 * root))) *
          ((48 * (80 + 32 * root)) * 15) =
        (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) * 15 := by
          rw [← mul_assoc, leftCancel]
      _ = (10 - 2 * root) * (48 * (80 + 32 * root)) := by
        apply sub_eq_zero.mp
        calc
          (48 * (80 + 32 * root) - (32 + 16 * root) ^ 2) * 15 -
              (10 - 2 * root) * (48 * (80 + 32 * root)) =
            -768 * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [rootSquare]; ring1
      _ = ((10 - 2 * root) / 15) *
          ((48 * (80 + 32 * root)) * 15) := by
        calc
          (10 - 2 * root) * (48 * (80 + 32 * root)) =
              (((10 - 2 * root) / 15) * 15) *
                (48 * (80 + 32 * root)) := by rw [rightCancel]
          _ = ((10 - 2 * root) / 15) *
              ((48 * (80 + 32 * root)) * 15) := by ring1
  constructor
  · rw [directionSpread_residual_formula]
    rw [metrics.2.1, metrics.2.2.1, metrics.2.2.2.2.1]
    apply eq_of_mul_eq_mul_right
      (RFAP.ExplicitField.mul_ne_zero denominatorNonzero fifteenNonzero)
    have leftCancel := RFAP.ExplicitField.div_mul_cancel
      (48 * (80 + 32 * root) - (-16) ^ 2) denominatorNonzero
    have rightCancel := RFAP.ExplicitField.div_mul_cancel
      (10 + 2 * root) fifteenNonzero
    calc
      ((48 * (80 + 32 * root) - (-16) ^ 2) /
          (48 * (80 + 32 * root))) *
          ((48 * (80 + 32 * root)) * 15) =
        (48 * (80 + 32 * root) - (-16) ^ 2) * 15 := by
          rw [← mul_assoc, leftCancel]
      _ = (10 + 2 * root) * (48 * (80 + 32 * root)) := by
        apply sub_eq_zero.mp
        calc
          (48 * (80 + 32 * root) - (-16) ^ 2) * 15 -
              (10 + 2 * root) * (48 * (80 + 32 * root)) =
            -3072 * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [rootSquare]; ring1
      _ = ((10 + 2 * root) / 15) *
          ((48 * (80 + 32 * root)) * 15) := by
        calc
          (10 + 2 * root) * (48 * (80 + 32 * root)) =
              (((10 + 2 * root) / 15) * 15) *
                (48 * (80 + 32 * root)) := by rw [rightCancel]
          _ = ((10 + 2 * root) / 15) *
              ((48 * (80 + 32 * root)) * 15) := by ring1
  · exact metrics.2.2.2.2.2

/-- The complete finite face-spread summary in the source order:
tetrahedron, cube, octahedron, icosahedron, dodecahedron. -/
theorem platonic_face_spread_summary
    (root Q : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    ClearedIsoscelesSpread Q 1 (3 * Q) 4 8 9 ∧
      (1 : K) = 1 ∧
      ClearedIsoscelesSpread (2 * Q) 1 (3 * Q) 4 8 9 ∧
      ClearedIsoscelesSpread
        (Golden.beta root * Q) (Golden.alpha root) (3 * Q) 4 4 9 ∧
      ClearedIsoscelesSpread
        (Golden.beta root * Q) (Golden.alpha root)
          (Golden.beta root * Q) 1 4 5 := by
  exact ⟨tetrahedron_face_spread_cleared Q, rfl,
    octahedron_face_spread_cleared Q,
    icosahedron_face_spread_cleared root Q rootSquare twoNonzero,
    dodecahedron_face_spread_cleared root Q rootSquare twoNonzero⟩

end PlatonicSolids
end DivineProportions
