import DivineProportions.Applications.RationalSphericalCoordinates
import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

namespace DivineProportions
namespace Ellipson

variable {K : Type*} [RFAP.ExplicitField K]

/-- The residual of the ellipson's Triple-spread equation. -/
def polynomial (x y z : K) : K :=
  (x + y + z) ^ 2 - 2 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * x * y * z

/-- The ellipson consists of the zeros of its defining polynomial. -/
def Contains (x y z : K) : Prop :=
  polynomial x y z = 0

/-! ## Symmetry and the tetrahedral cube boundary -/

/-- The defining polynomial is invariant under every permutation of its
three coordinates. -/
theorem polynomial_permutations (x y z : K) :
    polynomial x y z = polynomial x z y ∧
      polynomial x y z = polynomial y x z ∧
      polynomial x y z = polynomial y z x ∧
      polynomial x y z = polynomial z x y ∧
      polynomial x y z = polynomial z y x := by
  unfold polynomial
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- Consequently the ellipson has the full coordinate-permutation symmetry
visible in its equation. -/
theorem contains_permutations (x y z : K) :
    (Contains x y z ↔ Contains x z y) ∧
      (Contains x y z ↔ Contains y x z) ∧
      (Contains x y z ↔ Contains y z x) ∧
      (Contains x y z ↔ Contains z x y) ∧
      (Contains x y z ↔ Contains z y x) := by
  rcases polynomial_permutations x y z with
    ⟨first, second, third, fourth, fifth⟩
  unfold Contains
  constructor
  · rw [first]
  constructor
  · rw [second]
  constructor
  · rw [third]
  constructor
  · rw [fourth]
  · rw [fifth]

/-- The four vertices named in Appendix B lie on the ellipson. -/
theorem tetrahedron_vertices :
    Contains (0 : K) 0 0 ∧
      Contains (1 : K) 1 0 ∧
      Contains (1 : K) 0 1 ∧
      Contains (0 : K) 1 1 := by
  unfold Contains polynomial
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The oriented determinant of the three tetrahedral edge vectors is `-2`.
Its magnitude gives the numerator `2` in the usual `2/6=1/3` volume. -/
theorem tetrahedron_oriented_six_volume :
    Quadrilateral.determinantThree
      (1 : K) 1 0
      1 0 1
      0 1 1 = -2 := by
  unfold Quadrilateral.determinantThree
  ring1

/-- Denominator-cleared certificate for the source's tetrahedron volume
`1/3`, paired with the determinant calculation that supplies it. -/
theorem tetrahedron_volume_certificate :
    Quadrilateral.determinantThree
        (1 : K) 1 0
        1 0 1
        0 1 1 = -2 ∧
      3 * 2 = 6 * (1 : K) := by
  exact ⟨tetrahedron_oriented_six_volume, by ring1⟩

/-- The algebraic boundary of the unit cube: at least one coordinate is
`0` or `1`.  This definition is meaningful over every explicit field and
does not invoke an ordered interval. -/
def OnCubeBoundary (x y z : K) : Prop :=
  x = 0 ∨ x = 1 ∨ y = 0 ∨ y = 1 ∨ z = 0 ∨ z = 1

/-- The six edges of the tetrahedron printed in Appendix B. -/
def OnTetrahedronEdge (x y z : K) : Prop :=
  (x = 0 ∧ y = z) ∨
    (x = 1 ∧ y + z = 1) ∨
    (y = 0 ∧ x = z) ∨
    (y = 1 ∧ x + z = 1) ∨
    (z = 0 ∧ x = y) ∨
    (z = 1 ∧ x + y = 1)

theorem x_zero_face_square (y z : K) :
    Contains 0 y z ↔ (y - z) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (y - z) ^ 2 = -((0 + y + z) ^ 2 -
          2 * (0 ^ 2 + y ^ 2 + z ^ 2) - 4 * 0 * y * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (0 + y + z) ^ 2 - 2 * (0 ^ 2 + y ^ 2 + z ^ 2) -
          4 * 0 * y * z = -(y - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

theorem x_one_face_square (y z : K) :
    Contains 1 y z ↔ (1 - y - z) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (1 - y - z) ^ 2 = -((1 + y + z) ^ 2 -
          2 * (1 ^ 2 + y ^ 2 + z ^ 2) - 4 * 1 * y * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (1 + y + z) ^ 2 - 2 * (1 ^ 2 + y ^ 2 + z ^ 2) -
          4 * 1 * y * z = -(1 - y - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

theorem y_zero_face_square (x z : K) :
    Contains x 0 z ↔ (x - z) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (x - z) ^ 2 = -((x + 0 + z) ^ 2 -
          2 * (x ^ 2 + 0 ^ 2 + z ^ 2) - 4 * x * 0 * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + 0 + z) ^ 2 - 2 * (x ^ 2 + 0 ^ 2 + z ^ 2) -
          4 * x * 0 * z = -(x - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

theorem y_one_face_square (x z : K) :
    Contains x 1 z ↔ (1 - x - z) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (1 - x - z) ^ 2 = -((x + 1 + z) ^ 2 -
          2 * (x ^ 2 + 1 ^ 2 + z ^ 2) - 4 * x * 1 * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + 1 + z) ^ 2 - 2 * (x ^ 2 + 1 ^ 2 + z ^ 2) -
          4 * x * 1 * z = -(1 - x - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

theorem z_zero_face_square (x y : K) :
    Contains x y 0 ↔ (x - y) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (x - y) ^ 2 = -((x + y + 0) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + 0 ^ 2) - 4 * x * y * 0) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + y + 0) ^ 2 - 2 * (x ^ 2 + y ^ 2 + 0 ^ 2) -
          4 * x * y * 0 = -(x - y) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

theorem z_one_face_square (x y : K) :
    Contains x y 1 ↔ (1 - x - y) ^ 2 = 0 := by
  unfold Contains polynomial
  constructor
  · intro equation
    calc
      (1 - x - y) ^ 2 = -((x + y + 1) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + 1 ^ 2) - 4 * x * y * 1) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + y + 1) ^ 2 - 2 * (x ^ 2 + y ^ 2 + 1 ^ 2) -
          4 * x * y * 1 = -(1 - x - y) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

private theorem square_eq_zero_iff [DecidableEq K] (value : K) :
    value ^ 2 = 0 ↔ value = 0 := by
  constructor
  · intro squareZero
    by_cases valueZero : value = 0
    · exact valueZero
    · have squareNonzero : value * value ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
      exact False.elim (squareNonzero (by simpa [pow_two] using squareZero))
  · intro valueZero
    rw [valueZero]
    ring1

private theorem equal_of_difference_square_zero [DecidableEq K]
    (left right : K) (squareZero : (left - right) ^ 2 = 0) :
    left = right := by
  exact sub_eq_zero.mp ((square_eq_zero_iff (left - right)).mp squareZero)

private theorem sum_eq_one_of_square_zero [DecidableEq K]
    (left right : K) (squareZero : (1 - left - right) ^ 2 = 0) :
    left + right = 1 := by
  have linearZero := (square_eq_zero_iff (1 - left - right)).mp squareZero
  apply sub_eq_zero.mp
  calc
    left + right - 1 = -(1 - left - right) := by ring1
    _ = 0 := by rw [linearZero]; ring1

/-- On fields with decidable equality, the ellipson meets the algebraic cube
boundary at exactly the six edges of the displayed tetrahedron. -/
theorem cube_boundary_intersection [DecidableEq K] (x y z : K) :
    Contains x y z ∧ OnCubeBoundary x y z ↔ OnTetrahedronEdge x y z := by
  constructor
  · rintro ⟨onEllipson, boundary⟩
    rcases boundary with xZero | xOne | yZero | yOne | zZero | zOne
    · apply Or.inl
      refine ⟨xZero, ?_⟩
      apply equal_of_difference_square_zero y z
      exact (x_zero_face_square y z).mp (by simpa [xZero] using onEllipson)
    · apply Or.inr
      apply Or.inl
      refine ⟨xOne, ?_⟩
      apply sum_eq_one_of_square_zero y z
      exact (x_one_face_square y z).mp (by simpa [xOne] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨yZero, ?_⟩
      apply equal_of_difference_square_zero x z
      exact (y_zero_face_square x z).mp (by simpa [yZero] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨yOne, ?_⟩
      apply sum_eq_one_of_square_zero x z
      exact (y_one_face_square x z).mp (by simpa [yOne] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨zZero, ?_⟩
      apply equal_of_difference_square_zero x y
      exact (z_zero_face_square x y).mp (by simpa [zZero] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      refine ⟨zOne, ?_⟩
      apply sum_eq_one_of_square_zero x y
      exact (z_one_face_square x y).mp (by simpa [zOne] using onEllipson)
  · intro edge
    rcases edge with xEdge | xOpposite | yEdge | yOpposite | zEdge | zOpposite
    · rcases xEdge with ⟨xZero, yzEqual⟩
      constructor
      · rw [xZero]
        apply (x_zero_face_square y z).mpr
        rw [yzEqual]
        ring1
      · exact Or.inl xZero
    · rcases xOpposite with ⟨xOne, yzSum⟩
      constructor
      · rw [xOne]
        apply (x_one_face_square y z).mpr
        rw [← yzSum]
        ring1
      · exact Or.inr (Or.inl xOne)
    · rcases yEdge with ⟨yZero, xzEqual⟩
      constructor
      · rw [yZero]
        apply (y_zero_face_square x z).mpr
        rw [xzEqual]
        ring1
      · exact Or.inr (Or.inr (Or.inl yZero))
    · rcases yOpposite with ⟨yOne, xzSum⟩
      constructor
      · rw [yOne]
        apply (y_one_face_square x z).mpr
        rw [← xzSum]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inl yOne)))
    · rcases zEdge with ⟨zZero, xyEqual⟩
      constructor
      · rw [zZero]
        apply (z_zero_face_square x y).mpr
        rw [xyEqual]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl zZero))))
    · rcases zOpposite with ⟨zOne, xySum⟩
      constructor
      · rw [zOne]
        apply (z_one_face_square x y).mpr
        rw [← xySum]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr zOne))))

/-! ## Coordinate-plane ellipse sections -/

/-- The quadratic equation of a section with the third coordinate fixed. -/
def CoordinateCrossSection (fixed x y : K) : Prop :=
  x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
      2 * fixed * (x + y) + fixed ^ 2 = 0

theorem fixed_third_cross_section (fixed x y : K) :
    Contains x y fixed ↔ CoordinateCrossSection fixed x y := by
  unfold Contains polynomial CoordinateCrossSection
  constructor
  · intro ellipsonZero
    calc
      x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 =
        -((x + y + fixed) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + fixed ^ 2) - 4 * x * y * fixed) := by
          ring1
      _ = 0 := by rw [ellipsonZero]; ring1
  · intro sectionZero
    calc
      (x + y + fixed) ^ 2 - 2 * (x ^ 2 + y ^ 2 + fixed ^ 2) -
          4 * x * y * fixed =
        -(x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2) := by ring1
      _ = 0 := by rw [sectionZero]; ring1

/-- The same equation describes sections in either other coordinate
direction, by the ellipson's symmetry. -/
theorem all_coordinate_cross_sections (fixed first second : K) :
    (Contains fixed first second ↔ CoordinateCrossSection fixed first second) ∧
      (Contains first fixed second ↔ CoordinateCrossSection fixed first second) ∧
      (Contains first second fixed ↔ CoordinateCrossSection fixed first second) := by
  constructor
  · exact (contains_permutations fixed first second).2.2.1.trans
      (fixed_third_cross_section fixed first second)
  constructor
  · exact (contains_permutations first fixed second).1.trans
      (fixed_third_cross_section fixed first second)
  · exact fixed_third_cross_section fixed first second

/-- Diagonalizing the coordinate section about `[1/2,1/2]` yields its
denominator-free ellipse form. -/
theorem coordinate_cross_section_centered (fixed x y : K) :
    CoordinateCrossSection fixed x y ↔
      fixed * (x + y - 1) ^ 2 +
        (1 - fixed) * (x - y) ^ 2 = fixed * (1 - fixed) := by
  unfold CoordinateCrossSection
  constructor
  · intro sectionZero
    apply sub_eq_zero.mp
    calc
      fixed * (x + y - 1) ^ 2 +
          (1 - fixed) * (x - y) ^ 2 - fixed * (1 - fixed) =
        x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 := by ring1
      _ = 0 := sectionZero
  · intro centered
    calc
      x ^ 2 + y ^ 2 + (4 * fixed - 2) * x * y -
          2 * fixed * (x + y) + fixed ^ 2 =
        fixed * (x + y - 1) ^ 2 +
          (1 - fixed) * (x - y) ^ 2 - fixed * (1 - fixed) := by ring1
      _ = 0 := sub_eq_zero.mpr centered

theorem cross_section_x_zero (fixed y : K) :
    CoordinateCrossSection fixed 0 y ↔ (y - fixed) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (y - fixed) ^ 2 =
          0 ^ 2 + y ^ 2 + (4 * fixed - 2) * 0 * y -
            2 * fixed * (0 + y) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      0 ^ 2 + y ^ 2 + (4 * fixed - 2) * 0 * y -
          2 * fixed * (0 + y) + fixed ^ 2 = (y - fixed) ^ 2 := by ring1
      _ = 0 := equation

theorem cross_section_x_one (fixed y : K) :
    CoordinateCrossSection fixed 1 y ↔ (y - (1 - fixed)) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (y - (1 - fixed)) ^ 2 =
          1 ^ 2 + y ^ 2 + (4 * fixed - 2) * 1 * y -
            2 * fixed * (1 + y) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      1 ^ 2 + y ^ 2 + (4 * fixed - 2) * 1 * y -
          2 * fixed * (1 + y) + fixed ^ 2 =
        (y - (1 - fixed)) ^ 2 := by ring1
      _ = 0 := equation

theorem cross_section_y_zero (fixed x : K) :
    CoordinateCrossSection fixed x 0 ↔ (x - fixed) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (x - fixed) ^ 2 =
          x ^ 2 + 0 ^ 2 + (4 * fixed - 2) * x * 0 -
            2 * fixed * (x + 0) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      x ^ 2 + 0 ^ 2 + (4 * fixed - 2) * x * 0 -
          2 * fixed * (x + 0) + fixed ^ 2 = (x - fixed) ^ 2 := by ring1
      _ = 0 := equation

theorem cross_section_y_one (fixed x : K) :
    CoordinateCrossSection fixed x 1 ↔ (x - (1 - fixed)) ^ 2 = 0 := by
  unfold CoordinateCrossSection
  constructor <;> intro equation
  · calc
      (x - (1 - fixed)) ^ 2 =
          x ^ 2 + 1 ^ 2 + (4 * fixed - 2) * x * 1 -
            2 * fixed * (x + 1) + fixed ^ 2 := by ring1
      _ = 0 := equation
  · calc
      x ^ 2 + 1 ^ 2 + (4 * fixed - 2) * x * 1 -
          2 * fixed * (x + 1) + fixed ^ 2 =
        (x - (1 - fixed)) ^ 2 := by ring1
      _ = 0 := equation

/-- The four double boundary roots are the exact algebraic form of tangency
to the unit square. -/
theorem coordinate_cross_section_tangencies (fixed : K) :
    CoordinateCrossSection fixed 0 fixed ∧
      CoordinateCrossSection fixed 1 (1 - fixed) ∧
      CoordinateCrossSection fixed fixed 0 ∧
      CoordinateCrossSection fixed (1 - fixed) 1 := by
  constructor
  · exact (cross_section_x_zero fixed fixed).mpr (by ring1)
  constructor
  · exact (cross_section_x_one fixed (1 - fixed)).mpr (by ring1)
  constructor
  · exact (cross_section_y_zero fixed fixed).mpr (by ring1)
  · exact (cross_section_y_one fixed (1 - fixed)).mpr (by ring1)

/-! ## The oblique section and rational polar conversion -/

/-- The direct two-coordinate equation obtained by substituting
`z=2-x-y` into the ellipson. -/
def PlaneTwoCrossSection (x y : K) : Prop :=
  4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
      4 * x * y * (2 - x - y) = 0

theorem plane_two_cross_section (x y : K) :
    Contains x y (2 - x - y) ↔ PlaneTwoCrossSection x y := by
  unfold Contains polynomial PlaneTwoCrossSection
  constructor <;> intro equation
  · calc
      4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) =
        (x + y + (2 - x - y)) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) := by ring1
      _ = 0 := equation
  · calc
      (x + y + (2 - x - y)) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) =
        4 - 2 * (x ^ 2 + y ^ 2 + (2 - x - y) ^ 2) -
          4 * x * y * (2 - x - y) := by ring1
      _ = 0 := equation

/-- The source's suitable-coordinate oblique equation, multiplied by six to
remove its sole scalar denominator. -/
def ObliqueCoordinateCurve (root a b : K) : Prop :=
  6 * root * a * (3 * b ^ 2 - a ^ 2) -
      36 * (a ^ 2 + b ^ 2) + 5 = 0

/-- The oblique curve has the source's rational polar equation, with
`root²=6` supplied as a finite witness and all denominators cleared. -/
theorem oblique_rational_polar_cleared
    (root a b spread Q : K)
    (rootSquare : root ^ 2 = 6)
    (coordinates : RationalSphericalCoordinates.PolarCoordinateSquares
      (a ^ 2) (b ^ 2) spread Q)
    (onCurve : ObliqueCoordinateCurve root a b) :
    (6 * Q) ^ 3 * (spread * (3 - 4 * spread) ^ 2) =
      (36 * Q - 5) ^ 2 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      (a ^ 2) (b ^ 2) spread Q coordinates
  have linearEquation :
      6 * root * a * ((3 - 4 * spread) * Q) = 36 * Q - 5 := by
    apply sub_eq_zero.mp
    calc
      6 * root * a * ((3 - 4 * spread) * Q) - (36 * Q - 5) =
        6 * root * a * (3 * b ^ 2 - a ^ 2) -
          36 * (a ^ 2 + b ^ 2) + 5 := by
        rw [squareCoordinates.1, squareCoordinates.2, coordinates.1]
        ring1
      _ = 0 := onCurve
  calc
    (6 * Q) ^ 3 * (spread * (3 - 4 * spread) ^ 2) =
        36 * 6 * (spread * Q) * Q ^ 2 * (3 - 4 * spread) ^ 2 := by
      ring1
    _ = 36 * root ^ 2 * a ^ 2 * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by
      rw [rootSquare, coordinates.2]
    _ = (6 * root * a * ((3 - 4 * spread) * Q)) ^ 2 := by ring1
    _ = (36 * Q - 5) ^ 2 := by rw [linearEquation]

/-- The left side of the oblique equation is exactly the third spread
polynomial, as asserted in Appendix B. -/
theorem oblique_left_is_third_spread_polynomial (spread : K) :
    spreadPolynomial 3 spread = spread * (3 - 4 * spread) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

end Ellipson
end DivineProportions
