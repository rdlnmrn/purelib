import DivineProportions.Quadrilaterals.FourPoint

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace DivineProportions
namespace RationalSphericalCoordinates

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_left
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

/-! ## §27.1: rational polar coordinates -/

/-- The denominator-cleared definition of rational polar coordinates. -/
def PolarCoordinateSquares (xSquared ySquared spread Q : K) : Prop :=
  Q = xSquared + ySquared ∧ spread * Q = xSquared

/-- Equation (27.1): the two squared Cartesian coordinates are recovered
from spread and quadrance without choosing either sign. -/
theorem polar_coordinate_squares
    (xSquared ySquared spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q) :
    xSquared = spread * Q ∧
      ySquared = (1 - spread) * Q := by
  constructor
  · exact coordinates.2.symm
  · calc
      ySquared = Q - xSquared := by rw [coordinates.1]; ring1
      _ = Q - spread * Q := by rw [← coordinates.2]
      _ = (1 - spread) * Q := by ring1

def determinantTwo (a b c d : K) : K := a * d - b * c

/-- Equation (27.2): the finite determinant of the differential coefficient
matrix is exactly `Q`. -/
theorem polar_jacobian_determinant (spread Q : K) :
    determinantTwo Q spread (-Q) (1 - spread) = Q := by
  unfold determinantTwo
  ring1

/-- The square of the source's area-density identity.  This is the part that
does not require a square-root selector. -/
theorem polar_squared_density
    (xSquared ySquared spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q) :
    xSquared * ySquared =
      spread * (1 - spread) * Q ^ 2 := by
  rcases polar_coordinate_squares xSquared ySquared spread Q coordinates with
    ⟨xValue, yValue⟩
  rw [xValue, yValue]
  ring1

/-! ## Exercise 27.1: finite substitution algebra -/

/-- The four algebraic identities behind Exercise 27.1's substitutions.
They make no claim about an improper integral or a limiting endpoint. -/
theorem exercise_27_1_substitution_identities
    (r t u v : K) :
    r ^ 2 * (1 - r ^ 2) = r ^ 2 - r ^ 4 ∧
      t ^ 2 - t = t * (t - 1) ∧
      (1 + u ^ 2) ^ 2 - (2 * u) ^ 2 = (1 - u ^ 2) ^ 2 ∧
      (1 + v ^ 2) ^ 2 - (2 * v) ^ 2 = (1 - v ^ 2) ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The reciprocal substitution `s=1/t`, expressed without division. -/
theorem exercise_27_1_reciprocal_spread
    (spread t : K) (clearedReciprocal : spread * t = 1) :
    t ^ 2 * (spread * (1 - spread)) = t - 1 := by
  calc
    t ^ 2 * (spread * (1 - spread)) =
        (spread * t) * (t - spread * t) := by ring1
    _ = t - 1 := by rw [clearedReciprocal]; ring1

/-- The final reciprocal substitution `v=1/u`, also denominator-free. -/
theorem exercise_27_1_reciprocal_denominator
    (u v : K) (clearedReciprocal : u * v = 1) :
    v ^ 2 * (1 + u ^ 2) = 1 + v ^ 2 := by
  calc
    v ^ 2 * (1 + u ^ 2) = v ^ 2 + (u * v) ^ 2 := by ring1
    _ = 1 + v ^ 2 := by rw [clearedReciprocal]; ring1

/-! ## Example 27.2: lemniscate of Bernoulli -/

/-- The Cartesian lemniscate equation becomes the cleared polar equation
`Q(Q-(2s-1))=0`. -/
theorem example_27_2_lemniscate_cleared
    (xSquared ySquared spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscate : (xSquared + ySquared) ^ 2 = xSquared - ySquared) :
    Q * (Q - (2 * spread - 1)) = 0 := by
  rcases polar_coordinate_squares xSquared ySquared spread Q coordinates with
    ⟨xValue, yValue⟩
  calc
    Q * (Q - (2 * spread - 1)) =
        Q ^ 2 - (spread * Q - (1 - spread) * Q) := by ring1
    _ = (xSquared + ySquared) ^ 2 - (xSquared - ySquared) := by
      rw [← xValue, ← yValue, coordinates.1]
    _ = 0 := by rw [lemniscate]; ring1

/-- Away from the origin, Example 27.2 has the printed polar equation
`Q=2s-1`. -/
theorem example_27_2_lemniscate
    (xSquared ySquared spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscate : (xSquared + ySquared) ^ 2 = xSquared - ySquared) :
    Q = 2 * spread - 1 := by
  have productZero := example_27_2_lemniscate_cleared
    xSquared ySquared spread Q coordinates lemniscate
  apply eq_of_mul_eq_mul_left QNonzero
  calc
    Q * Q = Q * (2 * spread - 1) +
        Q * (Q - (2 * spread - 1)) := by ring1
    _ = Q * (2 * spread - 1) := by rw [productZero]; ring1

/-! ## §27.2 and Exercise 27.2: finite polygon refinement -/

/-- One explicitly witnessed radical-refinement step.  `scale` is the
current power-of-four coefficient, while `scaleRoot²=scale` and
`nextRoot²=2+root` are the two finite square witnesses used in the source
recurrence. -/
def PolygonAreaRefinementStep
    (scale scaleRoot root nextRoot current next : K) : Prop :=
  scaleRoot ^ 2 = scale ∧
    current = scale * (2 - root) ∧
    nextRoot ^ 2 = 2 + root ∧
    next = 4 * scale * (2 - nextRoot)

/-- Exercise 27.2 at the agreed finite boundary: every supplied radical
step extends the displayed closed pattern and satisfies the source recurrence
with the explicit square-root witness `scaleRoot nextRoot`. -/
theorem exercise_27_2_finite_step
    (scale scaleRoot root nextRoot current next : K)
    (step : PolygonAreaRefinementStep
      scale scaleRoot root nextRoot current next) :
    (scaleRoot * nextRoot) ^ 2 = 4 * scale - current ∧
      next = 8 * scale -
        (4 * scaleRoot) * (scaleRoot * nextRoot) := by
  rcases step with ⟨scaleSquare, currentValue, nextRootSquare, nextValue⟩
  constructor
  · rw [currentValue]
    apply sub_eq_zero.mp
    calc
      (scaleRoot * nextRoot) ^ 2 -
          (4 * scale - scale * (2 - root)) =
        scaleRoot ^ 2 * nextRoot ^ 2 -
          scale * (2 + root) := by ring1
      _ = 0 := by rw [scaleSquare, nextRootSquare]; ring1
  · rw [nextValue]
    apply sub_eq_zero.mp
    calc
      4 * scale * (2 - nextRoot) -
          (8 * scale -
            (4 * scaleRoot) * (scaleRoot * nextRoot)) =
        4 * nextRoot * (scaleRoot ^ 2 - scale) := by ring1
      _ = 0 := by rw [scaleSquare]; ring1

/-- The first three nested-radical values printed after the recurrence are
linked by exact finite square certificates. -/
theorem exercise_27_2_first_terms
    (firstRoot secondRoot thirdRoot : K)
    (firstSquare : firstRoot ^ 2 = 2)
    (secondSquare : secondRoot ^ 2 = 2 + firstRoot)
    (thirdSquare : thirdRoot ^ 2 = 2 + secondRoot) :
    firstRoot ^ 2 = 2 ∧
      secondRoot ^ 2 = 4 - (2 - firstRoot) ∧
      (2 * thirdRoot) ^ 2 = 16 - 4 * (2 - secondRoot) ∧
      4 * (2 - secondRoot) = 8 - 4 * secondRoot ∧
      16 * (2 - thirdRoot) = 32 - 16 * thirdRoot := by
  constructor
  · exact firstSquare
  constructor
  · rw [secondSquare]
    ring1
  constructor
  · apply sub_eq_zero.mp
    calc
      (2 * thirdRoot) ^ 2 - (16 - 4 * (2 - secondRoot)) =
        4 * (thirdRoot ^ 2 - (2 + secondRoot)) := by ring1
      _ = 0 := by rw [thirdSquare]; ring1
  constructor <;> ring1

/-! ## §27.4: three-dimensional rational spherical coordinates -/

def SphericalCoordinateSquares
    (xSquared ySquared zSquared spread polarSpread R : K) : Prop :=
  let horizontal := xSquared + ySquared
  R = horizontal + zSquared ∧
    spread * horizontal = xSquared ∧
    polarSpread * R = horizontal

/-- Equation (27.7), with signs deliberately absent. -/
theorem spherical_coordinate_squares
    (xSquared ySquared zSquared spread polarSpread R : K)
    (coordinates : SphericalCoordinateSquares
      xSquared ySquared zSquared spread polarSpread R) :
    xSquared = spread * polarSpread * R ∧
      ySquared = (1 - spread) * polarSpread * R ∧
      zSquared = (1 - polarSpread) * R := by
  change
    R = xSquared + ySquared + zSquared ∧
      spread * (xSquared + ySquared) = xSquared ∧
      polarSpread * R = xSquared + ySquared at coordinates
  constructor
  · calc
      xSquared = spread * (xSquared + ySquared) := coordinates.2.1.symm
      _ = spread * (polarSpread * R) := by rw [← coordinates.2.2]
      _ = spread * polarSpread * R := by ring1
  constructor
  · calc
      ySquared = (xSquared + ySquared) - xSquared := by ring1
      _ = polarSpread * R - spread * (xSquared + ySquared) := by
        rw [coordinates.2.1, coordinates.2.2]
      _ = (1 - spread) * polarSpread * R := by
        rw [← coordinates.2.2]
        ring1
  · calc
      zSquared = R - (xSquared + ySquared) := by rw [coordinates.1]; ring1
      _ = (1 - polarSpread) * R := by rw [← coordinates.2.2]; ring1

def sphericalJacobianDeterminant (spread polarSpread R : K) : K :=
  Quadrilateral.determinantThree
    (polarSpread * R) (spread * R) (spread * polarSpread)
    (-polarSpread * R) ((1 - spread) * R) ((1 - spread) * polarSpread)
    0 (-R) (1 - polarSpread)

/-- The determinant calculation preceding equation (27.8). -/
theorem spherical_jacobian_determinant (spread polarSpread R : K) :
    sphericalJacobianDeterminant spread polarSpread R =
      polarSpread * R ^ 2 := by
  unfold sphericalJacobianDeterminant Quadrilateral.determinantThree
  ring1

/-- The square of equation (27.8)'s numerator identity. -/
theorem spherical_squared_density
    (xSquared ySquared zSquared spread polarSpread R : K)
    (coordinates : SphericalCoordinateSquares
      xSquared ySquared zSquared spread polarSpread R) :
    xSquared * ySquared * zSquared =
      spread * (1 - spread) * polarSpread ^ 2 *
        (1 - polarSpread) * R ^ 3 := by
  rcases spherical_coordinate_squares
      xSquared ySquared zSquared spread polarSpread R coordinates with
    ⟨xValue, yValue, zValue⟩
  rw [xValue, yValue, zValue]
  ring1

/-! ## Example 27.5: the ice-cream cone region -/

/-- On the cone `z²=x²+y²`, the second polar spread is `1/2`; on the
projective sphere `x²+y²+z²=z`, its radial bound is `R=1-q`. -/
theorem example_27_5_cone_sphere_coordinates
    (horizontal zSquared z polarSpread R : K)
    (twoNonzero : (2 : K) ≠ 0) (RNonzero : R ≠ 0)
    (radialQuadrance : R = horizontal + zSquared)
    (polarCoordinate : polarSpread * R = horizontal)
    (cone : zSquared = horizontal)
    (projectiveSphere : R = z)
    (zSquare : zSquared = z ^ 2) :
    polarSpread = 1 / 2 ∧ R = 1 - polarSpread := by
  have coneCleared : (2 * polarSpread - 1) * R = 0 := by
    calc
      (2 * polarSpread - 1) * R =
          2 * (polarSpread * R) - R := by ring1
      _ = 2 * horizontal - (horizontal + zSquared) := by
        rw [polarCoordinate, radialQuadrance]
      _ = 0 := by rw [cone]; ring1
  have twicePolar : 2 * polarSpread = 1 := by
    apply eq_of_mul_eq_mul_left RNonzero
    calc
      R * (2 * polarSpread) = R + (2 * polarSpread - 1) * R := by ring1
      _ = R := by rw [coneCleared]; ring1
      _ = R * 1 := by ring1
  have twoCancel : ((1 : K) / 2) * 2 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 twoNonzero
  have polarValue : polarSpread = 1 / 2 := by
    apply eq_of_mul_eq_mul_left twoNonzero
    calc
      2 * polarSpread = 1 := twicePolar
      _ = ((1 : K) / 2) * 2 := twoCancel.symm
      _ = 2 * ((1 : K) / 2) := by ring1
  have zPolar : zSquared = (1 - polarSpread) * R := by
    calc
      zSquared = R - horizontal := by rw [radialQuadrance]; ring1
      _ = R - polarSpread * R := by rw [polarCoordinate]
      _ = (1 - polarSpread) * R := by ring1
  have radialProduct : R * (R - (1 - polarSpread)) = 0 := by
    calc
      R * (R - (1 - polarSpread)) =
          R ^ 2 - (1 - polarSpread) * R := by ring1
      _ = z ^ 2 - zSquared := by rw [← zPolar, projectiveSphere]
      _ = 0 := by rw [zSquare]; ring1
  have radialValue : R = 1 - polarSpread := by
    apply eq_of_mul_eq_mul_left RNonzero
    calc
      R * R = R * (1 - polarSpread) +
          R * (R - (1 - polarSpread)) := by ring1
      _ = R * (1 - polarSpread) := by rw [radialProduct]; ring1
  exact ⟨polarValue, radialValue⟩

/-! ## §27.6: four-dimensional rational spherical coordinates -/

def FourSphericalCoordinateSquares
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K) : Prop :=
  let firstPartial := xSquared + ySquared
  let secondPartial := firstPartial + zSquared
  T = secondPartial + wSquared ∧
    spread * firstPartial = xSquared ∧
    secondSpread * secondPartial = firstPartial ∧
    thirdSpread * T = secondPartial

/-- Equation (27.9), in denominator-free squared-coordinate form. -/
theorem four_spherical_coordinate_squares
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K)
    (coordinates : FourSphericalCoordinateSquares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T) :
    xSquared = spread * secondSpread * thirdSpread * T ∧
      ySquared = (1 - spread) * secondSpread * thirdSpread * T ∧
      zSquared = (1 - secondSpread) * thirdSpread * T ∧
      wSquared = (1 - thirdSpread) * T := by
  change
    T = xSquared + ySquared + zSquared + wSquared ∧
      spread * (xSquared + ySquared) = xSquared ∧
      secondSpread * (xSquared + ySquared + zSquared) =
        xSquared + ySquared ∧
      thirdSpread * T = xSquared + ySquared + zSquared at coordinates
  have firstPartial :
      xSquared + ySquared = secondSpread * thirdSpread * T := by
    calc
      xSquared + ySquared =
          secondSpread * (xSquared + ySquared + zSquared) :=
        coordinates.2.2.1.symm
      _ = secondSpread * (thirdSpread * T) := by
        rw [← coordinates.2.2.2]
      _ = secondSpread * thirdSpread * T := by ring1
  constructor
  · calc
      xSquared = spread * (xSquared + ySquared) := coordinates.2.1.symm
      _ = spread * (secondSpread * thirdSpread * T) := by rw [firstPartial]
      _ = spread * secondSpread * thirdSpread * T := by ring1
  constructor
  · calc
      ySquared = (xSquared + ySquared) - xSquared := by ring1
      _ = (xSquared + ySquared) -
          spread * (xSquared + ySquared) := by rw [coordinates.2.1]
      _ = (1 - spread) * (xSquared + ySquared) := by ring1
      _ = (1 - spread) * secondSpread * thirdSpread * T := by
        rw [firstPartial]
        ring1
  constructor
  · calc
      zSquared = (xSquared + ySquared + zSquared) -
          (xSquared + ySquared) := by ring1
      _ = thirdSpread * T - secondSpread * thirdSpread * T := by
        rw [coordinates.2.2.2, firstPartial]
      _ = (1 - secondSpread) * thirdSpread * T := by ring1
  · calc
      wSquared = T - (xSquared + ySquared + zSquared) := by
        rw [coordinates.1]
        ring1
      _ = (1 - thirdSpread) * T := by
        rw [← coordinates.2.2.2]
        ring1

def fourSphericalJacobianDeterminant
    (spread secondSpread thirdSpread T : K) : K :=
  Quadrilateral.determinantFour
    (secondSpread * thirdSpread * T)
      (spread * thirdSpread * T)
      (spread * secondSpread * T)
      (spread * secondSpread * thirdSpread)
    (-secondSpread * thirdSpread * T)
      ((1 - spread) * thirdSpread * T)
      ((1 - spread) * secondSpread * T)
      ((1 - spread) * secondSpread * thirdSpread)
    0 (-thirdSpread * T) ((1 - secondSpread) * T)
      ((1 - secondSpread) * thirdSpread)
    0 0 (-T) (1 - thirdSpread)

/-- The four-dimensional determinant printed after equation (27.9). -/
theorem four_spherical_jacobian_determinant
    (spread secondSpread thirdSpread T : K) :
    fourSphericalJacobianDeterminant
        spread secondSpread thirdSpread T =
      secondSpread * thirdSpread ^ 2 * T ^ 3 := by
  unfold fourSphericalJacobianDeterminant Quadrilateral.determinantFour
    Quadrilateral.determinantThree
  ring1

/-- The square of the four-dimensional content-density numerator. -/
theorem four_spherical_squared_density
    (xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T : K)
    (coordinates : FourSphericalCoordinateSquares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T) :
    xSquared * ySquared * zSquared * wSquared =
      spread * (1 - spread) * secondSpread ^ 2 *
        (1 - secondSpread) * thirdSpread ^ 3 *
        (1 - thirdSpread) * T ^ 4 := by
  rcases four_spherical_coordinate_squares
      xSquared ySquared zSquared wSquared
      spread secondSpread thirdSpread T coordinates with
    ⟨xValue, yValue, zValue, wValue⟩
  rw [xValue, yValue, zValue, wValue]
  ring1

/-! ## Finite endpoint algebra from Examples 27.1 and 27.3--27.15 -/

/-- The polynomial endpoint simplification common to the spherical cap
(Example 27.6) and hyperbolic cap (Example 27.11). -/
theorem examples_27_6_27_11_cap_factorization (k d : K) :
    d ^ 3 - 3 * d * k ^ 2 + 2 * k ^ 3 =
      (k - d) ^ 2 * (2 * k + d) := by
  ring1

/-- The sphere and hyperboloid ring endpoint evaluations both discard the
ambient quadrance and leave the cubic coefficient `4d³/3`. -/
theorem examples_27_7_27_12_ring_endpoint (d : K) :
    2 * ((2 * d ^ 3) - 0) = 4 * d ^ 3 := by
  ring1

/-- Example 27.8's final paraboloid endpoint calculation. -/
theorem example_27_8_paraboloid_endpoint
    (r : K) (twoNonzero : (2 : K) ≠ 0) :
    2 * (r ^ 2 - r ^ 2 / 2) = r ^ 2 := by
  have halfCancel : (r ^ 2 / 2) * 2 = r ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  calc
    2 * (r ^ 2 - r ^ 2 / 2) =
        2 * r ^ 2 - (r ^ 2 / 2) * 2 := by ring1
    _ = r ^ 2 := by rw [halfCancel]; ring1

/-- Example 27.9: after clearing the common nonzero circle constant, mass
`2π/3` and moment `π/4` put the centroid at `3/8`. -/
theorem example_27_9_hemisphere_centroid
    (circleConstant mass moment centroidHeight : K)
    (circleConstantNonzero : circleConstant ≠ 0)
    (massValue : 3 * mass = 2 * circleConstant)
    (momentValue : 4 * moment = circleConstant)
    (centroidRelation : mass * centroidHeight = moment) :
    8 * centroidHeight = 3 := by
  apply eq_of_mul_eq_mul_left circleConstantNonzero
  calc
    circleConstant * (8 * centroidHeight) =
        4 * (2 * circleConstant) * centroidHeight := by ring1
    _ = 4 * (3 * mass) * centroidHeight := by rw [massValue]
    _ = 12 * (mass * centroidHeight) := by ring1
    _ = 12 * moment := by rw [centroidRelation]
    _ = 3 * (4 * moment) := by ring1
    _ = 3 * circleConstant := by rw [momentValue]
    _ = circleConstant * 3 := by ring1

/-- Example 27.10's finite Gamma-recurrence arithmetic
`B(2,1/2)=4/3`.  The Gamma values are displayed witnesses; no integral or
function on an infinite domain is introduced. -/
theorem example_27_10_beta_coefficient
    (gammaHalf gammaThreeHalves gammaFiveHalves betaValue : K)
    (gammaFiveHalvesNonzero : gammaFiveHalves ≠ 0)
    (firstRecurrence : 2 * gammaThreeHalves = gammaHalf)
    (secondRecurrence : 2 * gammaFiveHalves = 3 * gammaThreeHalves)
    (betaCleared : gammaFiveHalves * betaValue = gammaHalf) :
    3 * betaValue = 4 := by
  have fourGammaFive : 4 * gammaFiveHalves = 3 * gammaHalf := by
    calc
      4 * gammaFiveHalves = 2 * (2 * gammaFiveHalves) := by ring1
      _ = 2 * (3 * gammaThreeHalves) := by rw [secondRecurrence]
      _ = 3 * gammaHalf := by rw [← firstRecurrence]; ring1
  apply eq_of_mul_eq_mul_left gammaFiveHalvesNonzero
  calc
    gammaFiveHalves * (3 * betaValue) =
        3 * (gammaFiveHalves * betaValue) := by ring1
    _ = 3 * gammaHalf := by rw [betaCleared]
    _ = gammaFiveHalves * 4 := by rw [← fourGammaFive]; ring1

/-- Example 27.15's finite Gamma-recurrence arithmetic
`B(3/2,1/2)=π/2`, with the symbol for `π` represented only by the
displayed product `Γ(1/2)²`. -/
theorem example_27_15_beta_coefficient
    (gammaHalf gammaThreeHalves betaValue circleConstant : K)
    (recurrence : 2 * gammaThreeHalves = gammaHalf)
    (betaProduct : betaValue = gammaThreeHalves * gammaHalf)
    (circleProduct : circleConstant = gammaHalf ^ 2) :
    2 * betaValue = circleConstant := by
  rw [betaProduct, circleProduct, ← recurrence]
  ring1

/-- Example 27.14's cap-area simplification, with division by `k` cleared. -/
theorem example_27_14_surface_cap_cleared
    (circleConstant k d area : K)
    (areaFormula : area = 2 * circleConstant * (k - d)) :
    area = 2 * circleConstant * k - 2 * circleConstant * d := by
  rw [areaFormula]
  ring1

end RationalSphericalCoordinates
end DivineProportions
