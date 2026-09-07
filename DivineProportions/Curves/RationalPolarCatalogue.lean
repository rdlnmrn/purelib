import DivineProportions.Applications.RationalSphericalCoordinates
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace DivineProportions
namespace RationalPolarCatalogue

variable {K : Type*} [RFAP.ExplicitField K]

abbrev PolarCoordinateSquares
    (xSquared ySquared spread Q : K) : Prop :=
  RationalSphericalCoordinates.PolarCoordinateSquares
    xSquared ySquared spread Q

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

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  apply eq_of_mul_eq_mul_left factorNonzero
  calc
    factor * value = 0 := productZero
    _ = factor * 0 := by ring1

/-! ## Line, ellipse, and hyperbola -/

/-- A central circle `x²+y²=K` is simply the constant-quadrance locus
`Q=K`; its spread remains the free directional coordinate. -/
theorem circle_rational_polar
    (xSquared ySquared circleQuadrance spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (circleEquation : xSquared + ySquared = circleQuadrance) :
    Q = circleQuadrance :=
  coordinates.1.trans circleEquation

/-- The line `y=ax` has the cleared rational polar equation
`(1+A)s=1`, where `A=a²`. -/
theorem line_rational_polar_cleared
    (x y a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (lineEquation : y = a * x) :
    (1 + A) * spread = 1 := by
  apply eq_of_mul_eq_mul_left QNonzero
  calc
    Q * ((1 + A) * spread) =
        (1 + A) * (spread * Q) := by ring1
    _ = (1 + A) * x ^ 2 := by rw [coordinates.2]
    _ = x ^ 2 + y ^ 2 := by rw [lineEquation, ← aSquare]; ring1
    _ = Q := coordinates.1.symm
    _ = Q * 1 := by ring1

/-- The ellipse `Bx²+Ay²=AB` has the printed rational polar equation
`sQ(A-B)=A(Q-B)`. -/
theorem ellipse_rational_polar
    (xSquared ySquared A B spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (ellipseEquation : B * xSquared + A * ySquared = A * B) :
    spread * Q * (A - B) = A * (Q - B) := by
  apply sub_eq_zero.mp
  calc
    spread * Q * (A - B) - A * (Q - B) =
        -(B * xSquared + A * ySquared - A * B) := by
      rw [coordinates.2, coordinates.1]
      ring1
    _ = 0 := by rw [ellipseEquation]; ring1

/-- The hyperbola `Bx²-Ay²=AB` has the printed rational polar equation
`sQ(A+B)=A(Q+B)`. -/
theorem hyperbola_rational_polar
    (xSquared ySquared A B spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (hyperbolaEquation : B * xSquared - A * ySquared = A * B) :
    spread * Q * (A + B) = A * (Q + B) := by
  apply sub_eq_zero.mp
  calc
    spread * Q * (A + B) - A * (Q + B) =
        B * xSquared - A * ySquared - A * B := by
      rw [coordinates.2, coordinates.1]
      ring1
    _ = 0 := by rw [hyperbolaEquation]; ring1

/-! ## Parabola, cardioid, limacon, and trisectrix -/

/-- Squaring `y²=4ax` gives the origin-safe parabola equation. -/
theorem parabola_rational_polar_origin_safe
    (x y a A spread Q : K)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (parabolaEquation : y ^ 2 = 4 * a * x) :
    Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) = 0 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  calc
    Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) =
        ((1 - spread) * Q) ^ 2 - 16 * A * (spread * Q) := by ring1
    _ = (y ^ 2) ^ 2 - 16 * A * x ^ 2 := by
      rw [← squareCoordinates.2, coordinates.2]
    _ = (4 * a * x) ^ 2 - 16 * a ^ 2 * x ^ 2 := by
      rw [parabolaEquation, aSquare]
    _ = 0 := by ring1

/-- Away from the origin, the preceding result is exactly the source's
`(1-s)²Q=16As`. -/
theorem parabola_rational_polar
    (x y a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (parabolaEquation : y ^ 2 = 4 * a * x) :
    (1 - spread) ^ 2 * Q = 16 * A * spread := by
  apply sub_eq_zero.mp
  exact eq_zero_of_mul_eq_zero_left QNonzero
    (parabola_rational_polar_origin_safe
      x y a A spread Q coordinates aSquare parabolaEquation)

/-- The denominator-cleared completed-square form printed for the parabola. -/
theorem parabola_centered_rational_polar
    (A spread Q : K)
    (polarEquation : (1 - spread) ^ 2 * Q = 16 * A * spread) :
    (spread * Q - (Q + 8 * A)) ^ 2 = 16 * A * (Q + 4 * A) := by
  apply sub_eq_zero.mp
  calc
    (spread * Q - (Q + 8 * A)) ^ 2 - 16 * A * (Q + 4 * A) =
        Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) := by ring1
    _ = 0 := by rw [polarEquation]; ring1

/-- Both orientations of the cardioid are covered by taking
`orientedX=x` or `orientedX=-x`. -/
theorem cardioid_rational_polar_cleared
    (x y orientedX a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (orientedXSquare : orientedX ^ 2 = x ^ 2)
    (aSquare : a ^ 2 = A)
    (cardioidEquation :
      (x ^ 2 + y ^ 2 - 2 * a * orientedX) ^ 2 =
        4 * A * (x ^ 2 + y ^ 2)) :
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 16 * A * Q := by
  have cartesianInQ : (Q - 2 * a * orientedX) ^ 2 = 4 * A * Q := by
    rw [coordinates.1]
    exact cardioidEquation
  have productZero :
      Q * (Q - 4 * a * orientedX + 4 * A * spread - 4 * A) = 0 := by
    have orientedSpread : Q * spread = orientedX ^ 2 := by
      calc
        Q * spread = spread * Q := by ring1
        _ = x ^ 2 := coordinates.2
        _ = orientedX ^ 2 := orientedXSquare.symm
    calc
      Q * (Q - 4 * a * orientedX + 4 * A * spread - 4 * A) =
          Q ^ 2 - 4 * a * Q * orientedX +
            4 * a ^ 2 * (Q * spread) - 4 * a ^ 2 * Q := by
        rw [aSquare]
        ring1
      _ =
          (Q - 2 * a * orientedX) ^ 2 - 4 * A * Q := by
        rw [orientedSpread, ← aSquare]
        ring1
      _ = 0 := by rw [cartesianInQ]; ring1
  have linearZero :=
    eq_zero_of_mul_eq_zero_left QNonzero productZero
  have centeredRelation :
      4 * A * spread - (Q + 4 * A) =
        2 * (2 * a * orientedX - Q) := by
    apply sub_eq_zero.mp
    calc
      4 * A * spread - (Q + 4 * A) -
          2 * (2 * a * orientedX - Q) =
        Q - 4 * a * orientedX + 4 * A * spread - 4 * A := by ring1
      _ = 0 := linearZero
  rw [centeredRelation]
  calc
    (2 * (2 * a * orientedX - Q)) ^ 2 =
        4 * (Q - 2 * a * orientedX) ^ 2 := by ring1
    _ = 4 * (4 * A * Q) := by rw [cartesianInQ]
    _ = 16 * A * Q := by ring1

/-- The limacon `r=2a cos(theta)+b`, expressed through explicit square
witnesses, has the source's denominator-cleared rational polar equation. -/
theorem limacon_rational_polar_cleared
    (radial cosine a b A B spread Q : K)
    (radialSquare : radial ^ 2 = Q) (cosineSquare : cosine ^ 2 = spread)
    (aSquare : a ^ 2 = A) (bSquare : b ^ 2 = B)
    (limaconEquation : radial = 2 * a * cosine + b) :
    (4 * A * spread - (Q + B)) ^ 2 = 4 * B * Q := by
  have centeredRelation :
      4 * A * spread - (Q + B) = -2 * b * radial := by
    rw [← radialSquare, ← cosineSquare, ← aSquare, ← bSquare,
      limaconEquation]
    ring1
  rw [centeredRelation, ← radialSquare, ← bSquare]
  ring1

/-- Setting `B=4A` in the limacon equation gives the cardioid equation. -/
theorem limacon_specializes_to_cardioid
    (A B spread Q : K)
    (limaconEquation :
      (4 * A * spread - (Q + B)) ^ 2 = 4 * B * Q)
    (parameterSpecialization : B = 4 * A) :
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 16 * A * Q := by
  rw [parameterSpecialization] at limaconEquation
  calc
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 4 * (4 * A) * Q :=
      limaconEquation
    _ = 16 * A * Q := by ring1

/-- The corrected trisectrix specialization has a minus sign. -/
theorem trisectrix_rational_polar_cleared
    (radial cosine a A spread Q : K)
    (radialSquare : radial ^ 2 = Q) (cosineSquare : cosine ^ 2 = spread)
    (aSquare : a ^ 2 = A)
    (trisectrixEquation : radial = 2 * a * cosine + a) :
    (4 * A * spread - (Q + A)) ^ 2 = 4 * A * Q := by
  exact limacon_rational_polar_cleared
    radial cosine a a A A spread Q
    radialSquare cosineSquare aSquare aSquare trisectrixEquation

/-- The source's printed plus-sign trisectrix equation fails at
`A=1`, `Q=9`, `s=1`, a point satisfying the corrected equation. -/
theorem printed_trisectrix_counterexample :
    let R := RFAP.ConstructiveFraction.Rational
    (4 * (1 : R) * 1 - (9 + 1)) ^ 2 = 4 * 1 * 9 ∧
      (4 * (1 : R) * 1 + (9 + 1)) ^ 2 ≠ 4 * 1 * 9 := by
  decide

/-! ## Even algebraic curves -/

/-- The astroid polynomial gives the source's cleared centered equation. -/
theorem astroid_rational_polar_cleared
    (xSquared ySquared A spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (astroidEquation :
      (xSquared + ySquared - A) ^ 3 +
        27 * A * xSquared * ySquared = 0) :
    27 * A * Q ^ 2 * (2 * spread - 1) ^ 2 =
      27 * A * Q ^ 2 - 4 * (A - Q) ^ 3 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply sub_eq_zero.mp
  calc
    27 * A * Q ^ 2 * (2 * spread - 1) ^ 2 -
        (27 * A * Q ^ 2 - 4 * (A - Q) ^ 3) =
      -4 * ((Q - A) ^ 3 +
        27 * A * (spread * Q) * ((1 - spread) * Q)) := by ring1
    _ = -4 * ((xSquared + ySquared - A) ^ 3 +
        27 * A * xSquared * ySquared) := by
      rw [← coordinates.1, ← squareCoordinates.1, ← squareCoordinates.2]
    _ = 0 := by rw [astroidEquation]; ring1

/-- The eight curve, or lemniscate of Gerono, has the printed cleared
completed-square equation. -/
theorem eight_curve_rational_polar_cleared
    (xSquared ySquared A spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (eightCurveEquation : xSquared ^ 2 = A * (xSquared - ySquared)) :
    (spread * Q - A) ^ 2 = (A - Q) * A := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply sub_eq_zero.mp
  calc
    (spread * Q - A) ^ 2 - (A - Q) * A =
        xSquared ^ 2 - A * (xSquared - ySquared) := by
      rw [squareCoordinates.1, squareCoordinates.2]
      ring1
    _ = 0 := by rw [eightCurveEquation]; ring1

/-- The corrected completion of the bullet-nose quadratic.  The source's
right side is four times too large. -/
theorem bullet_nose_rational_polar_corrected
    (xSquared ySquared A B spread Q : K)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (bulletNoseEquation :
      A * ySquared - B * xSquared = xSquared * ySquared) :
    (2 * Q * spread - (A + B + Q)) ^ 2 =
      (A + B + Q) ^ 2 - 4 * A * Q := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply sub_eq_zero.mp
  calc
    (2 * Q * spread - (A + B + Q)) ^ 2 -
        ((A + B + Q) ^ 2 - 4 * A * Q) =
      4 * Q *
        (A * (1 - spread) - B * spread -
          spread * (1 - spread) * Q) := by ring1
    _ = 4 *
        (A * ySquared - B * xSquared - xSquared * ySquared) := by
      rw [squareCoordinates.1, squareCoordinates.2]
      ring1
    _ = 0 := by rw [bulletNoseEquation]; ring1

/-- The source's bullet-nose equation fails on the exact polar data
`A=B=1`, `x²=1/2`, `y²=1`, `Q=3/2`, `s=1/3`. -/
theorem printed_bullet_nose_counterexample :
    let R := RFAP.ConstructiveFraction.Rational
    let A : R := 1
    let B : R := 1
    let Q : R := 3 / 2
    let spread : R := 1 / 3
    (2 * Q * spread - (A + B + Q)) ^ 2 =
        (A + B + Q) ^ 2 - 4 * A * Q ∧
      (2 * Q * spread - (A + B + Q)) ^ 2 ≠
        4 * ((A + B + Q) ^ 2 - 4 * A * Q) := by
  decide

/-! ## Deltoid and hippopede -/

/-- Squaring the one odd Cartesian term in the deltoid equation produces
the third-spread polynomial `s(3-4s)²`. -/
theorem deltoid_rational_polar_cleared
    (x y a A spread Q : K)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A)
    (deltoidEquation :
      (x ^ 2 + y ^ 2) ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) +
          18 * A * (x ^ 2 + y ^ 2) = 27 * A ^ 2) :
    64 * Q ^ 3 * A * (spread * (3 - 4 * spread) ^ 2) =
      (Q ^ 2 + 18 * A * Q - 27 * A ^ 2) ^ 2 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  have oddTerm :
      Q ^ 2 + 18 * A * Q - 27 * A ^ 2 =
        8 * a * x * (x ^ 2 - 3 * y ^ 2) := by
    apply sub_eq_zero.mp
    calc
      Q ^ 2 + 18 * A * Q - 27 * A ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) =
        (x ^ 2 + y ^ 2) ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) +
          18 * A * (x ^ 2 + y ^ 2) - 27 * A ^ 2 := by
        rw [coordinates.1]
        ring1
    _ = 0 := by rw [deltoidEquation]; ring1
  rw [oddTerm]
  calc
    64 * Q ^ 3 * A * (spread * (3 - 4 * spread) ^ 2) =
        64 * a ^ 2 * (spread * Q) * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by
      rw [aSquare]
      ring1
    _ = 64 * a ^ 2 * x ^ 2 * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by rw [coordinates.2]
    _ =
        (8 * a * x *
          ((spread * Q) - 3 * ((1 - spread) * Q))) ^ 2 := by
      ring1
    _ = (8 * a * x * (x ^ 2 - 3 * y ^ 2)) ^ 2 := by
      rw [coordinates.2, ← squareCoordinates.2]

/-- The Cartesian hippopede equation yields this corrected cleared form. -/
theorem hippopede_rational_polar_corrected
    (xSquared ySquared A B spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (hippopedeEquation :
      Q ^ 2 + 4 * B * (B - A) * Q = 4 * B ^ 2 * xSquared) :
    4 * B ^ 2 * spread = Q + 4 * B * (B - A) := by
  have productZero :
      Q * (Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) = 0 := by
    calc
      Q * (Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) =
          Q ^ 2 + 4 * B * (B - A) * Q -
            4 * B ^ 2 * (spread * Q) := by ring1
      _ =
          Q ^ 2 + 4 * B * (B - A) * Q - 4 * B ^ 2 * xSquared := by
        rw [coordinates.2]
      _ = 0 := by rw [hippopedeEquation]; ring1
  have linearZero :=
    eq_zero_of_mul_eq_zero_left QNonzero productZero
  apply sub_eq_zero.mp
  calc
    4 * B ^ 2 * spread - (Q + 4 * B * (B - A)) =
        -(Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) := by ring1
    _ = 0 := by rw [linearZero]; ring1

/-- The printed hippopede form fails at `A=1`, `B=4`, `Q=16`, `s=1`,
although the corrected form and Cartesian equation both hold. -/
theorem printed_hippopede_counterexample :
    let R := RFAP.ConstructiveFraction.Rational
    let A : R := 1
    let B : R := 4
    let Q : R := 16
    let spread : R := 1
    Q ^ 2 + 4 * B * (B - A) * Q = 4 * B ^ 2 * (spread * Q) ∧
      4 * B ^ 2 * spread = Q + 4 * B * (B - A) ∧
      4 * B * spread ≠ Q + 4 * B * (B - A) := by
  decide

/-! ## Lemniscate of Bernoulli and folium of Descartes -/

/-- The Appendix A normalization of Bernoulli's lemniscate has the printed
equation `4s=Q+2` away from the origin. -/
theorem bernoulli_lemniscate_rational_polar
    (xSquared ySquared spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscateEquation : Q ^ 2 = 2 * (xSquared - ySquared)) :
    4 * spread = Q + 2 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  have productZero : Q * (Q - (4 * spread - 2)) = 0 := by
    calc
      Q * (Q - (4 * spread - 2)) =
          Q ^ 2 - 2 * (xSquared - ySquared) := by
        rw [squareCoordinates.1, squareCoordinates.2]
        ring1
      _ = 0 := by rw [lemniscateEquation]; ring1
  have linearZero :=
    eq_zero_of_mul_eq_zero_left QNonzero productZero
  apply sub_eq_zero.mp
  calc
    4 * spread - (Q + 2) = -(Q - (4 * spread - 2)) := by ring1
    _ = 0 := by rw [linearZero]; ring1

/-- The folium `x³+y³+3xy=0` implies the source's rational polar
polynomial at every non-origin point. -/
theorem folium_rational_polar
    (x y spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (foliumEquation : x ^ 3 + y ^ 3 + 3 * x * y = 0) :
    (2 * spread - 1) ^ 2 * (spread ^ 2 - spread + 1) ^ 2 * Q ^ 2 -
        18 * spread * (1 - spread) *
          (1 - 3 * spread + 3 * spread ^ 2) * Q +
        81 * spread ^ 2 * (1 - spread) ^ 2 = 0 := by
  have squareCoordinates :=
    RationalSphericalCoordinates.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  have productSquare :
      (x * y) ^ 2 = spread * (1 - spread) * Q ^ 2 := by
    rw [mul_pow, squareCoordinates.1, squareCoordinates.2]
    ring1
  have sumSquare : (x + y) ^ 2 = Q + 2 * (x * y) := by
    rw [coordinates.1]
    ring1
  have factoredFolium :
      (x + y) * (Q - x * y) + 3 * x * y = 0 := by
    calc
      (x + y) * (Q - x * y) + 3 * x * y =
          x ^ 3 + y ^ 3 + 3 * x * y := by
        rw [coordinates.1]
        ring1
      _ = 0 := foliumEquation
  have factorEquality :
      (x + y) * (Q - x * y) = -(3 * x * y) := by
    apply sub_eq_zero.mp
    calc
      (x + y) * (Q - x * y) - -(3 * x * y) =
          (x + y) * (Q - x * y) + 3 * x * y := by ring1
      _ = 0 := factoredFolium
  have squaredFactor :
      (x + y) ^ 2 * (Q - x * y) ^ 2 = (3 * x * y) ^ 2 := by
    calc
      (x + y) ^ 2 * (Q - x * y) ^ 2 =
          ((x + y) * (Q - x * y)) ^ 2 := by ring1
      _ = (-(3 * x * y)) ^ 2 := by rw [factorEquality]
      _ = (3 * x * y) ^ 2 := by ring1
  let linearResidual : K :=
    2 * spread * (1 - spread) * (x * y) +
      Q * (1 - 3 * spread * (1 - spread)) -
      9 * spread * (1 - spread)
  have scaledLinear : Q ^ 2 * linearResidual = 0 := by
    calc
      Q ^ 2 * linearResidual =
          Q ^ 3 - 3 * Q *
              (spread * (1 - spread) * Q ^ 2) +
            2 * (x * y) * (spread * (1 - spread) * Q ^ 2) -
            9 * (spread * (1 - spread) * Q ^ 2) := by
        dsimp only [linearResidual]
        ring1
      _ = Q ^ 3 - 3 * Q * (x * y) ^ 2 +
            2 * (x * y) * (x * y) ^ 2 - 9 * (x * y) ^ 2 := by
        rw [productSquare]
      _ =
          (Q + 2 * (x * y)) * (Q - x * y) ^ 2 -
            (3 * x * y) ^ 2 := by ring1
      _ = (x + y) ^ 2 * (Q - x * y) ^ 2 -
            (3 * x * y) ^ 2 := by rw [sumSquare]
      _ = 0 := by rw [squaredFactor]; ring1
  have onceCancelled : Q * linearResidual = 0 := by
    apply eq_zero_of_mul_eq_zero_left QNonzero
    calc
      Q * (Q * linearResidual) = Q ^ 2 * linearResidual := by ring1
      _ = 0 := scaledLinear
  have linearZero : linearResidual = 0 :=
    eq_zero_of_mul_eq_zero_left QNonzero onceCancelled
  have centeredEquality :
      Q * (1 - 3 * spread * (1 - spread)) -
          9 * spread * (1 - spread) =
        -(2 * spread * (1 - spread) * (x * y)) := by
    apply sub_eq_zero.mp
    calc
      Q * (1 - 3 * spread * (1 - spread)) -
          9 * spread * (1 - spread) -
          -(2 * spread * (1 - spread) * (x * y)) =
        linearResidual := by
          dsimp only [linearResidual]
          ring1
      _ = 0 := linearZero
  calc
    (2 * spread - 1) ^ 2 * (spread ^ 2 - spread + 1) ^ 2 * Q ^ 2 -
          18 * spread * (1 - spread) *
            (1 - 3 * spread + 3 * spread ^ 2) * Q +
          81 * spread ^ 2 * (1 - spread) ^ 2 =
        (Q * (1 - 3 * spread * (1 - spread)) -
            9 * spread * (1 - spread)) ^ 2 -
          4 * spread ^ 2 * (1 - spread) ^ 2 * (x * y) ^ 2 := by
      rw [productSquare]
      ring1
    _ = (Q * (1 - 3 * spread * (1 - spread)) -
            9 * spread * (1 - spread)) ^ 2 -
          (2 * spread * (1 - spread) * (x * y)) ^ 2 := by ring1
    _ = (-(2 * spread * (1 - spread) * (x * y))) ^ 2 -
          (2 * spread * (1 - spread) * (x * y)) ^ 2 := by
      rw [centeredEquality]
    _ = 0 := by ring1

end RationalPolarCatalogue
end DivineProportions
