module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Square
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation
open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

/-!
# Squarefree Newton extraction thresholds

Protected-radius, derivative, Taylor and displacement bounds determine the
original extraction radius and source diagonal threshold from retained owners.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense

/-- Radius below the protected strip, the unit scale, and the finite Taylor
dominance scale.

The original half-protected-radius cap, unit cap and derivative-to-Taylor
quotient retain their same nested minimum. The supplied squarefree
certificate and boundary clearance remain attached to the original box. -/
@[expose] public def baseExtractionRadius
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient) :
      Fraction.Rational :=
  min ((1 / 2 : Fraction.Rational) *
      ProtectedRadius.protectedBoundaryRadius p ambient clearance)
    (min 1 (Squarefree.derivativeMargin squarefree ambient /
      (Band.Parameters.extractionTaylorScale * Bounds.Box.Taylor.denseTaylorRemainderBound
        p ambient)))

/-- The base extraction radius is positive for a proper box with its retained boundary clearance.

A proper ambient box has a positive protected boundary radius, and the
retained squarefree derivative margin and Taylor bound are positive.
These original quantities make the same minimum strictly positive. -/
public theorem baseExtractionRadius_pos
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) :
    0 < baseExtractionRadius squarefree ambient clearance := by
  have onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
  have denominatorPositive := Arithmetic.mul_pos_direct
    Band.Parameters.extractionTaylorScale_pos
    (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  exact Basic.lt_min
    (Arithmetic.mul_pos_direct (by decide)
      (ProtectedRadius.protectedBoundaryRadius_pos p clearance proper))
    (Basic.lt_min onePositive
      (Field.div_pos_direct
        (Squarefree.derivativeMargin_pos squarefree ambient) denominatorPositive))

/-- The requested radius also enforces the final diagonal request.

The original base radius is capped by one eighth of the supplied
tolerance using the same rational minimum. The original squarefree
certificate, ambient box and boundary clearance determine its other cap. -/
@[expose] public def extractionRadius
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  min (baseExtractionRadius squarefree ambient clearance)
    ((1 / 8 : Fraction.Rational) * epsilon)

/-- The extraction radius is positive for a proper ambient box and a positive requested tolerance.

The proper ambient box and supplied positive tolerance make both
original minimum entries positive. The retained squarefree and boundary
clearance evidence therefore certifies the same extraction radius. -/
public theorem extractionRadius_pos
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    0 < extractionRadius squarefree ambient clearance epsilon := by
  exact Basic.lt_min (baseExtractionRadius_pos squarefree clearance proper)
    (Arithmetic.mul_pos_direct (by decide) epsilonPositive)

/-- The extraction radius is bounded by the retained protected boundary radius.

The same nested radius minimum is bounded by half the protected radius.
Nonnegativity of that retained protected radius then supplies the stated
bound, including degenerate ambient boxes and arbitrary tolerances. -/
public theorem extractionRadius_le_protected
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    extractionRadius squarefree ambient clearance epsilon ≤
      ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
  have halfBound : extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 2 : Fraction.Rational) *
        ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
    (Basic.min_le_left _ _).trans (Basic.min_le_left _ _)
  calc
    extractionRadius squarefree ambient clearance epsilon ≤
        (1 / 2 : Fraction.Rational) *
          ProtectedRadius.protectedBoundaryRadius p ambient clearance := halfBound
    _ ≤ 1 * ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Fraction.Rational) ≤ 1 by decide)
        (ProtectedRadius.protectedBoundaryRadius_nonneg p ambient clearance)
    _ = ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
      exact _root_.one_mul _

/-- Twice the extraction radius is bounded by the retained protected boundary radius.

The original half-protected-radius cap bounds the same extraction radius.
Multiplying by the positive scalar two cancels that half exactly; no
positivity condition on the requested tolerance is needed. -/
public theorem extractionRadius_twice_le_protected
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    2 * extractionRadius squarefree ambient clearance epsilon ≤
      ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
  have halfBound : extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 2 : Fraction.Rational) *
        ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
    (Basic.min_le_left _ _).trans (Basic.min_le_left _ _)
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 2) (by decide)).le
  calc
    2 * extractionRadius squarefree ambient clearance epsilon ≤
        2 * ((1 / 2 : Fraction.Rational) *
          ProtectedRadius.protectedBoundaryRadius p ambient clearance) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct halfBound
        twoNonnegative
    _ = ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
      have twoHalf : (2 : Fraction.Rational) * (1 / 2) = 1 := by decide
      calc
        2 * ((1 / 2 : Fraction.Rational) *
            ProtectedRadius.protectedBoundaryRadius p ambient clearance) =
            (2 * (1 / 2 : Fraction.Rational)) *
              ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
          (Fraction.Field.mul_assoc _ _ _).symm
        _ = 1 * ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
          rw [twoHalf]
        _ = ProtectedRadius.protectedBoundaryRadius p ambient clearance := _root_.one_mul _

/-- The extraction radius is at most one.

The retained unit cap occurs inside the original base-radius minimum.
The two exact minimum projections bound the same extraction radius
without any extra condition on the supplied tolerance. -/
public theorem extractionRadius_le_one
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    extractionRadius squarefree ambient clearance epsilon ≤ 1 :=
  (Basic.min_le_left _ _).trans ((Basic.min_le_right _ _).trans
    (Basic.min_le_left _ _))

/-- The extraction radius is at most one eighth of the requested tolerance.

The second entry of the original outer minimum is exactly one eighth
of the supplied tolerance. Its direct projection bounds the same
computed radius for arbitrary rational tolerance. -/
public theorem extractionRadius_le_eighth
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    extractionRadius squarefree ambient clearance epsilon ≤
      (1 / 8 : Fraction.Rational) * epsilon :=
  Basic.min_le_right _ _

/-- The computed extraction radius satisfies the doubled Taylor-budget inequality.

For a proper ambient box and positive tolerance, the retained radius
is positive, at most one and below the derivative-to-Taylor quotient.
Those same caps bound its square and certify the doubled Taylor
coefficient against the original squarefree derivative margin. -/
public theorem extractionRadius_taylor
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    let r := extractionRadius squarefree ambient clearance epsilon
    2 * (Band.Parameters.extractionBandTaylorCoefficient *
      Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
      Squarefree.derivativeMargin squarefree ambient := by
  let r := extractionRadius squarefree ambient clearance epsilon
  let eta := Squarefree.derivativeMargin squarefree ambient
  let taylor := Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  have radiusPositive : 0 < r :=
    extractionRadius_pos squarefree clearance proper epsilonPositive
  have radiusLeOne : r ≤ 1 :=
    extractionRadius_le_one squarefree ambient clearance epsilon
  have radiusRatio : r ≤ eta / (Band.Parameters.extractionTaylorScale * taylor) :=
    (Basic.min_le_left _ _).trans ((Basic.min_le_right _ _).trans
      (Basic.min_le_right _ _))
  have denominatorPositive : 0 < Band.Parameters.extractionTaylorScale * taylor :=
    Arithmetic.mul_pos_direct
      Band.Parameters.extractionTaylorScale_pos
      (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (Band.Parameters.extractionTaylorScale * taylor) ≤ eta :=
    (Field.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = r := by ring1
  have scaledSquare : Band.Parameters.extractionTaylorScale * taylor * r ^ 2 ≤
      Band.Parameters.extractionTaylorScale * taylor * r :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct squareLeRadius
      denominatorPositive.le
  calc
    2 * (Band.Parameters.extractionBandTaylorCoefficient *
        Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) =
        Band.Parameters.extractionTaylorScale * taylor * r ^ 2 := by
      dsimp only [Band.Parameters.extractionBandTaylorCoefficient,
        Band.Parameters.extractionTaylorScale,
        taylor]
      ring1
    _ ≤ Band.Parameters.extractionTaylorScale * taylor * r := scaledSquare
    _ = r * (Band.Parameters.extractionTaylorScale * taylor) := by ring1
    _ ≤ eta := ratioScaled

/-- Squared-diagonal threshold sufficient for the protected strip, derivative
separation, and Newton displacement.

The retained protected radius square, derivative-to-Lipschitz quotient
and displacement-to-Lipschitz quotient form the same nested minimum.
Each term uses the original squarefree certificate, box and extraction radius. -/
@[expose] public def sourceDiagonalThreshold
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  let rho := ProtectedRadius.protectedBoundaryRadius p ambient clearance
  let margin := Squarefree.derivativeMargin squarefree ambient
  let baseRadius := min ((1 / 2 : Fraction.Rational) * rho)
    (min 1 (margin / (Band.Parameters.extractionTaylorScale *
      Bounds.Box.Taylor.denseTaylorRemainderBound p ambient)))
  let radius := min baseRadius ((1 / 8 : Fraction.Rational) * epsilon)
  let lipschitz := Bounds.Box.denseLipschitzBound p ambient
  min (Fraction.square rho)
    (min (Squarefree.derivativeThreshold squarefree ambient / lipschitz)
      (margin * Fraction.square radius / lipschitz))

/-- Sharing the radius and derivative readings retains the complete original nested threshold expression.

The equality holds for every original squarefree certificate, box, clearance
and accuracy, including nonpositive accuracies. It preserves all three
minimum terms and the original extraction-radius caps exactly.
-/
public theorem sourceDiagonalThreshold_eq_original
    {p : CoefficientPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon =
      let rho := ProtectedRadius.protectedBoundaryRadius p ambient clearance
      let radius := extractionRadius squarefree ambient clearance epsilon
      let lipschitz := Bounds.Box.denseLipschitzBound p ambient
      min (rho ^ 2)
        (min (Squarefree.derivativeThreshold squarefree ambient / lipschitz)
          (Squarefree.derivativeMargin squarefree ambient * radius ^ 2 / lipschitz)) := by
  dsimp only [sourceDiagonalThreshold, extractionRadius, baseExtractionRadius]
  rewrite [Fraction.square_eq_mul, Fraction.square_eq_mul, pow_two, pow_two]
  rfl

/-- The source squared-diagonal threshold is positive for a proper ambient box and positive tolerance.

A proper ambient box and positive tolerance give positive protected
and extraction radii. The retained squarefree derivative quantities
and Lipschitz bound then make all three original minimum entries positive. -/
public theorem sourceDiagonalThreshold_pos
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    {ambient : Box} (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    0 < sourceDiagonalThreshold squarefree ambient clearance epsilon := by
  rewrite [sourceDiagonalThreshold_eq_original]
  have rhoPositive := ProtectedRadius.protectedBoundaryRadius_pos p clearance proper
  have radiusPositive := extractionRadius_pos squarefree clearance proper
    epsilonPositive
  have lipschitzPositive := Bounds.Box.denseLipschitzBound_pos p ambient
  exact Basic.lt_min
    (Arithmetic.pow_pos_direct rhoPositive 2)
    (Basic.lt_min
      (Field.div_pos_direct
        (Squarefree.derivativeThreshold_pos squarefree ambient) lipschitzPositive)
      (Field.div_pos_direct
        (Arithmetic.mul_pos_direct
          (Squarefree.derivativeMargin_pos squarefree ambient)
          (Arithmetic.pow_pos_direct radiusPositive 2))
        lipschitzPositive))

/-- The source diagonal threshold is at most the squared protected boundary radius.

The first original minimum entry is the retained protected radius
square. Its direct projection bounds the same diagonal threshold
without imposing a positivity condition on the tolerance. -/
public theorem sourceDiagonalThreshold_le_protected
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      ProtectedRadius.protectedBoundaryRadius p ambient clearance ^ 2 := by
  rewrite [sourceDiagonalThreshold_eq_original]
  exact Basic.min_le_left _ _

/-- The source diagonal threshold times the Lipschitz scale fits within the derivative threshold, expressed as a
quotient bound.

The original inner minimum retains the derivative threshold divided
by the same box Lipschitz bound. Its two scalar projections bound the
same source diagonal threshold by that quotient. -/
public theorem sourceDiagonalThreshold_le_derivative
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      Squarefree.derivativeThreshold squarefree ambient /
        Bounds.Box.denseLipschitzBound p ambient :=
  (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)

/-- The source diagonal threshold is bounded by the derivative margin times the squared extraction radius divided by the
Lipschitz scale.

The original final minimum entry retains the derivative margin times
the extraction radius square divided by the same Lipschitz bound.
Its projections certify the displayed displacement quotient bound. -/
public theorem sourceDiagonalThreshold_le_displacement
    {p : CoefficientPolynomial} (squarefree :
      SquarefreeCertificate
      p)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) :
    sourceDiagonalThreshold squarefree ambient clearance epsilon ≤
      Squarefree.derivativeMargin squarefree ambient *
          extractionRadius squarefree ambient clearance epsilon ^ 2 /
        Bounds.Box.denseLipschitzBound p ambient := by
  rewrite [sourceDiagonalThreshold_eq_original]
  exact (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)

end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
