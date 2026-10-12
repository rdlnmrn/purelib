module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Clearance.Box.Boundary.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic (Certificate)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate (SeparatedNewtonCenterCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated

/-! ## Newton transfer from an explicit derivative separation -/

/-- The same Taylor gap, parameterized by the exact quantitative resource
rather than by the particular Bézout certificate from which it arose. -/
def separatedNewtonDominanceMargin
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (r : Fraction.Rational) : Fraction.Rational :=
  separation.margin * r ^ 2 - Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget p ambient r

/-- The Newton dominance margin is positive under the doubled Taylor-budget bound.

A strictly positive radius and a derivative margin exceeding the doubled Taylor coefficient leave a positive gap after
the complete error budget. -/
theorem separatedNewtonDominanceMargin_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    0 < separatedNewtonDominanceMargin separation r := by
  have radiusSquarePositive :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  let base := 36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2
  have thirtySixPositive : (0 : Fraction.Rational) < 36 :=
    Fraction.Cast.Order.natCast_pos_direct
      (n := 36) (by decide)
  have basePositive : 0 < base :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct thirtySixPositive
        (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)) radiusSquarePositive
  have halfStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have coefficientBound :
      36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2 <
        separation.margin := by
    change base < separation.margin
    exact halfStrict.trans_le taylorSmall
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    coefficientBound radiusSquarePositive
  apply Fraction.Order.Arithmetic.sub_pos_direct
  calc
    Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget p ambient r =
        (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) * r ^ 2 := by
      dsimp only [Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget]
      ring1
    _ < separation.margin * r ^ 2 := scaled

/-- Bound the Newton error on the centered square boundary by its Taylor budget.

The positive-radius square and source refine the ambient box, and the squared displacement from the source anchor to the
Newton center is at most the squared radius. -/
theorem separatedNewtonError_le_budget
    {p : CoefficientPolynomial} {ambient source : Box}
    {separation : Certificate p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) ≤
      Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget p ambient r := by
  have insideTarget := boundary.1
  have insideAmbient := targetRefines.contains insideTarget
  have distance := Dense.Gaussian.Newton.Box.Square.Bounds.centeredSquare_normSq_sub_anchor_le
    positive displacementSmall insideTarget
  have distanceSquared : Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 ≤
      (6 * r ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Gaussian.Norm.Basic.normSq_nonneg (z - source.anchor)) distance 2
  have rawError := Dense.Gaussian.Newton.Box.Taylor.normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) ≤
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
          Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * (6 * r ^ 2) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        distanceSquared (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient).le
    _ = Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget p ambient r := by
      dsimp only [Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget]
      ring1

/-- Bound the affine Newton term below on the centered square boundary.

Its squared norm is at least the retained derivative margin times the squared positive radius. -/
theorem separatedNewtonLinearization_boundary_lower
    {p : CoefficientPolynomial} {ambient source : Box}
    {separation : Certificate p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    {r : Fraction.Rational} (positive : 0 < r) {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    separation.margin * r ^ 2 ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval
        z) := by
  let affineClearance := Clearance.Box.Boundary.Affine.affineCoordinate_boundaryClearance
    newton.derivativeNonzero (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) positive
  have affineLower := affineClearance.lower z boundary
  have affineLowerExact :
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval source.anchor) *
          r ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p
            source).eval z) :=
    by
      change Gaussian.Basic.Canonical.normSq
          ((Dense.Gaussian.GCD.derivative p).eval source.anchor) * r ^ 2 ≤
        Gaussian.Basic.Canonical.normSq
          ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval z)
        at affineLower
      simpa only [← Gaussian.Norm.Basic.normSq_eq_canonical] using affineLower
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    newton.derivativeLower
    (Fraction.Order.Arithmetic.sq_nonneg_direct r)).trans affineLowerExact

/-- The retained Newton dominance margin is a lower bound for the boundary norm gap.

The affine-term lower bound and complete Taylor error budget apply on the same centered square, with the ambient
refinement and displacement bounds retained. -/
theorem separatedNewtonDominanceMargin_le
    {p : CoefficientPolynomial} {ambient source : Box}
    {separation : Certificate p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    separatedNewtonDominanceMargin separation r ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval
        z) -
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) :=
          by
  have errorUpper : Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p
    source).eval z) ≤
      Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget p ambient r :=
    separatedNewtonError_le_budget newton sourceRefines positive
      targetRefines
      displacementSmall boundary
  have linearLower : separation.margin * r ^ 2 ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval
        z) :=
    separatedNewtonLinearization_boundary_lower newton positive boundary
  exact Fraction.Order.Arithmetic.sub_le_sub_direct linearLower errorUpper
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated

end
