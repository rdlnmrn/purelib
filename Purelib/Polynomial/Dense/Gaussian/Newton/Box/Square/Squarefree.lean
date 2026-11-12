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
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
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

open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree (NewtonCenterCertificate)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Squarefree

/-- The positive norm gap left after paying the complete Taylor budget. -/
def newtonDominanceMargin {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient :
      Box)
    (r : Fraction.Rational) : Fraction.Rational :=
  Squarefree.derivativeMargin squarefree ambient * r ^ 2 -
    Bounds.newtonErrorBudget p ambient r

/-- Bound the Newton error on the centered square boundary by its Taylor budget.

The positive-radius square and source refine the ambient box, and the squared displacement from the source anchor to the
Newton center is at most the squared radius. -/
theorem newtonError_le_budget
    {p : CoefficientPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    Gaussian.Norm.Basic.normSq ((Linearization.newtonError p source).eval z) ≤
      Bounds.newtonErrorBudget p ambient r := by
  have insideTarget := boundary.1
  have insideAmbient := targetRefines.contains insideTarget
  have distance := Bounds.centeredSquare_normSq_sub_anchor_le
    positive displacementSmall insideTarget
  have distanceSquared : Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 ≤
      (6 * r ^ 2) ^ 2 :=
    Arithmetic.pow_le_pow_direct
      (Gaussian.Norm.Basic.normSq_nonneg (z - source.anchor)) distance 2
  have rawError := Taylor.normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    Gaussian.Norm.Basic.normSq ((Linearization.newtonError p source).eval z) ≤
        Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
          Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * (6 * r ^ 2) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        distanceSquared (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient).le
    _ = Bounds.newtonErrorBudget p ambient r := by
      dsimp only [Bounds.newtonErrorBudget]
      ring1

/-- The Newton dominance margin is positive under the doubled Taylor-budget bound.

A strictly positive radius and a derivative margin exceeding the doubled Taylor coefficient leave a positive gap after
the complete error budget. -/
theorem newtonDominanceMargin_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    {r : Fraction.Rational} (positive : 0 < r)
    (taylorSmall :
      2 * (36 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
        Squarefree.derivativeMargin squarefree ambient) :
    0 < newtonDominanceMargin squarefree ambient r := by
  have radiusSquarePositive :=
    Arithmetic.pow_pos_direct positive 2
  let base := 36 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2
  have thirtySixPositive : (0 : Fraction.Rational) < 36 :=
    Fraction.Cast.Order.natCast_pos_direct
      (n := 36) (by decide)
  have basePositive : 0 < base :=
    Arithmetic.mul_pos_direct
      (Arithmetic.mul_pos_direct thirtySixPositive
        (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)) radiusSquarePositive
  have halfStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        Arithmetic.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have coefficientBound :
      36 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2 <
        Squarefree.derivativeMargin squarefree ambient := by
    change base < Squarefree.derivativeMargin squarefree ambient
    exact halfStrict.trans_le taylorSmall
  have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
    coefficientBound radiusSquarePositive
  apply Arithmetic.sub_pos_direct
  calc
    Bounds.newtonErrorBudget p ambient r =
        (36 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) * r ^ 2 := by
      dsimp only [Bounds.newtonErrorBudget]
      ring1
    _ < Squarefree.derivativeMargin squarefree ambient * r ^ 2 := scaled

/-- Bound the affine Newton term below on the centered square boundary.

Its squared norm is at least the retained derivative margin times the squared positive radius. -/
theorem newtonLinearization_boundary_lower
    {p : CoefficientPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    {r : Fraction.Rational} (positive : 0 < r) {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    Squarefree.derivativeMargin squarefree ambient * r ^ 2 ≤
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval
        z) := by
  let affineClearance := Clearance.Box.Boundary.Affine.affineCoordinate_boundaryClearance
    newton.derivativeNonzero (Anchor.anchorNewtonCenter p source) positive
  have affineLower := affineClearance.lower z boundary
  have affineLowerExact :
      Gaussian.Norm.Basic.normSq ((GCD.derivative p).eval source.anchor) *
          r ^ 2 ≤ Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p
            source).eval z) := by
    change Gaussian.Basic.Canonical.normSq
        ((GCD.derivative p).eval source.anchor) * r ^ 2 ≤
      Gaussian.Basic.Canonical.normSq
        ((Linearization.newtonLinearization p source).eval z)
      at affineLower
    simpa only [← Gaussian.Norm.Basic.normSq_eq_canonical] using affineLower
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
    newton.derivativeLower
    (Arithmetic.sq_nonneg_direct r)).trans affineLowerExact

/-- The retained Newton dominance margin is a lower bound for the boundary norm gap.

The affine-term lower bound and complete Taylor error budget apply on the same centered square, with the ambient
refinement and displacement bounds retained. -/
theorem newtonDominanceMargin_le
    {p : CoefficientPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r)
    (targetRefines :
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le).Refines ambient)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    newtonDominanceMargin squarefree ambient r ≤
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval
        z) -
        Gaussian.Norm.Basic.normSq ((Linearization.newtonError p source).eval z) :=
          by
  have errorUpper : Gaussian.Norm.Basic.normSq ((Linearization.newtonError p
    source).eval z) ≤
      Bounds.newtonErrorBudget p ambient r :=
    newtonError_le_budget (p := p) (ambient := ambient) (source := source)
      (squarefree := squarefree) newton sourceRefines positive targetRefines
      displacementSmall boundary
  have linearLower : Squarefree.derivativeMargin squarefree ambient * r ^ 2 ≤
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval
        z) :=
    newtonLinearization_boundary_lower (p := p) (ambient := ambient)
      (source := source) (squarefree := squarefree) newton positive boundary
  exact Arithmetic.sub_le_sub_direct linearLower errorUpper
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Squarefree

end
