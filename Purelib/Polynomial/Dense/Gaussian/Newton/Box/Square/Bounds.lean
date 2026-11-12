module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds

/-- If the Newton displacement is at most `r²`, every point of the
centered square is within `6r²` (in squared norm) of the source anchor. -/
theorem centeredSquare_normSq_sub_anchor_le
    {p : CoefficientPolynomial} {source : Box} {r :
      Fraction.Rational}
    (positive : 0 < r)
    (displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source - source.anchor)
        ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical}
    (inside : (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source)
      r positive.le).Contains z) :
    Gaussian.Norm.Basic.normSq (z - source.anchor) ≤ 6 * r ^ 2 := by
  have radial := Box.Square.Centered.centeredSquare_normSq_sub_center_le
    (Anchor.anchorNewtonCenter p source) positive.le inside
  have decomposition : z - source.anchor =
      (z - Anchor.anchorNewtonCenter p source) +
        (Anchor.anchorNewtonCenter p source - source.anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
      ring1
  rw [decomposition]
  have sumBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (z - Anchor.anchorNewtonCenter p source)
    (Anchor.anchorNewtonCenter p source - source.anchor)
  calc
    Gaussian.Norm.Basic.normSq ((z - Anchor.anchorNewtonCenter p source) +
        (Anchor.anchorNewtonCenter p source - source.anchor)) ≤
        2 * (Gaussian.Norm.Basic.normSq (z - Anchor.anchorNewtonCenter p source) +
          Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source -
            source.anchor)) := sumBound
    _ ≤ 2 * (2 * r ^ 2 + r ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add radial displacementSmall) (by decide)
    _ = 6 * r ^ 2 := by ring1

/-- Coarse Taylor-error budget on the Newton square. -/
def newtonErrorBudget (p :
  CoefficientPolynomial) (ambient : Box)
    (r : Fraction.Rational) : Fraction.Rational :=
  36 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * (r ^ 2) ^ 2

/-- Explicit upper bound for the Newton linearization on its centered-square
boundary. -/
def separatedNewtonLinearizationMajorant
    (p : CoefficientPolynomial) (ambient : Box) (r :
      Fraction.Rational) :
      Fraction.Rational :=
  2 * Bounds.Box.denseEvalNormMajorant (GCD.derivative p) ambient * r ^ 2

/-- The Newton boundary majorant is positive at every positive radius. -/
theorem separatedNewtonLinearizationMajorant_pos
    (p : CoefficientPolynomial) (ambient : Box) {r :
      Fraction.Rational}
    (positive : 0 < r) :
    0 < separatedNewtonLinearizationMajorant p ambient r :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Bounds.Box.denseEvalNormMajorant_pos
        (GCD.derivative p) ambient))
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)

/-- Bound the Newton linearization on its centered-square boundary.

The source box refines the ambient box, which bounds the derivative at its anchor; the centered square supplies the
radial bound. -/
theorem newtonLinearization_boundary_le_majorant
    {p : CoefficientPolynomial} {ambient source : Box}
    (sourceRefines : source.Refines ambient)
    {r : Fraction.Rational} (positive : 0 < r) {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p source) r
        positive.le) z) :
    Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p source).eval z)
      ≤
      separatedNewtonLinearizationMajorant p ambient r := by
  have sourceAnchorInside : ambient.Contains source.anchor :=
    sourceRefines.contains source.contains_anchor
  have derivativeBound := Bounds.Box.normSq_eval_le_denseEvalNormMajorant
    (GCD.derivative p) sourceAnchorInside
  have radial := Box.Square.Centered.centeredSquare_normSq_sub_center_le
    (Anchor.anchorNewtonCenter p source) positive.le boundary.1
  rw [Linearization.newtonLinearization, Linear.Affine.affineCoordinate_eval,
    Gaussian.Norm.Basic.normSq_mul]
  calc
    Gaussian.Norm.Basic.normSq ((GCD.derivative p).eval source.anchor) *
        Gaussian.Norm.Basic.normSq (z - Anchor.anchorNewtonCenter p source) ≤
      Bounds.Box.denseEvalNormMajorant (GCD.derivative p) ambient *
        (2 * r ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct derivativeBound radial
        (Gaussian.Norm.Basic.normSq_nonneg (z - Anchor.anchorNewtonCenter p source))
        (Bounds.Box.denseEvalNormMajorant_pos
          (GCD.derivative p) ambient).le
    _ = separatedNewtonLinearizationMajorant p ambient r := by
      unfold separatedNewtonLinearizationMajorant
      ring1
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds

end
