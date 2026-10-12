module
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Even
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Winding.Box.Parity

/-- A closed coprime polynomial boundary has even raw winding.

The imaginary-coordinate zero flags at shared vertices cancel between successive edges, leaving an explicit even
integer. -/
theorem quadrupledBoxWinding_even_of_boundaryCoprime
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (coprime : Dense.Gaussian.Path.Box.NoCommonZero.BoundaryCoprime p box) :
    Even (Winding.Box.Basic.quadrupledBoxWinding p box) := open Purelib.Data in by
  have bottom := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.bottom
  have right := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.right
  have top := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.top
  have left := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.left
  simp only [Dense.Gaussian.Path.Box.Sides.horizontalEdge_imag_eval] at bottom top
  simp only [Dense.Gaussian.Path.Box.Sides.verticalEdge_imag_eval] at right left
  let lowerLeftFlag : Int :=
    if (p.eval (Gaussian.Components.Basic.point box.xLower box.yLower)).im = 0 then 1 else 0
  let lowerRightFlag : Int :=
    if (p.eval (Gaussian.Components.Basic.point box.xUpper box.yLower)).im = 0 then 1 else 0
  let upperRightFlag : Int :=
    if (p.eval (Gaussian.Components.Basic.point box.xUpper box.yUpper)).im = 0 then 1 else 0
  let upperLeftFlag : Int :=
    if (p.eval (Gaussian.Components.Basic.point box.xLower box.yUpper)).im = 0 then 1 else 0
  change Even ((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower
      box.xUpper).doubledWinding -
    (lowerLeftFlag - lowerRightFlag)) at bottom
  change Even ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower
      box.yUpper).doubledWinding -
    (lowerRightFlag - upperRightFlag)) at right
  change Even ((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper
      box.xLower).doubledWinding -
    (upperRightFlag - upperLeftFlag)) at top
  change Even ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper
      box.yLower).doubledWinding -
    (upperLeftFlag - lowerLeftFlag)) at left
  rcases bottom with ⟨bottomHalf, bottomIdentity⟩
  rcases right with ⟨rightHalf, rightIdentity⟩
  rcases top with ⟨topHalf, topIdentity⟩
  rcases left with ⟨leftHalf, leftIdentity⟩
  let k := ((bottomHalf + rightHalf) + topHalf) + leftHalf
  have hk :
      (((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower
            box.xUpper).doubledWinding -
          (lowerLeftFlag - lowerRightFlag)) +
        ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower
            box.yUpper).doubledWinding -
          (lowerRightFlag - upperRightFlag)) +
        ((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper
            box.xLower).doubledWinding -
          (upperRightFlag - upperLeftFlag))) +
        ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper
            box.yLower).doubledWinding -
          (upperLeftFlag - lowerLeftFlag)) = k + k := by
    rewrite [bottomIdentity, rightIdentity, topIdentity, leftIdentity]
    dsimp [k]
    ring1
  refine ⟨k, ?_⟩
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  calc
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower
          box.xUpper).doubledWinding +
        (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower
          box.yUpper).doubledWinding +
        (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper
          box.xLower).doubledWinding +
        (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper
          box.yLower).doubledWinding =
      (((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower
            box.xUpper).doubledWinding -
          (lowerLeftFlag - lowerRightFlag)) +
        ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower
            box.yUpper).doubledWinding -
          (lowerRightFlag - upperRightFlag)) +
        ((Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper
            box.xLower).doubledWinding -
          (upperRightFlag - upperLeftFlag))) +
        ((Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper
            box.yLower).doubledWinding -
          (upperLeftFlag - lowerLeftFlag)) := by
        ring1
    _ = k + k := hk
end Purelib.Polynomial.Winding.Box.Parity

end
