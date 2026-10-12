module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary.Interior
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Nearby
import Purelib.Polynomial.Winding.Box.Residual.Nearby
public import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.RootIsolation.State.WindingOne.Interior

/-- A winding-one box lies strictly inside a clear cell when its anchor is inside and the cell clearance dominates
nearby residual variation.

Both boxes retain the same ambient domain; a boundary intersection would force zero winding by the displayed finite
residual bound. -/
theorem strictInterior_of_anchor_mem_of_dominates
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient cell : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient)
    (degreePositive : 0 < p.natDegree)
    (cellRefines : cell.Refines ambient)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p cell)
    (anchorInside : cell.Contains state.box.anchor)
    (dominates : 2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient state.box +
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * state.box.diagonalSq) <
      clearance.bound) :
    state.box.StrictInterior cell := open Purelib.Data in by
  cases Box.strictInteriorDecidable state.box cell with
  | isTrue strict => exact strict
  | isFalse notStrict =>
    obtain ⟨point, boundary, pointInside⟩ :=
      Box.Boundary.Interior.exists_boundary_point_of_anchor_mem_of_not_strictInterior
        anchorInside notStrict
    let nearby : Dense.Gaussian.Bounds.Box.Residual.Nearby.NearbyClearPointCertificate p ambient state.box :=
      { point := point
        point_mem := cellRefines.contains boundary.1
        clearance := clearance.bound
        radiusSq := state.box.diagonalSq
        clearance_lower := by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using clearance.lower point boundary
        anchor_distance := state.box.normSq_sub_anchor_le pointInside
        dominates := dominates }
    have zero := Winding.Box.Residual.Nearby.quadrupledBoxWinding_eq_zero_of_nearby_clear_point
      p degreePositive state.refinesAmbient state.proper nearby
    rw [state.rawWindingFour] at zero
    exact ((by decide : (4 : Int) ≠ 0) zero).elim
end Purelib.RootIsolation.State.WindingOne.Interior

end
