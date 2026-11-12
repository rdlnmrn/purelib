module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Clear proper polynomial states with nonzero winding

The polynomial and fixed ambient box index a retained subbox, its refinement and properness evidence, its positive
boundary clearance and its original nonzero quadrupled winding.
-/

public section

namespace Purelib.RootIsolation.State.Raw

set_option genInjectivity false in
/-- A clear proper subbox carrying nonzero raw winding.

The polynomial and fixed ambient box index a retained subbox, its refinement and properness evidence, its positive
boundary clearance and its original nonzero quadrupled winding. -/
structure RawWindingState
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) where
  /-- The retained rational box carrying the winding certificate. -/ box : Box
  /-- The retained box lies within the specified original ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The retained box has strictly positive width and height. -/ proper : box.Proper
  /-- A positive finite boundary-clearance certificate for the original polynomial and retained box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The original polynomial has nonzero quadrupled winding on the retained box. -/ rawWinding_ne :
    Winding.Box.Basic.quadrupledBoxWinding p box ≠ 0

constructive_injectivity RawWindingState

/-- Raw states with the same box and boundary-clearance bound retain the same complete state record.

The polynomial and ambient indices stay fixed. Properness, refinement,
boundary inequalities and nonzero winding are proof fields, so equality of
these two executable readings identifies the whole original state.
-/
theorem RawWindingState.eq_of_box_bound
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {left right : RawWindingState p ambient}
    (boxSame : left.box = right.box)
    (boundSame : left.clearance.bound = right.clearance.bound) : left = right := by
  cases left with
  | mk leftBox leftRefines leftProper leftClearance leftWinding =>
    cases right with
    | mk rightBox rightRefines rightProper rightClearance rightWinding =>
      cases boxSame
      cases leftClearance with
      | mk leftBound leftPositive leftLower =>
        cases rightClearance with
        | mk rightBound rightPositive rightLower =>
          cases boundSame
          rfl

end Purelib.RootIsolation.State.Raw

end
