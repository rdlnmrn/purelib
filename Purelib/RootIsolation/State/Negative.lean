module

public import Purelib.RootIsolation.State.Raw
import Purelib.Data.Int.Order

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Clear proper polynomial states with negative winding

The original polynomial and ambient box index the retained proper subbox, its positive boundary clearance and the strict
negativity of its quadrupled winding.
-/

public section

namespace Purelib.RootIsolation.State.Negative

set_option genInjectivity false in
/-- A clear negative-raw-winding region in one fixed finite ambient box.

The original polynomial and ambient box index the retained proper subbox, its positive boundary clearance and the strict
negativity of its quadrupled winding. -/
structure NegativeState
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) where
  /-- The retained rational box carrying the winding certificate. -/ box : Box
  /-- The retained box lies within the specified original ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The retained box has strictly positive width and height. -/ proper : box.Proper
  /-- A positive finite boundary-clearance certificate for the original polynomial and retained box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The original polynomial has strictly negative quadrupled winding on the retained box. -/ rawWinding_neg :
    Winding.Box.Basic.quadrupledBoxWinding p box < 0

constructive_injectivity NegativeState

end Purelib.RootIsolation.State.Negative

end

namespace Purelib.RootIsolation.State.Negative.NegativeState

open Purelib.Data
open Purelib.RootIsolation

/-- Retain a negative state as a nonzero raw-winding state.

The original box, ambient refinement, properness and clearance are unchanged.
Integer irreflexivity turns the stored negative winding bound into a nonzero
certificate for that same box and polynomial. -/
@[expose] public def raw
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.Negative.NegativeState p ambient) :
    State.Raw.RawWindingState p ambient where
  box := state.box
  refinesAmbient := state.refinesAmbient
  proper := state.proper
  clearance := state.clearance
  rawWinding_ne := by
    intro equal
    have impossible : (0 : Int) < 0 := equal ▸ state.rawWinding_neg
    exact Int.Order.lt_irrefl 0 impossible

end Purelib.RootIsolation.State.Negative.NegativeState
