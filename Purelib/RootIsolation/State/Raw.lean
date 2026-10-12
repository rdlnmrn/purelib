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

end Purelib.RootIsolation.State.Raw

end
