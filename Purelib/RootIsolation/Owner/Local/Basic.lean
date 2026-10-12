module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Local winding-one polynomial owners

The original polynomial indexes one retained proper rational box, its positive boundary-clearance certificate and its
exact quadrupled winding four.
-/

public section

namespace Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- The local data needed to continue one winding-one owner.  Unlike a full
Paper-I track, it does not bake in a fixed ambient box; this makes the same
rational box reusable as the ambient of the next coefficient reading.

The original polynomial indexes one retained proper rational box, its positive boundary-clearance certificate and its
exact quadrupled winding four. -/
structure LocalOwner (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The retained rational box for this local polynomial owner. -/ box : Box
  /-- The retained box has strictly positive width and height. -/ proper : box.Proper
  /-- The polynomial has the retained positive boundary-clearance certificate. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The original polynomial has raw winding four around the retained box. -/ rawWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding p box = 4

constructive_injectivity LocalOwner

end Purelib.RootIsolation.Owner.Local.Basic

end
