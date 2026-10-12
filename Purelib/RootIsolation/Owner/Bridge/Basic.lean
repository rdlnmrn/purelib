module

public import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Rouche.Connection
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Boundary-clearance bridges between polynomial owners

The same retained rational box has separate boundary certificates and winding witnesses for the two polynomials. These
data give each original local owner without replacing either polynomial.
-/

public section

namespace Purelib.RootIsolation.Owner.Bridge.Basic

set_option genInjectivity false in
/-- One rational winding-one owner carried by both endpoint polynomials of a
finite path piece.  The connection field records the finite Rouché reason
that these are two readings of the same local owner.

The same retained rational box has separate boundary certificates and winding witnesses for the two polynomials. These
data give each original local owner without replacing either polynomial. -/
structure OwnerBridge (left right : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The shared retained rational box for the two endpoint polynomials. -/ box : Box
  /-- The shared box has strictly positive width and height. -/ proper : box.Proper
  /-- The left polynomial has positive boundary clearance on the shared box. -/ leftClearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance left box
  /-- The right polynomial has positive boundary clearance on the shared box. -/ rightClearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance right box
  /-- The left polynomial has quadrupled winding four on the shared box. -/ leftWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding left box = 4
  /-- The right polynomial has quadrupled winding four on the shared box. -/ rightWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding right box = 4
  /-- The finite Rouché connection between the two original polynomial readings on their shared box. -/ connection :
    Winding.Box.Rouche.Connection.RoucheConnection left right box

constructive_injectivity OwnerBridge

namespace OwnerBridge

/-- Make a reflexive bridge from an existing local owner, reusing its box and clearance.

The same original local owner supplies both endpoint boxes, properness, boundary clearance and winding certificates;
reflexive polynomial equality supplies the retained Rouché connection. -/
@[expose] def reflexive {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (owner : Owner.Local.Basic.LocalOwner polynomial) : Owner.Bridge.Basic.OwnerBridge polynomial polynomial where
  box := owner.box
  proper := owner.proper
  leftClearance := owner.clearance
  rightClearance := owner.clearance
  leftWindingFour := owner.rawWindingFour
  rightWindingFour := owner.rawWindingFour
  connection := .equal rfl

/-- Reverse a retained owner bridge, exchanging endpoint certificates and reversing its Rouché connection.

The same shared box is retained while the original left and right clearance and winding certificates exchange places.
Reversal applies to the retained connection between those same endpoint polynomials. -/
@[expose] def reverse {left right : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) : Owner.Bridge.Basic.OwnerBridge right left where
  box := bridge.box
  proper := bridge.proper
  leftClearance := bridge.rightClearance
  rightClearance := bridge.leftClearance
  leftWindingFour := bridge.rightWindingFour
  rightWindingFour := bridge.leftWindingFour
  connection := bridge.connection.reverse

/-- Read the left local owner from the shared box and retained left certificates.

The original shared box, properness, left clearance and left winding certificate form the local owner of the same left
polynomial. -/
@[expose] def leftOwner {left right : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) : Owner.Local.Basic.LocalOwner left where
  box := bridge.box
  proper := bridge.proper
  clearance := bridge.leftClearance
  rawWindingFour := bridge.leftWindingFour

/-- Read the right local owner from the shared box and retained right certificates.

The original shared box, properness, right clearance and right winding certificate form the local owner of the same
right polynomial. -/
@[expose] def rightOwner {left right : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) : Owner.Local.Basic.LocalOwner right where
  box := bridge.box
  proper := bridge.proper
  clearance := bridge.rightClearance
  rawWindingFour := bridge.rightWindingFour

end OwnerBridge

end Purelib.RootIsolation.Owner.Bridge.Basic

end
