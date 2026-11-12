module

public import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Cached local owners with complete original-owner readback -/

public section

namespace Purelib.RootIsolation.Owner.Local.Preparation

open Purelib.Polynomial
open Purelib.Geometry.Rational
open Purelib.Data.Rat
open Basic (LocalOwner)

set_option genInjectivity false in
/-- A retained local owner equal to one original mathematical owner.

The equality identifies the complete box and clearance certificate, rather
than only the selected root or one numerical reading. -/
structure Prepared {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (original : LocalOwner p) where
  /-- The actual cached local owner consumed by numerical construction. -/
  owner : LocalOwner p
  /-- The cached record is exactly the supplied original local owner. -/
  owner_eq : owner = original

constructive_injectivity Prepared

/-- Reconstruct an original local owner from exact cached box and bound readings.

Only the supplied box and bound are executable inputs. The complete original
owner certifies their readbacks and supplies the same properness, boundary
inequality and winding proofs. -/
@[expose] def fromReadback
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (original : LocalOwner p) (box : Box) (bound : Fraction.Rational)
    (box_eq : box = original.box) (bound_eq : bound = original.clearance.bound) : Prepared original :=
  let owner : LocalOwner p :=
    { box := box
      proper := by rewrite [box_eq]; exact original.proper
      clearance :=
        { bound := bound
          positive := by rewrite [bound_eq]; exact original.clearance.positive
          lower := by
            intro value boundary
            rewrite [box_eq] at boundary
            rewrite [bound_eq]
            exact original.clearance.lower value boundary }
      rawWindingFour := by rewrite [box_eq]; exact original.rawWindingFour }
  { owner := owner
    owner_eq := by
      cases original with
      | mk originalBox proper clearance winding =>
          cases box_eq
          cases clearance with
          | mk originalBound positive lower =>
              cases bound_eq
              rfl }

/-- The prepared owner's box is the actual supplied cached box. -/
theorem fromReadback_box
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (original : LocalOwner p) (box : Box) (bound : Fraction.Rational)
    (box_eq : box = original.box) (bound_eq : bound = original.clearance.bound) :
    (fromReadback original box bound box_eq bound_eq).owner.box = box := rfl

/-- The prepared boundary certificate consumes the actual supplied cached bound. -/
theorem fromReadback_bound
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (original : LocalOwner p) (box : Box) (bound : Fraction.Rational)
    (box_eq : box = original.box) (bound_eq : bound = original.clearance.bound) :
    (fromReadback original box bound box_eq bound_eq).owner.clearance.bound = bound := rfl

end Purelib.RootIsolation.Owner.Local.Preparation
