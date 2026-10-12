module
public import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.RootIsolation.Owner.Local.Transport

/-- Change only the displayed polynomial index of a local owner along an
exact coefficientwise equality. -/
def castOwner {left right :
  CoefficientPolynomial}
    (same : left = right) (owner : LocalOwner left) : LocalOwner right := by
  rw [← same]
  exact owner

/-- Transporting a local owner along polynomial equality preserves its exact box. -/
@[simp] theorem castOwner_box {left right :
  CoefficientPolynomial}
    (same : left = right) (owner : LocalOwner left) :
    (castOwner same owner).box = owner.box := by
  subst right
  rfl

/-- Transporting a local owner along polynomial equality preserves its exact clearance bound. -/
@[simp] theorem castOwner_clearance_bound
    {left right : CoefficientPolynomial}
    (same : left = right) (owner : LocalOwner left) :
    (castOwner same owner).clearance.bound = owner.clearance.bound := by
  subst right
  rfl

end Purelib.RootIsolation.Owner.Local.Transport

end
