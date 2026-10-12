module
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Polynomial.Winding.Box.Rouche.Connection
public import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Winding.Box.Basic

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

namespace Purelib.RootIsolation.Owner.Bridge.Basic
namespace OwnerBridge

/-- Construct the target side of a bridge from one dominant endpoint and an
explicit finite boundary comparison. -/
def ofForward {left right :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (owner : Owner.Local.Basic.LocalOwner left)
    (certificate : Winding.Box.Rouche.Connection.OrientedRouche left right owner.box) :
    Owner.Bridge.Basic.OwnerBridge left right where
  box := owner.box
  proper := owner.proper
  leftClearance := owner.clearance
  rightClearance := by
    rw [certificate.target_eq_add]
    exact
      Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper
          certificate.dominance
  leftWindingFour := owner.rawWindingFour
  rightWindingFour := by
    rw [certificate.target_eq_add]
    exact
      (Purelib.Polynomial.Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper owner.clearance
          certificate.dominance).trans owner.rawWindingFour
  connection := .forward certificate

/-- The target-side clearance stored by a forward owner bridge is exactly
the finite boundary-dominance clearance used to construct it. -/
@[simp] theorem ofForward_rightClearance_bound
    {left right : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (owner : Owner.Local.Basic.LocalOwner left)
    (certificate : Winding.Box.Rouche.Connection.OrientedRouche left right owner.box) :
    (ofForward owner certificate).rightClearance.bound =
      (Clearance.Box.Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper
          certificate.dominance).bound := by
  obtain ⟨perturbation, targetEq, dominance⟩ := certificate
  subst right
  rfl
end OwnerBridge

end Purelib.RootIsolation.Owner.Bridge.Basic

end
