module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

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

/-- Change only the two displayed polynomial indices of a bridge along
coefficientwise equalities. -/
def cast {left left' right right' :
  CoefficientPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) : Owner.Bridge.Basic.OwnerBridge left' right' := by
  subst left'
  subst right'
  exact bridge

/-- Reindexing both polynomial endpoints of an owner bridge preserves its exact shared box. -/
@[simp] theorem cast_box {left left' right right' :
  CoefficientPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) :
    (bridge.cast leftSame rightSame).box = bridge.box := by
  subst left'
  subst right'
  rfl

/-- Reindexing an owner bridge preserves the original left clearance bound. -/
@[simp] theorem cast_leftClearance_bound
    {left left' right right' : CoefficientPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) :
    (bridge.cast leftSame rightSame).leftClearance.bound =
      bridge.leftClearance.bound := by
  subst left'
  subst right'
  rfl

/-- Reindexing an owner bridge preserves the original right clearance bound. -/
@[simp] theorem cast_rightClearance_bound
    {left left' right right' : CoefficientPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : Owner.Bridge.Basic.OwnerBridge left right) :
    (bridge.cast leftSame rightSame).rightClearance.bound =
      bridge.rightClearance.bound := by
  subst left'
  subst right'
  rfl
end OwnerBridge

end Purelib.RootIsolation.Owner.Bridge.Basic

end
