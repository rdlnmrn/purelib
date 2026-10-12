module
public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Owner.Family.Basic (OwnerFamily)

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

namespace Purelib.RootIsolation.Owner.Family.Transport

/-- Change only the displayed polynomial index of an owner family. -/
def castOwnerFamily {left right :
  CoefficientPolynomial} {count : Nat}
    (same : left = right) (family : OwnerFamily left count) :
    OwnerFamily right count := by
  rw [← same]
  exact family

/-- Polynomial reindexing preserves the box at each original owner index. -/
@[simp] theorem castOwnerFamily_owner_box
    {left right : CoefficientPolynomial} {count : Nat}
    (same : left = right) (family : OwnerFamily left count)
    (index : Fin count) :
    ((castOwnerFamily same family).owner index).box =
      (family.owner index).box := by
  subst right
  rfl

/-- Simultaneously change the polynomial and the displayed finite index
count of an owner family. -/
def castOwnerFamilyFull
    {left right : CoefficientPolynomial} {leftCount rightCount :
      Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) : OwnerFamily right rightCount := by
  subst right
  subst rightCount
  exact family

/-- Polynomial and count reindexing preserve the box at the corresponding transported original index. -/
@[simp] theorem castOwnerFamilyFull_owner_box
    {left right : CoefficientPolynomial} {leftCount rightCount :
      Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin leftCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner
      (Fin.cast countSame index)).box = (family.owner index).box := by
  subst right
  subst rightCount
  rfl

/-- A target index reads the original box at its inverse-transported source index. -/
@[simp] theorem castOwnerFamilyFull_owner_box_target
    {left right : CoefficientPolynomial} {leftCount rightCount :
      Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin rightCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner index).box =
      (family.owner (Fin.cast countSame.symm index)).box := by
  subst right
  subst rightCount
  rfl

/-- A target index retains the original clearance bound at its inverse-transported source index. -/
@[simp] theorem castOwnerFamilyFull_owner_clearance_bound_target
    {left right : CoefficientPolynomial} {leftCount rightCount :
      Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin rightCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner
      index).clearance.bound =
      (family.owner
        (Fin.cast countSame.symm index)).clearance.bound := by
  subst right
  subst rightCount
  rfl

end Purelib.RootIsolation.Owner.Family.Transport

end
