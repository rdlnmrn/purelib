module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Owner.Family.FTA
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Progressive.Chamber.Frame
public import Purelib.RootIsolation.Progressive.Power.Frame.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Family.Transport
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

/-!
# Degree-indexed track readback from retained power-polynomial isolation

The original isolation result and chamber family share their numerical tracks.
Polynomial/count transports preserve the exact initial boxes and clearance bounds.
-/

namespace Purelib.RootIsolation.Power.Isolation.Track

/-- The globally supported Paper-I track underlying one degree-indexed owner
of the independently isolated chamber frame.

The supplied original finite degree index is transported by the retained
polynomial-degree equality. It reads the same numerical isolation track
without selecting a new owner or recomputing an independent track. -/
@[expose] public def isolatedTrack
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Track.Basic.WindingOneTrack (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree))
        :=
  (Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo).trackAt
    (Fin.cast (Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree parameter degree).symm index)

/-- The independently isolated track starts in exactly the corresponding chamber owner's box.

The chamber owner family transports the same isolation result through
its polynomial and count equations. Inverse count transport preserves the
original index and reads the same retained initial box. -/
@[simp] public theorem isolatedTrack_initial_box_eq_chamber_owner
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo
      (Fin.cast
        (Progressive.Power.Frame.Basic.chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
        index)).initial.box =
      ((Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
        index).box := by
  let result := Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo
  let countSame : (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).natDegree =
      (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree :=
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree parameter degree).trans
      (Power.Gaussian.Progressive.Coefficients.coefficientTable_degree parameter degree).symm
  have retained := Owner.Family.Transport.castOwnerFamilyFull_owner_box_target
    (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree).symm
    countSame (Owner.Family.Basic.OwnerFamily.ofResult result) index
  exact retained.symm

/-- The isolated track's initial boundary bound is exactly the corresponding chamber owner's bound.

The chamber owner retains the original isolation track clearance.
Its inverse index transport reads that same certificate and quantitative
bound; no replacement clearance or new witness is selected. -/
@[simp] public theorem isolatedTrack_initial_clearance_bound_eq_chamber_owner
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo
      (Fin.cast
        (Progressive.Power.Frame.Basic.chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
        index)).initial.clearance.bound =
      ((Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
        index).clearance.bound := by
  let result := Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo
  let countSame : (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).natDegree =
      (Power.Gaussian.Progressive.Coefficients.coefficientTable parameter degree).degree :=
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree parameter degree).trans
      (Power.Gaussian.Progressive.Coefficients.coefficientTable_degree parameter degree).symm
  have retained := Owner.Family.Transport.castOwnerFamilyFull_owner_clearance_bound_target
    (Power.Gaussian.Progressive.Coefficients.coefficientTable_polynomial parameter degree).symm
    countSame (Owner.Family.Basic.OwnerFamily.ofResult result) index
  exact retained.symm

end Purelib.RootIsolation.Power.Isolation.Track
