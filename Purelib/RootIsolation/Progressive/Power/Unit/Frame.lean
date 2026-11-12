module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Family.Transport
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Clearance
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Target
public import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Progressive.Power.Unit.Owner
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Power.Unit.Box.Separation
import Purelib.RootIsolation.Power.Unit.Box.Winding
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Power.Gaussian.Progressive

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame

open Purelib.Data.Gaussian

/-- The exact coefficient table equipped with the common-scale robust owner
family.  Maximality is unchanged because it is a statement about every
separated globally supported family for the same displayed polynomial. -/
@[expose] def robustChamberFrame
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    ChamberFrame where
  reference := Coefficients.coefficientTable parameter degree
  chamber := by
    let rawOwners := Owner.unitRobustOwnerFamily parameterNonzero parameterUnit degree
      degreeAtLeastTwo
    have countSame : degree.value =
        (Coefficients.coefficientTable parameter degree).degree := by
      rw [Coefficients.coefficientTable_degree]
    let owners : Owner.Family.Basic.OwnerFamily
        (Coefficients.coefficientTable parameter degree).polynomial
        (Coefficients.coefficientTable parameter degree).degree :=
      Owner.Family.Transport.castOwnerFamilyFull
        (Coefficients.coefficientTable_polynomial parameter degree).symm countSame rawOwners
    let original := (Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).chamber
    exact
      { degreeAtLeastTwo := original.degreeAtLeastTwo
        squarefree := Power.Gaussian.Progressive.Coefficients.coefficientTableSquarefree parameterNonzero degree
        owners := owners
        referenceSmall := Coefficients.coefficientTable_allowances_lt parameter degree
          (Chamber.Target.simpleRootChamberTarget_pos
            (Coefficients.coefficientTable parameter degree) original.squarefree owners)
        referenceMaximality := original.referenceMaximality }

/-- The robust frame retains the exact original squarefree certificate without constructing unused generic owners. -/
theorem robustChamberFrame_squarefree {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1) (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame parameterNonzero parameterUnit degree degreeAtLeastTwo).chamber.squarefree =
      (Progressive.Power.Frame.Basic.chamberFrame parameterNonzero degree degreeAtLeastTwo).chamber.squarefree :=
  (Progressive.Power.Frame.Basic.chamberFrame_squarefree parameterNonzero degree degreeAtLeastTwo).symm
end Purelib.RootIsolation.Progressive.Power.Unit.Frame

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame

open Purelib.Data.Gaussian

/-- The robust chamber frame retains the supplied power degree exactly. -/
@[simp] theorem robustChamberFrame_degree
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).degree = degree.value :=
  Coefficients.coefficientTable_degree parameter degree
end Purelib.RootIsolation.Progressive.Power.Unit.Frame

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame

open Purelib.Data.Gaussian

/-- The indexed robust chamber owner retains exactly the corresponding computed robust Newton box. -/
@[simp] theorem robustChamberFrame_owner_box
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).Index) :
    ((robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).owner index).box =
      Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        (Fin.cast
          (robustChamberFrame_degree parameterNonzero parameterUnit degree
            degreeAtLeastTwo)
          index) := by
  simp [-eq_self, -iff_self, robustChamberFrame,
    ChamberFrame.owner,
    Owner.unitRobustOwnerFamily, Owner.unitRobustOwner]
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Frame

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame

open Purelib.Data.Gaussian

/-- The robust chamber owner's boundary bound is exactly the original computed robust certificate bound. -/
@[simp] theorem robustChamberFrame_owner_clearance_bound
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).Index) :
    ((robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).owner index).clearance.bound =
      (Power.Unit.Clearance.unitRobustBoundaryClearance parameterNonzero parameterUnit degree
        degreeAtLeastTwo
        (Fin.cast
          (robustChamberFrame_degree parameterNonzero parameterUnit degree
            degreeAtLeastTwo)
          index)).bound := by
  simp [-eq_self, -iff_self, robustChamberFrame,
    ChamberFrame.owner,
    Owner.unitRobustOwnerFamily, Owner.unitRobustOwner]
  rfl
end Purelib.RootIsolation.Progressive.Power.Unit.Frame

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Frame

open Purelib.Data.Gaussian

/-- The robust chamber frame represents exactly the original power polynomial at the supplied unit parameter. -/
@[simp] theorem robustChamberFrame_polynomial
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).polynomial = Power.Gaussian.rootPolynomial parameter degree :=
  Coefficients.coefficientTable_polynomial parameter degree
end Purelib.RootIsolation.Progressive.Power.Unit.Frame

end
