module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Power.Unit.Box
public import Purelib.RootIsolation.Power.Unit.Box.Separation
public import Purelib.RootIsolation.Power.Unit.Box.Winding
public import Purelib.RootIsolation.Power.Unit.Clearance
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Owner

open Purelib.Data.Gaussian

/-- One explicit local owner at the common robust unit-circuit scale. -/
def unitRobustOwner
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Owner.Local.Basic.LocalOwner (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) :=
  { box := Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index
    proper := Power.Unit.Box.unitRobustBox_proper parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
    clearance := Power.Unit.Clearance.unitRobustBoundaryClearance parameterNonzero parameterUnit
      degree degreeAtLeastTwo index
    rawWindingFour := Power.Unit.Box.Winding.unitRobustBox_rawWindingFour parameterNonzero
      parameterUnit degree degreeAtLeastTwo index }
end Purelib.RootIsolation.Progressive.Power.Unit.Owner

end

section
@[expose] public section

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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Owner

open Purelib.Data.Gaussian

/-- The degree-many robust local owners at one exact unit parameter. -/
def unitRobustOwnerFamily
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Owner.Family.Basic.OwnerFamily
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) degree.value where
  owner := unitRobustOwner parameterNonzero parameterUnit degree degreeAtLeastTwo
  pairwiseSeparated := Power.Unit.Box.Separation.unitRobustBox_pairwiseSeparated parameterNonzero
    parameterUnit degree degreeAtLeastTwo
end Purelib.RootIsolation.Progressive.Power.Unit.Owner

end
