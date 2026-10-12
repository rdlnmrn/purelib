module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
public import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Data

open Purelib

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Basic

open Purelib.Data.Gaussian
namespace UnitVertex

/-- Construct the robust chamber frame of the power polynomial at this retained unit vertex. -/
def frame (vertex :
  Geometry.Gaussian.UnitCircle.Basic.UnitVertex) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Progressive.Chamber.Frame.ChamberFrame :=
  Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
    vertex.unit degree
    degreeAtLeastTwo
end UnitVertex
end Purelib.Geometry.Gaussian.UnitCircle.Basic

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

namespace Purelib.Geometry.Gaussian.UnitCircle.Basic

open Purelib.Data.Gaussian
namespace UnitVertex

/-- Read the exact anchor of the indexed robust chamber owner at this unit vertex. -/
def ownerAnchor (vertex :
  Geometry.Gaussian.UnitCircle.Basic.UnitVertex) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (vertex.frame degree degreeAtLeastTwo).Index) : Gaussian.Basic.Canonical :=
  ((vertex.frame degree degreeAtLeastTwo).owner index).box.anchor
end UnitVertex
end Purelib.Geometry.Gaussian.UnitCircle.Basic

end
