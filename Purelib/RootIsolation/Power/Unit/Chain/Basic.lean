module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Clearance
public import Purelib.RootIsolation.Power.Unit.Move.Budget
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- A finite chain of uniformly small unit-parameter moves.  Its dependent
endpoints guarantee that the chamber paths assembled from it really join. -/
inductive UnitChain (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : UnitVertex →
      UnitVertex → Type 1
  /-- The empty chain retaining the same exact start and finish vertex. -/ | nil (vertex :
    UnitVertex) : UnitChain degree
    degreeAtLeastTwo vertex vertex
  /-- One certified small unit move followed by the retained chain from its exact target. -/ | cons {source middle
    target : UnitVertex}
      (small : Power.Unit.Move.Budget.UnitMoveSmall source.unit middle.unit degree degreeAtLeastTwo)
      (remaining : UnitChain degree degreeAtLeastTwo middle target) :
      UnitChain degree degreeAtLeastTwo source target

constructive_injectivity UnitChain

end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Concatenate the two original finite unit-move chains at their shared dependent endpoint. -/
@[expose] def append {degree :
  RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : UnitVertex}
    (first : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start middle)
    (second : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo middle finish) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish :=
  match first with
  | .nil _ => second
  | .cons small remaining => .cons small (remaining.append second)
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Transport a retained chain along equality of its finish vertex. -/
@[expose] def castFinish {degree :
  RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start left right : UnitVertex} (same : left = right)
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start left) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start right := by
  subst right
  exact chain
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Transport a retained chain along equality of its start vertex. -/
@[expose] def castStart {degree :
  RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right finish : UnitVertex} (same : left = right)
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo right finish) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo left finish := by
  subst right
  exact chain
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Join two differently packaged unit vertices whose displayed Gaussian
values are equal.  The inserted move has exact squared distance zero. -/
@[expose] def equalValue {degree :
  RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right : UnitVertex} (same : left.value = right.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo left right :=
  open Purelib.Data.Rat in .cons
    { distance := by
        rw [same, Gaussian.Basic.sub_self,
          Gaussian.Norm.Basic.normSq_zero]
        exact Power.Unit.Clearance.uniformRobustClearance_pos degree degreeAtLeastTwo
      liftMargin := by
        rw [same, Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
        exact Fraction.Order.Field.div_nonneg_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 1) (by decide)).le
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 128) (by decide)).le }
    (.nil right)
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
