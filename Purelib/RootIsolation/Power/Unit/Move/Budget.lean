module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Clearance
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Power.Unit.Move.Budget

open Purelib.Data.Gaussian

/-- A single parameter-distance comparison suffices for every robust owner. -/
structure UnitMoveSmall
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Prop where
  /-- The squared parameter displacement is strictly below the common robust boundary clearance. -/ distance : normSq
    (source - target) <
    Power.Unit.Clearance.uniformRobustClearance degree degreeAtLeastTwo
  /-- The same squared displacement is at most the fixed power-lift margin of one over 128. -/ liftMargin : normSq
    (source - target) ≤ (1 / 128 : Fraction.Rational)
end Purelib.RootIsolation.Power.Unit.Move.Budget

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

namespace Purelib.RootIsolation.Power.Unit.Move.Budget.UnitMoveSmall

open Purelib.Data.Gaussian

/-- A stationary unit-parameter move meets both the positive clearance budget and the fixed lift margin. -/
theorem reflexive
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Move.Budget.UnitMoveSmall parameterUnit parameterUnit degree degreeAtLeastTwo where
  distance := by
    rw [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact Power.Unit.Clearance.uniformRobustClearance_pos degree degreeAtLeastTwo
  liftMargin := by
    rw [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 1) (by decide)).le
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 128) (by decide)).le
end Purelib.RootIsolation.Power.Unit.Move.Budget.UnitMoveSmall

end
