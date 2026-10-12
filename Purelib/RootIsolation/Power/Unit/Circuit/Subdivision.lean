module
import Purelib.Algebra.NatCast

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Circuit.Budget
import Purelib.RootIsolation.Power.Unit.Clearance
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib

open Purelib.Data.Rat

open Purelib.RootIsolation

open Purelib.Data

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The number of rational subedges used on each quarter of the unit circuit.
It is computed directly from the common move budget. -/
@[expose] def unitCircuitStepCount (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Nat :=
  Data.Rat.Rounding.Floor.ceilNat
      (4 / Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo) + 1
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The computed positive subdivision count times the common move budget exceeds four. -/
theorem four_lt_unitCircuitStepCount_mul_budget (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (4 : Fraction.Rational) <
      (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) *
        Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo := by
  let budget := Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo
  let ceiling := Data.Rat.Rounding.Floor.ceilNat (4 / budget)
  have budgetPositive : 0 < budget :=
    Power.Unit.Circuit.Budget.unitCircuitMoveBudget_pos degree degreeAtLeastTwo
  have ratioNonnegative : (0 : Fraction.Rational) ≤ 4 / budget :=
    (Fraction.Order.Field.div_pos_direct (by decide)
      budgetPositive).le
  have ratioLeCeiling :
      4 / budget ≤ (ceiling : Fraction.Rational) :=
    Data.Rat.Rounding.Floor.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtStepsNat :
      ceiling < unitCircuitStepCount degree degreeAtLeastTwo := by
    dsimp only [ceiling, budget]
    unfold unitCircuitStepCount
    exact Nat.lt_succ_self _
  have ceilingLtSteps :
      (ceiling : Fraction.Rational) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct ceilingLtStepsNat
  have ratioLtSteps :
      4 / budget <
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) :=
    ratioLeCeiling.trans_lt ceilingLtSteps
  exact (Fraction.Order.Field.div_lt_iff_pos budgetPositive).1
    ratioLtSteps
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The rational subdivision parameter `index/N` on one stereographic
quarter. -/
@[expose] def unitCircuitParameter (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : Fraction.Rational :=
  (index : Fraction.Rational) /
    (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The first rational subdivision parameter is exactly zero. -/
theorem unitCircuitParameter_zero (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitParameter degree degreeAtLeastTwo 0 = 0 := by
  unfold unitCircuitParameter
  exact Fraction.Field.zero_div_direct _
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The computed quarter subdivision uses at least one step. -/
theorem unitCircuitStepCount_one_le (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    1 ≤ unitCircuitStepCount degree degreeAtLeastTwo := by
  unfold unitCircuitStepCount
  exact Nat.succ_le_succ (Nat.zero_le _)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The computed quarter subdivision count is positive. -/
theorem unitCircuitStepCount_pos (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitCircuitStepCount degree degreeAtLeastTwo := by
  unfold unitCircuitStepCount
  exact Nat.zero_lt_succ _
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Four divided by the computed subdivision count is strictly below the common move budget. -/
theorem four_div_unitCircuitStepCount_lt_budget (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (4 : Fraction.Rational) /
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) <
      Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo := by
  have stepsPositive :
      (0 : Fraction.Rational) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  apply (Fraction.Order.Field.div_lt_iff_pos stepsPositive).2
  calc
    (4 : Fraction.Rational) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) *
          Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo :=
      four_lt_unitCircuitStepCount_mul_budget degree degreeAtLeastTwo
    _ = Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo *
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) := by ring1
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- The subdivision parameter at the retained step count is exactly one. -/
theorem unitCircuitParameter_last (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitParameter degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo) = 1 := by
  unfold unitCircuitParameter
  change
    (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) *
        (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational)⁻¹ = 1
  exact Fraction.Field.mul_inv_cancel _
    (Fraction.Cast.Order.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)).ne'
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Every parameter with index at most the retained step count is at most one. -/
theorem unitCircuitParameter_le_one (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index ≤ unitCircuitStepCount degree degreeAtLeastTwo) :
    unitCircuitParameter degree degreeAtLeastTwo index ≤ 1 := by
  let steps := unitCircuitStepCount degree degreeAtLeastTwo
  have stepsPositive : (0 : Fraction.Rational) < (steps : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  unfold unitCircuitParameter
  apply (Fraction.Order.Field.div_le_iff_pos stepsPositive).2
  have castBound : (index : Fraction.Rational) ≤ (steps : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct indexBound
  simpa only [-eq_self, -iff_self, Fraction.Field.one_mul] using castBound
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Every natural-indexed rational subdivision parameter is nonnegative. -/
theorem unitCircuitParameter_nonnegative (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    0 ≤ unitCircuitParameter degree degreeAtLeastTwo index := by
  unfold unitCircuitParameter
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct
      (m := 0) (n := index) (Nat.zero_le index))
    (Fraction.Cast.Order.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)).le
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Four times the squared difference of consecutive rational parameters is below the common move budget. -/
private theorem unitCircuitParameter_step_bound
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    4 * (unitCircuitParameter degree degreeAtLeastTwo index -
        unitCircuitParameter degree degreeAtLeastTwo (index + 1)) ^ 2 <
      Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo := by
  let steps : Fraction.Rational :=
    (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational)
  have stepsPositive : 0 < steps := by
    exact Fraction.Cast.Order.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  have oneLeStepsCast : (1 : Fraction.Rational) ≤
      (unitCircuitStepCount degree degreeAtLeastTwo : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := unitCircuitStepCount degree degreeAtLeastTwo)
      (unitCircuitStepCount_one_le degree degreeAtLeastTwo)
  have oneLeSteps : (1 : Fraction.Rational) ≤ steps := by
    exact oneLeStepsCast
  have inversePositive : 0 < steps⁻¹ :=
    Fraction.Order.Field.inv_pos_direct stepsPositive
  have inverseLeOne : steps⁻¹ ≤ (1 : Fraction.Rational)⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide) oneLeSteps
  have inverseOne : (1 : Fraction.Rational)⁻¹ = 1 := by decide
  rw [inverseOne] at inverseLeOne
  have inverseSquareLeInverse : steps⁻¹ ^ 2 ≤ steps⁻¹ := by
    rw [pow_two]
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
      inverseLeOne (le_refl steps⁻¹) inversePositive.le (by decide)
    simpa only [-eq_self, -iff_self, Fraction.Field.one_mul] using multiplied
  have scaled : 4 * steps⁻¹ ^ 2 ≤ 4 * steps⁻¹ :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      inverseSquareLeInverse (by decide)
  have parameterDifference :
      unitCircuitParameter degree degreeAtLeastTwo index -
          unitCircuitParameter degree degreeAtLeastTwo (index + 1) =
        -steps⁻¹ := by
    dsimp only [unitCircuitParameter, steps]
    rw [Algebra.NatCast.add, Nat.cast_one]
    change (index : Fraction.Rational) * steps⁻¹ -
        ((index : Fraction.Rational) + 1) * steps⁻¹ = -steps⁻¹
    ring1
  rw [parameterDifference]
  have negativeSquare : (-steps⁻¹) ^ 2 = steps⁻¹ ^ 2 := by ring1
  rw [negativeSquare]
  exact scaled.trans_lt (by
    change (4 : Fraction.Rational) / steps <
      Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo
    exact four_div_unitCircuitStepCount_lt_budget degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Consecutive stereographic quarter points have squared distance below the common move budget. -/
theorem unitQuarterSubdivision_budget
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
          (unitCircuitParameter degree degreeAtLeastTwo index) -
          Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo :=
  (Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_distance_le _ _).trans_lt
    (unitCircuitParameter_step_bound degree degreeAtLeastTwo index)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Consecutive stereographic quarter points satisfy the strict one-over-128 lift margin. -/
theorem unitQuarterSubdivision_liftMargin
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
          (unitCircuitParameter degree degreeAtLeastTwo index) -
          Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      (1 / 128 : Fraction.Rational) :=
  (unitQuarterSubdivision_budget degree degreeAtLeastTwo index).trans_le
    (Power.Unit.Circuit.Budget.unitCircuitMoveBudget_le_liftMargin degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

open Purelib.Data.Gaussian

/-- Consecutive stereographic quarter points have squared distance below the uniform robust clearance. -/
theorem unitQuarterSubdivision_small
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
          (unitCircuitParameter degree degreeAtLeastTwo index) -
          Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      Power.Unit.Clearance.uniformRobustClearance degree degreeAtLeastTwo :=
  (unitQuarterSubdivision_budget degree degreeAtLeastTwo index).trans_le
    (Power.Unit.Circuit.Budget.unitCircuitMoveBudget_le_clearance degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

end
