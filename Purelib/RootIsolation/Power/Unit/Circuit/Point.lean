module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
import Purelib.RootIsolation.Power.Unit.Clearance
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Gaussian.UnitCircle

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- The `index`th rational parameter vertex on a selected quarter. -/
def unitCircuitPoint (quarter :
  UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : Gaussian :=
  Quarter.unitCircuitMultiplier quarter *
    Stereographic.unitQuarterPoint (Subdivision.unitCircuitParameter
      degree degreeAtLeastTwo index)
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- Consecutive quarter-circuit point differences equal the fixed quarter multiplier times the original stereographic
difference. -/
private theorem unitCircuitPoint_difference
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) =
      Quarter.unitCircuitMultiplier quarter *
        (Stereographic.unitQuarterPoint
            (Subdivision.unitCircuitParameter degree degreeAtLeastTwo index) -
          Stereographic.unitQuarterPoint
            (Subdivision.unitCircuitParameter degree degreeAtLeastTwo (index + 1))) := by
  apply Basic.ext <;>
    simp only [unitCircuitPoint, Basic.mul_re, Basic.mul_im,
      Basic.sub_re, Basic.sub_im] <;> ring1
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- Every retained rational quarter-circuit point has quadrance one. -/
theorem unitCircuitPoint_unit (quarter :
  UnitCircuitQuarter)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index) = 1 := by
  rw [unitCircuitPoint, Norm.Basic.normSq_mul,
    Quarter.unitCircuitMultiplier_unit,
    Stereographic.unitQuarterPoint_unit, Fraction.Field.one_mul]
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- The quarter-specific rotation carries each retained point to the same diagonally rotated stereographic point. -/
theorem unitCircuitRotation_mul_point
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    Quarter.unitCircuitRotation quarter *
        unitCircuitPoint quarter degree degreeAtLeastTwo index =
      ⟨1, -1⟩ *
        Stereographic.unitQuarterPoint
          (Subdivision.unitCircuitParameter degree degreeAtLeastTwo index) := by
  unfold unitCircuitPoint
  rw [← Basic.mul_assoc,
    Quarter.unitCircuitRotation_mul_multiplier]
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- Every retained rotated quarter vertex has real coordinate at least one. -/
theorem unitCircuitRotatedPoint_real_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index ≤ Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) :
    1 ≤ (Quarter.unitCircuitRotation quarter *
      unitCircuitPoint quarter degree degreeAtLeastTwo index).re := by
  rw [unitCircuitRotation_mul_point]
  rw [Gaussian.Coordinates.Rotation.diagonalRotation_real]
  exact Stereographic.unitQuarterPoint_re_add_im_ge_one
    (Subdivision.unitCircuitParameter_nonnegative degree degreeAtLeastTwo index)
    (Subdivision.unitCircuitParameter_le_one degree degreeAtLeastTwo indexBound)
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- Consecutive retained quarter-circuit points satisfy the strict one-over-128 lift margin. -/
theorem unitCircuitSubdivision_liftMargin
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)) <
      (1 / 128 : Fraction.Rational) := by
  rw [unitCircuitPoint_difference, Norm.Basic.normSq_mul,
    Quarter.unitCircuitMultiplier_unit, Fraction.Field.one_mul]
  exact Subdivision.unitQuarterSubdivision_liftMargin degree degreeAtLeastTwo index
end Purelib.RootIsolation.Power.Unit.Circuit.Point

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Point

open Purelib.Data.Gaussian

/-- Consecutive retained quarter-circuit points have squared distance below the uniform robust clearance. -/
theorem unitCircuitSubdivision_small
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)) <
      Clearance.uniformRobustClearance degree degreeAtLeastTwo := by
  rw [unitCircuitPoint_difference, Norm.Basic.normSq_mul,
    Quarter.unitCircuitMultiplier_unit, Fraction.Field.one_mul]
  exact Subdivision.unitQuarterSubdivision_small degree degreeAtLeastTwo index
end Purelib.RootIsolation.Power.Unit.Circuit.Point

end
