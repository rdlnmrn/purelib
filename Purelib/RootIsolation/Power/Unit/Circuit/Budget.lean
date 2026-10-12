module

import Purelib.Data.Gaussian.Basic
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

open Purelib

open Purelib.Data.Rat

open Purelib.RootIsolation

section
public section

/-!
# Move budget for the power-family circuit

The retained minimum reserves both the original robust boundary clearance
and the fixed lift margin. Its positivity and projections preserve the
original positive degree and the same clearance certificate.
-/

namespace Purelib.RootIsolation.Power.Unit.Circuit.Budget

open Purelib.Data.Gaussian

/-- The common move budget also reserves a fixed margin for the later
power-lift homotopy. -/
@[expose] def unitCircuitMoveBudget (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  min (Power.Unit.Clearance.uniformRobustClearance degree degreeAtLeastTwo) (1 / 128)
end Purelib.RootIsolation.Power.Unit.Circuit.Budget

end

section
public section

/-!
# Move budget for the power-family circuit

The retained minimum reserves both the original robust boundary clearance
and the fixed lift margin. Its positivity and projections preserve the
original positive degree and the same clearance certificate.
-/

namespace Purelib.RootIsolation.Power.Unit.Circuit.Budget

open Purelib.Data.Gaussian

/-- The common circuit-move budget is no larger than the uniform robust boundary clearance. -/
theorem unitCircuitMoveBudget_le_clearance (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo ≤
      Power.Unit.Clearance.uniformRobustClearance degree degreeAtLeastTwo :=
  Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
end Purelib.RootIsolation.Power.Unit.Circuit.Budget

end

section
public section

/-!
# Move budget for the power-family circuit

The retained minimum reserves both the original robust boundary clearance
and the fixed lift margin. Its positivity and projections preserve the
original positive degree and the same clearance certificate.
-/

namespace Purelib.RootIsolation.Power.Unit.Circuit.Budget

open Purelib.Data.Gaussian

/-- The common circuit-move budget is at most the retained power-lift margin of one over 128. -/
theorem unitCircuitMoveBudget_le_liftMargin (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo ≤ (1 / 128 : Fraction.Rational) :=
  Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _
end Purelib.RootIsolation.Power.Unit.Circuit.Budget

end

section
public section

/-!
# Move budget for the power-family circuit

The retained minimum reserves both the original robust boundary clearance
and the fixed lift margin. Its positivity and projections preserve the
original positive degree and the same clearance certificate.
-/

namespace Purelib.RootIsolation.Power.Unit.Circuit.Budget

open Purelib.Data.Gaussian

/-- The common clearance-and-lift budget is positive. -/
theorem unitCircuitMoveBudget_pos (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < Power.Unit.Circuit.Budget.unitCircuitMoveBudget degree degreeAtLeastTwo := by
  exact Purelib.Data.Rat.Fraction.Order.Basic.lt_min (Power.Unit.Clearance.uniformRobustClearance_pos degree
    degreeAtLeastTwo)
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))
end Purelib.RootIsolation.Power.Unit.Circuit.Budget

end
