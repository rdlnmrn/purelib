module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Stability targets for retained coefficient tables and clearances

The retained boundary bound and evaluation scale determine the rational
target. Direct scalar positivity and division certify the budget bound for
the same table, box and clearance owner.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- The retained clearance and evaluation scale determine a rational stability target.

The retained clearance owner supplies its positive bound. Dividing it by
the sum of that bound and the same coefficient table's box evaluation scale
gives the displayed rational target. -/
@[expose] public def stabilityTarget (table : CoefficientTable) (box : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance table.polynomial box) :
    Fraction.Rational :=
  clearance.bound /
    (clearance.bound + table.refinementEvaluationScale box)

/-- A displayed clearance bound and evaluation scale determine a rational target.

The numerator is the displayed rational bound; the denominator adds that
same bound to the retained table's box evaluation scale. Positivity claims
use separate supplied evidence that the displayed bound is positive. -/
@[expose] public def stabilityTargetForBound (table : CoefficientTable) (box : Box)
    (bound : Fraction.Rational) : Fraction.Rational :=
  bound / (bound + table.refinementEvaluationScale box)

/-- The stability target makes the refinement budget smaller than a positive bound.

Its rational denominator combines that bound with the positive box evaluation scale. -/
public theorem refinementEvaluationBound_stabilityTargetForBound_lt
    (table : CoefficientTable) (box : Box) {bound : Fraction.Rational}
    (positive : 0 < bound) :
    table.refinementEvaluationBound
        (table.stabilityTargetForBound box bound) box < bound := by
  rw [table.refinementEvaluationBound_eq_target_mul_scale]
  let scale := table.refinementEvaluationScale box
  have scalePositive : 0 < scale := table.refinementEvaluationScale_pos box
  have denominatorPositive : 0 < bound + scale :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive scalePositive.le
  change bound / (bound + scale) * scale < bound
  calc
    bound / (bound + scale) * scale =
        (bound * scale) / (bound + scale) := by
      change (bound * (bound + scale)⁻¹) * scale =
        (bound * scale) * (bound + scale)⁻¹
      ring1
    _ < bound := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        denominatorPositive).2
      exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        positive (by
          calc
            scale = 0 + scale := by ring1
            _ < bound + scale :=
              Fraction.Order.Arithmetic.add_lt_add_right_direct
                positive scale)

/-- The stability target makes the refinement budget smaller than retained boundary clearance.

The estimate uses the same coefficient table, box and positive clearance owner. -/
public theorem refinementEvaluationBound_stabilityTarget_lt
    (table : CoefficientTable) (box : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance table.polynomial box) :
    table.refinementEvaluationBound
        (table.stabilityTarget box clearance) box < clearance.bound := by
  rw [table.refinementEvaluationBound_eq_target_mul_scale]
  let scale := table.refinementEvaluationScale box
  have scalePositive : 0 < scale := table.refinementEvaluationScale_pos box
  have denominatorPositive : 0 < clearance.bound + scale :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct clearance.positive scalePositive.le
  change clearance.bound / (clearance.bound + scale) * scale <
    clearance.bound
  calc
    clearance.bound / (clearance.bound + scale) * scale =
        (clearance.bound * scale) / (clearance.bound + scale) := by
      change (clearance.bound * (clearance.bound + scale)⁻¹) * scale =
        (clearance.bound * scale) * (clearance.bound + scale)⁻¹
      ring1
    _ < clearance.bound := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        denominatorPositive).2
      exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        clearance.positive (by
          calc
            scale = 0 + scale := by ring1
            _ < clearance.bound + scale :=
              Fraction.Order.Arithmetic.add_lt_add_right_direct
                clearance.positive scale)

/-- A positive proposed clearance bound gives a positive stability target.

A positive displayed bound and the positive evaluation scale give a
positive denominator. Direct rational division retains the positivity of
the same numerator and denominator. -/
public theorem stabilityTargetForBound_pos (table : CoefficientTable) (box : Box)
    {bound : Fraction.Rational} (positive : 0 < bound) :
    0 < table.stabilityTargetForBound box bound :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (table.refinementEvaluationScale_pos box).le)

/-- The target computed from retained boundary clearance is positive.

The boundary clearance retains a positive bound for the same table and
box. Adding its positive evaluation scale gives the positive denominator
of the displayed target. -/
public theorem stabilityTarget_pos (table : CoefficientTable) (box : Box)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance table.polynomial box) :
    0 < table.stabilityTarget box clearance :=
  Fraction.Order.Field.div_pos_direct clearance.positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct clearance.positive
      (table.refinementEvaluationScale_pos box).le)

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
