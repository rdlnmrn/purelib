module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Rows
public import Purelib.Geometry.Rational.Box.Enlargement
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Bounds
import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Bounds.Refinement
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Fin.Two

/-! # One computed box ceiling for all four original arithmetic rows

The original value/first ceiling formulas are evaluated on one physical box
and one positive root floor. Their numerical coefficient tables are independent
of parameter indices. The maximum covers both differential coordinates and
orders while the actual indexed differential and observation owners remain.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rational.Box.Square.Centered
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (centeredBox_refines)

/-- Compute one rational ceiling for both orders and coordinates on a fixed box and positive root floor.

The original four numerical ceilings are evaluated at zero parameter
indices, using their existing exact parameter-independence laws. The
retained reciprocal box is the original normBox of the floor reciprocal;
no observation, preparation, sheet or programme is constructed.
-/
def boxCeiling (box : Box) (floor : Rational) (positive : 0 < floor) : Rational :=
  let reciprocalBox := normBox floor⁻¹ (Order.Field.inv_pos_direct positive).le
  max (max (Arithmetic.valueCeiling 0 0 0 box floor floor (4 * floor))
      (Arithmetic.valueCeiling 0 0 1 box floor floor (4 * floor)))
    (max (Arithmetic.firstCeiling 0 0 0 box reciprocalBox floor floor (4 * floor))
      (Arithmetic.firstCeiling 0 0 1 box reciprocalBox floor floor (4 * floor)))

/-- The computed four-row box ceiling is nonnegative from its original positive floors. -/
theorem boxCeiling_nonnegative (box : Box) {floor : Rational} (positive : 0 < floor) :
    0 ≤ boxCeiling box floor positive :=
  (Arithmetic.valueCeiling_nonnegative 0 0 0 box positive positive
    (Order.Arithmetic.mul_pos_direct (by decide +kernel : (0 : Rational) < 4) positive)).trans
    ((Order.Basic.le_max_left _ _).trans (Order.Basic.le_max_left _ _))

/-- The fixed quarter-of-quarter radicand floor of an original continued neighborhood is positive. -/
private theorem shiftedFloor_positive {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) :
    0 < (patch.base.site.denominatorValue / 4) / 4 :=
  Order.Field.div_pos_direct
    (Order.Field.div_pos_direct patch.base.site.denominatorValue_positive
      (by decide +kernel : (0 : Rational) < 4))
    (by decide +kernel : (0 : Rational) < 4)

/-- Compute the shifted-window four-row ceiling from the actual retained original neighborhood.

Its fixed box is enlarged once and its original shifted-clearance floor
computes the reciprocal margin. This operation reads the supplied cache;
it does not execute the PreparedPatch.neighborhood or grow producer.
-/
def shiftedEnvelopeCeiling {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) : Rational :=
  boxCeiling (patch.box.enlarge 1 (by decide +kernel))
    ((1 / 4) / (2 + 3 / ((patch.base.site.denominatorValue / 4) / 4)))
    (ContinuedNeighborhood.rootFloor_positive (shiftedFloor_positive patch))

/-- The retained-neighborhood ceiling is exactly the original fixed-box computation at the derived positive margin. -/
theorem shiftedEnvelopeCeiling_eq {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (positive : 0 < (patch.base.site.denominatorValue / 4) / 4) :
    shiftedEnvelopeCeiling patch = boxCeiling (patch.box.enlarge 1 (by decide +kernel))
      ((1 / 4) / (2 + 3 / ((patch.base.site.denominatorValue / 4) / 4)))
      (ContinuedNeighborhood.rootFloor_positive positive) := by rfl

/-- The actual original-neighborhood envelope gives a nonnegative coefficient scale before fine mesh selection. -/
theorem shiftedEnvelopeCeiling_nonnegative {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) : 0 ≤ shiftedEnvelopeCeiling patch :=
  boxCeiling_nonnegative _ (ContinuedNeighborhood.rootFloor_positive (shiftedFloor_positive patch))

/-- A lower bound on the actual recorded floor encloses its original reciprocal box in the fixed reciprocal box. -/
theorem inverseBox_refines {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ patch.rootLower) :
    (inverseBox patch).Refines (normBox floor⁻¹ (Order.Field.inv_pos_direct positive).le) := by
  unfold inverseBox normBox
  exact centeredBox_refines 0
    (normRadius_nonnegative (Order.Field.inv_pos_direct patch.rootLower_positive).le)
    (normRadius_nonnegative (Order.Field.inv_pos_direct positive).le)
    (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
      (Order.Field.inv_le_inv_of_pos_direct positive lower))

/-- The actual value-row ceiling is bounded by the computed fixed-box ceiling with no parameter-index restriction.

The original actual patch and floor remain the left input of every scalar
comparison. The existing parameter readback changes only numerical indices
after box/floor monotonicity; no actual differential owner is transported.
-/
theorem valueCeiling_le_box {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) (increment : Canonical)
    (coordinate : Fin 2) {box : Box} (refines : patch.box.Refines box) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ patch.rootLower) :
    valueCeiling patch increment coordinate ≤ boxCeiling box floor positive := by
  have sumPositive := Order.Arithmetic.mul_pos_direct (by decide +kernel : (0 : Rational) < 4) positive
  have sumBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
    (by decide +kernel : (0 : Rational) ≤ 4)
  have actualBound := Arithmetic.valueCeiling_mono parameter increment coordinate refines
    positive lower positive lower sumPositive sumBound
  have normalized := Arithmetic.valueCeiling_parameters parameter increment 0 0 coordinate box floor floor (4 * floor)
  have insideMaximum : Arithmetic.valueCeiling 0 0 coordinate box floor floor (4 * floor) ≤
      boxCeiling box floor positive := by
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact (Order.Basic.le_max_left _ _).trans (Order.Basic.le_max_left _ _)
    · subst coordinate
      exact (Order.Basic.le_max_right _ _).trans (Order.Basic.le_max_left _ _)
  exact (actualBound.trans_eq normalized).trans insideMaximum

/-- The actual first-row ceiling is bounded by the same computed fixed-box four-row maximum.

The original actual reciprocal box is refined using the same positive floor
bound. Its cached cubic ceiling and all three independent arithmetic
allowances keep their existing formulas and actual observation indices.
-/
theorem firstCeiling_le_box {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) (increment : Canonical)
    (coordinate : Fin 2) {box : Box} (refines : patch.box.Refines box) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ patch.rootLower) :
    firstCeiling patch increment coordinate ≤ boxCeiling box floor positive := by
  have sumPositive := Order.Arithmetic.mul_pos_direct (by decide +kernel : (0 : Rational) < 4) positive
  have sumBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
    (by decide +kernel : (0 : Rational) ≤ 4)
  have actualBound := Arithmetic.firstCeiling_mono parameter increment coordinate refines
    (inverseBox_refines patch positive lower) positive lower positive lower sumPositive sumBound
  have normalized := Arithmetic.firstCeiling_parameters parameter increment 0 0 coordinate box
    (normBox floor⁻¹ (Order.Field.inv_pos_direct positive).le) floor floor (4 * floor)
  have insideMaximum : Arithmetic.firstCeiling 0 0 coordinate box
      (normBox floor⁻¹ (Order.Field.inv_pos_direct positive).le) floor floor (4 * floor) ≤
      boxCeiling box floor positive := by
    rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
    · subst coordinate
      exact (Order.Basic.le_max_left _ _).trans (Order.Basic.le_max_right _ _)
    · subst coordinate
      exact (Order.Basic.le_max_right _ _).trans (Order.Basic.le_max_right _ _)
  exact (actualBound.trans_eq normalized).trans insideMaximum

/-- Both orders and coordinates of the actual cached patch obey one computed fixed-box ceiling. -/
theorem rowCeiling_le_box {parameter : Canonical} {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) (increment : Canonical)
    (order coordinate : Fin 2) {box : Box} (refines : patch.box.Refines box) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ patch.rootLower) :
    rowCeiling patch increment order coordinate ≤ boxCeiling box floor positive := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    exact valueCeiling_le_box patch increment coordinate refines positive lower
  · subst order
    exact firstCeiling_le_box patch increment coordinate refines positive lower

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

end
