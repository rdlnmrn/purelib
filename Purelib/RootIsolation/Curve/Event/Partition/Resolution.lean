module
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Guard
public import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
import Purelib.RootIsolation.Sturm.Count.Basic
public import Purelib.RootIsolation.Sturm.Event.Resolution
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.RootIsolation.Curve.Event.Partition

/-- Compute the event-resolution width for every retained active box-condition polynomial.

The list preserves the active condition order and computes each width on the same proper root cell. -/
@[expose] def conditionLeafWidths
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) : List
      Fraction.Rational :=
  (Curve.Box.activeConditionPolynomials curve box).map
    fun polynomial => Sturm.Event.eventLeafWidth polynomial root

/-- Take one positive width threshold fitting both the main event and all active box conditions.

The rational minimum retains the main event width and the positive minimum over the active condition widths. -/
@[expose] def commonLeafWidth
    (event : RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      (root : Cell) :
    Fraction.Rational :=
  min (Sturm.Event.eventLeafWidth event root)
    (Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum (conditionLeafWidths curve box root))

/-- The common finite event-resolution width is strictly positive.

Every active condition contributes a positive event width, so their retained minimum and the main event width are
positive. -/
theorem commonLeafWidth_pos
    (event : RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      (root : Cell) :
    0 < commonLeafWidth event curve box root := by
  apply Fraction.Order.Basic.lt_min (Sturm.Event.eventLeafWidth_pos event root)
  apply Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum_pos
  intro width member
  change width ∈ (Curve.Box.activeConditionPolynomials curve box).map
    (fun polynomial => Sturm.Event.eventLeafWidth polynomial root) at member
  rcases Data.List.Map.mem_map.mp member with ⟨polynomial, _polynomialMember, rfl⟩
  exact Sturm.Event.eventLeafWidth_pos polynomial root

/-- The common width fits the original main event's leaf-resolution threshold.

The main event width is the first entry of the retained rational minimum. -/
theorem commonLeafWidth_le_event
    (event : RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      (root : Cell) :
    commonLeafWidth event curve box root ≤ Sturm.Event.eventLeafWidth event root :=
  Fraction.Order.Basic.min_le_left _ _

/-- The common width fits every retained active condition's leaf-resolution threshold.

Membership in the active conditions bounds the retained positive minimum by the corresponding event width. -/
theorem commonLeafWidth_le_condition
    (event : RationalPolynomial) {curve : Curve.RationalCurve} {box : Box}
      (root : Cell)
    {condition : RationalPolynomial}
    (member : condition ∈
      Curve.Box.activeConditionPolynomials curve box) :
    commonLeafWidth event curve box root ≤ Sturm.Event.eventLeafWidth condition root := by
  exact (Fraction.Order.Basic.min_le_right _ _).trans (Data.Rat.List.Minimum.BoxEventPartition.positiveMinimum_le_of_mem
    (Data.List.Map.mem_map.mpr ⟨condition, member, rfl⟩))

/-- Compute a finite two-thirds contraction depth reaching half the common leaf-width threshold.

The original contraction search uses the root interval width and half of its common positive threshold. -/
@[expose] def commonDepth
    (event : RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      (root : Cell) :
    Nat :=
  Approximation.Rational.Contraction.geometricDepth (Bounds.width root.interval)
    (commonLeafWidth event curve box root / 2)

/-- Build the common safe-cut subdivision at the computed event-resolution depth.

The original nonzero event, curve, box and proper root cell determine every retained leaf. -/
@[expose] def commonSubdivision
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    Subdivision event curve box :=
  Subdivision.build event eventNonzero curve box
    (commonDepth event curve box root) root

/-- Every common-resolution leaf refines the original root cell. -/
theorem commonSubdivision_leaf_refines
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    leaf.interval.Refines root.interval :=
  Subdivision.build_leaf_refines event eventNonzero curve box
    (commonDepth event curve box root) root member

/-- Every retained common-resolution leaf is strictly narrower than the common threshold. -/
theorem commonSubdivision_leaf_width_lt
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (commonSubdivision event eventNonzero curve box root).leaves) :
    (Bounds.width leaf.interval) < commonLeafWidth event curve box root := open
      Purelib.Algebra.Field in by
  let leafWidth := commonLeafWidth event curve box root
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using commonLeafWidth_pos event curve box root
  have geometric :=
    Approximation.Rational.Contraction.geometricDepth_sufficient
      (width := (Bounds.width root.interval)) (epsilon := leafWidth / 2)
      (Bounds.width_nonneg root.interval)
      (Fraction.Order.Field.div_pos_direct leafWidthPositive
        (show (0 : Fraction.Rational) < 2 by decide))
  have geometric' :
      (2 / 3 : Fraction.Rational) ^ commonDepth event curve box root *
          (Bounds.width root.interval) ≤ leafWidth / 2 := by
    simpa only [commonDepth, leafWidth] using geometric
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Fraction.Rational) < 1 by decide) leafWidthPositive
    rw [ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Fraction.Rational)⁻¹ = 1 / 2 := by
      rw [ExplicitField.div_eq_mul_inv]
      exact (_root_.one_mul _).symm
    rw [halfInverse]
    simpa only [Fraction.Field.mul_comm, one_mul] using scaled
  exact (Subdivision.build_leaf_width_le event eventNonzero curve box
    (commonDepth event curve box root) root member).trans_lt
      (geometric'.trans_lt halfBelow)

/-- Every parameter in the original root cell belongs to a retained common-resolution leaf. -/
theorem commonSubdivision_covers
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell)
    (parameter : Fraction.Rational) (inside : root.interval.Contains parameter) :
    ∃ leaf,
      leaf ∈ (commonSubdivision event eventNonzero curve box root).leaves ∧
        leaf.interval.Contains parameter :=
  Subdivision.build_covers event eventNonzero curve box
    (commonDepth event curve box root) root parameter inside

/-- The aligned common leaves preserve the exact parent curve-event count. -/
theorem commonSubdivision_eventCount_sum
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) :
    Sturm.Count.Basic.cellCount2 event root =
      ((commonSubdivision event eventNonzero curve box root).leaves.map
        (Sturm.Count.Basic.cellCount2 event)).sum :=
  Subdivision.build_cellEventCount_sum event eventNonzero curve box
    (commonDepth event curve box root) root
end Purelib.RootIsolation.Curve.Event.Partition

end
