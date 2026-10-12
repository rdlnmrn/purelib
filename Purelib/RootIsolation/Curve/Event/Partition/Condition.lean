module
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Guard
public import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Sturm.Event.Resolution
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Width
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Signs
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

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

/-- Certificate-retaining resolution of the main curve-root event. -/
def polynomialEventResolution
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves) :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
      (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
      leaf.interval :=
  Sturm.Event.polynomialEventResolutionOfBounds event root leaf
    (Curve.Event.Partition.commonSubdivision_leaf_refines event eventNonzero curve box root leaf member)
    ((Curve.Event.Partition.commonSubdivision_leaf_width_lt event eventNonzero curve box
      root leaf member).trans_le
        (Curve.Event.Partition.commonLeafWidth_le_event event curve box root))

/-- Read the main polynomial-event signs on one original common-resolution leaf. -/
def polynomialEventSigns
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns
      (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
      (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
      leaf.interval :=
  (polynomialEventResolution event eventNonzero curve box root leaf member).signs

set_option genInjectivity false in
/-- One aligned event record for a nontrivial box-edge polynomial. -/
structure ConditionEvent
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell) where
  /-- The original active box-condition polynomial retained in this event record. -/ polynomial :
    RationalPolynomial
  /-- The retained polynomial belongs to the original curve's active box conditions. -/ member : polynomial ∈
    Curve.Box.activeConditionPolynomials curve box
  /-- The retained derivative-quotient event resolution on the exact original leaf interval. -/ resolution :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
    (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative polynomial)
      polynomial)
    (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative polynomial)
      polynomial)
    leaf.interval

constructive_injectivity ConditionEvent

namespace ConditionEvent

/-- Read the exact event signs from this retained condition-polynomial resolution. -/
def signs
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root leaf : Cell}
    (condition : Curve.Event.Partition.ConditionEvent event eventNonzero curve box root leaf) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative condition.polynomial)
        condition.polynomial)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative condition.polynomial)
        condition.polynomial)
      leaf.interval :=
  condition.resolution.signs

end ConditionEvent

/-- Resolve one retained active box-condition polynomial on an original common-resolution leaf.

The common subdivision's containment and width bounds provide the original event-resolution certificates. -/
def conditionEvent
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves)
    (polynomial : RationalPolynomial)
    (member : polynomial ∈
      Curve.Box.activeConditionPolynomials curve box) :
    ConditionEvent event eventNonzero curve box root leaf where
  polynomial := polynomial
  member := member
  resolution :=
    Sturm.Event.polynomialEventResolutionOfBounds polynomial root leaf
      (Curve.Event.Partition.commonSubdivision_leaf_refines event eventNonzero curve box
        root leaf leafMember)
      ((Curve.Event.Partition.commonSubdivision_leaf_width_lt event eventNonzero
        curve box root leaf leafMember).trans_le
          (Curve.Event.Partition.commonLeafWidth_le_condition event root member))

/-- Resolve every retained active box-condition polynomial on the same original subdivision leaf.

The finite list keeps each original polynomial and its membership witness aligned with its resolution. -/
def conditionEvents
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves) :
    List (ConditionEvent event eventNonzero curve box root leaf) :=
  (Curve.Box.activeConditionPolynomials curve box).attach.map
    fun entry => conditionEvent event eventNonzero curve box root leaf
      leafMember entry.1 entry.2

open Purelib.Data.List in
/-- The aligned condition-event list has exactly one entry for every original active condition polynomial. -/
theorem conditionEvents_length
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (leafMember : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves) :
    (conditionEvents event eventNonzero curve box root leaf leafMember).length =
      (Curve.Box.activeConditionPolynomials
        curve box).length := by
  simp only [conditionEvents, -eq_self, -iff_self]
  rw [Map.length_map]
  have erased := attach_map_subtype_val
    (Curve.Box.activeConditionPolynomials curve box)
  have lengths := congrArg List.length erased
  rw [Map.length_map] at lengths
  exact lengths
end Purelib.RootIsolation.Curve.Event.Partition

end
