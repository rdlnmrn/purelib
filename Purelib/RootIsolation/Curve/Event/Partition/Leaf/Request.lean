module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RootIsolation.Curve.Event.Partition.Leaf
import Purelib.RootIsolation.Sturm.Track.Basic
public import Purelib.RootIsolation.Sturm.Track.Request
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.RootIsolation.Sturm.Count.Basic

open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)
open Purelib.RootIsolation.Sturm.Track.Basic (State)

open Purelib.Data.Rat

open Purelib

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
namespace ClassifiedLeaf

/-- A classified nonzero curve event starts the persistent shrinking
univariate event transducer without discarding its aligned parent leaf. -/
@[expose] def eventState
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) :
    State event where
  cell := leaf.cell
  countNonzero := by
    rw [← leaf.eventCount_eq_sturmRootCount2]
    exact countNonzero

/-- Refine a classified nonzero curve event to an arbitrary positive
rational parameter width. -/
@[expose] def requestEvent
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Fraction.Rational) :
    State event :=
  Sturm.Track.Request.request event eventNonzero
    (leaf.eventState countNonzero) epsilon

/-- Every event-width request refines the original classified leaf. -/
theorem requestEvent_refines
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Fraction.Rational) :
    (leaf.requestEvent countNonzero epsilon).cell.interval.Refines
      leaf.cell.interval :=
  Sturm.Track.Request.request_refines event eventNonzero
    (leaf.eventState countNonzero) epsilon

/-- A positive width request produces an event interval no wider than the requested bound. -/
theorem requestEvent_width_le
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root)
    (countNonzero : leaf.eventCount ≠ 0) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Data.Rat.Interval.Bounds.width (leaf.requestEvent countNonzero epsilon).cell.interval) ≤ epsilon :=
  Sturm.Track.Request.request_width_le event eventNonzero
    (leaf.eventState countNonzero) epsilon positive

set_option genInjectivity false in
/-- Executable zero/nonzero split of the already-classified curve-event
integer.  The nonzero branch carries the persistent shrinking state rather
than only a proposition about the count. -/
inductive CountStatus
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) where
  /-- The original classified event count is zero. -/ | zero (countZero : leaf.eventCount = 0)
  /-- The original event count is nonzero, with a retained event state on exactly the classified leaf. -/ | nonzero
    (state : State event)
      (cell_eq : state.cell = leaf.cell)

constructive_injectivity CountStatus

/-- Decide whether the retained event count is zero and retain a persistent event state in the nonzero branch. -/
@[expose] def classifyCount
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) :
    CountStatus leaf := by
  by_cases countNonzero : leaf.eventCount ≠ 0
  · exact .nonzero (leaf.eventState countNonzero) rfl
  · exact .zero (Decidable.not_not.mp countNonzero)

end ClassifiedLeaf
end Purelib.RootIsolation.Curve.Event.Partition

end
