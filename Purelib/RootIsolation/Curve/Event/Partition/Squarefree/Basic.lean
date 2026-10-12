module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Condition
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
public import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Condition
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Event.Resolution
import Purelib.RootIsolation.Sturm.Orientation.Event
public import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Data.Rat.Interval.Width
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Signs

section

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Curve.Event.Partition.Squarefree

set_option genInjectivity false in
/-- A squarefree common leaf retains the ordinary aligned box-condition
records and the stronger Taylor width that makes the root-event count
semantically exhaustive. -/
structure SquarefreeClassifiedLeaf
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Data.Rat.Interval.Proper.Cell) where
  /-- The actual retained squarefree-subdivision leaf. -/ cell : Data.Rat.Interval.Proper.Cell
  /-- The retained leaf belongs to the original squarefree subdivision. -/ member : cell ∈
    (Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree
      curve box root).leaves
  /-- The leaf interval refines the original root interval. -/ refines : cell.interval.Refines root.interval
  /-- The leaf is strictly narrower than the common squarefree orientation budget. -/ widthSmall :
    (Data.Rat.Interval.Bounds.width cell.interval) <
    Curve.Event.Partition.Squarefree.squarefreeLeafWidth event squarefree curve box root
  /-- The retained reduced derivative/event Cauchy resolution on this exact leaf. -/ eventResolution :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
    (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
    (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
    cell.interval
  /-- The original active box-condition resolutions on this same retained leaf. -/ boxConditionEvents :
    List (Curve.Event.Partition.ConditionEvent event eventNonzero curve box root cell)

constructive_injectivity SquarefreeClassifiedLeaf

/-- Classify an original squarefree-subdivision leaf with its aligned event and active-condition resolutions.

The retained leaf also meets the Taylor orientation width needed to interpret its root-event count exhaustively. -/
def classifySquarefreeLeaf
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Data.Rat.Interval.Proper.Cell)
    (member : leaf ∈
      (Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root where
  cell := leaf
  member := member
  refines := Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_refines event eventNonzero squarefree
    curve box root leaf member
  widthSmall := Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_width_lt event eventNonzero
    squarefree curve box root leaf member
  eventResolution :=
    Sturm.Event.polynomialEventResolutionOfBounds event root leaf
      (Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_refines event eventNonzero squarefree
        curve box root leaf member)
      ((Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_width_lt event eventNonzero squarefree
        curve box root leaf member).trans_le
          ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common event squarefree curve box root).trans
            (Purelib.RootIsolation.Curve.Event.Partition.commonLeafWidth_le_event event curve box root)))
  boxConditionEvents := Curve.Event.Partition.Squarefree.squarefreeConditionEvents event eventNonzero squarefree
    curve box root leaf member

namespace SquarefreeClassifiedLeaf

/-- Read the original Cauchy-event signs retained by this squarefree leaf. -/
def eventSigns
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns
      (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
      (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
      leaf.cell.interval :=
  leaf.eventResolution.signs

/-- Read the doubled event index from the retained squarefree leaf's original sign resolution. -/
def eventCount
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) : Int :=
  Dense.Rational.CauchyIndex.EventPartition.Index.eventIndex2 leaf.eventSigns

/-- The retained squarefree event index equals the doubled Sturm root count on the original leaf interval. -/
theorem eventCount_eq_sturmRootCount2
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) :
    leaf.eventCount = Sturm.Count.Basic.sturmRootCount2 event
      leaf.cell.interval.lower leaf.cell.interval.upper := by
  unfold Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf.eventCount
    Dense.Rational.CauchyIndex.EventPartition.Index.eventIndex2
    Sturm.Count.Basic.sturmRootCount2 Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2
  exact leaf.eventSigns.index.symm

/-- The key semantic closure: every displayed rational root in a squarefree
leaf forces the stored event integer to be nonzero. -/
theorem eventCount_ne_zero_of_root
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root)
    (parameter : Fraction.Rational) (inside : leaf.cell.interval.Contains parameter)
    (rootZero : event.eval parameter = 0) : leaf.eventCount ≠ 0 := by
  rw [leaf.eventCount_eq_sturmRootCount2]
  exact Sturm.Orientation.Event.sturmRootCount2_ne_zero_of_root
    event squarefree leaf.refines leaf.cell.proper
      (leaf.widthSmall.trans_le
        (Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_orientation event squarefree curve box root))
      leaf.eventResolution parameter inside rootZero

/-- Retain the original squarefree leaf as a persistent Sturm state when its event count is nonzero. -/
def eventState
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root)
    (countNonzero : leaf.eventCount ≠ 0) :
    Sturm.Track.Basic.State event where
  cell := leaf.cell
  countNonzero := by
    rw [← leaf.eventCount_eq_sturmRootCount2]
    exact countNonzero

set_option genInjectivity false in
/-- Exhaustive squarefree leaf status.  A zero event count now carries a
pointwise no-root certificate; the other branch starts the persistent
nonzero-event transducer. -/
inductive Status
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) where
  /-- The original event polynomial is nonzero at every displayed parameter of this leaf. -/ | clear (noRoot : ∀
    parameter, leaf.cell.interval.Contains parameter →
      event.eval parameter ≠ 0)
  /-- A nonzero-event Sturm state retained on exactly the original classified leaf. -/ | event (state :
    Sturm.Track.Basic.State event)
      (cell_eq : state.cell = leaf.cell)

constructive_injectivity Status

/-- Classify a squarefree leaf as root-free or retain its nonzero-event Sturm state.

A zero retained count gives pointwise nonvanishing throughout the same leaf by its Taylor orientation certificate. -/
def classify
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (leaf : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
      curve box root) : Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf.Status leaf := by
  by_cases countNonzero : leaf.eventCount ≠ 0
  · exact .event (leaf.eventState countNonzero) rfl
  · have countZero : leaf.eventCount = 0 :=
      Decidable.not_not.mp countNonzero
    exact .clear fun parameter inside rootZero =>
      (leaf.eventCount_ne_zero_of_root parameter inside rootZero countZero).elim

end SquarefreeClassifiedLeaf

set_option genInjectivity false in
/-- Executed squarefree/Taylor subdivision with an exhaustive classifier on
every emitted leaf. -/
structure SquarefreeEventPartition
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Data.Rat.Interval.Proper.Cell) where
  /-- The actual retained squarefree event-subdivision tree. -/ tree : Curve.Event.Partition.Subdivision event curve box
  /-- The retained tree equals the original squarefree-subdivision construction. -/ tree_eq : tree =
    Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree
    curve box root
  /-- The exhaustive classifier for each actual member of the retained leaf list. -/ classify : (leaf :
    Data.Rat.Interval.Proper.Cell) → leaf ∈ tree.leaves →
    Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree curve box root
  /-- Classification preserves the supplied original leaf exactly. -/ classify_cell : ∀ (leaf :
    Data.Rat.Interval.Proper.Cell) (member : leaf ∈ tree.leaves),
    (classify leaf member).cell = leaf

constructive_injectivity SquarefreeEventPartition

/-- Build the retained squarefree event subdivision with a total exhaustive classifier on its original leaves. -/
def classifySquarefreeEvents
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root : Data.Rat.Interval.Proper.Cell) :
    Curve.Event.Partition.Squarefree.SquarefreeEventPartition event eventNonzero squarefree curve box root where
  tree := Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree curve box root
  tree_eq := rfl
  classify := fun leaf member => Curve.Event.Partition.Squarefree.classifySquarefreeLeaf event eventNonzero
    squarefree curve box root leaf member
  classify_cell := fun _leaf _member => rfl

set_option genInjectivity false in
/-- Constructive location in the exhaustive squarefree partition. -/
structure LocatedSquarefreeParameter
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (partition : Curve.Event.Partition.Squarefree.SquarefreeEventPartition event eventNonzero squarefree
      curve box root)
    (parameter : Fraction.Rational) where
  /-- The original squarefree leaf selected for the query parameter. -/ leaf : Data.Rat.Interval.Proper.Cell
  /-- The selected leaf belongs to the retained subdivision tree. -/ member : leaf ∈ partition.tree.leaves
  /-- The selected interval contains the original query parameter. -/ contains : leaf.interval.Contains parameter
  /-- The retained exhaustive classification of the selected leaf. -/ classification :
    Curve.Event.Partition.Squarefree.SquarefreeClassifiedLeaf event eventNonzero squarefree
    curve box root
  /-- The retained classification is exactly the original partition classifier's result. -/ classification_eq :
    classification = partition.classify leaf member
  /-- The classified cell is the exact selected original leaf. -/ classification_cell : classification.cell = leaf

constructive_injectivity LocatedSquarefreeParameter

/-- Locate a displayed parameter in the retained squarefree subdivision and return the exact selected leaf's
classification. -/
def SquarefreeEventPartition.locate
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (partition : Curve.Event.Partition.Squarefree.SquarefreeEventPartition event eventNonzero squarefree
      curve box root)
    (parameter : Fraction.Rational) (inside : root.interval.Contains parameter) :
    Curve.Event.Partition.Squarefree.LocatedSquarefreeParameter partition parameter := by
  let found := Curve.Event.Partition.Subdivision.locateBuild event eventNonzero curve box
    (Curve.Event.Partition.Squarefree.squarefreeDepth event squarefree curve box root) root parameter inside
  have treeMember : found.leaf ∈ partition.tree.leaves := by
    rw [partition.tree_eq]
    exact found.member
  exact
    { leaf := found.leaf
      member := treeMember
      contains := found.contains
      classification := partition.classify found.leaf treeMember
      classification_eq := rfl
      classification_cell := partition.classify_cell found.leaf treeMember }
end Purelib.RootIsolation.Curve.Event.Partition.Squarefree

end

end
