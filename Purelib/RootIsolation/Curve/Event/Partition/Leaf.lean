module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RootIsolation.Curve.Event.Partition.Condition
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Count.Squarefree
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Signs
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Basic (RationalPolynomial)

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

set_option genInjectivity false in
/-- One common leaf with every aligned event classification already
executed. -/
structure ClassifiedLeaf
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Cell) where
  /-- The actual parameter interval selected from the original common subdivision. -/ cell :
    Cell
  /-- The retained interval belongs to the original common leaf list. -/ member : cell ∈
    (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves
  /-- The retained leaf refines the original parameter interval. -/ refines : cell.interval.Refines root.interval
  /-- The retained leaf meets the common event-resolution width budget. -/ widthSmall :
    (Data.Rat.Interval.Bounds.width cell.interval) < Curve.Event.Partition.commonLeafWidth event curve box root
  /-- The original event-resolution outcome on this exact retained leaf. -/ eventResolution :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
    (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
    (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
    cell.interval
  /-- The resolutions of the original active box conditions on this same retained leaf. -/ boxConditionEvents :
    List (Curve.Event.Partition.ConditionEvent event eventNonzero curve box root cell)

constructive_injectivity ClassifiedLeaf

/-- Classify an original common-subdivision leaf using its retained event and box-condition resolutions.

The leaf, its membership, interval refinement and width bound remain indexed by the original simultaneous subdivision.
-/
@[expose] def classifyLeaf
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Cell)
    (member : leaf ∈
      (Curve.Event.Partition.commonSubdivision event eventNonzero curve box root).leaves) :
    ClassifiedLeaf event eventNonzero curve box root where
  cell := leaf
  member := member
  refines := Curve.Event.Partition.commonSubdivision_leaf_refines event eventNonzero curve box
    root leaf member
  widthSmall := Curve.Event.Partition.commonSubdivision_leaf_width_lt event eventNonzero curve box
    root leaf member
  eventResolution :=
    Curve.Event.Partition.polynomialEventResolution event eventNonzero curve box root leaf member
  boxConditionEvents := Curve.Event.Partition.conditionEvents event eventNonzero curve box
    root leaf member

namespace ClassifiedLeaf

/-- Read the finite event-sign data retained by this leaf's original event resolution. -/
@[expose] def eventSigns
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns
      (Dense.Rational.Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
      (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
      leaf.cell.interval :=
  leaf.eventResolution.signs

set_option genInjectivity false in
/-- Quantitative zero-event evidence retained from the neutral scanner
branch. -/
structure NeutralCertificate
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) where
  /-- The original denominator-sign certificate on the retained neutral leaf. -/ denominator :
    Dense.Rational.Sign.Interval.Basic.Certificate
    (Dense.Rational.Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
    leaf.cell.interval

constructive_injectivity NeutralCertificate

/-- Extract the retained denominator-sign certificate precisely when the classified leaf is neutral. -/
@[expose] def neutralCertificate?
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) :
    Option (Curve.Event.Partition.ClassifiedLeaf.NeutralCertificate leaf) :=
  match leaf.eventResolution with
  | .neutral denominator _chain => some ⟨denominator⟩
  | .numerator _certificate _tail => none

/-- The squarefree event polynomial is nonzero at every point of the retained neutral leaf. -/
theorem NeutralCertificate.event_eval_ne_zero
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    {leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root}
    (neutral : Curve.Event.Partition.ClassifiedLeaf.NeutralCertificate leaf)
    (squarefree : Dense.Rational.Bezout.Basic.CoprimeCertificate event
      (Dense.Derivative.derivative event))
    {parameter : Fraction.Rational}
    (inside : leaf.cell.interval.Contains parameter) :
    event.eval parameter ≠ 0 :=
  Sturm.Count.Squarefree.denominator_eval_ne_zero_of_reduced_of_coprime squarefree
    (neutral.denominator.eval_ne_zero inside)

/-- The finite integer attached to the main curve-root event in this aligned
leaf.  It is definitionally the displayed doubled Sturm count, but retaining
the classified finite-sign presentation avoids recomputing the chain. -/
@[expose] def eventCount
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) : Int :=
  Dense.Rational.CauchyIndex.EventPartition.Index.eventIndex2 leaf.eventSigns

/-- The retained doubled event count equals the original Sturm root count on this leaf. -/
theorem eventCount_eq_sturmRootCount2
    {event : RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Cell}
    (leaf : Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root) :
    leaf.eventCount = Sturm.Count.Basic.sturmRootCount2 event
      leaf.cell.interval.lower leaf.cell.interval.upper := by
  unfold Curve.Event.Partition.ClassifiedLeaf.eventCount Dense.Rational.CauchyIndex.EventPartition.Index.eventIndex2
    Sturm.Count.Basic.sturmRootCount2 Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2
  exact leaf.eventSigns.index.symm
end ClassifiedLeaf
end Purelib.RootIsolation.Curve.Event.Partition

end
