module
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Cut
import Purelib.Data.Rat.Interval.Proper
import Purelib.Data.Rat.Sign.Typed
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Cut
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Subdivision
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Pair.Reduction

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Read the gcd-reduced doubled Cauchy index across a proper rational cell.

The original reduced numerator and denominator are evaluated at the
retained interval endpoints. Their displayed doubled Cauchy index is
read without changing the cell owner or recomputing a subdivision. -/
@[expose] public def cellIndex2
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial) (cell : Interval.Proper.Cell) : Int :=
  CauchyIndex.Reduced.reducedCauchyIndex2 numerator denominator
    cell.interval.lower cell.interval.upper

/-- The root cell index equals the sum of the indices over every leaf of a finite safe subdivision.

Each retained safe split supplies additive index agreement at its
actual cut. The original ordered leaf lists and integer sum fold
compose that same finite decomposition over the requested depth. -/
public theorem build_cellIndex2_sum
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Interval.Proper.Cell) :
    cellIndex2 numerator denominator root =
      ((Subdivision.build numerator denominator denominatorNonzero depth
        root).leaves.map
        (cellIndex2 numerator denominator)).sum := by
  induction depth generalizing root with
  | zero =>
      change cellIndex2 numerator denominator root =
        cellIndex2 numerator denominator root + 0
      exact (Int.add_zero _).symm
  | succ depth inductionHypothesis =>
      let data := CauchyIndex.EventPartition.Cut.safeSplit numerator denominator denominatorNonzero root
      have splitIndex : cellIndex2 numerator denominator root =
          cellIndex2 numerator denominator data.leftCell +
            cellIndex2 numerator denominator data.rightCell := by
        unfold cellIndex2
        simpa only [CauchyIndex.EventPartition.Cut.SafeSplit.leftCell,
          CauchyIndex.EventPartition.Cut.SafeSplit.rightCell, Interval.Proper.Cell.left,
          Interval.Proper.Cell.right, Data.Rat.Interval.Bounds.leftChild, Data.Rat.Interval.Bounds.rightChild] using
          CauchyIndex.Reduced.reducedCauchyIndex2_add numerator denominator root.interval.lower
            data.cut root.interval.upper
      rw [splitIndex, inductionHypothesis data.leftCell,
        inductionHypothesis data.rightCell]
      change
        ((Subdivision.build
          numerator denominator denominatorNonzero depth data.leftCell).leaves.map
            (cellIndex2 numerator denominator)).sum +
          ((Subdivision.build
            numerator denominator denominatorNonzero depth data.rightCell).leaves.map
              (cellIndex2 numerator denominator)).sum =
        (((Subdivision.build
          numerator denominator denominatorNonzero depth data.leftCell).leaves ++
          (Subdivision.build
            numerator denominator denominatorNonzero depth data.rightCell).leaves).map
              (cellIndex2 numerator denominator)).sum
      rw [Data.List.Map.map_append]
      exact (Data.List.Fold.sum_append Data.Int.Arithmetic.zero_add
        Data.Int.Arithmetic.add_assoc _ _).symm

/-- Read the local doubled index from a certified event and its four endpoint signs.

The original event and polynomial pair determine the four endpoint
signs. The doubled local index uses those signed values in their
retained lower/upper and numerator/denominator order. -/
@[expose] public def eventIndex2
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (event : CauchyIndex.Events.Signs.CauchyEventSigns R S interval) : Int :=
  event.numerator.eventIndex2 event.denominator
    (Data.Sign.ofCoordinate
      (R.eval interval.lower))
    (Data.Sign.ofCoordinate
      (S.eval interval.lower))
    (Data.Sign.ofCoordinate
      (R.eval interval.upper))
    (Data.Sign.ofCoordinate
      (S.eval interval.upper))

/-- The reduced index of a computed leaf equals the index read from its retained event certificate.

The leaf event is selected from the original reduced-pair classifier
at the displayed cell. Its existing event-index certificate identifies
the same reduced index and four original endpoint signs. -/
public theorem leafEvent_index2
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Interval.Proper.Cell)
    (member : leaf ∈
      (CauchyIndex.EventPartition.Resolution.eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    cellIndex2 numerator denominator leaf =
      eventIndex2
        (CauchyIndex.EventPartition.Basic.leafEvent numerator denominator denominatorNonzero root leaf member) := by
  unfold cellIndex2 CauchyIndex.Reduced.reducedCauchyIndex2 eventIndex2
  exact (CauchyIndex.EventPartition.Basic.leafEvent numerator denominator denominatorNonzero
    root leaf member).index

/-- The computed event subdivision preserves the root index as the exact finite sum of leaf indices.

The original computed depth and safe subdivision supply the complete
ordered leaf list. Finite additivity gives its exact integer sum,
including every retained occurrence of a leaf cell. -/
public theorem eventSubdivision_cellIndex2_sum
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Interval.Proper.Cell) :
    cellIndex2 numerator denominator root =
      ((CauchyIndex.EventPartition.Resolution.eventSubdivision numerator denominator denominatorNonzero root).leaves.map
        (cellIndex2 numerator denominator)).sum :=
  build_cellIndex2_sum numerator denominator denominatorNonzero
    (CauchyIndex.EventPartition.Resolution.eventDepth numerator denominator root) root

end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index
