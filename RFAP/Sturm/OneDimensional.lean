import RFAP.Sturm.EventPartition
import RFAP.Sturm.NonzeroEvent

/-!
# Paper-facing one-dimensional Sturm tracks

This module packages the existing gcd-reduced event partition and persistent
nonzero-count refinement behind one finite API.  It deliberately states the
result actually proved by the implementation: classified finite leaves have
an exact telescoping doubled-index sum, and any explicitly selected nonzero
leaf can be refined to arbitrary positive rational width while preserving a
nonzero doubled Sturm count.

It does not strengthen a nonzero signed count to a count-one theorem and does
not introduce a completed zero between rational endpoints.
-/

namespace RFAP.OneDimensional

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Cell := RFAP.SturmEventPartition.Cell
abbrev State := RFAP.SturmNonzeroEvent.State

open RFAP.SturmRootCount
open RFAP.SturmEventPartition

/-- One coefficient-computed finite event partition together with the exact
telescoping identity for all emitted leaf indices. -/
structure ClassifiedPartition
    (numerator denominator : Polynomial) (root : Cell) where
  partition : RFAP.SturmEventPartition.EventPartition
    numerator denominator root
  indexSum :
    cellIndex2 numerator denominator root =
      (partition.tree.leaves.map
        (cellIndex2 numerator denominator)).sum

/-- Execute and package the complete finite gcd-reduced event partition. -/
def classify
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Cell) : ClassifiedPartition numerator denominator root := by
  let partition := RFAP.SturmEventPartition.classifyEvents
    numerator denominator denominatorNonzero root
  exact
    { partition := partition
      indexSum := by
        simpa only [partition,
          RFAP.SturmEventPartition.classifyEvents] using
          RFAP.SturmEventPartition.eventSubdivision_cellIndex2_sum
            numerator denominator denominatorNonzero root }

/-- A total finite refinement machine for one displayed nonzero Sturm event.
The current interval and its nonzero doubled count are explicit finite data. -/
structure ZeroEventTrack (polynomial : Polynomial) where
  polynomialNonzero : polynomial.isZero = false
  current : State polynomial

namespace ZeroEventTrack

/-- Answer one positive rational width request and retain the same executable
track interface at the returned interval. -/
def request
    {polynomial : Polynomial} (track : ZeroEventTrack polynomial)
    (epsilon : Coordinate) : ZeroEventTrack polynomial :=
  { polynomialNonzero := track.polynomialNonzero
    current := RFAP.SturmNonzeroEvent.request polynomial
      track.polynomialNonzero track.current epsilon }

/-- Every request returns a rational subinterval of the current interval. -/
theorem request_refines
    {polynomial : Polynomial} (track : ZeroEventTrack polynomial)
    (epsilon : Coordinate) :
    (track.request epsilon).current.cell.interval.Refines
      track.current.cell.interval :=
  RFAP.SturmNonzeroEvent.request_refines polynomial
    track.polynomialNonzero track.current epsilon

/-- A positive request bounds the returned rational interval width. -/
theorem request_width_le
    {polynomial : Polynomial} (track : ZeroEventTrack polynomial)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (track.request epsilon).current.cell.interval.width ≤ epsilon :=
  RFAP.SturmNonzeroEvent.request_width_le polynomial
    track.polynomialNonzero track.current epsilon positive

/-- The returned state retains an explicit nonzero doubled Sturm count. -/
theorem request_countNonzero
    {polynomial : Polynomial} (track : ZeroEventTrack polynomial)
    (epsilon : Coordinate) :
    sturmRootCount2 polynomial
      (track.request epsilon).current.cell.interval.lower
      (track.request epsilon).current.cell.interval.upper ≠ 0 :=
  (track.request epsilon).current.countNonzero

/-- Successive requests are nested by direct composition of their displayed
rational refinement certificates. -/
theorem successive_refines
    {polynomial : Polynomial} (track : ZeroEventTrack polynomial)
    (first second : Coordinate) :
    ((track.request first).request second).current.cell.interval.Refines
      track.current.cell.interval :=
  RFAP.SturmNonzeroEvent.intervalRefines_trans
    (request_refines (track.request first) second)
    (request_refines track first)

end ZeroEventTrack

end RFAP.OneDimensional
