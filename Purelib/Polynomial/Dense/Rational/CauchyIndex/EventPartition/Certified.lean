module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Subdivision
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.Pair.Reduction

open Purelib

open Purelib.Polynomial

section
@[expose] public section

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Certified

set_option genInjectivity false in
/-- One coefficient-computed finite event partition together with the exact
telescoping identity for all emitted leaf indices. -/
structure ClassifiedPartition
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial) (root : Data.Rat.Interval.Proper.Cell) where
  /-- The retained safe subdivision and classifier of its actual leaf events. -/ partition :
    Dense.Rational.CauchyIndex.EventPartition.Basic.Partition
    numerator denominator root
  /-- The classified leaf indices sum to the Cauchy index on the original interval. -/ indexSum :
    Dense.Rational.CauchyIndex.EventPartition.Index.cellIndex2 numerator denominator root =
      (partition.tree.leaves.map
        (Dense.Rational.CauchyIndex.EventPartition.Index.cellIndex2 numerator denominator)).sum

constructive_injectivity ClassifiedPartition

/-- Execute and package the complete finite gcd-reduced event partition. -/
def classify
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Data.Rat.Interval.Proper.Cell) : ClassifiedPartition
      numerator denominator root := by
  let partition := Dense.Rational.CauchyIndex.EventPartition.Basic.classifyEvents
    numerator denominator denominatorNonzero root
  exact
    { partition := partition
      indexSum := by
        simpa only [partition,
          Dense.Rational.CauchyIndex.EventPartition.Basic.classifyEvents] using
          Dense.Rational.CauchyIndex.EventPartition.Index.eventSubdivision_cellIndex2_sum
            numerator denominator denominatorNonzero root }

end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Certified

end
