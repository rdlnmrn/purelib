module

import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Subdivision
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Basic

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Every leaf of the coefficient-computed subdivision carries a total finite
sign record for the complete gcd-reduced Cauchy--Sturm chain.

The retained leaf occurrence supplies its original root refinement and
strict width bound. Those same observations extract the exact sign record
selected by the original reduced-pair event scanner. -/
@[expose] public def leafEvent
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root leaf : Interval.Proper.Cell)
    (member : leaf ∈
      (CauchyIndex.EventPartition.Resolution.eventSubdivision numerator denominator denominatorNonzero root).leaves) :
    CauchyIndex.Events.Signs.CauchyEventSigns (Pair.Reduction.reducedNumerator numerator denominator)
      (Pair.Reduction.reducedDenominator numerator denominator) leaf.interval :=
  CauchyIndex.Events.Resolution.cauchyEventSignsOfRefinedRadiusSq
    (CauchyIndex.EventPartition.Resolution.reducedClearance numerator denominator root)
    (CauchyIndex.EventPartition.Resolution.eventSubdivision_leaf_refines numerator denominator denominatorNonzero
      root leaf member)
    (Interval.Radius.EventPartition.sampleRadiusSq_lt_of_width_lt leaf.proper
      (CauchyIndex.EventPartition.Resolution.eventSubdivision_leaf_width_lt numerator denominator denominatorNonzero
        root leaf member))

set_option genInjectivity false in
/-- The finite event partition packages its executable safe-cut tree together
with the total classifier for every emitted leaf.

The stored tree retains the original safe-cut cells and witnesses. Its
classifier is indexed by membership in that exact ordered leaf list and
returns the original reduced numerator and denominator sign records. -/
public structure Partition
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial) (root : Interval.Proper.Cell) where
  /-- The retained executable safe-cut tree for the polynomial pair. -/ tree :
    Subdivision numerator denominator
  /-- A complete gcd-reduced Cauchy-event sign record for each certified leaf of the retained tree. -/ classify : (leaf
    : Interval.Proper.Cell) → leaf ∈ tree.leaves →
    CauchyIndex.Events.Signs.CauchyEventSigns (Pair.Reduction.reducedNumerator numerator denominator)
      (Pair.Reduction.reducedDenominator numerator denominator) leaf.interval

constructive_injectivity Partition

/-- Build the safe subdivision and its total leaf-event classifier.

The tree uses the computed resolution depth, and each classifier is indexed by membership in that exact tree's leaf
list. -/
@[expose] public def classifyEvents
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (root : Interval.Proper.Cell) : Partition numerator denominator root where
  tree := CauchyIndex.EventPartition.Resolution.eventSubdivision numerator denominator denominatorNonzero root
  classify := leafEvent numerator denominator denominatorNonzero root

end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Basic
