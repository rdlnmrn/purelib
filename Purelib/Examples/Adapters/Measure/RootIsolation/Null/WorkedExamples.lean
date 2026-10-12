module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Operational
import Purelib.Approximation.Bound.Process
import Purelib.Approximation.CCL.BoxedName.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Geometry.Affine.Gaussian.Distance
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Box.Cell
import Purelib.Integration.Cell.Basic
import Purelib.Integration.Cover.Null
import Purelib.Measure.Box.Cover
public import Purelib.Measure.Box.Null
import Purelib.Measure.CCL.BoxedName.Area
import Purelib.Measure.CCL.BoxedName.FamilyArea

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Cover.Null
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Adapters.Measure.RootIsolation.Null.WorkedExamples

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Geometry.Rational
open Purelib.Measure
open Purelib
open Purelib.Integration
open Purelib.Data.CCL.Name
open Purelib.Approximation.Rational
open Purelib.Data

/-- The Gaussian rational point (2,-3). -/
def displayedPoint : Basic.Canonical :=
  ⟨2, -3⟩

/-- Every requested singleton cover of the displayed point has zero content. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((Box.Null.singletonNull displayedPoint).request epsilon
      positive).content = 0 := by
  simp only [Box.Null.singletonNull,
    Box.Cover.BoxCover.content, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Box.Content.pointBox_content,
    add_zero]

/-- An effective null certificate for equality with the displayed point.

Uses the singleton box-cover construction and its exact conversion to the generic cover scheme. -/
def displayedPointGenericNull :
    Measure.EffectiveNull Box.Cover.boxCoverScheme
      (fun candidate => candidate = displayedPoint) :=
  (Box.Null.singletonNull displayedPoint).toGeneric

/-- Converting the singleton null cover to the generic scheme preserves zero content. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (displayedPointGenericNull.request epsilon positive).content = 0
      := by
  simp only [displayedPointGenericNull,
    Box.Null.EffectiveNull.toGeneric,
    Box.Null.singletonNull,
    Box.Cover.BoxCover.toCover_content,
    Box.Cover.BoxCover.content, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Box.Content.pointBox_content,
    add_zero]

/-- Requested bounded cells over the singleton null set have upper integral below tolerance.

Uses the original null cover at every positive rational tolerance with the certified unit bound. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Integration.upperIntegral
      (Box.Cell.boxIntegrationCells
        ((Cover.Null.EffectiveNull.requestedBoundedCells (Box.Null.singletonNull
          displayedPoint))
          1 (by decide) epsilon positive)) < epsilon :=
  Cover.Null.EffectiveNull.requestedBoundedCells_upper_lt
    (Box.Null.singletonNull displayedPoint) 1 (by decide)
      epsilon positive

/-- The displayed point and origin admit finite covers below every positive tolerance. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((Box.Null.pointsNull
      [displayedPoint, ⟨0, 0⟩]).request epsilon positive).content <
        epsilon :=
  (Box.Null.pointsNull
    [displayedPoint, ⟨0, 0⟩]).small epsilon positive

/-- Singleton null predicates for the displayed point and the origin. -/
def twoNullPredicates : List
  Box.Null.NullPredicate :=
  [⟨fun point => point = displayedPoint,
      Box.Null.singletonNull displayedPoint⟩,
    ⟨fun point => point = ⟨0, 0⟩,
      Box.Null.singletonNull ⟨0, 0⟩⟩]

/-- The retained two-predicate null union has arbitrarily small requested content. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((Box.Null.NullPredicate.effectiveUnion
      twoNullPredicates).request
      epsilon positive).content < epsilon :=
  (Box.Null.NullPredicate.effectiveUnion
    twoNullPredicates).small
    epsilon positive

/-- The rational indicator of the displayed point. -/
def rationalSpike (point : Basic.Canonical) :
  Fraction.Rational :=
  if point = displayedPoint then 1 else 0

/-- The displayed-point indicator agrees with zero outside a certified null set.

Retains the singleton null cover and proves that every disagreement occurs at its original point. -/
def rationalSpike_equalExceptNull :
    Box.Null.EqualExceptNull rationalSpike (fun _ => 0) :=
  Box.Null.EffectiveNull.mono
    (Box.Null.singletonNull displayedPoint)
    (by
      intro point different
      by_cases equal : point = displayedPoint
      · exact equal
      · have spikeZero : rationalSpike point = 0 := by
          rw [rationalSpike]
          exact if_neg equal
        exact (different spikeZero).elim)

/-! ## CCL finite area observations -/

/-- A boxed progressive name yields an area certificate below any positive target. -/
example (name : Boxed.Process.ProgressiveName)
    (target : Fraction.Rational) (positive : 0 < target) :
    Box.Content.boxContent
      (CCL.BoxedName.ProgressiveName.areaCertificate
        name name.initial target positive).box < target :=
  CCL.BoxedName.ProgressiveName.areaCertificate_content_lt
    name name.initial target positive

/-- Adding two boxed-name area processes preserves their operational equivalence to zero. -/
example (name : Boxed.Process.ProgressiveName) :
    Approximation.OperationallyEquivalent
      ((CCL.BoxedName.ProgressiveName.toAreaProcess name).add
        (CCL.BoxedName.ProgressiveName.toAreaProcess name))
      ((Approximation.BoundProcess.exact 0).add (Approximation.BoundProcess.exact 0)) :=
  Approximation.operationallyEquivalent_add
    (CCL.BoxedName.ProgressiveName.toAreaProcess_operationallyEquivalent_zero
      name)
    (CCL.BoxedName.ProgressiveName.toAreaProcess_operationallyEquivalent_zero
      name)

/-- The sum of two boxed-name area processes is operationally equivalent to exact zero.

Uses their retained zero anchors and the exact addition identity. -/
example (name : Boxed.Process.ProgressiveName) :
    Approximation.OperationallyEquivalent
      ((CCL.BoxedName.ProgressiveName.toAreaProcess name).add
        (CCL.BoxedName.ProgressiveName.toAreaProcess name))
      (Approximation.BoundProcess.exact 0) := by
  apply Approximation.operationallyEquivalent_exact_of_anchoredAt
  simpa only [zero_add] using
    Approximation.BoundProcess.anchoredAt_add
      (CCL.BoxedName.ProgressiveName.toAreaProcess name)
      (CCL.BoxedName.ProgressiveName.toAreaProcess name)
      0 0
      (CCL.BoxedName.ProgressiveName.toAreaProcess_anchored name)
      (CCL.BoxedName.ProgressiveName.toAreaProcess_anchored name)

/-- The retained result of a finite accuracy-request list satisfies each member tolerance.

Any two possible Gaussian points of the actual resulting state are closer than the selected request's positive
tolerance. -/
example (name : Boxed.Process.ProgressiveName)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) {left right : Basic.Canonical}
    (leftPossible :
      (name.certificate
        (Approximation.CCL.BoxedName.ProgressiveName.runAccuracyRequests
          name name.initial requests)).Possible left)
    (rightPossible :
      (name.certificate
        (Approximation.CCL.BoxedName.ProgressiveName.runAccuracyRequests
          name name.initial requests)).Possible right) :
    Geometry.Affine.Gaussian.affineDistance left right <
      request.tolerance :=
  Approximation.CCL.BoxedName.ProgressiveName.runAccuracyRequests_pairwise_lt_of_mem
    name name.initial requests request member leftPossible rightPossible

/-- A two-name family receives certificates whose total content is below the target. -/
example (left right : Boxed.Process.ProgressiveName)
    (target : Fraction.Rational) (positive : 0 < target) :
    CCL.BoxedName.familyContent
        (CCL.BoxedName.familyCertificates [left, right] target positive) <
      target :=
  CCL.BoxedName.familyCertificates_content_lt [left, right]
    target positive

/-- The finite dyadic block count yields a spread below every positive target. -/
example (target : Fraction.Rational) (positive : 0 < target) :
    (1 / 2 : Fraction.Rational) ^ Budget.Dyadic.requiredBlockCount target <
      target :=
  Budget.Dyadic.requiredBlockCount_spread_lt positive

/-- The displayed three-bit prefix has weight one eighth. -/
example : List.BinaryPrefix.rawPrefixWeight [true, false, true] = 1 / 8 := by
  decide

/-- Extending a one-bit prefix by three bits produces eight extensions. -/
example : (List.BinaryPrefix.rawExtensions [true] 3).length = 8 := by
  decide

end Purelib.Examples.Adapters.Measure.RootIsolation.Null.WorkedExamples

end
