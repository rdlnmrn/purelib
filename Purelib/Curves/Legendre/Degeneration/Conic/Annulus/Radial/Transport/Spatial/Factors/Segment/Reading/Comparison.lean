module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Movement
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Gaussian.Norm.Basic

/-! # Original physical factor readings at the same spatial point

Two independent physical factor preparations keep their separate complete
queries, Owners, certificates and products. Their exact common point and the
original shared source budgets compare both factors internally. Actual
supplied product observations can then be compared without re-sampling or
relabeling either original state.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Comparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {firstBudgets lastBudgets : Budgets anchor}
variable {firstStart firstFinish lastStart lastFinish : Canonical}
variable {firstSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) firstStart firstFinish}
variable {lastSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) lastStart lastFinish}
variable {firstWithin : firstSegment.WithinAmbient} {lastWithin : lastSegment.WithinAmbient}
variable {firstCompleted : Segment firstBudgets firstSegment firstWithin}
variable {lastCompleted : Segment lastBudgets lastSegment lastWithin}
variable {firstTime lastTime : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside firstTime} {lastInside : FixedRootBoxPath.Inside lastTime}

/-- Compare both original normalized Owners through the identical source Seed budget at their exact common point. -/
def normal_owners (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent (ownerRootName first.normal.parameterNonzero first.normal)
      (ownerRootName last.normal.parameterNonzero last.normal) := by
  have physical := firstSegment.pointAt_contains firstWithin firstTime firstInside
  have nonzero := firstBudgets.normalized_nonzero physical
  have movement := firstBudgets.normalized_movement physical
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  exact firstBudgets.normalized.retainedOwnersEquivalentOfEq
    (congrArg (Clearance.normalizedRadicand site parameter) point_eq) nonzero movement
    first.normal last.normal first.normal_refines last.normal_refines

/-- Compare the distinct original cofactor Owners through the same unchanged prepared quarter reference budget. -/
def unit_owners (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent (ownerRootName first.unit.parameterNonzero first.unit)
      (ownerRootName last.unit.parameterNonzero last.unit) := by
  have physical := firstSegment.pointAt_contains firstWithin firstTime firstInside
  have nonzero := firstBudgets.unit_nonzero physical
  have movement := firstBudgets.unit_movement physical
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  exact firstBudgets.unit.retainedOwnersEquivalentOfEq
    (congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq) nonzero movement
    first.unit last.unit first.unit_refines last.unit_refines

/-- The two original normalized certificate caches agree without substituting a common certificate for either input. -/
def normal (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent first.values.normalRoot.value.name last.values.normalRoot.value.name := by
  have firstName : first.values.normalRoot.value.name = ownerRootName first.normal.parameterNonzero first.normal := by
    rewrite [first.values.normalRoot_eq]
    rfl
  have lastName : last.values.normalRoot.value.name = ownerRootName last.normal.parameterNonzero last.normal := by
    rewrite [last.values.normalRoot_eq]
    rfl
  exact NamedEquivalent.transport firstName.symm lastName.symm (normal_owners first last point_eq)

/-- The two separately retained cofactor certificate caches agree by their original owner-name readbacks. -/
def unit (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent first.values.unitRoot.value.name last.values.unitRoot.value.name := by
  have firstName : first.values.unitRoot.value.name = ownerRootName first.unit.parameterNonzero first.unit := by
    rewrite [first.values.unitRoot_eq]
    rfl
  have lastName : last.values.unitRoot.value.name = ownerRootName last.unit.parameterNonzero last.unit := by
    rewrite [last.values.unitRoot_eq]
    rfl
  exact NamedEquivalent.transport firstName.symm lastName.symm (unit_owners first last point_eq)

/-- Compare the complete original full-cubic product programs from the derived independent factor comparisons. -/
def agree (first : Reading firstCompleted firstTime firstInside) (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent first.values.value.name last.values.value.name := by
  rewrite [first.values.value_eq, last.values.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    first.values.unitRoot.value last.values.unitRoot.value first.values.normalRoot.value last.values.normalRoot.value
    (unit first last point_eq) (normal first last point_eq)

variable {firstUnit firstNormal lastUnit lastNormal : AccuracyRequest}

/-- Compare the exact supplied original factor-product observations, retaining both complete Samples unchanged.

The comparison uses their actual paired states, witnesses and radii. It
constructs the same-point relation internally and delegates to the original
retained observation comparator. No new source or target observation is
sampled, and no old state is retagged as a state of the other product process.
-/
def compare_samples {first : Reading firstCompleted firstTime firstInside}
    {last : Reading lastCompleted lastTime lastInside}
    (firstSamples : Samples first firstUnit firstNormal) (lastSamples : Samples last lastUnit lastNormal)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    Equivalence.Observation.Comparison firstSamples.product lastSamples.product target :=
  Equivalence.Observation.Comparison.build firstSamples.product lastSamples.product (agree first last point_eq)
    target targetPositive

section IndependentSources

variable {otherQuarter : UnitCircuitQuarter} {otherPositive : (0 : Fraction.Rational) < 2}
variable {otherActual : Transport.Quarter site parameter 2 otherQuarter otherPositive}
variable {otherReference : Fraction.Rational} {otherReferenceInside : FixedRootBoxPath.Inside otherReference}
variable {otherSource : Transport.Reading otherActual otherReference otherReferenceInside}
variable {otherAnchor : Parameter.Anchor otherSource.lift} {otherBudgets : Budgets otherAnchor}
variable {otherStart otherFinish : Canonical}
variable {otherSegment : ClearSegment (Paths.polynomial parameter) (sourceBox otherAnchor) otherStart otherFinish}
variable {otherWithin : otherSegment.WithinAmbient} {otherCompleted : Segment otherBudgets otherSegment otherWithin}
variable {otherTime : Fraction.Rational} {otherInside : FixedRootBoxPath.Inside otherTime}

/-- Compare retained physical factor readings from independent signed source anchors at their exact common point.

Both original Readings keep their separate queried Owners, certificates,
products and paid Samples. Actual indexed witnesses remain possible in
their own process states. The two original signed-window sum floors pay
new square-residual comparisons with independent requested starts; only
the radicand endpoint equalities are transported across the common point.
-/
def agree_across {first : Reading firstCompleted firstTime firstInside}
    {other : Reading otherCompleted otherTime otherInside}
    (firstSamples : Samples first firstUnit firstNormal) (otherSamples : Samples other lastUnit lastNormal)
    (point_eq : firstSegment.pointAt firstTime = otherSegment.pointAt otherTime) :
    NamedEquivalent first.values.value.name other.values.value.name := by
  have unitSquare : SquareRootProvenance.SquareIdentity other.values.unitRoot.value
      ((unitPolynomial site).eval (firstSegment.pointAt firstTime)) :=
    NamedEquivalent.transport rfl
      (congrArg Name.Basic.Named.exact (congrArg (fun point : Canonical => (unitPolynomial site).eval point)
        point_eq.symm)) other.values.unitRoot.square
  let unitCompared := SquareRootChannelOwnership.equivalent_of_sum_lower
    first.values.unitRoot.square unitSquare 1 (by decide +kernel) 0 0
    (fun firstIndex otherIndex _firstLater _otherLater => by
      have firstPossible := Process.Sampling.witnessAt_possible first.values.unitRoot.value.name.process
        first.values.unitRoot.value.name.state firstIndex
      have otherPossible := Process.Sampling.witnessAt_possible other.values.unitRoot.value.name.process
        other.values.unitRoot.value.name.state otherIndex
      exact (UnitRoot.box_sum_lower site (firstSamples.unit_inside firstPossible)
        (otherSamples.unit_inside otherPossible)).trans_eq (Norm.Basic.normSq_eq_canonical _))
  have normalSquare : SquareRootProvenance.SquareIdentity other.values.normalRoot.value
      (Clearance.normalizedRadicand site parameter (firstSegment.pointAt firstTime)) :=
    NamedEquivalent.transport rfl
      (congrArg Name.Basic.Named.exact
        (congrArg (Clearance.normalizedRadicand site parameter) point_eq.symm)) other.values.normalRoot.square
  let normalCompared := SquareRootChannelOwnership.equivalent_of_sum_lower first.values.normalRoot.square
    normalSquare ((1 / 4096) * Norm.Basic.normSq (halfGap site parameter))
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) anchor.gapNorm_positive) 0 0
    (fun firstIndex otherIndex _firstLater _otherLater => by
      have firstPossible := Process.Sampling.witnessAt_possible first.values.normalRoot.value.name.process
        first.values.normalRoot.value.name.state firstIndex
      have otherPossible := Process.Sampling.witnessAt_possible other.values.normalRoot.value.name.process
        other.values.normalRoot.value.name.state otherIndex
      exact (firstSamples.normal_sum_lower otherSamples point_eq firstPossible otherPossible).trans_eq
        (Norm.Basic.normSq_eq_canonical _))
  rewrite [first.values.value_eq, other.values.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    first.values.unitRoot.value other.values.unitRoot.value first.values.normalRoot.value other.values.normalRoot.value
    unitCompared normalCompared

end IndependentSources

end Reading.Comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
