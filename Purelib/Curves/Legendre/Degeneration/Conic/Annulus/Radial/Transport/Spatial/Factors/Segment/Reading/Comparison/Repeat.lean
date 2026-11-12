module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Comparison
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Repeat
import Purelib.Riemann.Topology.SquareRootContinuationChain.Exact.Transport
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Distance
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence

/-! # Signed full-cubic comparison at actual repeats of sufficiently fine Routes

Both original physical factor queries retain their separate quarter, Anchor,
seed, budget and preparation Owners. The literal Routes' actual visit/width
certificates pay the original neighboring seed-window sum floor. Existing
square comparison and cofactor reference laws derive full product agreement.
No key, sheet label, closed-loop return or matrix equality supplies the sign.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Comparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {firstReference firstTargetTime lastReference lastTargetTime : Fraction.Rational}
variable {firstReferenceInside : FixedRootBoxPath.Inside firstReference}
variable {firstTargetInside : FixedRootBoxPath.Inside firstTargetTime}
variable {lastReferenceInside : FixedRootBoxPath.Inside lastReference}
variable {lastTargetInside : FixedRootBoxPath.Inside lastTargetTime}
variable {firstSource : Transport.Reading firstActual firstReference firstReferenceInside}
variable {firstTarget : Transport.Reading firstActual firstTargetTime firstTargetInside}
variable {lastSource : Transport.Reading lastActual lastReference lastReferenceInside}
variable {lastTarget : Transport.Reading lastActual lastTargetTime lastTargetInside}
variable {firstAnchor : Parameter.Anchor firstSource.lift} {lastAnchor : Parameter.Anchor lastSource.lift}
variable {firstBudgets : Budgets firstAnchor} {lastBudgets : Budgets lastAnchor}
variable {firstPayment : (firstTargetTime - firstReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {lastPayment : (lastTargetTime - lastReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable (firstGeometry : Parallel.Geometry firstSource firstTarget firstAnchor.regular firstPayment)
variable (lastGeometry : Parallel.Geometry lastSource lastTarget lastAnchor.regular lastPayment)
variable {firstStart firstFinish lastStart lastFinish : Canonical}
variable {firstSegment : ClearSegment (Paths.polynomial parameter) (sourceBox firstAnchor) firstStart firstFinish}
variable {lastSegment : ClearSegment (Paths.polynomial parameter) (sourceBox lastAnchor) lastStart lastFinish}
variable {firstWithin : firstSegment.WithinAmbient} {lastWithin : lastSegment.WithinAmbient}
variable {firstCompleted : Segment firstBudgets firstSegment firstWithin}
variable {lastCompleted : Segment lastBudgets lastSegment lastWithin}
variable {firstTime lastTime : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside firstTime} {lastInside : FixedRootBoxPath.Inside lastTime}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- Cofactor queries from distinct original quarter references compare through their retained identical signed box. -/
def unit_owners_at_repeat (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent (ownerRootName first.unit.parameterNonzero first.unit)
      (ownerRootName last.unit.parameterNonzero last.unit) := by
  have boxes : firstActual.data.source.track.initial.box = lastActual.data.source.track.initial.box :=
    (congrArg (fun owner : Owner (UnitRoot.seed site ^ 2) => owner.track.initial.box)
      firstActual.data.source_eq).trans
        (congrArg (fun owner : Owner (UnitRoot.seed site ^ 2) => owner.track.initial.box)
          lastActual.data.source_eq).symm
  have lastRefines : last.unit.track.initial.box.Refines firstActual.data.source.track.initial.box := by
    rewrite [boxes]
    exact last.unit_refines
  have physical := firstSegment.pointAt_contains firstWithin firstTime firstInside
  have nonzero := firstBudgets.unit_nonzero physical
  have movement := firstBudgets.unit_movement physical
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  exact firstBudgets.unit.retainedOwnersEquivalentOfEq
    (congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq) nonzero movement
    first.unit last.unit first.unit_refines lastRefines

/-- Actual repeat geometry derives signed normalized-root agreement across both original source seed families.

Every actual sampled candidate stays in its own original seed square.
The original neighboring-window sum theorem consumes the internally derived
Route payment. The existing square comparator preserves both original
sampling starts and actual root processes without a common replacement Owner.
-/
def normal_at_repeat (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (firstVisit : firstGeometry.route.path.HalfOpen (firstSegment.pointAt firstTime))
    (lastVisit : lastGeometry.route.path.HalfOpen (lastSegment.pointAt lastTime))
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent first.values.normalRoot.value.name last.values.normalRoot.value.name := by
  have lastHere : lastGeometry.route.path.HalfOpen (firstSegment.pointAt firstTime) :=
    Eq.mpr (congrArg (fun point => lastGeometry.route.path.HalfOpen point) point_eq) lastVisit
  have near := Parallel.Geometry.source_ordinates_near_of_repeat
    (firstAnchor := firstAnchor) (lastAnchor := lastAnchor) firstGeometry lastGeometry
    firstWidth lastWidth (firstSegment.pointAt firstTime) firstVisit lastHere
  have lastSquare : SquareRootProvenance.SquareIdentity last.values.normalRoot.value
      (Clearance.normalizedRadicand site parameter (firstSegment.pointAt firstTime)) :=
    NamedEquivalent.transport rfl
      (congrArg Name.Basic.Named.exact (congrArg (Clearance.normalizedRadicand site parameter) point_eq.symm))
      last.values.normalRoot.square
  apply SquareRootProvenance.equivalent_of_sum_lower first.values.normalRoot.square lastSquare
    (firstAnchor.seed.separation.radius ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct firstAnchor.seed.separation.positive 2)
  intro firstIndex lastIndex
  have firstPossible := Process.Sampling.witnessAt_possible
    first.values.normalRoot.value.name.process first.values.normalRoot.value.name.state firstIndex
  have lastPossible := Process.Sampling.witnessAt_possible
    last.values.normalRoot.value.name.process last.values.normalRoot.value.name.state lastIndex
  have firstContained := firstAnchor.seed.retained_candidate_inside first.normal first.values.normalRoot
    first.values.normalRoot_eq first.normal_refines firstPossible
  have lastContained := lastAnchor.seed.retained_candidate_inside last.normal last.values.normalRoot
    last.values.normalRoot_eq last.normal_refines lastPossible
  have paid := firstAnchor.seed.separation.near_sum_normSq_lower lastAnchor.seed.separation near
    firstContained lastContained
  rewrite [Norm.Basic.normSq_eq_canonical] at paid
  exact paid

/-- The actual full-cubic product channels agree at a repeated point on sufficiently fine original Routes.

Both cofactor and normalized factors retain their original certificates,
processes and product caches. Their derived comparisons, not a coordinate or
sheet key, determine the signed full-cubic relation.
-/
def agree_at_repeat (first : Reading firstCompleted firstTime firstInside)
    (last : Reading lastCompleted lastTime lastInside)
    (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (firstVisit : firstGeometry.route.path.HalfOpen (firstSegment.pointAt firstTime))
    (lastVisit : lastGeometry.route.path.HalfOpen (lastSegment.pointAt lastTime))
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime) :
    NamedEquivalent first.values.value.name last.values.value.name := by
  have firstUnit : first.values.unitRoot.value.name = ownerRootName first.unit.parameterNonzero first.unit := by
    rewrite [first.values.unitRoot_eq]
    rfl
  have lastUnit : last.values.unitRoot.value.name = ownerRootName last.unit.parameterNonzero last.unit := by
    rewrite [last.values.unitRoot_eq]
    rfl
  have units := NamedEquivalent.transport firstUnit.symm lastUnit.symm (unit_owners_at_repeat first last point_eq)
  have normals := normal_at_repeat firstGeometry lastGeometry first last firstWidth lastWidth
    firstVisit lastVisit point_eq
  rewrite [first.values.value_eq, last.values.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    first.values.unitRoot.value last.values.unitRoot.value first.values.normalRoot.value last.values.normalRoot.value
    units normals

variable {firstUnit firstNormal lastUnit lastNormal : AccuracyRequest}

/-- Compare the two actual OLD full-product observations with both original states, requests and radii unchanged. -/
def compare_repeat_samples {first : Reading firstCompleted firstTime firstInside}
    {last : Reading lastCompleted lastTime lastInside}
    (firstSamples : Samples first firstUnit firstNormal) (lastSamples : Samples last lastUnit lastNormal)
    (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (firstVisit : firstGeometry.route.path.HalfOpen (firstSegment.pointAt firstTime))
    (lastVisit : lastGeometry.route.path.HalfOpen (lastSegment.pointAt lastTime))
    (point_eq : firstSegment.pointAt firstTime = lastSegment.pointAt lastTime)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    Equivalence.Observation.Comparison firstSamples.product lastSamples.product target :=
  Equivalence.Observation.Comparison.build firstSamples.product lastSamples.product
    (agree_at_repeat firstGeometry lastGeometry first last firstWidth lastWidth firstVisit lastVisit point_eq)
    target targetPositive

end Reading.Comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
