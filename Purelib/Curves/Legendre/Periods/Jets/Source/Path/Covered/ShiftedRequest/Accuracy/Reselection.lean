module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Nat.Order

/-! # Paid reselection against two fixed original programme families

Two actual six-channel comparison banks precede the two new Requests. Their
right indices determine the common starting stage. Their left indices give
all-later floors for the fixed reference samples in every channel.
Both geometries and the reference preparation families remain unchanged.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

section One

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {nonempty : geometry.parents ≠ []} {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (retained : Requested geometry nonempty current floor rootStage accuracy)

/-- The actual reference programme model is the identical typed modelAt on the same retained Request. -/
theorem programme_modelAt (channel : Fin 6) (stage : Nat) :
    (retained.request.programme channel).model stage = retained.modelAt channel stage :=
  retained.request.programme_model (parameter := parameter) (increment := increment) (basis := basis)
    (target := target) (count := count) (geometry := geometry) (index := retained.selected.stage)
    (floor := floor) (rootStage := rootStage) channel stage

/-- An actual original programme comparison pays this fresh selected model without changing either stage.

The supplied comparison has the reference programme and its unchanged
factory programme as owners. The fresh Request has the same geometry and
source floor; its original selected preparation factory derives the only
model identity needed here.
-/
theorem comparison_selected {referenceIndex referenceRootStage firstStart lastStart : Nat}
    (reference : Request geometry referenceIndex floor referenceRootStage)
    {comparisonAccuracy : AccuracyRequest} {channel : Fin 6}
    (compared : Comparison (reference.programme channel).approximation
      (reference.originalProgramme channel).approximation firstStart lastStart comparisonAccuracy.tolerance)
    {firstLater : Nat} (firstAfter : compared.leftIndex ≤ firstLater)
    (lastAfter : compared.rightIndex ≤ retained.selected.stage) :
    Norm.Basic.normSq (((reference.programme channel).model firstLater).integralSample -
      (retained.modelAt channel retained.selected.stage).integralSample) < comparisonAccuracy.tolerance := by
  have paid := reference.comparison_selected
    (parameter := parameter) (increment := increment) (basis := basis) (target := target)
    (count := count) (geometry := geometry) (index := referenceIndex) (floor := floor)
    (rootStage := referenceRootStage) (accuracy := comparisonAccuracy) (channel := channel)
    compared retained.request firstAfter lastAfter
  have scalar := congrArg (fun value : PathModel => value.integralSample)
    (retained.programme_modelAt channel retained.selected.stage)
  exact (congrArg (fun sample : Canonical => Norm.Basic.normSq
    (((reference.programme channel).model firstLater).integralSample - sample)) scalar).symm.trans_lt paid

end One

/-- Compare both fixed six-channel families before building one fresh Request pair.

The complete comparison banks precede both selections. Their right floors
choose the common starting stage; every channel then pays the same actual
fourth-order increment target. The continuation retains both banks, both
new Requests, their stage payments and all-later reference-model bounds.
The original shifted geometry and reference preparations remain inputs.
-/
def withReselectedPair
    {parameter firstOffset lastOffset : Canonical} {basis : Differential 1} {count : Nat}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstPoint lastPoint : LiftedPoint 2} {firstRoot lastRoot : Named}
    {firstGeometry : ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
      firstPoint firstPoint firstRoot firstRoot}
    {lastGeometry : ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
      lastPoint lastPoint lastRoot lastRoot}
    {firstNonempty : firstGeometry.parents ≠ []} {lastNonempty : lastGeometry.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstReference : Requested firstGeometry firstNonempty firstCurrent firstFloor firstRootStage firstAccuracy)
    (lastReference : Requested lastGeometry lastNonempty lastCurrent lastFloor lastRootStage lastAccuracy)
    (firstStart lastStart freshStart : Nat)
    (increment : Canonical) (nonzero : increment ≠ 0) (spatial : AccuracyRequest)
    {Result : Type u}
    (consume :
      (first : firstReference.request.Comparisons firstStart freshStart
        (Variation.Sampling.incrementRequest increment nonzero)) →
      (last : lastReference.request.Comparisons lastStart freshStart
        (Variation.Sampling.incrementRequest increment nonzero)) →
      (firstFresh : Requested firstGeometry firstNonempty
        (Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first)
          (Request.Comparisons.rightFloor last))) firstFloor firstRootStage
        (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))) →
      (lastFresh : Requested lastGeometry lastNonempty
        (Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first)
          (Request.Comparisons.rightFloor last))) lastFloor lastRootStage
        (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))) →
      (∀ channel, (first.get channel).rightIndex ≤ firstFresh.selected.stage) →
      (∀ channel, (last.get channel).rightIndex ≤ lastFresh.selected.stage) →
      (∀ channel index, Request.Comparisons.leftFloor first ≤ index →
        Norm.Basic.normSq (((firstReference.request.programme channel).model index).integralSample -
          (firstFresh.modelAt channel firstFresh.selected.stage).integralSample) <
            Norm.Basic.normSq increment ^ 2) →
      (∀ channel index, Request.Comparisons.leftFloor last ≤ index →
        Norm.Basic.normSq (((lastReference.request.programme channel).model index).integralSample -
          (lastFresh.modelAt channel lastFresh.selected.stage).integralSample) <
            Norm.Basic.normSq increment ^ 2) → Result) : Result :=
  let accuracy := Variation.Sampling.incrementRequest increment nonzero
  let first := Request.Comparisons.build (parameter := parameter) (increment := firstOffset)
    (basis := basis) (target := firstFrame) (count := count) (geometry := firstGeometry)
    (index := firstReference.selected.stage) (floor := firstFloor) (rootStage := firstRootStage)
    firstReference.request firstStart freshStart accuracy
  let last := Request.Comparisons.build (parameter := parameter) (increment := lastOffset)
    (basis := basis) (target := lastFrame) (count := count) (geometry := lastGeometry)
    (index := lastReference.selected.stage) (floor := lastFloor) (rootStage := lastRootStage)
    lastReference.request lastStart freshStart accuracy
  let start := Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first)
    (Request.Comparisons.rightFloor last))
  let firstFresh := build (parameter := parameter) (increment := firstOffset) (basis := basis)
    (target := firstFrame) (count := count) firstGeometry firstNonempty start firstFloor firstRootStage
    (spatial.minimum accuracy)
  let lastFresh := build (parameter := parameter) (increment := lastOffset) (basis := basis)
    (target := lastFrame) (count := count) lastGeometry lastNonempty start lastFloor lastRootStage
    (spatial.minimum accuracy)
  have firstRight (channel : Fin 6) : (first.get channel).rightIndex ≤ firstFresh.selected.stage :=
    (Request.Comparisons.right_le first channel).trans
      (((Order.le_max_left _ _).trans (Order.le_max_right _ _)).trans firstFresh.selected.lower)
  have lastRight (channel : Fin 6) : (last.get channel).rightIndex ≤ lastFresh.selected.stage :=
    (Request.Comparisons.right_le last channel).trans
      (((Order.le_max_right _ _).trans (Order.le_max_right _ _)).trans lastFresh.selected.lower)
  consume first last firstFresh lastFresh firstRight lastRight
    (fun channel _index after => firstFresh.comparison_selected
      (parameter := parameter) (increment := firstOffset) (basis := basis) (target := firstFrame)
      (count := count) (point := firstPoint) (root := firstRoot) (geometry := firstGeometry)
      (current := start) (floor := firstFloor) (rootStage := firstRootStage) (accuracy := spatial.minimum accuracy)
      (comparisonAccuracy := accuracy) (channel := channel) firstReference.request (first.get channel)
      ((Request.Comparisons.left_le first channel).trans after) (firstRight channel))
    (fun channel _index after => lastFresh.comparison_selected
      (parameter := parameter) (increment := lastOffset) (basis := basis) (target := lastFrame)
      (count := count) (point := lastPoint) (root := lastRoot) (geometry := lastGeometry)
      (current := start) (floor := lastFloor) (rootStage := lastRootStage) (accuracy := spatial.minimum accuracy)
      (comparisonAccuracy := accuracy) (channel := channel) lastReference.request (last.get channel)
      ((Request.Comparisons.left_le last channel).trans after) (lastRight channel))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

end
