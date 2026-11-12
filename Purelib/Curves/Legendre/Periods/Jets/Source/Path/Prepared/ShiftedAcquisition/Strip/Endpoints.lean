module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Samples
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source

/-! # Actual time-section endpoint Steps and signed source-chain handoffs

Given original zero/unit observation bundles keep their whole factory
identities. The original advanceStripAt runs once on each supplied bundle;
exact Cell/Point factory transports view its SAME completed Step at the
original firstSample or lastSample. Adjacent and returning comparisons
then consume those actual views and the same closed source RootChain.
Repeated and stationary occurrences retain both independent endpoint slots.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

namespace PreparedParent

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage} (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (budget : FixedRootBoxBudget.Budget (patch.neighborhood count).base.seed.owner)
    (budget_eq : budget = range.seedBudget)

/-- The original first time-section cache and its exact original-endpoint Step view. -/
@[expose] def FirstStripEndpoint (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 0)
    (observed_eq : observed = prepared.preparation.query.observe frame 0 inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  (raw : StripStep prepared range budget budget_eq 0 inside observed observed_eq increment admitted time timeInside) ×
  { retained : Variation.Point.Step prepared.firstSample ((⟨time, 0⟩ : Canonical) * increment) //
    HEq retained raw.1.val ∧ retained.root.value.name = raw.1.val.root.value.name }

/-- Construct the first actual time-section once and retain its SAME Step at the original firstSample. -/
def firstStripAt (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 0)
    (observed_eq : observed = prepared.preparation.query.observe frame 0 inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    FirstStripEndpoint prepared range budget budget_eq inside observed observed_eq increment admitted time timeInside :=
  let raw := prepared.advanceStripAt range budget budget_eq 0 inside observed observed_eq
    increment admitted time timeInside
  let retained := prepared.firstQueryStep fromFactory inside observed observed_eq raw.1.val
  ⟨raw, retained⟩

/-- The original last time-section cache and its exact original-endpoint Step view. -/
@[expose] def LastStripEndpoint (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 1)
    (observed_eq : observed = prepared.preparation.query.observe frame 1 inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  (raw : StripStep prepared range budget budget_eq 1 inside observed observed_eq increment admitted time timeInside) ×
  { retained : Variation.Point.Step prepared.lastSample ((⟨time, 0⟩ : Canonical) * increment) //
    HEq retained raw.1.val ∧ retained.root.value.name = raw.1.val.root.value.name }

/-- Construct the last actual time-section once and retain its SAME Step at the original lastSample. -/
def lastStripAt (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 1)
    (observed_eq : observed = prepared.preparation.query.observe frame 1 inside.1 inside.2)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    LastStripEndpoint prepared range budget budget_eq inside observed observed_eq increment admitted time timeInside :=
  let raw := prepared.advanceStripAt range budget budget_eq 1 inside observed observed_eq
    increment admitted time timeInside
  let retained := prepared.lastQueryStep fromFactory inside observed observed_eq raw.1.val
  ⟨raw, retained⟩

end PreparedParent

namespace PreparedParents.ShiftedGeometry

/-- Construct both actual per-time endpoint caches and derive their signed adjacent handoff from the original chain.

Each supplied observation retains its original whole factory. One last
section and one first section execute, preserving their two raw caches and
original endpoint views. The same source RootChain and geometry derive the
comparison; no source observation or desired target relation is acquired.
-/
def adjacentAt {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {left right : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain (left :: right :: remaining) (start := start) (finish := finish))
    {first last : Named} (roots : RootChain (left :: right :: remaining) first last)
    {leftPatch : PreparedPatch left} {rightPatch : PreparedPatch right} {count floor : Nat}
    {leftCovered : (leftPatch.neighborhood count).box.Contains (left.edge.point 1)}
    {rightCovered : (rightPatch.neighborhood count).box.Contains (right.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage}
    (leftSource : PreparedParent leftPatch count floor leftCovered targets)
    (leftFactory : leftSource = prepareParent (frame := frame) leftPatch count floor leftCovered targets)
    (rightSource : PreparedParent rightPatch count floor rightCovered targets)
    (rightFactory : rightSource = prepareParent (frame := frame) rightPatch count floor rightCovered targets)
    (leftRange : Variation.Point.Range (leftPatch.neighborhood count))
    (rightRange : Variation.Point.Range (rightPatch.neighborhood count))
    (leftBudget : FixedRootBoxBudget.Budget (leftPatch.neighborhood count).base.seed.owner)
    (leftBudget_eq : leftBudget = leftRange.seedBudget)
    (rightBudget : FixedRootBoxBudget.Budget (rightPatch.neighborhood count).base.seed.owner)
    (rightBudget_eq : rightBudget = rightRange.seedBudget)
    (oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (leftObserved : CellModels.Observations frame (PreparedParent.liftedCell left)
      leftSource.preparation.cell.models leftSource.preparation.query.requests 1)
    (leftObserved_eq : leftObserved = leftSource.preparation.query.observe frame 1 oneInside.1 oneInside.2)
    (zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (rightObserved : CellModels.Observations frame (PreparedParent.liftedCell right)
      rightSource.preparation.cell.models rightSource.preparation.query.requests 0)
    (rightObserved_eq : rightObserved = rightSource.preparation.query.observe frame 0 zeroInside.1 zeroInside.2)
    (leftAdmitted : Norm.Basic.normSq increment ≤ leftRange.stripBound)
    (rightAdmitted : Norm.Basic.normSq increment ≤ rightRange.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    (left : PreparedParent.LastStripEndpoint leftSource leftRange leftBudget leftBudget_eq
      oneInside leftObserved leftObserved_eq increment leftAdmitted time timeInside) ×
    (right : PreparedParent.FirstStripEndpoint rightSource rightRange rightBudget rightBudget_eq
      zeroInside rightObserved rightObserved_eq increment rightAdmitted time timeInside) ×
    NamedEquivalent left.2.val.root.value.name right.2.val.root.value.name :=
  let left := leftSource.lastStripAt leftRange leftBudget leftBudget_eq leftFactory
    oneInside leftObserved leftObserved_eq increment leftAdmitted time timeInside
  let right := rightSource.firstStripAt rightRange rightBudget rightBudget_eq rightFactory
    zeroInside rightObserved rightObserved_eq increment rightAdmitted time timeInside
  let compared := adjacentSteps (parameter := parameter) (offset := (⟨time, 0⟩ : Canonical) * increment)
    (frame := frame) (basis := basis) chain roots leftSource rightSource left.2.val right.2.val
  ⟨left, right, compared⟩

/-- Construct the distinct last/first time-section caches and derive the original closed chain's actual signed return.

The literal prefix equality identifies the final occurrence. Repeated or
stationary parents keep both observation slots and both completed Steps.
The original return relation is derived through returningSteps and the
same whole RootChain; no closing comparison is an input.
-/
def returningAt {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {head final : CenteredEdge (Fibre.frameCurve frame) basis}
    {tail before : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (chain : CenteredPathChain (head :: tail)
      (start := PreparedParent.startPoint head) (finish := PreparedParent.startPoint head))
    (same : head :: tail = before ++ [final]) {root : Named} (roots : RootChain (head :: tail) root root)
    {firstPatch : PreparedPatch head} {finalPatch : PreparedPatch final} {count floor : Nat}
    {firstCovered : (firstPatch.neighborhood count).box.Contains (head.edge.point 1)}
    {finalCovered : (finalPatch.neighborhood count).box.Contains (final.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage}
    (firstSource : PreparedParent firstPatch count floor firstCovered targets)
    (firstFactory : firstSource = prepareParent (frame := frame) firstPatch count floor firstCovered targets)
    (finalSource : PreparedParent finalPatch count floor finalCovered targets)
    (finalFactory : finalSource = prepareParent (frame := frame) finalPatch count floor finalCovered targets)
    (firstRange : Variation.Point.Range (firstPatch.neighborhood count))
    (finalRange : Variation.Point.Range (finalPatch.neighborhood count))
    (firstBudget : FixedRootBoxBudget.Budget (firstPatch.neighborhood count).base.seed.owner)
    (firstBudget_eq : firstBudget = firstRange.seedBudget)
    (finalBudget : FixedRootBoxBudget.Budget (finalPatch.neighborhood count).base.seed.owner)
    (finalBudget_eq : finalBudget = finalRange.seedBudget)
    (zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (firstObserved : CellModels.Observations frame (PreparedParent.liftedCell head)
      firstSource.preparation.cell.models firstSource.preparation.query.requests 0)
    (firstObserved_eq : firstObserved = firstSource.preparation.query.observe frame 0 zeroInside.1 zeroInside.2)
    (oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (finalObserved : CellModels.Observations frame (PreparedParent.liftedCell final)
      finalSource.preparation.cell.models finalSource.preparation.query.requests 1)
    (finalObserved_eq : finalObserved = finalSource.preparation.query.observe frame 1 oneInside.1 oneInside.2)
    (firstAdmitted : Norm.Basic.normSq increment ≤ firstRange.stripBound)
    (finalAdmitted : Norm.Basic.normSq increment ≤ finalRange.stripBound)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    (last : PreparedParent.LastStripEndpoint finalSource finalRange finalBudget finalBudget_eq
      oneInside finalObserved finalObserved_eq increment finalAdmitted time timeInside) ×
    (first : PreparedParent.FirstStripEndpoint firstSource firstRange firstBudget firstBudget_eq
      zeroInside firstObserved firstObserved_eq increment firstAdmitted time timeInside) ×
    NamedEquivalent last.2.val.root.value.name first.2.val.root.value.name :=
  let last := finalSource.lastStripAt finalRange finalBudget finalBudget_eq finalFactory
    oneInside finalObserved finalObserved_eq increment finalAdmitted time timeInside
  let first := firstSource.firstStripAt firstRange firstBudget firstBudget_eq firstFactory
    zeroInside firstObserved firstObserved_eq increment firstAdmitted time timeInside
  let compared := returningSteps (parameter := parameter) (offset := (⟨time, 0⟩ : Canonical) * increment)
    (frame := frame) (basis := basis) chain same roots firstSource finalSource last.2.val first.2.val
  ⟨last, first, compared⟩

end PreparedParents.ShiftedGeometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
