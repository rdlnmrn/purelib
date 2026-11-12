module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Point.Transport
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Endpoints
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source

/-! # Whole physical Points across original numerical source preparations

The same original prepared patch and physical fraction determine the whole
Point. Original endpoint factory laws and the strict-fraction acquisition
law preserve its actual owner across independent numerical Targets/floors.
Channel observations and their numerical accuracy remain separate caches.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point (Step)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

/-- Original preparations on the SAME patch retain the same whole Point at each fixed physical fraction.

Zero and one retain their actual endpoint Point factory results. Every
other fraction retains the identical original Point.acquire operation on
the same neighborhood and admission. No coordinate coincidence, sheet
label or numerical model accuracy identifies the two Point owners.
-/
theorem prepareParent_sampleAt_eq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (patch : PreparedPatch parent) (count firstFloor lastFloor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} (firstTargets : CellEndpoints.Targets firstPath firstStage)
    (lastTargets : CellEndpoints.Targets lastPath lastStage)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (prepareParent (frame := frame) patch count firstFloor covered firstTargets).sampleAt fraction inside =
      (prepareParent (frame := frame) patch count lastFloor covered lastTargets).sampleAt fraction inside := by
  by_cases atZero : fraction = 0
  · cases atZero
    have samples := (prepareParent_firstSample (frame := frame) patch count firstFloor covered firstTargets).trans
      (prepareParent_firstSample (frame := frame) patch count lastFloor covered lastTargets).symm
    have first := (prepareParent (frame := frame) patch count firstFloor covered firstTargets).sampleAt_zero inside
    have last := (prepareParent (frame := frame) patch count lastFloor covered lastTargets).sampleAt_zero inside
    exact first.trans
      ((congrArg (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count)
        (startPoint parent).coordinate => ContinuedNeighborhood.Point.castPoint parent.edge.point_zero sample)
        samples).trans last.symm)
  by_cases atOne : fraction = 1
  · cases atOne
    have samples := (prepareParent_lastSample (frame := frame) patch count firstFloor covered firstTargets).trans
      (prepareParent_lastSample (frame := frame) patch count lastFloor covered lastTargets).symm
    have first := (prepareParent (frame := frame) patch count firstFloor covered firstTargets).sampleAt_one inside
    have last := (prepareParent (frame := frame) patch count lastFloor covered lastTargets).sampleAt_one inside
    exact first.trans
      ((congrArg (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count)
        (finishPoint parent).coordinate => ContinuedNeighborhood.Point.castPoint parent.edge.point_one sample)
        samples).trans last.symm)
  have first := (prepareParent (frame := frame) patch count firstFloor covered firstTargets).sampleAt_strict
    inside atZero atOne
  have last := (prepareParent (frame := frame) patch count lastFloor covered lastTargets).sampleAt_strict
    inside atZero atOne
  exact first.trans last.symm

/-- Given actual preparation caches retain that SAME whole Point through their original factory identities.

Only the supplied whole cache equations and the original producer law are
consumed. Neither source preparation nor Point acquisition is executed by
this readback, and the distinct numerical observation caches are retained.
-/
theorem sampleAt_eq_of_factories
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)} {firstFloor lastFloor : Nat}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (first : PreparedParent patch count firstFloor covered firstTargets)
    (last : PreparedParent patch count lastFloor covered lastTargets)
    (firstFactory : first = prepareParent (frame := frame) patch count firstFloor covered firstTargets)
    (lastFactory : last = prepareParent (frame := frame) patch count lastFloor covered lastTargets)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    first.sampleAt fraction inside = last.sampleAt fraction inside :=
  (congrArg (fun prepared : PreparedParent patch count firstFloor covered firstTargets =>
    prepared.sampleAt fraction inside) firstFactory).trans
      ((prepareParent_sampleAt_eq (parameter := parameter) (frame := frame) (basis := basis)
        (parent := parent) patch count firstFloor lastFloor covered firstTargets lastTargets fraction inside).trans
        (congrArg (fun prepared : PreparedParent patch count lastFloor covered lastTargets =>
          prepared.sampleAt fraction inside) lastFactory).symm)

section QueryEndpoints

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage} (prepared : PreparedParent patch count floor covered targets)

/-- The actual source Cell's original factory retains the identical neighborhood count. -/
theorem queryCount_eq : prepared.preparation.cell.count = count :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) => cell.count)
    prepared.preparation.cell_eq

/-- The same whole Cell factory retains its original neighborhood heterogeneously. -/
theorem queryPatch_heq : HEq prepared.preparation.cell.patch (patch.neighborhood count) :=
  Eq.rec (motive := fun (cell : Cell (parameter := parameter) (liftedCell parent)) _ =>
    HEq prepared.preparation.cell.patch cell.patch) (HEq.rfl) prepared.preparation.cell_eq

/-- A retained zero query has the SAME whole original first Point through both actual acquisition factories.

The whole observer equation supplies its cached Point.acquire readback.
The Cell factory transports the nominal count and patch, the exact affine
zero law transports the point, and the given preparation factory supplies
the retained firstSample acquisition. No query or Point is executed here.
-/
theorem firstQuerySample_heq
    (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 0)
    (observed_eq : observed = prepared.preparation.query.observe frame 0 inside.1 inside.2) :
    HEq observed.retained.sample prepared.firstSample := by
  have retained := (congrArg (fun answer : CellModels.Observations frame (liftedCell parent)
    prepared.preparation.cell.models prepared.preparation.query.requests 0 => answer.retained.sample)
    observed_eq).trans (prepared.preparation.query.observe_sample frame 0 inside.1 inside.2)
  have original := ContinuedNeighborhood.Point.acquire_heq_of_eq
    prepared.queryCount_eq prepared.queryPatch_heq prepared.preparation.cell.models.coordinate.point_zero
    (prepared.preparation.cell.models.coordinate.point_inside prepared.preparation.cell.startInside
      prepared.preparation.cell.finishInside inside.1 inside.2) (start_inside patch count)
  have endpoint := (congrArg (fun kept : PreparedParent patch count floor covered targets => kept.firstSample)
    fromFactory).trans (prepareParent_firstSample (frame := frame) patch count floor covered targets)
  exact (heq_of_eq retained).trans (original.trans (heq_of_eq endpoint.symm))

/-- A retained unit query has the SAME independent original final Point through its two whole factory readbacks. -/
theorem lastQuerySample_heq
    (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 1)
    (observed_eq : observed = prepared.preparation.query.observe frame 1 inside.1 inside.2) :
    HEq observed.retained.sample prepared.lastSample := by
  have retained := (congrArg (fun answer : CellModels.Observations frame (liftedCell parent)
    prepared.preparation.cell.models prepared.preparation.query.requests 1 => answer.retained.sample)
    observed_eq).trans (prepared.preparation.query.observe_sample frame 1 inside.1 inside.2)
  have original := ContinuedNeighborhood.Point.acquire_heq_of_eq
    prepared.queryCount_eq prepared.queryPatch_heq prepared.preparation.cell.models.coordinate.point_one
    (prepared.preparation.cell.models.coordinate.point_inside prepared.preparation.cell.startInside
      prepared.preparation.cell.finishInside inside.1 inside.2) (finish_inside patch count covered)
  have endpoint := (congrArg (fun kept : PreparedParent patch count floor covered targets => kept.lastSample)
    fromFactory).trans (prepareParent_lastSample (frame := frame) patch count floor covered targets)
  exact (heq_of_eq retained).trans (original.trans (heq_of_eq endpoint.symm))

/-- View a supplied actual zero-query Step at its SAME retained original firstSample without new transport work. -/
def firstQueryStep
    (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 0)
    (observed_eq : observed = prepared.preparation.query.observe frame 0 inside.1 inside.2)
    {increment : Canonical} (step : Step observed.retained.sample increment) :
    { retained : Step prepared.firstSample increment //
      HEq retained step ∧ retained.root.value.name = step.root.value.name } :=
  let same := prepared.firstQuerySample_heq fromFactory inside observed observed_eq
  let point := prepared.preparation.cell.models.coordinate.point_zero
  let retained := Step.castSource (parameter := parameter) (increment := increment)
    (firstSource := observed.retained.sample) (lastSource := prepared.firstSample)
    prepared.queryCount_eq prepared.queryPatch_heq point same step
  ⟨retained,
    Step.castSource_heq (parameter := parameter) (increment := increment)
      (firstSource := observed.retained.sample) (lastSource := prepared.firstSample)
      prepared.queryCount_eq prepared.queryPatch_heq point same step,
    Step.castSource_name (parameter := parameter) (increment := increment)
      (firstSource := observed.retained.sample) (lastSource := prepared.firstSample)
      prepared.queryCount_eq prepared.queryPatch_heq point same step⟩

/-- View the supplied unit-query Step at the distinct original lastSample with its SAME complete Step and name. -/
def lastQueryStep
    (fromFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests 1)
    (observed_eq : observed = prepared.preparation.query.observe frame 1 inside.1 inside.2)
    {increment : Canonical} (step : Step observed.retained.sample increment) :
    { retained : Step prepared.lastSample increment //
      HEq retained step ∧ retained.root.value.name = step.root.value.name } :=
  let same := prepared.lastQuerySample_heq fromFactory inside observed observed_eq
  let point := prepared.preparation.cell.models.coordinate.point_one
  let retained := Step.castSource (parameter := parameter) (increment := increment)
    (firstSource := observed.retained.sample) (lastSource := prepared.lastSample)
    prepared.queryCount_eq prepared.queryPatch_heq point same step
  ⟨retained,
    Step.castSource_heq (parameter := parameter) (increment := increment)
      (firstSource := observed.retained.sample) (lastSource := prepared.lastSample)
      prepared.queryCount_eq prepared.queryPatch_heq point same step,
    Step.castSource_name (parameter := parameter) (increment := increment)
      (firstSource := observed.retained.sample) (lastSource := prepared.lastSample)
      prepared.queryCount_eq prepared.queryPatch_heq point same step⟩

end QueryEndpoints

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
