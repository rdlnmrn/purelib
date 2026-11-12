module

import all Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Blocks
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Integration.Path.Primitive.Cells.Targets

/-! # One retained global source bank at the original covered-block boundaries

These actual constructions keep the original global centered chain and
its count-paid Targets. Every Source entry is acquired once globally;
all six row lists are read from that same retained source product.
-/

namespace TestPurelib.Curves.Legendre.SourceBlockRows

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Source.Cell (PreparedParents)
open Purelib.Riemann.Periods

variable {parameter : Canonical} {frame : Curves.Legendre.Paths.Frame parameter} {basis : Differential 1}
variable {sheet : Fin 2} {start finish : Canonical}
variable {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
variable {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
variable {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}

/-- Retain one actual global source acquisition and its six original block-row cell lists.

Both natural indices are chosen before preparation. One centered chain
and one global allocation precede one prepareCovered call. Splitting and
bounded channel lookup do not reacquire any source, point or model.
-/
def cachedBlocks (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame)
    basis sheet blocks) (floor stage : Nat) :
    Σ chain : {actual : Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain caches.parents
        (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) // actual = caches.centeredChain},
    Σ targets : {actual : CellEndpoints.Targets chain.val.path stage //
      actual = CellEndpoints.Targets.build chain.val.path stage},
    Σ prepared : {actual : PreparedParents (frame := frame) (basis := basis) (count := 1)
        (parents := caches.parents) caches.covered floor targets.val //
      actual = Source.Cell.prepareCovered caches.covered floor targets.val},
    Σ whole : {actual : Source.Path parameter chain.val.path //
      actual = PreparedParents.sources caches.covered prepared.val chain.val},
    {rows : List (DependentVector (fun _ : Fin 6 => List CellModel)) //
      rows = PreparedParents.blockRows caches prepared.val ∧
        ∀ channel : Fin 6, whole.val.cells channel = (rows.map (fun row => row.get channel)).flatten} :=
  PreparedParents.blockSources caches floor stage

/-- Delegating to the original library owner preserves the complete former construction for every supplied cache. -/
example (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame)
    basis sheet blocks) (floor stage : Nat) :
    cachedBlocks caches floor stage = (by
    let chain := caches.centeredChain
    let targets := CellEndpoints.Targets.build chain.path stage
    let prepared := Source.Cell.prepareCovered caches.covered floor targets
    let whole := PreparedParents.sources caches.covered prepared chain
    let rows := PreparedParents.blockRows caches prepared
    refine ⟨⟨chain, rfl⟩, ⟨targets, rfl⟩, ⟨prepared, rfl⟩, ⟨whole, rfl⟩, ⟨rows, rfl, ?_⟩⟩
    intro channel
    exact PreparedParents.sources_cells_blockRows caches prepared channel
) := rfl

/-- Retain actual model-wrapped programmes through pointwise source ownership rather than whole-function equality.

The supplied source family is shared by all six wrappers. The returned
table is the exact one passed to the ownership constructor; neither that
constructor nor its bounded readback re-prepares any source.
-/
private def wrappedProgrammes {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {first last : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    {allocationStart allocationFinish : LiftedPoint 2}
    (allocation : LiftedPath 2 allocationStart allocationFinish) (floor : Nat) :
    Σ values : Data.Vector RefinementProgram 6,
      {actual : PreparedParents.Programs covered chain // ∀ channel, actual.get channel = values channel} := by
  let saved := fun index => Source.Cell.prepareCovered covered floor (CellEndpoints.Targets.build allocation index)
  let original := fun channel => PreparedParents.program covered chain saved channel
  let models := fun channel index => PathModel.mk ((PreparedParents.sources covered (saved index) chain).cells channel)
  let wrapped := fun channel => (original channel).withModels (models channel)
    (fun index => congrArg PathModel.integralSample
      (PreparedParents.program_model covered chain saved channel index).symm)
    (fun index => (congrArg PathModel.aggregateAllowance
      (PreparedParents.program_model covered chain saved channel index).symm).trans_le
        ((original channel).modelAllowance_le index))
  let values := vectorOfFn wrapped
  have cells (channel : Fin 6) (index : Nat) :
      ((values channel).model index).cells = (PreparedParents.sources covered (saved index) chain).cells channel := by
    rewrite [vectorOfFn_apply, RefinementProgram.withModels_model]
    rfl
  have scales (channel : Fin 6) : (values channel).errorScale = PreparedParents.errorScale parents := by
    rewrite [vectorOfFn_apply]
    exact PreparedParents.program_errorScale covered chain saved channel
  exact ⟨values, PreparedParents.Programs.ofPrograms allocation floor saved values cells scales,
    PreparedParents.Programs.ofPrograms_get allocation floor saved values cells scales⟩

/-- Independently allocated model-wrapped blocks compare with the original whole programme across a stationary handoff.

The two moving paths keep distinct ambient boxes, original owner traces,
three allocation paths and three source floors. The original cache builder
supplies their physical parent lists; no sample inequality or equality of
allocation paths is an input to the construction.
-/
def independentBlocks {middle : Canonical} {firstAmbient lastAmbient : Geometry.Rational.Box}
    {firstPath : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial firstAmbient start middle}
    {lastPath : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial lastAmbient middle finish}
    (entered : CoveredTracedPath firstPath source) (join : Blocks.Join entered.traced.finishOwner)
    (following : CoveredTracedPath lastPath join.1)
    {wholeStart wholeFinish firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (wholeAllocation : LiftedPath 2 wholeStart wholeFinish)
    (firstAllocation : LiftedPath 2 firstStart firstFinish)
    (lastAllocation : LiftedPath 2 lastStart lastFinish) (wholeFloor firstFloor lastFloor : Nat) :
    let blocks := Blocks.cons entered (.handoff join (.cons following (.nil finish following.traced.finishOwner)))
    let caches := Blocks.ParentCaches.build (curve := Fibre.frameCurve frame) basis sheet blocks
    Σ whole : PreparedParents.Programs caches.covered caches.centeredChain,
    Σ actual : {retained : PreparedParents.BlockPrograms caches //
        (PreparedParents.BlockPrograms.values retained).length = 2},
      ∀ channel : Fin 6, NamedEquivalent (whole.get channel).output.name
        (PeriodMatrix.sumNamed (fun entry : Fin (PreparedParents.BlockPrograms.values actual.val).length =>
          (((PreparedParents.BlockPrograms.values actual.val)[entry.val]'entry.isLt) channel).output)).name := by
  intro blocks caches
  let whole := (wrappedProgrammes caches.covered caches.centeredChain wholeAllocation wholeFloor).2.val
  let earlier := (wrappedProgrammes caches.1.covered caches.1.centeredChain firstAllocation firstFloor).2.val
  let later := (wrappedProgrammes caches.2.1.covered caches.2.1.centeredChain lastAllocation lastFloor).2.val
  let actual : PreparedParents.BlockPrograms caches := ⟨earlier, later, PUnit.unit⟩
  exact ⟨whole, ⟨actual, rfl⟩, fun channel => PreparedParents.BlockPrograms.output_equivalent whole actual channel⟩

/-- The empty original block spine agrees with the existing empty named sum at every source floor. -/
def emptyBlocks (point : Canonical) (owner : Owner ((Fibre.frameCurve frame).polynomial.eval point))
    {allocationStart allocationFinish : LiftedPoint 2}
    (allocation : LiftedPath 2 allocationStart allocationFinish) (floor : Nat) :
    let caches := Blocks.ParentCaches.build (curve := Fibre.frameCurve frame) basis sheet (.nil point owner)
    Σ whole : PreparedParents.Programs caches.covered caches.centeredChain,
      ∀ channel : Fin 6, NamedEquivalent (whole.get channel).output.name
        (PeriodMatrix.sumNamed (fun index : Fin 0 => Fin.elim0 index)).name := by
  intro caches
  let whole := (wrappedProgrammes caches.covered caches.centeredChain allocation floor).2.val
  exact ⟨whole, fun channel => PreparedParents.BlockPrograms.output_equivalent whole PUnit.unit channel⟩

/-- Compare the actual six Stage-backed programmes with the original independently allocated block outputs.

The closed original block cache supplies its whole physical chain. Actual
source Stages and one retained preparation family determine the original
certified programmes, including an empty closed spine. The ownership view
keeps those complete values, and the comparison uses each supplied local
programme with its own allocation and floor without rebuilding it.
-/
def stagedBlocks {point : Canonical}
    {firstOwner lastOwner : Owner ((Fibre.frameCurve frame).polynomial.eval point)}
    {closedBlocks : Blocks (Fibre.frameCurve frame).polynomial point firstOwner point lastOwner}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet closedBlocks) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents caches.covered floor
      (CellEndpoints.Targets.build caches.centeredChain.path index))
    (stages : (index : Nat) → Source.Stage parameter ⟨⟨point, sheet⟩, caches.centeredChain.path⟩ index)
    (exactSources : ∀ index,
      (stages index).sources = PreparedParents.sources caches.covered (prepared index) caches.centeredChain)
    (actual : PreparedParents.BlockPrograms caches) :
    Σ values : Data.Vector RefinementProgram 6,
    Σ _whole : {retained : PreparedParents.Programs caches.covered caches.centeredChain //
        ∀ channel, retained.get channel = values channel},
      ∀ channel : Fin 6, NamedEquivalent (values channel).output.name
        (PeriodMatrix.sumNamed (fun entry : Fin (PreparedParents.BlockPrograms.values actual).length =>
          (((PreparedParents.BlockPrograms.values actual)[entry.val]'entry.isLt) channel).output)).name := by
  let values := vectorOfFn (fun channel : Fin 6 =>
    (PreparedParents.staged caches.covered caches.centeredChain prepared stages exactSources channel).integral)
  have cells (channel : Fin 6) (index : Nat) :
      ((values channel).model index).cells = (stages index).sources.cells channel := by
    rewrite [vectorOfFn_apply]
    exact PreparedParents.staged_cells caches.covered caches.centeredChain prepared stages exactSources channel index
  have scales (channel : Fin 6) : (values channel).errorScale = PreparedParents.errorScale caches.parents := by
    rewrite [vectorOfFn_apply]
    exact PreparedParents.staged_errorScale caches.covered caches.centeredChain prepared stages exactSources channel
  let whole := PreparedParents.Programs.ofStages caches.centeredChain caches.centeredChain.path floor
    prepared stages exactSources values cells scales
  have retained := PreparedParents.Programs.ofStages_get caches.centeredChain caches.centeredChain.path floor
    prepared stages exactSources values cells scales
  refine ⟨values, ⟨whole, retained⟩, ?_⟩
  intro channel
  let compared := PreparedParents.BlockPrograms.output_equivalent whole actual channel
  exact Eq.mp (congrArg (fun programme : RefinementProgram => NamedEquivalent programme.output.name
    (PeriodMatrix.sumNamed (fun entry : Fin (PreparedParents.BlockPrograms.values actual).length =>
      (((PreparedParents.BlockPrograms.values actual)[entry.val]'entry.isLt) channel).output)).name)
    (retained channel)) compared

end TestPurelib.Curves.Legendre.SourceBlockRows
