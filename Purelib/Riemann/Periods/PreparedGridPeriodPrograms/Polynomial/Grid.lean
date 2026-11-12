module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Models
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
public import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Riemann.Periods.StandardPeriodGridLines
public import Purelib.Riemann.Periods.StandardPeriodAmbient
public import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Polynomial.Geometry.Grid.Extension
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Actual current-grid fragments of an original polynomial period

The retained initial spine and request supply genuine parent support,
root closure and covering patches. The original splitting/sheet producers
place that SAME request on its actual current grid before a numerical bank
is selected. Neither an identity refinement nor an independent cycle/owner
relation is an input.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
  (PrimitiveAxes SplitPrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources
  (Rooted)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (allParentsProper_map_recast)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (SwitchedPathChain)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation
  (prepared_endpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (ParentCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    (lifted : LiftedPuncturedGrid framed) (vertex : Fin lifted.vertices.count) {source : Differential 1}
    (walk : PeriodWalk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.owner lifted.frames vertex) source)
    (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk)

/-- The actual cached initial parents keep their original strict parameter ordering under differential recast. -/
theorem parents_proper : AllParentsProper spine.parents :=
  Eq.mpr (congrArg AllParentsProper spine.parents_eq)
    (allParentsProper_map_recast walk.initial.state.proper)

/-- The actual initial polynomial parents lie on their SAME retained grid lines.

The original prepared path and actual vertex bank give line membership.
No face clearance is promoted to clearance of an ambient line.
-/
theorem onLines : StandardPeriodGridLines.Grid.ParentsOnLines framed.bank.grid spine.parents := by
  apply Eq.mpr (congrArg (StandardPeriodGridLines.Grid.ParentsOnLines framed.bank.grid) spine.parents_eq)
  apply StandardPeriodGridLines.Grid.ParentsOnLines.recast
  rewrite [walk.initial_eq, RootClosedWalk.initial_parents]
  exact StandardPeriodGridLines.Grid.prepared_onLines framed.bank.grid source 0 walk.closed.traced.prepared
    (walk.closed.walk.vertices (lifted.vertices.coordinate_onGrid vertex))

/-- Both actual initial-parent endpoints remain in the original curve ambient under whole parent-list transport. -/
theorem endpoints : EndpointsIn
    (Ambient (Fibre.frameCurve frame)) spine.parents := by
  apply Eq.mpr (congrArg
    (EndpointsIn (Ambient (Fibre.frameCurve frame)))
    spine.parents_eq)
  apply StandardPeriodAmbient.EndpointsIn.recast
  rewrite [walk.initial_eq, RootClosedWalk.initial_parents]
  exact prepared_endpoints
    (Fibre.frameCurve frame) source 0 walk.closed.traced.prepared

/-- The literal cached initial parent word consists of original directed sources for the SAME complete grid walk. -/
theorem pathSources : PathSources 0 walk.closed.walk.path spine.parents := by
  have original : PathSources 0 walk.closed.walk.path walk.initial.state.parents := by
    rewrite [walk.initial_eq, RootClosedWalk.initial_parents]
    exact PathSources.ofPreparedPath source 0 walk.closed.traced.prepared
  exact Eq.mpr (congrArg (PathSources 0 walk.closed.walk.path) spine.parents_eq)
    (original.recast (PeriodMatrix.standardDifferential (0 : Fin 1)))

/-- The whole original initial lifted base equals its actual retained vertex and local chart sheet. -/
theorem initial_start : walk.initial.state.start = (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2) := by
  have stored := congrArg (fun current => current.state.start) (walk.state_eq 0)
  have preserved := RootClosedState.states_start_eq walk.initial (standardDifferentials 1) 0
  exact (stored.trans preserved).symm.trans (walk.state_base 0)

/-- Reindex the SAME cached centered chain at its actual original vertex, preserving the full lifted endpoint. -/
def vertexChain : CenteredPathChain spine.parents
    (start := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
    (finish := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)) :=
  (spine.chain.castStart (initial_start lifted vertex walk)).castFinish (initial_start lifted vertex walk)

/-- Read the coordinate chain of the SAME cached parents from their whole centered chain. -/
theorem coordinates : ParentCoordinates spine.parents
    (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate vertex) :=
  ParentCoordinates.ofSwitched (SwitchedPathChain.ofCenteredPathChain (vertexChain lifted vertex walk spine))

variable {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    (selection : PrimitiveSelection walk sourceStart periodStart tolerance positive)
    (domains : FaceDomainBank lifted.frames framed.faces.regulars)

/-- The exact given grid, cycle, initial spine, request selection and domain payload. -/
@[expose] def GridFragments.InputData : Type _ :=
  LiftedPuncturedGrid framed × Fin lifted.vertices.count ×
      PeriodWalk framed.bank.grid (lifted.vertices.coordinate vertex)
        (lifted.vertices.owner lifted.frames vertex) source ×
      PolynomialSpine walk × PrimitiveSelection walk sourceStart periodStart tolerance positive ×
      FaceDomainBank lifted.frames framed.faces.regulars

/-- The complete original period/grid/request inputs retained before any fragment or numerical-bank preparation. -/
@[expose] def GridFragments.Inputs : Type _ :=
  {inputs : GridFragments.InputData (lifted := lifted) (vertex := vertex) (walk := walk)
      (sourceStart := sourceStart) (periodStart := periodStart) (tolerance := tolerance) (positive := positive) //
    inputs = (lifted, vertex, walk, spine, selection, domains)}

/-- The exact original signed root cache, kept apart from physical word preparation. -/
@[expose] def GridFragments.RootCache : Type _ :=
  {value : RootChain spine.parents
      (ownerName (lifted.vertices.owner lifted.frames vertex))
      (ownerName (lifted.vertices.owner lifted.frames vertex)) // value = spine.roots}

/-- Read the same retained signed root chain without unfolding its factory. -/
@[expose] def GridFragments.RootCache.roots
    (retained : GridFragments.RootCache (lifted := lifted) (vertex := vertex) (walk := walk) (spine := spine)) :
    RootChain spine.parents
      (ownerName (lifted.vertices.owner lifted.frames vertex))
      (ownerName (lifted.vertices.owner lifted.frames vertex)) := retained.val

/-- The exact physical fragment execution indexed by the same original signed roots. -/
@[expose] def GridFragments.Execution (roots : RootChain spine.parents
      (ownerName (lifted.vertices.owner lifted.frames vertex))
      (ownerName (lifted.vertices.owner lifted.frames vertex))) : Type _ :=
  Σ _geometry : {value : CenteredPathChain spine.parents
      (start := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
      (finish := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)) //
    value = vertexChain lifted vertex walk spine},
  Σ request : {value : ControlledSumRequest spine.parents 1 (tolerance / 64) //
    value = ControlledSumRequest.castParents selection.1.val spine.parents_eq.symm ∧ HEq value selection.1.val},
  Σ axes : {value : PrimitiveAxes framed.bank.grid // value = PrimitiveAxes.build framed.bank.grid},
  Σ split : {value : SplitPrimitiveRequest axes.val request.val //
    value = SplitPrimitiveRequest.build axes.val request.val},
  Σ located : {value : LocatedPrimitiveSplits axes.val split.val.splits //
    value = LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
      (fun _ present => StandardPeriodAmbient.EndpointsIn.member (endpoints lifted vertex walk spine) present)},
  Σ cells : {value : RegularPrimitiveSplits (base := framed) axes.val split.val.splits //
    value = RegularPrimitiveSplits.build located.val (onLines lifted vertex walk spine)},
  Σ entries : {value : Fragment.SplitSheets domains cells.val request.val.requests //
    value = Fragment.SplitSheets.build domains cells.val request.val.requests},
  Σ _points : {value : List Canonical //
    value = Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries.val},
  Σ sources : {value : LiftedSources lifted.mesh entries.val //
    value = LiftedSources.build lifted.mesh entries.val},
  {value : Rooted entries.val lifted.mesh
      (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex))
      (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex)) //
    value = Rooted.build sources.val (coordinates lifted vertex walk spine) roots}

attribute [local irreducible] GridFragments.InputData GridFragments.Inputs
  GridFragments.RootCache GridFragments.Execution in
set_option genInjectivity false in
/-- The actual current-grid physical fragment preparation of one retained initial polynomial spine.

The original request, roots, centered chain, partitions, sheet entries,
point list and lifted sources are cached with complete producer equations.
No numerical bank has been selected. Repeated and stationary occurrences
remain in their actual ordered request and sheet spines.
-/
structure GridFragments : Type _ where
  /-- The same given grid, cycle, spine, request selection and domains with their whole factory. -/
  inputCache : GridFragments.Inputs lifted vertex walk spine selection domains
  /-- The original complete signed root chain and its exact spine factory. -/
  rootData : GridFragments.RootCache (lifted := lifted) (vertex := vertex) (walk := walk) (spine := spine)
  /-- The original once-materialized physical fragments on the retained roots. -/
  execution : GridFragments.Execution (lifted := lifted) (vertex := vertex) (walk := walk) (spine := spine)
    (selection := selection) (domains := domains) rootData.roots

attribute [local irreducible] GridFragments.InputData GridFragments.Inputs GridFragments.Execution in
constructive_injectivity GridFragments

/-- Prepare the actual fresh fragment geometry once, before selecting a point bank or any new P observations.

The selected old request is transported whole to its SAME cached parent
list. Every original fragment constructor consumes the immediately
preceding stored cache. The old request primitive remains unchanged;
no full-numerator accuracy is inferred from its holomorphic readings.
-/
def gridFragments : GridFragments lifted vertex walk spine selection domains :=
  let inputs : GridFragments.Inputs lifted vertex walk spine selection domains :=
    ⟨(lifted, vertex, walk, spine, selection, domains), rfl⟩
  let roots : {value : RootChain spine.parents
      (ownerName (lifted.vertices.owner lifted.frames vertex))
      (ownerName (lifted.vertices.owner lifted.frames vertex)) // value = spine.roots} := ⟨spine.roots, rfl⟩
  let geometry : {value : CenteredPathChain spine.parents
      (start := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
      (finish := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)) //
      value = vertexChain lifted vertex walk spine} := ⟨vertexChain lifted vertex walk spine, rfl⟩
  let request : {value : ControlledSumRequest spine.parents 1 (tolerance / 64) //
      value = ControlledSumRequest.castParents selection.1.val spine.parents_eq.symm ∧ HEq value selection.1.val} :=
    ⟨ControlledSumRequest.castParents selection.1.val spine.parents_eq.symm, rfl,
      ControlledSumRequest.castParents_heq selection.1.val spine.parents_eq.symm⟩
  let axes : {value : PrimitiveAxes framed.bank.grid // value = PrimitiveAxes.build framed.bank.grid} :=
    ⟨PrimitiveAxes.build framed.bank.grid, rfl⟩
  let split : {value : SplitPrimitiveRequest axes.val request.val //
      value = SplitPrimitiveRequest.build axes.val request.val} :=
    ⟨SplitPrimitiveRequest.build axes.val request.val, rfl⟩
  let located : {value : LocatedPrimitiveSplits axes.val split.val.splits //
      value = LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
        (fun _ present => StandardPeriodAmbient.EndpointsIn.member (endpoints lifted vertex walk spine) present)} :=
    ⟨LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
      (fun _ present => StandardPeriodAmbient.EndpointsIn.member (endpoints lifted vertex walk spine) present), rfl⟩
  let cells : {value : RegularPrimitiveSplits (base := framed) axes.val split.val.splits //
      value = RegularPrimitiveSplits.build located.val (onLines lifted vertex walk spine)} :=
    ⟨RegularPrimitiveSplits.build located.val (onLines lifted vertex walk spine), rfl⟩
  let entries : {value : Fragment.SplitSheets domains cells.val request.val.requests //
      value = Fragment.SplitSheets.build domains cells.val request.val.requests} :=
    ⟨Fragment.SplitSheets.build domains cells.val request.val.requests, rfl⟩
  let points : {value : List Canonical //
      value = Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries.val} :=
    ⟨Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries.val, rfl⟩
  let sources : {value : LiftedSources lifted.mesh entries.val //
      value = LiftedSources.build lifted.mesh entries.val} := ⟨LiftedSources.build lifted.mesh entries.val, rfl⟩
  let rooted : {value : Rooted entries.val lifted.mesh
      (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex))
      (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex)) //
      value = Rooted.build sources.val (coordinates lifted vertex walk spine) roots.val} :=
    ⟨Rooted.build sources.val (coordinates lifted vertex walk spine) roots.val, rfl⟩
  { inputCache := inputs
    rootData := roots
    execution := ⟨geometry, request, axes, split, located, cells, entries, points, sources, rooted⟩ }

namespace GridFragments

variable {lifted vertex walk spine selection domains}
    (kept : GridFragments lifted vertex walk spine selection domains)

/-- Read the complete original retained grid, cycle, spine, request selection and domain owners. -/
@[expose] def inputs : GridFragments.InputData (lifted := lifted) (vertex := vertex) (walk := walk)
    (sourceStart := sourceStart) (periodStart := periodStart) (tolerance := tolerance) (positive := positive) :=
      kept.inputCache.val

/-- The stored complete input product is exactly the given original product. -/
theorem inputs_eq : kept.inputs = (lifted, vertex, walk, spine, selection, domains) := kept.inputCache.property

/-- Read the genuine cached root closure on these same parents. -/
@[expose] def roots : RootChain spine.parents
      (ownerName (lifted.vertices.owner lifted.frames vertex))
      (ownerName (lifted.vertices.owner lifted.frames vertex)) := kept.rootData.val

/-- The root chain is the actual original recast operation on the cached spine. -/
theorem roots_eq : kept.roots = spine.roots := kept.rootData.property

/-- Read the SAME cached centered chain with its whole original lifted endpoint transport. -/
@[expose] def geometry : CenteredPathChain spine.parents
    (start := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2))
    (finish := (⟨lifted.vertices.coordinate vertex, 0⟩ : LiftedPoint 2)) := kept.execution.1.val

/-- The centered chain retains the exact original whole endpoint reindexing. -/
theorem geometry_eq : kept.geometry = vertexChain lifted vertex walk spine := kept.execution.1.property

/-- Read the complete original selected request after its cached-parent index transport. -/
@[expose] def request : ControlledSumRequest spine.parents 1 (tolerance / 64) := kept.execution.2.1.val

/-- The request retains the whole original equality-elimination factory. -/
theorem request_eq : kept.request = ControlledSumRequest.castParents selection.1.val spine.parents_eq.symm :=
  kept.execution.2.1.property.1

/-- Both nominal request values are the SAME complete observation cache under the parent equality. -/
theorem request_heq : HEq kept.request selection.1.val := kept.execution.2.1.property.2

/-- Read the retained original grid-axis cache. -/
@[expose] def axes : PrimitiveAxes framed.bank.grid := kept.execution.2.2.1.val

/-- The axes retain the actual original grid factory. -/
theorem axes_eq : kept.axes = PrimitiveAxes.build framed.bank.grid := kept.execution.2.2.1.property

/-- Read the actual ordered parameter partitions and original request increments. -/
@[expose] def split : SplitPrimitiveRequest kept.axes kept.request := kept.execution.2.2.2.1.val

/-- The complete ordered split retains its original given-request factory. -/
theorem split_eq : kept.split = SplitPrimitiveRequest.build kept.axes kept.request := kept.execution.2.2.2.1.property

/-- Read the actual original retained fragment locations. -/
@[expose] def located : LocatedPrimitiveSplits kept.axes kept.split.splits := kept.execution.2.2.2.2.1.val

/-- Read the actual original regular-face assignments of those same fragment locations. -/
@[expose] def cells : RegularPrimitiveSplits (base := framed) kept.axes kept.split.splits :=
  kept.execution.2.2.2.2.2.1.val

/-- Read the actual parent-indexed sheet entries, including their independent incoming Point comparisons. -/
@[expose] def entries : Fragment.SplitSheets domains kept.cells kept.request.requests :=
  kept.execution.2.2.2.2.2.2.1.val

/-- Read the literal fresh endpoint list before any numerical bank is acquired. -/
@[expose] def points : List Canonical := kept.execution.2.2.2.2.2.2.2.1.val

/-- The fresh points come from the whole exact original retained sheet-entry list. -/
theorem points_eq : kept.points = Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points kept.entries :=
  kept.execution.2.2.2.2.2.2.2.1.property

/-- Read the original lifted partial-edge source occurrences on the supplied current mesh. -/
@[expose] def sources : LiftedSources lifted.mesh kept.entries := kept.execution.2.2.2.2.2.2.2.2.1.val

/-- The lifted source cache retains its complete original given-sheet factory. -/
theorem sources_eq : kept.sources = LiftedSources.build lifted.mesh kept.entries :=
  kept.execution.2.2.2.2.2.2.2.2.1.property

/-- Read the actual cached rooted fragment word, preserving both literal closing names. -/
@[expose] def rooted : Rooted kept.entries lifted.mesh
    (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex))
    (lifted.vertices.coordinate vertex) (ownerName (lifted.vertices.owner lifted.frames vertex)) :=
      kept.execution.2.2.2.2.2.2.2.2.2.val

/-- The whole rooted word retains its actual source/coordinate/root factory. -/
theorem rooted_eq : kept.rooted = Rooted.build kept.sources (coordinates lifted vertex walk spine) kept.roots :=
  kept.execution.2.2.2.2.2.2.2.2.2.property

/-- The retained rooted-word factory forwards the SAME actual lifted-source cache. -/
theorem rooted_sources : kept.rooted.sources = kept.sources :=
  congrArg (fun actual => actual.sources) kept.rooted_eq

/-- The complete cached piece list is the literal flattening of those same stored lifted sources. -/
theorem rooted_pieces : kept.rooted.pieces = SheetEntries.LiftedSources.pieces kept.sources :=
  kept.rooted.pieces_eq.trans (congrArg SheetEntries.LiftedSources.pieces kept.rooted_sources)

/-- The complete physical request cover is the SAME old selected cover under its whole parent-list transport. -/
theorem request_covered : kept.request.requests.covered =
    selection.1.val.requests.covered.castParents spine.parents_eq.symm :=
  (congrArg (fun actual : ControlledSumRequest spine.parents 1 (tolerance / 64) => actual.requests.covered)
    kept.request_eq).trans (ControlledSumRequest.castParents_covered selection.1.val spine.parents_eq.symm)

/-- The whole request transport preserves its actual original primitive sum, including all constants. -/
theorem request_primitiveSum : kept.request.primitiveSum = selection.1.val.primitiveSum :=
  (congrArg (fun actual : ControlledSumRequest spine.parents 1 (tolerance / 64) => actual.primitiveSum)
    kept.request_eq).trans (ControlledSumRequest.castParents_primitiveSum selection.1.val spine.parents_eq.symm)

/-- Jointly view the GIVEN original comparison Work and Models on the actual cached physical request cover.

The two original whole-cover transports consume only the retained parent
and request factories. Their complete Work and Models values stay the
same heterogeneously; no polynomial, source, request or query factory is
executed to recover data.
-/
def withModels {floor stage : Nat} {differential : OddPowerDifferential (Fibre.frameCurve frame).polynomial}
    (work : PolynomialWork selection.1.val.requests.covered floor differential) (models : work.Models stage)
    {Result : Sort u}
    (consume : (viewedWork : PolynomialWork kept.request.requests.covered floor differential) →
      HEq viewedWork work → (viewedModels : viewedWork.Models stage) → HEq viewedModels models →
      (PathModel.mk (PolynomialWork.Models.cells kept.request.requests.covered
        viewedWork viewedModels)).integralSample =
        (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample →
      Result) : Result :=
  PolynomialWork.Models.withParents spine.parents_eq.symm selection.1.val.requests.covered work models
    (fun _viewedCover coverEq _coverHEq viewedWork workHEq viewedModels modelsHEq integralEq =>
      let sameCover := coverEq.trans kept.request_covered.symm
      PolynomialWork.Models.withCovered sameCover viewedWork viewedModels
        (fun actualWork actualWorkHEq actualModels actualModelsHEq actualIntegralEq =>
          consume actualWork (actualWorkHEq.trans workHEq) actualModels (actualModelsHEq.trans modelsHEq)
            (actualIntegralEq.trans integralEq)))

end GridFragments

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
