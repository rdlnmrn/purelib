module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
public import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
public import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Integration.PreparedEdgeRecasting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Tactic.QuotientFreeOmega

/-!
# Retained programs for the actual lifted exterior tours

Degree parity selects the existing two-lap or one-lap grid walks. The initial
owner is read from the shared grid frame, and the prepared trace proves its
operational return. All later parent consumers reuse this period's cache.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Winding
open Purelib.Riemann
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Paths.PreparedExteriorPathGeometry
open Purelib.Riemann.Paths.PreparedExteriorPathGeometry.Grid
open Purelib.Riemann.Paths.PreparedPathParentCaches
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels
open Purelib.Riemann.Paths.PreparedPathWinding
open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ClearPath (OnBoxSides)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- The existing exterior walk, with the actual required number of laps.

An odd-degree curve traverses the retained exterior twice; an even-degree curve traverses it once. Both choices use the
same original boundary walk. -/
@[expose] def exteriorWalk (base : Meshes.FramedPuncturedGrid curve branches higher) :
    Walks.Walk base.bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor :=
  match curve.degreeShape with
  | .odd _ => base.bank.exterior.append base.bank.exterior
  | .even _ => base.bank.exterior

/-- Every original parity-selected exterior tour segment lies on the retained ambient box sides.

Each retained lap lies on the same ambient sides. Concatenating the two odd-degree laps preserves that geometric
certificate. -/
theorem exteriorWalk_sides (base : Meshes.FramedPuncturedGrid curve branches higher) :
    ClearPath.OnBoxSides (Cuts.Ambient curve) (PeriodPrograms.exteriorWalk base).path := by
  cases shape : curve.degreeShape with
  | odd _ =>
      simp only [PeriodPrograms.exteriorWalk, shape]
      exact Walk.onBoxSides_append _ _ (AmbientFrame.boundary_onBoxSides base.bank.frame)
        (AmbientFrame.boundary_onBoxSides base.bank.frame)
  | even _ =>
      simp only [PeriodPrograms.exteriorWalk, shape]
      exact AmbientFrame.boundary_onBoxSides base.bank.frame

/-- The retained exterior tour has raw winding divisible by eight and therefore closes its original root sheet.

The parity-selected lap count cancels the original degree contribution modulo eight, so the endpoint keeps its original
root sheet. -/
theorem exteriorWalk_even (base : Meshes.FramedPuncturedGrid curve branches higher) :
    ClearPath.rawWinding (PeriodPrograms.exteriorWalk base).path =
      8 * (ClearPath.rawWinding (PeriodPrograms.exteriorWalk base).path / 8) := by
  have winding := base.bank.exterior_winding
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [PeriodPrograms.exteriorWalk, shape, Walk.append_winding, winding]
      omega
  | even degree =>
      simp only [PeriodPrograms.exteriorWalk, shape, winding]
      omega

/-- Read the original shared-grid root owner at the ambient anchor on the retained sheet. -/
@[expose] def exteriorOwner (lifted : Meshes.LiftedPuncturedGrid base) (sheet : Fin 2) :
    SquareRootContinuationChain.Owner (curve.polynomial.eval (Cuts.Ambient curve).anchor) :=
  (lifted.frames.frameAt _ ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩).owners sheet

set_option genInjectivity false in
/-- A period cache tied to the same grid tour and original shared owner.

The sheet and closed period retain their original grid, differential and tour equation. -/
structure ExteriorProgram (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus)
  where
  /-- The original retained sheet on which this exterior period starts. -/ sheet : Fin 2
  /-- The cached actual exterior period program with its original grid owner and differential. -/ period :
    PreparedGridPeriodPrograms.PeriodWalk base.bank.grid (Cuts.Ambient curve).anchor (PeriodPrograms.exteriorOwner
    lifted sheet) source
  /-- The cached period walk is exactly the original parity-selected exterior tour. -/ walk_eq : period.closed.walk =
    (PeriodPrograms.exteriorWalk base)

constructive_injectivity ExteriorProgram

namespace ExteriorProgram

/-- Retain a supplied checked preparation, including its original endpoint owner. The winding proof closes that exact
trace.

The supplied traced path and primitive cover are cached directly. Its winding equation identifies the final root with
the original shared sheet owner. -/
@[expose] def ofCovered (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus)
  (sheet : Fin 2)
    (covered : PreparedClearPathModels.CoveredTracedPath (PeriodPrograms.exteriorWalk base).path
      (PeriodPrograms.exteriorOwner lifted sheet)) : PeriodPrograms.ExteriorProgram lifted source :=
  let reference := (BranchCellBank.referenceAt base.bank.toBranchCellBank _ ⟨base.bank.frame.xLower,
    base.bank.frame.yLower⟩).toLoop
  let closed : Grid.RootClosedWalk base.bank.grid (Cuts.Ambient curve).anchor (PeriodPrograms.exteriorOwner lifted
    sheet) :=
    ⟨(PeriodPrograms.exteriorWalk base), covered.traced, covered.cover, OwnerTraceReadings.ownerName
      (PeriodPrograms.exteriorOwner lifted sheet), OwnerTraceReadings.ownerName covered.traced.finishOwner,
      rfl, rfl, OwnerPath.rootEquivalent_of_even_with_reference reference covered.traced.trace.get
        (ClearPath.rawWinding (PeriodPrograms.exteriorWalk base).path / 8)
        ((TracedPath.winding_original covered.traced).trans (PeriodPrograms.exteriorWalk_even base))⟩
  ⟨sheet, PeriodWalk.ofClosed closed source, rfl⟩

/-- Prepare and retain the actual exterior period from the original shared owner on the requested sheet.

The preparation follows the parity-selected exterior walk from the retained anchor owner, then caches its exact closed
period. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus) (sheet
  : Fin 2) : PeriodPrograms.ExteriorProgram lifted source :=
  PeriodPrograms.ExteriorProgram.ofCovered lifted source sheet (CoveredTracedPath.build (PeriodPrograms.exteriorWalk
    base).path (PeriodPrograms.exteriorWalk base).withinAmbient (PeriodPrograms.exteriorOwner lifted sheet))

/-- Preparing an exterior period preserves its original requested sheet. -/
theorem build_sheet (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus) (sheet
  : Fin 2) :
    (PeriodPrograms.ExteriorProgram.build lifted source sheet).sheet = sheet := by
  change (PeriodPrograms.ExteriorProgram.ofCovered lifted source sheet
    (CoveredTracedPath.build (PeriodPrograms.exteriorWalk base).path (PeriodPrograms.exteriorWalk base).withinAmbient
      (PeriodPrograms.exteriorOwner lifted sheet))).sheet = sheet
  unfold PeriodPrograms.ExteriorProgram.ofCovered
  rfl

variable {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Read the already retained traced path and primitive cover from the original period cache. -/
@[expose] def covered (program : PeriodPrograms.ExteriorProgram lifted source) :
    PreparedClearPathModels.CoveredTracedPath program.period.closed.walk.path (PeriodPrograms.exteriorOwner lifted
      program.sheet) :=
  ⟨program.period.closed.traced, program.period.closed.cover⟩

/-- Package the already materialized period parents and primitive covers. -/
@[expose] def cache (program : PeriodPrograms.ExteriorProgram lifted source) : PreparedClearPathModels.ParentCache
  program.covered source 0 :=
  ⟨program.period.initial.state.parents, by rw [program.period.initial_eq]; rfl, program.period.covered⟩

/-- Every original cached exterior-period parent lies on the retained ambient boundary. -/
theorem onBoundary (program : PeriodPrograms.ExteriorProgram lifted source) :
    ∀ parent ∈ program.cache.parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve) :=
  ParentCache.onBoundary program.cache
    (by rw [program.walk_eq]; exact PeriodPrograms.exteriorWalk_sides base)

/-- Recasting the original standard-differential period parents preserves exactly the retained cache parent list. -/
theorem recast_cache (program : PeriodPrograms.ExteriorProgram lifted source) :
    program.period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential source.index)) =
        program.cache.parents := by
  change program.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge source) =
    program.period.initial.state.parents
  rw [program.period.initial_eq]
  exact CenteredPathChain.ofPreparedPath_recast_self curve source 0 program.period.closed.traced.prepared

/-- The original controlled source bank is also a request on this period's standard differential; no coefficient or
child path is recomputed. -/
@[expose] def periodRequest (program : PeriodPrograms.ExteriorProgram lifted source) {target :
  InverseRootPolynomial.Coordinate}
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest program.cache.parents genus target) :
    PreparedControlledPrimitiveRequests.ControlledSumRequest (program.period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential source.index))) genus target :=
  ControlledSumRequest.castParents request program.recast_cache.symm

/-- Transporting an original source-bank request preserves its exact retained primitive sum. -/
theorem periodRequest_sum (program : PeriodPrograms.ExteriorProgram lifted source) {target :
  InverseRootPolynomial.Coordinate}
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest program.cache.parents genus target) :
    (program.periodRequest request).primitiveSum = request.primitiveSum := ControlledSumRequest.castParents_primitiveSum
      request _

/-- Read the original period's indexed lifted edge word from its retained shared sheet. -/
@[expose] def indexed (program : PeriodPrograms.ExteriorProgram lifted source) : List (Stokes.OrientedEdge
  lifted.vertices.count) :=
  lifted.edges.indexedEdges lifted.vertices program.period.closed.walk program.sheet

/-- The original period's indexed word equals the parity-selected exterior tour on its retained sheet. -/
theorem indexed_eq (program : PeriodPrograms.ExteriorProgram lifted source) :
    program.indexed = lifted.edges.indexedEdges lifted.vertices (PeriodPrograms.exteriorWalk base) program.sheet := by
  unfold PeriodPrograms.ExteriorProgram.indexed
  rw [program.walk_eq]

end ExteriorProgram

/-- Exactly the parity-selected exterior components, without added bridges.

The odd-degree case keeps one doubled tour; the even-degree case keeps one tour on each original sheet. -/
@[expose] def exteriorPrograms (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential
  genus) : List (PeriodPrograms.ExteriorProgram lifted source) :=
  match curve.degreeShape with
  | .odd _ => [PeriodPrograms.ExteriorProgram.build lifted source 0]
  | .even _ => [PeriodPrograms.ExteriorProgram.build lifted source 0, PeriodPrograms.ExteriorProgram.build lifted source
    1]

/-- The numerical programs retain the precise oriented surface boundary tours.

The parity-selected component list uses the same retained sheet and exterior tour as the oriented boundary list. -/
theorem exteriorPrograms_indexed (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential
  genus) :
    (PeriodPrograms.exteriorPrograms lifted source).map PeriodPrograms.ExteriorProgram.indexed =
      LiftedPuncturedGrid.exteriorBoundaries lifted := by
  cases shape : curve.degreeShape
  all_goals
    rewrite [PeriodPrograms.exteriorPrograms, shape]
    dsimp only [List.map_cons, List.map_nil]
    repeat' rewrite [ExteriorProgram.indexed_eq]
    repeat' rewrite [ExteriorProgram.build_sheet]
    repeat' rewrite [PeriodPrograms.exteriorWalk]
    rewrite [LiftedPuncturedGrid.exteriorBoundaries]
    repeat' rewrite [shape]
    exact Eq.refl _

/-- The retained parity-selected exterior period programs account for the exact original two-sheet exterior area.

The finite sum retains the original oriented edge occurrences on each sheet. Mapping the cached programs to their words
preserves those exact area readings. -/
theorem exteriorPrograms_area (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential
  genus)
    (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    CellBoundary.sumValues (fun program => Stokes.edgeListArea primitive program.indexed)
      (PeriodPrograms.exteriorPrograms lifted source) =
      lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior := by
  have mapArea (programs : List (PeriodPrograms.ExteriorProgram lifted source)) :
      CellBoundary.sumValues (Stokes.edgeListArea primitive) (programs.map PeriodPrograms.ExteriorProgram.indexed) =
        CellBoundary.sumValues (fun program => Stokes.edgeListArea primitive program.indexed) programs := by
    induction programs with
    | nil => rfl
    | cons program programs ih => exact congrArg (fun tail => Stokes.edgeListArea primitive program.indexed + tail) ih
  have mapped := mapArea (PeriodPrograms.exteriorPrograms lifted source)
  rw [PeriodPrograms.exteriorPrograms_indexed] at mapped
  exact mapped.symm.trans (LiftedPuncturedGrid.exteriorBoundaries_area lifted primitive)

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
