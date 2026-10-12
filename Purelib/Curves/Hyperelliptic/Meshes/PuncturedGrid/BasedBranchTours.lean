module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Closure
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Approximation.Gaussian.Equivalence
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid

open Purelib.Data.Vector

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.Winding

open Purelib.Riemann

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)

open Purelib.RootIsolation.SquareRoot.Grid.Walk

open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

@[expose] public section

/-!
# Labelled branch tours with a shared exterior starting root

Each stem travels up the left exterior and then horizontally to its retained
branch cell. Its loop follows that cell's actual winding-one boundary and
the reversed stem. A pair of these loops continues through the exchanged
sheet at the common base and returns to the original owner. The cached path
can then seed all standard differential programs without new root choices.

This constructs the common-root geometry needed for a branch-cycle change
of basis. It does not assert a cyclic order, intersection table, or equality
with the old two-leg reference-tour period names.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid (connect WindingOneReference)
open Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell (boundaryWalk)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace FramedBranchCellBank

/-- The original ambient-box anchor is a retained vertex of the framed branch grid. -/
theorem baseMember (bank : Branches.FramedBranchCellBank curve branches higher) :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid
  (Cuts.Ambient curve).anchor :=
  ⟨bank.frame.xLower, bank.frame.yLower⟩

set_option genInjectivity false in
/-- The branch index remains in the type, tying the loop to its own cached cell and winding-one certificate. -/
structure BasedBranchLoop (bank : Branches.FramedBranchCellBank curve branches higher) (index :
  BranchIsolation.Data.Index branches) where
  /-- The cached path from the shared exterior anchor to this exact retained branch cell. -/ stem : Walks.Walk bank.grid
    (Cuts.Ambient curve).anchor (bank.cell index).box.anchor
  /-- The stem is exactly the reversed canonical retained grid connection. -/ stem_eq : stem = (Grid.connect bank.grid
    (bank.cell index).box.anchor (Cuts.Ambient curve).anchor
    ((bank.cell index).anchor_mem (bank.cell_mem index))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember bank)).reverse
  /-- The cached winding-one boundary of the original branch cell. -/ boundary : Walks.Walk bank.grid (bank.cell
    index).box.anchor (bank.cell index).box.anchor
  /-- The boundary walk is exactly the original retained cell boundary. -/ boundary_eq : boundary =
    CellBoundary.Cell.boundaryWalk (bank.cell index) (bank.cell_mem index)
  /-- The cached winding-one branch loop based at the common exterior anchor. -/ reference : Grid.WindingOneReference
    bank.grid (Cuts.Ambient curve).anchor
  /-- The reference walk is exactly the retained stem, branch boundary and reversed stem. -/ reference_eq :
    reference.walk = stem.append (boundary.append stem.reverse)

constructive_injectivity BasedBranchLoop

/-- Cache the original branch-cell stem, winding-one boundary and their based concatenation. -/
def BasedBranchLoop.build (bank : Branches.FramedBranchCellBank curve branches higher) (index :
  BranchIsolation.Data.Index branches) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.BasedBranchLoop bank index :=
  let stem := (Grid.connect bank.grid (bank.cell index).box.anchor (Cuts.Ambient curve).anchor
    ((bank.cell index).anchor_mem (bank.cell_mem index))
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember bank)).reverse
  let boundary := CellBoundary.Cell.boundaryWalk (bank.cell index) (bank.cell_mem index)
  ⟨stem, rfl, boundary, rfl,
    ⟨stem.append (boundary.append stem.reverse), by
      rw [Walk.append_winding, Walk.append_winding, Walk.reverse_winding stem,
        CellBoundary.Cell.boundaryWalk_winding, BranchCellWinding.selected_winding_four bank.toBranchCellBank index]
      omega⟩, rfl⟩

end FramedBranchCellBank

namespace LiftedPuncturedGrid

variable {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

set_option genInjectivity false in
/-- A cached branch-indexed bank of original based loops on one retained lifted punctured grid. -/
structure BasedBranchBank (lifted : Meshes.LiftedPuncturedGrid base) where
  /-- The cached based loop for every original branch index. -/ rows : Data.Vector.DependentVector (fun index :
    BranchIsolation.Data.Index branches =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.BasedBranchLoop base.bank index)

constructive_injectivity BasedBranchBank

namespace BasedBranchBank

variable {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base}

/-- Cache the original labelled branch loops on the retained framed grid. -/
def build (lifted : Meshes.LiftedPuncturedGrid base) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted :=
  ⟨DependentVector.ofFn
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.BasedBranchLoop.build base.bank)⟩

/-- Read the actual retained lifted exterior anchor on the supplied sheet. -/
def anchor (lifted : Meshes.LiftedPuncturedGrid base) (sheet : Fin 2) : Fin lifted.vertices.count :=
  lifted.vertices.index (Cuts.Ambient curve).anchor
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank) sheet

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- A single branch circuit joins the two distinct retained sheet indices; it is deliberately not typed as a root-closed
loop. -/
def liftedLoop (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    Vertex.VertexWalk lifted.vertices lifted.edges
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet) (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor
      lifted (BranchCutLifts.otherSheet sheet)) :=
  let reference := (bank.rows.get index).reference
  let liftedLoop : RootEdgeBank.LiftedWalk lifted.edges (Cuts.Ambient curve).anchor sheet
      (Cuts.Ambient curve).anchor (BranchCutLifts.otherSheet sheet) :=
    ⟨reference.walk, (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank), (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank),
      RootEdgeBank.target_odd lifted.edges reference.walk
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank) 0
        (reference.winding.trans (by decide)) sheet⟩
  VertexWalk.ofLifted liftedLoop _ _
    (lifted.vertices.coordinate_index _
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank) sheet)
    (lifted.vertices.coordinate_index _
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      (BranchCutLifts.otherSheet sheet))
    (lifted.vertices.sheet_index _
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank) sheet)
    (lifted.vertices.sheet_index _
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      (BranchCutLifts.otherSheet sheet))

/-- The lifted branch loop has exactly the original reference walk's transported indexed edge list. -/
theorem liftedLoop_indexed (bank :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    (bank.liftedLoop index sheet).indexed =
      lifted.edges.indexedEdges lifted.vertices (bank.rows.get index).reference.walk sheet := rfl

set_option genInjectivity false in
/-- The second branch is traversed on the actual arriving sheet. Store both indexed legs and their single root-closed
concatenation. -/
structure Pair (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (first last : BranchIsolation.Data.Index branches) (sheet : Fin 2) where
  /-- The retained first branch loop from the starting sheet to the opposite sheet. -/ outward : Vertex.VertexWalk
    lifted.vertices lifted.edges
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
    (BranchCutLifts.otherSheet sheet))
  /-- The outward leg is exactly the selected original first branch loop. -/ outward_eq : outward = bank.liftedLoop
    first sheet
  /-- The retained second branch loop from the arriving sheet back to the starting sheet. -/ returning :
    Vertex.VertexWalk lifted.vertices lifted.edges
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
    (BranchCutLifts.otherSheet sheet))
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
  /-- The returning leg is the exact second branch loop with only its final vertex equality transported. -/ returning_eq
    : returning = (bank.liftedLoop last (BranchCutLifts.otherSheet sheet)).castVertices rfl
    (congrArg (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor
      lifted) (BranchCutLifts.otherSheet_other sheet))
  /-- The cached root-closed concatenation of both retained branch legs. -/ closed : Vertex.VertexWalk lifted.vertices
    lifted.edges (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor
    lifted sheet) (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor
    lifted sheet)
  /-- The closed walk is exactly the retained outward leg followed by the returning leg. -/ closed_eq : closed =
    outward.append returning

constructive_injectivity Pair

/-- Cache the two original branch legs on their actual successive sheets and their root-closed concatenation. -/
def pair (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted)
  (first last : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
      sheet :=
  let outward := bank.liftedLoop first sheet
  let returning := (bank.liftedLoop last (BranchCutLifts.otherSheet sheet)).castVertices rfl
    (congrArg (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor
      lifted) (BranchCutLifts.otherSheet_other sheet))
  ⟨outward, rfl, returning, rfl, outward.append returning, rfl⟩

namespace Pair

variable {bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted} {first last : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
/-- Transporting the returning leg's vertex proof preserves its exact indexed edge list. -/
theorem returning_indexed (pair :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
  sheet) :
    pair.returning.indexed = (bank.liftedLoop last (BranchCutLifts.otherSheet sheet)).indexed := by
  rw [pair.returning_eq]
  exact VertexWalk.castVertices_indexed _ _ _

/-- The closed pair's edge list is exactly the two original branch loops on their successive sheets. -/
theorem indexed (pair :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
  sheet) :
    pair.closed.indexed =
      lifted.edges.indexedEdges lifted.vertices (bank.rows.get first).reference.walk sheet ++
      lifted.edges.indexedEdges lifted.vertices (bank.rows.get last).reference.walk (BranchCutLifts.otherSheet sheet) :=
        by
  rw [pair.closed_eq]
  change pair.outward.indexed ++ pair.returning.indexed = _
  rw [pair.outward_eq, pair.returning_indexed,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.liftedLoop_indexed,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.liftedLoop_indexed]

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
set_option genInjectivity false in
/-- A cached period preparation for the exact retained root-closed branch pair. -/
structure Prepared (pair :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first last
  sheet) (source : Differentials.Basic.Differential genus) where
  /-- The original period walk prepared from this pair's actual retained closed walk and starting owner. -/ period :
    PreparedGridPeriodPrograms.PeriodWalk base.bank.grid (lifted.vertices.coordinate
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
    sheet))
    (lifted.vertices.owner lifted.frames
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet)) source
  /-- The prepared period uses exactly the retained branch pair's closed walk. -/ walk_eq : period.closed.walk =
    pair.closed.walk

constructive_injectivity Prepared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- Prepare the exact retained root-closed branch pair for the supplied differential. -/
def prepare (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair
  bank first last sheet) (source : Differentials.Basic.Differential genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared pair
  source :=
  let reference := (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (lifted.vertices.coordinate_onGrid
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
    sheet))).toLoop
  ⟨PeriodWalk.ofClosed (pair.closed.rootClosed reference) source, rfl⟩

namespace Prepared

variable {pair :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair bank first
  last sheet} {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
set_option genInjectivity false in
/-- Attach shared mesh geometry to the already prepared integration spine. The frame owner is the actual initial owner
of this very period walk. -/
structure Faces (prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared pair
  source) where
  /-- The cached segment preparation of this exact retained period walk. -/ segments : PeriodSegmentBanks.SegmentBank
    prepared.period
  /-- The actual shared-mesh face assignment retaining the period's original starting owner. -/ geometry :
    FramedPuncturedGrid.OwnerWalkFaces lifted.mesh prepared.period.closed.walk
    (lifted.vertices.owner lifted.frames
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet))
  /-- The face-assigned word is exactly the retained branch pair's indexed closed walk. -/ indexed_eq :
    geometry.geometry.indexed = pair.closed.indexed

constructive_injectivity Faces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- Attach actual shared face geometry to the existing period segment cache without rebuilding its source walk. -/
def faces (prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared pair
  source) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared.Faces
  prepared :=
  let segments := SegmentBank.build prepared.period
  let geometry := OwnerWalkFaces.ofSheet lifted.mesh prepared.period.closed.walk
    (lifted.vertices.coordinate_onGrid
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet)) (lifted.vertices.sheet
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet))
    ⟨NamedEquivalent.refl _⟩
  ⟨segments, geometry, geometry.indexed_eq.trans
    ((congrArg (fun walk => lifted.edges.indexedEdges lifted.vertices walk (lifted.vertices.sheet
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted
      sheet)))
      prepared.walk_eq).trans pair.closed.indexed_eq.symm)⟩

namespace Faces

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared
  pair source}

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared
  in
/-- Build local primitive comparisons from the supplied shared domains and original retained period-parent caches. -/
def comparisons (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared.Faces
  prepared) (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
    AssignedSegments.Comparisons differential 0 (faces.geometry.assign faces.segments.pieces) :=
  faces.geometry.comparisons faces.segments.pieces domains differential 0 (faces.segments.parentCaches differential)

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared
  in
/-- The local comparisons retain the original period-parent list in order, recast only to the supplied differential. -/
theorem comparisons_parents (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared.Faces
  prepared)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (differential :
      Differentials.Basic.Differential genus) :
    Comparisons.parents differential 0
      (faces.geometry.assign faces.segments.pieces) (faces.comparisons domains differential) =
      prepared.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential) :=
  (faces.geometry.comparisons_parents faces.segments.pieces domains differential 0
    (faces.segments.parentCaches differential)).trans (faces.segments.parentCaches_parents differential)

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared
  in
/-- Every local comparison consumes the exact supplied shared domain bank. -/
theorem comparisons_shared (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.Prepared.Faces
  prepared)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (differential :
      Differentials.Basic.Differential genus) :
    Comparisons.UsesDomains domains differential 0
      (faces.geometry.assign faces.segments.pieces) (faces.comparisons domains differential) :=
  faces.geometry.comparisons_shared faces.segments.pieces domains differential 0 (faces.segments.parentCaches
    differential)

end Faces
end Prepared
end Pair
end BasedBranchBank
end LiftedPuncturedGrid
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
