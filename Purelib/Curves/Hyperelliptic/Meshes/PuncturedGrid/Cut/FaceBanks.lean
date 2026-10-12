module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedOwnerAlignment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Approximation.Gaussian.Equivalence
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

public section

/-!
# Actual cut-cycle preparations assigned to retained lifted faces

The supplied cut program already retains its routed walk and lifted indices.
Those caches construct all segment placements automatically. Each placement
contains the original segment's endpoints, and the concatenated integration
parents remain exactly the original program's cells for every differential.
The actual incoming owners agree with those indices. This is not yet the
global primitive-jump identity.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments (WalkMatches)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

/-- The retained routed cut-cycle word is exactly the actual period walk's indexed edge sequence. -/
theorem indexed_matches
  (prepared : CyclePrograms.CutCycleProgram lifted source) :
    prepared.routed.walk.indexed = lifted.edges.indexedEdges lifted.vertices prepared.period.closed.walk
      (lifted.vertices.sheet (lifted.cutPolygon.patch.cut.vertexLabels prepared.cycle.start)) := by
  rw [prepared.walk_eq]
  exact prepared.routed.walk.indexed_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

/-- Attach the retained face routes to the original period walk after transporting its exact initial point. -/
@[expose] public def pathFacesAt {point : Data.Gaussian.Basic.Canonical} (cachedPoint : Data.Gaussian.Basic.Canonical)
  (equal :
  cachedPoint = point)
    (walk : Walks.Walk base.bank.grid point point) (word : List (Stokes.OrientedEdge lifted.vertices.count))
    (matching : WalkFaceAssignments.WalkMatches (edges := lifted.edges) walk word)
    (routes : MeshPathWalks.RouteSpine lifted.mesh word) : LiftedMesh.PathFaces lifted.mesh walk.path := by
  subst point
  exact PathFaces.ofRoutes lifted.mesh walk word matching routes

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

/-- Retain the actual face placement of every edge in the original cut-cycle period walk. -/
@[expose] def pathFaces
  (prepared : CyclePrograms.CutCycleProgram lifted source) : LiftedMesh.PathFaces lifted.mesh
  prepared.period.closed.walk.path :=
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.pathFacesAt
    prepared.period.initial.state.start.coordinate (by rw [prepared.period.initial_eq]; rfl)
    prepared.period.closed.walk prepared.routed.walk.indexed
    ⟨_, prepared.indexed_matches⟩ (prepared.routed.spine.detoured.castWord prepared.routed.indexed_eq.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

/-- The transported original walk uses exactly the face placement obtained from its retained routes. -/
private theorem pathFacesAt_eq {point : Data.Gaussian.Basic.Canonical} (cachedPoint : Data.Gaussian.Basic.Canonical)
  (equal : cachedPoint = point)
    (walk : Walks.Walk base.bank.grid point point) (word : List (Stokes.OrientedEdge lifted.vertices.count))
    (matching : WalkFaceAssignments.WalkMatches (edges := lifted.edges) walk word)
    (routes : MeshPathWalks.RouteSpine lifted.mesh word) :
    pathFacesAt cachedPoint equal walk word matching
      routes = PathFaces.ofRoutes lifted.mesh walk word matching routes := by
  subst point
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

/-- The cached original period walk face placement reads back its actual retained route bank. -/
theorem pathFaces_eq
  (prepared : CyclePrograms.CutCycleProgram lifted source) : prepared.pathFaces =
    PathFaces.ofRoutes lifted.mesh prepared.period.closed.walk prepared.routed.walk.indexed
      ⟨_, prepared.indexed_matches⟩ (prepared.routed.spine.detoured.castWord prepared.routed.indexed_eq.symm) :=
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.pathFacesAt_eq _ _ _ _ _ _

/-- The original face-assigned period walk reads back exactly its retained routed indexed word. -/
theorem pathFaces_indexed
  (prepared : CyclePrograms.CutCycleProgram lifted source) :
    prepared.pathFaces.indexed = prepared.routed.walk.indexed := by
  rw [prepared.pathFaces_eq]
  exact PathFaces.ofRoutes_indexed _ _ _ _ _

/-- The retained original period segments align with their original vertex-bank endpoint owners. -/
theorem
  pathFaces_ownersAligned
  (prepared : CyclePrograms.CutCycleProgram lifted source)
    (pieces : PreparedPath.CoveredSegments prepared.period.closed.traced.prepared) :
    (AssignedSegments.build pieces prepared.pathFaces).OwnersAligned :=
  AssignedSegments.ownersAligned_of_indexed lifted.mesh prepared.period.closed.walk
    _ (lifted.vertices.coordinate_onGrid _) (AssignedSegments.build pieces prepared.pathFaces)
    ((AssignedSegments.build_indexed _ _).trans (prepared.pathFaces_indexed.trans prepared.indexed_matches))
    ⟨NamedEquivalent.refl _⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

set_option genInjectivity false in
/-- Geometry is attached to the actual period segment bank, not to a second preparation or a path having merely the same
endpoints. -/
structure FaceBank (prepared : CyclePrograms.CutCycleProgram lifted source) where
  /-- The actual original period segment bank retained by this face certificate. -/ segments :
    PeriodSegmentBanks.SegmentBank prepared.period
  /-- The cached face assignment for these exact original segments. -/ assigned : PreparedFaceSegments.AssignedSegments
    lifted.mesh segments.pieces
  /-- The retained assigned segments read back the original routed indexed word. -/ indexed_eq : assigned.indexed =
    prepared.routed.walk.indexed
  /-- Every retained face assignment preserves the actual original vertex-bank owners. -/ ownersAligned :
    assigned.OwnersAligned

constructive_injectivity FaceBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

section

variable {prepared : CutCycleProgram lifted source}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank

/-- Reuse the supplied original period segment bank and attach its exact retained face assignments. -/
@[expose] def ofSegments (prepared : CyclePrograms.CutCycleProgram lifted source) (segments :
  PeriodSegmentBanks.SegmentBank prepared.period) : FaceBanks.FaceBank
  prepared :=
  let assigned := AssignedSegments.build segments.pieces prepared.pathFaces
  ⟨segments, assigned, (AssignedSegments.build_indexed _ _).trans prepared.pathFaces_indexed,
    prepared.pathFaces_ownersAligned segments.pieces⟩

/-- Build the original period segment bank once and cache its exact aligned face assignments. -/
@[expose] def build (prepared : CyclePrograms.CutCycleProgram lifted source) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank prepared :=
  ofSegments prepared (SegmentBank.build
    prepared.period)

/-- The retained original segment count equals the length of the routed indexed word. -/
theorem count_eq_indexed (bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank prepared) :
  bank.segments.count = prepared.routed.walk.indexed.length := by
  rw [bank.segments.count_eq, ← bank.assigned.indexed_length, bank.indexed_eq]

/-- The retained parent count equals the original period model's initial parent count. -/
theorem parentCount_eq_initial (bank : FaceBanks.FaceBank prepared) :
    bank.segments.parentCount = prepared.period.initial.state.parents.length := bank.segments.parentCount_eq_initial

/-- The retained parents are exactly the differential recasting of the original state parents. -/
theorem parents_eq (bank : FaceBanks.FaceBank prepared) (differential :
  Differentials.Basic.Differential genus) :
    CoveredSegments.parents differential 0 bank.segments.pieces =
      prepared.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential) :=
        bank.segments.parents_eq differential

/-- The original initial period model cells are exactly the retained segment parent models. -/
theorem initial_cells (bank : FaceBanks.FaceBank prepared) (differential :
  Fin genus) :
    ((prepared.program differential).integral.model 0).cells =
      (CoveredSegments.parents
        (PeriodMatrix.standardDifferential differential) 0 bank.segments.pieces).map
        CenteredEdge.model := bank.segments.initial_cells differential

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank

end
end
