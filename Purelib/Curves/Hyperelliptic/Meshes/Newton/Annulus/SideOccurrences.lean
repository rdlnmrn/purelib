module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh

/-! The annular outer boundary's exact side-source representation. Its
boundary certificates refer to the selected Newton band, not the inner hole. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted doubleBoundary)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted :
    Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured} {region :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- Consume the cached assignments; numerical banks can reuse this finite list without replaying owner continuation or
selecting source triangles. -/
@[expose] def sideOccurrences (prepared : Lifted.OuterPreparation region) : List (LiftedMesh.SideOccurrence lifted.mesh)
  :=
  AssignedSegments.sideOccurrences prepared.assigned

/-- The retained annular side occurrences have exactly the cached original source-edge list. -/
theorem sideOccurrences_sources (prepared : Lifted.OuterPreparation region) :
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared).map SideOccurrence.source =
      prepared.sources :=
  (AssignedSegments.sideOccurrences_sources prepared.assigned).trans prepared.sources_eq.symm

/-- The retained annular side occurrences project to the exact original outer boundary word. -/
theorem sideOccurrences_project (prepared : Lifted.OuterPreparation region) :
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared).map (fun occurrence =>
      occurrence.source.project lifted.mesh.triangulation.faces) = region.outer :=
  (AssignedSegments.sideOccurrences_project prepared.assigned).trans prepared.indexed_eq

/-- There is exactly one retained side occurrence per original annular outer-boundary edge. -/
theorem sideOccurrences_count (prepared : Lifted.OuterPreparation region) :
    (Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared).length = region.outer.length
      := by
  have count := congrArg List.length (Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences_project
    prepared)
  rw [Purelib.Data.List.Map.length_map] at count
  exact count

/-- Every retained annular side occurrence lies on a common side of its original Newton band box. -/
theorem sideOccurrences_onBoundary (prepared : Lifted.OuterPreparation region) :
    ∀ occurrence ∈ Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared,
      SideOccurrence.OnBoundary occurrence (grid.bands.box index) :=
  AssignedSegments.sideOccurrences_onBoundary prepared.assigned (PrimitiveComparison.doubleBoundary_segments annulus)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
