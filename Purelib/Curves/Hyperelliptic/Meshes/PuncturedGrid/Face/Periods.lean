module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Sample

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Paths.PreparedPathDifferentialRecasting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Gaussian

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedCoveredParentLists

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.RectangularFaceModels

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid

@[expose] public section

/-!
# Actual contained face periods and their cached comparison meshes

One retained closed preparation supplies every standard differential. The
coarse inverse-root patch and cut axes are shared, while each differential
retains its actual parent splitting and scalar majorants. Generated caches
may satisfy these same contracts without reproducing the canonical search.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.PreparedParentSplitting (PreparedSplitMesh)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch RectangularLayout)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {source : Differential genus}

set_option genInjectivity false in
/-- The actual root-closed grid program, together with geometric containment. No vanishing-period or
primitive-compatibility certificate is an input. -/
structure ContainedPeriod (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source :
  Differentials.Basic.Differential genus) where
  /-- The actual original root-closed grid period on the retained face sheet. -/ period :
    PreparedGridPeriodPrograms.PeriodWalk bank.grid face.cell.box.anchor (models.frame.owners sheet) source
  /-- Every point of the original closed walk lies in the retained clear face box. -/ inside : ClearPath.InBox
    face.cell.box period.closed.walk.path

constructive_injectivity ContainedPeriod

namespace ContainedPeriod

/-- Reuse the original covered face walk and its traced owners to certify a root-closed period on the selected sheet. -/
def ofCovered (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source :
  Differentials.Basic.Differential genus)
    (walk : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor) (inside : ClearPath.InBox face.cell.box
      walk.path)
    (covered : PreparedClearPathModels.CoveredTracedPath walk.path (models.frame.owners sheet)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod models sheet source :=
  let reference := (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
  have winding := ClearPath.rawWinding_zero_of_inBox face.clearance (Nat.zero_lt_of_lt higher) walk.path inside
  let closed : Grid.RootClosedWalk bank.grid face.cell.box.anchor (models.frame.owners sheet) :=
    ⟨walk, covered.traced, covered.cover, OwnerTraceReadings.ownerName (models.frame.owners sheet),
      OwnerTraceReadings.ownerName covered.traced.finishOwner,
      rfl, rfl, OwnerPath.rootEquivalent_of_even_with_reference reference covered.traced.trace.get 0
        (by rw [TracedPath.winding_original covered.traced, winding]; rfl)⟩
  ⟨PeriodWalk.ofClosed closed source, inside⟩

/-- Prepare the actual contained face period, shared rectangular domain or differential mesh while retaining their
original owners. -/
def build (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source : Differentials.Basic.Differential
  genus)
    (walk : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor) (inside : ClearPath.InBox face.cell.box
      walk.path) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod models sheet source :=
  ofCovered models sheet source walk inside
    (CoveredTracedPath.build walk.path walk.withinAmbient (models.frame.owners sheet))

/-- Recasting the original period parents gives exactly the retained prepared path's differential parent list. -/
theorem parents_eq (loop : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod models sheet source)
  (target : Differentials.Basic.Differential genus) :
    loop.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge target) =
      (CenteredPathChain.ofPreparedPath curve target 0 loop.period.closed.traced.prepared).parents := by
  rw [loop.period.initial_eq, RootClosedWalk.initial_parents, PreparedPathDifferentialRecasting.ofPreparedPath_recast]

/-- Read the original closed centered-parent chain after differential recasting. -/
def chain (loop : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod models sheet source) (target :
  Differentials.Basic.Differential genus) :
    PreparedDirectDyadicRefinements.CenteredPathChain (loop.period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge target))
      (start := ⟨face.cell.box.anchor, 0⟩) (finish := ⟨face.cell.box.anchor, 0⟩) := by
  rw [loop.parents_eq target]
  exact (CenteredPathChain.ofPreparedPath curve target 0 loop.period.closed.traced.prepared).chain

end ContainedPeriod

/-- The four original face edges are contained in their own clear box. -/
theorem boundary_inside (face : PuncturedGridFaces.RegularFace bank) : ClearPath.InBox face.cell.box face.boundary.path
  := by
  change face.cell.box.Contains face.cell.box.anchor ∧
    face.cell.box.Contains (Components.Basic.point face.cell.box.xUpper face.cell.box.yLower) ∧
    face.cell.box.Contains (Components.Basic.point face.cell.box.xUpper face.cell.box.yUpper) ∧
    face.cell.box.Contains (Components.Basic.point face.cell.box.xLower face.cell.box.yUpper) ∧
    face.cell.box.Contains face.cell.box.anchor
  exact ⟨face.cell.box.contains_anchor,
    ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩,
    ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩,
    ⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩, face.cell.box.contains_anchor⟩

/-- An automatic actual boundary program on either local sheet. -/
def boundaryPeriod (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source :
  Differentials.Basic.Differential genus) :
    ContainedPeriod models sheet source :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod.build models sheet source face.boundary
    (boundary_inside face)

/-- The retained boundary period uses exactly the original regular face boundary walk. -/
theorem boundaryPeriod_walk (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) (source :
  Differentials.Basic.Differential genus) :
    (boundaryPeriod models sheet source).period.closed.walk =
      face.boundary := rfl

set_option genInjectivity false in
/-- The complete face, not merely an arbitrary family of refining cells. The materialized axes are reused by every
request. Checked generated axes may replace the uniform constructor through the same coverage contract. -/
structure PeriodDomain (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) where
  /-- The cached finite subdivision count on both original face axes. -/ steps : Nat
  /-- The retained rectangular grid on the complete original face box. -/ geometry : RectangularInverseModels.Geometry
    steps steps
  /-- The cached grid covers every point of the original face box. -/ covers : ∀ {point :
    Data.Gaussian.Basic.Canonical}, face.cell.box.Contains point → Geometry.Covers geometry point
  /-- The retained grid begins at the original face box anchor. -/ anchor_eq : (geometry.box 0 0).anchor =
    face.cell.box.anchor
  /-- The retained face inverse-model patch on this exact original grid and sheet. -/ patch :
    RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet) geometry
  /-- The cached cut axes used to split the original retained parent paths. -/ cuts :
    RectangularSegmentSplitting.GridCuts geometry

constructive_injectivity PeriodDomain

namespace PeriodDomain

/-- Prepare the actual contained face period, shared rectangular domain or differential mesh while retaining their
original owners. -/
def build (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet :=
  let steps := Geometry.Rectangle.Partition.RectangularUniformGeometry.dyadicSteps models.mesh.depth
  let geometry := Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform face.cell.box face.cell.box_proper
      steps
  ⟨steps, geometry, Geometry.uniform_covers face.cell.box face.cell.box_proper steps,
    Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform_anchor face.cell.box face.cell.box_proper steps,
    RectangularPatch.acquire (RectangularLayout.ofMesh models.mesh face.cell.box_proper) (models.frame.owners sheet),
    GridCuts.build geometry⟩

end PeriodDomain

set_option genInjectivity false in
/-- A cached differential mesh on an original contained period and shared face domain.

The parent splitting, coverage and analytic bounds retain the actual period parents, with the original face anchor
located in the cached mesh. -/
structure PeriodMesh (domain : PeriodDomain models sheet) (loop :
  ContainedPeriod models sheet source)
    (differential : Differentials.Basic.Differential genus) where
  /-- The cached splitting of the original differential-recast period parents. -/ mesh :
    PreparedParentSplitting.PreparedSplitMesh domain.cuts (loop.period.initial.state.parents.map
    (PreparedEdgeRecasting.recastCenteredEdge differential)) [face.cell.box.anchor]
  /-- The original recast parents retain their actual primitive coverage. -/ covered :
    UniformPreparedMesh.CoveredParents genus
    (loop.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential))
  /-- The cached fragment bounds for the original patch and differential. -/ bounds : FragmentReadings.FragmentBounds
    domain.patch differential
  /-- The retained global primitive overlap bounds from the original clear face and differential numerator. -/
    globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
    (PreparedPrimitiveSamples.differentialNumerator differential)
  /-- The cached original face anchor's index in the retained mesh vertex bank. -/ anchor : Fin
    mesh.mesh.surface.mesh.vertices.length
  /-- The cached mesh vertex reads back the exact original face anchor. -/ anchor_eq : mesh.mesh.surface.mesh.coordinate
    anchor = face.cell.box.anchor

constructive_injectivity PeriodMesh

namespace PeriodMesh

/-- Prepare the actual contained face period, shared rectangular domain or differential mesh while retaining their
original owners. -/
def build (domain : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet) (loop :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.ContainedPeriod models sheet source)
    (differential : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodMesh domain loop differential :=
  let mesh := PreparedSplitMesh.build domain.cuts
    (loop.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential))
    (fun parent member => by
      have present : parent ∈ (CenteredPathChain.ofPreparedPath curve differential 0
        loop.period.closed.traced.prepared).parents := by
        rw [← loop.parents_eq differential]; exact member
      have reached := PreparedFaceTracePrefixes.traced_parent_reached face.clearance differential 0
        loop.period.closed.traced loop.inside parent present
      exact ⟨domain.covers reached.first_inside, domain.covers reached.last_inside⟩) [face.cell.box.anchor]
  have member : face.cell.box.anchor ∈ mesh.points := by
    rw [mesh.points_eq]
    exact List.mem_append_right _ List.mem_cons_self
  have inside : (domain.geometry.box 0 0).Contains face.cell.box.anchor := by
    rw [← domain.anchor_eq]
    exact Rational.Box.contains_anchor _
  let anchor := mesh.mesh.lookup face.cell.box.anchor member 0 0 (Geometry.allCells_mem _ 0 0) inside
  ⟨mesh, CoveredParents.recast differential loop.period.covered, FragmentBounds.build domain.patch differential,
    PrimitiveOverlapBounds.build face.clearance (PreparedPrimitiveSamples.differentialNumerator differential),
      anchor.index, anchor.coordinate_eq⟩

end PeriodMesh

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
