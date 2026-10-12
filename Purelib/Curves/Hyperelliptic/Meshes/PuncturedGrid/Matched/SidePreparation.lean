module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The full matched side uses one cached family of prefix paths and root
owners, shared by every differential contact bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}

variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftRow : Fin leftMesh.partition.y.intervals.length} {rightRow : Fin rightMesh.partition.y.intervals.length}
  {height : Fraction.Rational} {depth : Nat}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh rightMesh leftRow
    rightRow height}

set_option genInjectivity false in
/-- One original common-origin path bank for the retained matched horizontal trace.

Both domain owners and containment certificates are retained for every indexed trace point. -/
structure MatchedSidePreparation (trace : side.Trace depth) where
  /-- The first retained horizontal trace point is the original common path origin. -/ origin_eq : trace.point
    (trace.vertices.indexed 0) = start
  /-- The original common-origin clear-box routes to every retained horizontal trace vertex. -/ routes :
    Data.Vector.DependentVector (fun vertex : Fin (trace.vertices.rest.length + 1) =>
    Paths.ClearBoxPaths.Route curve.polynomial firstFace.cell.box start (trace.point (trace.vertices.indexed vertex)))
  /-- The exact original path preparations using the retained common root owner. -/ prepared :
    Data.Vector.DependentVector (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (routes.get vertex).path owner)
  /-- Every retained original path stays inside the first face cell. -/ leftInside : ∀ vertex, (routes.get
    vertex).path.InBox firstFace.cell.box
  /-- Every retained original path stays inside the second face cell. -/ rightInside : ∀ vertex, (routes.get
    vertex).path.InBox lastFace.cell.box

constructive_injectivity MatchedSidePreparation

namespace MatchedSidePreparation

/-- The original axis-aligned clear-box route lies in a second box containing both retained endpoints. -/
public theorem route_inBox {polynomial : Geometry.ClearPath.GaussianPolynomial} {box other :
  Rational.Box}
    (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (start finish : Gaussian.Basic.Canonical) (first : box.Contains start) (last : box.Contains finish)
    (otherFirst : other.Contains start) (otherLast : other.Contains finish) :
    (Paths.ClearBoxPaths.Route.build clearance start finish first last).path.InBox other := by
  unfold Paths.ClearBoxPaths.Route.build
  split
  · rename_i equal
    subst finish
    exact otherFirst
  · dsimp only
    split
    · exact ⟨otherFirst, otherLast⟩
    · split
      · exact ⟨otherFirst, otherLast⟩
      · exact ⟨otherFirst, ⟨otherLast.1, otherLast.2.1, otherFirst.2.2⟩, otherLast⟩

/-- Each original matched horizontal trace point belongs to its retained first face box. -/
public theorem leftPoint (trace : side.Trace depth) (vertex : Fin (trace.vertices.rest.length + 1)) :
    firstFace.cell.box.Contains (trace.point (trace.vertices.indexed vertex)) := by
  let retained := trace.vertices.indexed vertex
  have inside := (trace.segments.get retained.1).left_contains retained.2
  exact (leftDomain.patch.cell_refines (side.pieces retained.1).leftColumn (side.pieces retained.1).leftRow).contains
    inside

/-- Each original matched horizontal trace point belongs to its retained second face box. -/
public theorem rightPoint (trace : side.Trace depth) (vertex : Fin (trace.vertices.rest.length + 1)) :
    lastFace.cell.box.Contains (trace.point (trace.vertices.indexed vertex)) := by
  let retained := trace.vertices.indexed vertex
  have inside := (trace.segments.get retained.1).right_contains retained.2
  exact (rightDomain.patch.cell_refines (side.pieces retained.1).rightColumn (side.pieces retained.1).rightRow).contains
    inside

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation in
/-- Prepare all original common-origin horizontal trace paths once with both actual face-containment certificates. -/
def build (trace : side.Trace depth) (origin_eq : trace.point (trace.vertices.indexed 0) = start) :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace := by
  have leftVertexInside := leftPoint trace
  have rightVertexInside := rightPoint trace
  have leftStart : firstFace.cell.box.Contains start := origin_eq ▸ leftVertexInside 0
  have rightStart : lastFace.cell.box.Contains start := origin_eq ▸ rightVertexInside 0
  let routes := Data.Vector.DependentVector.ofFn fun vertex =>
    Paths.ClearBoxPaths.Route.build firstFace.clearance start (trace.point (trace.vertices.indexed vertex)) leftStart
      (leftVertexInside vertex)
  refine ⟨origin_eq, routes, Data.Vector.DependentVector.ofFn (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build (routes.get vertex).path
      (routes.get vertex).within owner), ?_, ?_⟩
  · intro vertex
    exact Geometry.ClearPath.InBox.ofWithin (routes.get vertex).path (routes.get vertex).within leftStart
  · intro vertex
    dsimp only [routes]
    rw [Data.Vector.DependentVector.ofFn_get]
    exact Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation.route_inBox
      firstFace.clearance start (trace.point (trace.vertices.indexed vertex))
      leftStart (leftVertexInside vertex) rightStart (rightVertexInside vertex)

/-- Prepare the selected differential's original parent caches and fixed-domain contacts from the retained shared path
bank. -/
def contacts {trace : side.Trace depth}
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
      (fun vertex => trace.point (trace.vertices.indexed vertex)) differential parentSheet :=
  Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.build leftEntry rightEntry leftDomain
    rightDomain
    (fun vertex => trace.point (trace.vertices.indexed vertex)) preparation.origin_eq (fun _ => firstFace.cell.box)
    (fun vertex => (preparation.routes.get vertex).path) preparation.prepared
    preparation.leftInside preparation.rightInside differential parentSheet
    (Data.Vector.DependentVector.ofFn fun vertex =>
      Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build (preparation.prepared.get vertex)
      differential parentSheet)

end MatchedSidePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
