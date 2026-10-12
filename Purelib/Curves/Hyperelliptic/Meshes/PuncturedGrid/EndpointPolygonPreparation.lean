module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
public import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Contact paths for retained endpoint polygons. All differential pairs reuse
one path bank, with both original model owners and the common root retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

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

variable {count : Nat}
  {first : Fin (count + 1) → Path.JoinedTrace.VertexTrace (Integration.RectangularOwnedTriangulation.OwnedVertex
    leftDomain.geometry)}
  {last : Fin (count + 1) → Path.JoinedTrace.VertexTrace (Integration.RectangularOwnedTriangulation.OwnedVertex
    rightDomain.geometry)}

set_option genInjectivity false in
/-- One original bank of common-origin contact paths for the retained paired endpoint polygon.

Both domain owners and their containment certificates remain attached to each actual prepared path. -/
structure EndpointPolygonPreparation (geometry :
  Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first last) where
  /-- The retained polygon's first coordinate is the original shared path origin. -/ origin_eq : geometry.points 0 =
    start
  /-- The original finite clear-box routes from the shared origin to every retained polygon point. -/ routes :
    Data.Vector.DependentVector (fun vertex =>
    Paths.ClearBoxPaths.Route curve.polynomial firstFace.cell.box start (geometry.points vertex))
  /-- The exact retained path preparations using the original common root owner. -/ prepared :
    Data.Vector.DependentVector (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (routes.get vertex).path owner)
  /-- Every original retained contact route lies in the first face box. -/ leftInside : ∀ vertex, (routes.get
    vertex).path.InBox firstFace.cell.box
  /-- Every original retained contact route lies in the second face box. -/ rightInside : ∀ vertex, (routes.get
    vertex).path.InBox lastFace.cell.box

constructive_injectivity EndpointPolygonPreparation

namespace EndpointPolygonPreparation

/-- The original axis-aligned clear-box route lies in any other box containing both endpoints. -/
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

/-- Every original paired polygon coordinate lies in its retained first face box. -/
public theorem leftPoint (geometry : Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first
  last)
    (vertex : Fin ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length + 1)) :
    firstFace.cell.box.Contains (geometry.points vertex) := by
  rw [← geometry.left_point vertex]
  exact (leftDomain.patch.cell_refines (geometry.leftOwners vertex).column
    (geometry.leftOwners vertex).row).contains (geometry.leftOwners vertex).contains

/-- Every original paired polygon coordinate lies in its retained second face box. -/
public theorem rightPoint (geometry : Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first
  last)
    (vertex : Fin ((Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length + 1)) :
    lastFace.cell.box.Contains (geometry.points vertex) := by
  rw [← geometry.right_point vertex]
  exact (rightDomain.patch.cell_refines (geometry.rightOwners vertex).column
    (geometry.rightOwners vertex).row).contains (geometry.rightOwners vertex).contains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation in
/-- Prepare the original common-origin polygon routes once with both retained face-containment certificates. -/
def build (geometry : Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first last) (origin_eq :
  geometry.points 0 = start) :
    EndpointPolygonPreparation (leftEntry := leftEntry)
      (rightEntry := rightEntry) geometry := by
  have leftVertexInside := leftPoint geometry
  have rightVertexInside := rightPoint geometry
  have leftStart : firstFace.cell.box.Contains start := origin_eq ▸ leftVertexInside 0
  have rightStart : lastFace.cell.box.Contains start := origin_eq ▸ rightVertexInside 0
  let routes := Data.Vector.DependentVector.ofFn fun vertex =>
    Paths.ClearBoxPaths.Route.build firstFace.clearance start (geometry.points vertex) leftStart (leftVertexInside
      vertex)
  refine ⟨origin_eq, routes, Data.Vector.DependentVector.ofFn (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build (routes.get vertex).path
      (routes.get vertex).within owner), ?_, ?_⟩
  · intro vertex
    exact Geometry.ClearPath.InBox.ofWithin (routes.get vertex).path (routes.get vertex).within leftStart
  · intro vertex
    dsimp only [routes]
    rw [Data.Vector.DependentVector.ofFn_get]
    exact route_inBox
      firstFace.clearance start (geometry.points vertex)
      leftStart (leftVertexInside vertex) rightStart (rightVertexInside vertex)

/-- Prepare the selected differential's original parent caches and fixed-domain contacts using the retained shared path
bank. -/
def contacts {geometry : Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first last}
    (preparation : EndpointPolygonPreparation (leftEntry
      := leftEntry) (rightEntry := rightEntry) geometry)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
      (fun vertex => geometry.points vertex) differential parentSheet :=
  Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.build leftEntry rightEntry leftDomain
    rightDomain
    (fun vertex => geometry.points vertex) preparation.origin_eq (fun _ => firstFace.cell.box)
    (fun vertex => (preparation.routes.get vertex).path) preparation.prepared
    preparation.leftInside preparation.rightInside differential parentSheet
    (Data.Vector.DependentVector.ofFn fun vertex =>
      Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build (preparation.prepared.get vertex)
      differential parentSheet)

end EndpointPolygonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
