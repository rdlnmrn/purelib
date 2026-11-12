module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary

import Purelib.Riemann.Integration.RectangularSharedPrimitives

/-! # Actual old-left and new-right endpoint readings for one retained route

The supplied original endpoint view remains data. The actual route face
reads the same P bank and point list, retaining its own domain data, budget,
shared readings, two containing locations, two real lookups and point view.
Neither physical roots nor contact geometry are constructed by this operation.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
  (DomainMeshBudget DomainMeshReadings FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry (Located)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularSharedPrimitives
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
    {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
    {domains : FaceDomainBank frames base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
    {target tolerance : Rational} {points : List Canonical} {index : Nat}
    {ordinary : Ordinary curve.polynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := ordinary.numerator) domains}
    {shared : FaceSharedMeshes budgets numerics}
    {piece : LiftedFragment axes domains mesh source count target}
    {location : EdgeRoute mesh piece.occurrence.side.edge}
    {included : ∀ value ∈ piece.assigned.split.points, value ∈ points}

namespace EndpointView

/-- The two real containing cells in the actual selected route domain. -/
@[expose] def Locations := DependentVector fun slot : Fin 2 =>
  Located ((domains.atRoute location).domain location.sheet).geometry (EndpointReadings.point piece.fragment slot)

/-- Each literal partial endpoint lies in the retained route occurrence's actual face. -/
private theorem point_inside (slot : Fin 2) :
    location.face.cell.box.Contains (EndpointReadings.point piece.fragment slot) := by
  refine Fin.cases ?_ (fun _ => ?_) slot
  · exact (route_endpoints_inside piece location).1
  · exact (route_endpoints_inside piece location).2

/-- Locate both route endpoint slots once using their actual face-containment certificates. -/
def locateEndpoints : Locations (piece := piece) (location := location) :=
  DependentVector.ofFn fun slot => EnteredPaths.PeriodDomain.locate
    ((domains.atRoute location).domain location.sheet) (EndpointReadings.point piece.fragment slot)
    (point_inside (piece := piece) (location := location) slot)

/-- The original point-list membership gives both actual partial-route lookups. -/
@[expose] def Lookups
    (budget : DomainMeshBudget ((domains.atRoute location).domain location.sheet) source points tolerance
      (numerator := ordinary.numerator)) :=
  DependentVector fun slot : Fin 2 =>
    VertexLookup budget.mesh.surface.mesh.vertices (EndpointReadings.point piece.fragment slot)

/-- The whole original endpoint view and actual source/numerator/bank/route inputs remain data. -/
abbrev Inputs (originalLeft : EndpointReadings.Cache piece.assigned shared included) :=
  {value : EndpointReadings.Cache piece.assigned shared included // value = originalLeft} ×
  {value : FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains ×
      FacePrimitiveBank source index (numerator := ordinary.numerator) domains ×
      FaceSharedMeshes budgets numerics × Ordinary curve.polynomial × Differential genus × Nat ×
      LiftedFragment axes domains mesh source count target × EdgeRoute mesh piece.occurrence.side.edge //
    value = (budgets, numerics, shared, ordinary, source, index, piece, location)}

end EndpointView

/-- The supplied left view and one actual numerical right-route endpoint cache on the same bank.

Every right prefix value and whole factory is retained before constructing
its genuine two lookups and original PointReadings.ofShared. Both endpoint
slots survive even when their coordinates agree. Primitive offsets and
numeric/source stages are never identified across the two domains.
-/
@[expose] def EndpointView (originalLeft : EndpointReadings.Cache piece.assigned shared included) : Type _ :=
  EndpointView.Inputs (ordinary := ordinary) (piece := piece) (location := location) originalLeft ×
  (data : {value : DomainPrimitives ((domains.atRoute location).domain location.sheet) source index
      (numerator := ordinary.numerator) //
    value = (FacePrimitiveBank.atRoute numerics location).atSheet location.sheet}) ×
  (budget : {value : DomainMeshBudget ((domains.atRoute location).domain location.sheet) source points tolerance
      (numerator := ordinary.numerator) //
    value = (MeshWords.FaceMeshBudgets.atRoute budgets location).atSheet location.sheet}) ×
  (readings : {value : DomainMeshReadings budget.val data.val //
    HEq value ((MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet)}) ×
  (locations : {value : EndpointView.Locations (piece := piece) (location := location) //
    value = EndpointView.locateEndpoints (piece := piece) (location := location)}) ×
  (lookups : {value : EndpointView.Lookups (ordinary := ordinary) (piece := piece) (location := location) budget.val //
    value = budget.val.lookupPoints (EndpointReadings.point piece.fragment) locations.val
      (EndpointReadings.point_mem piece.assigned included)}) ×
  {value : PointReadings data.val.anchors data.val.offsets (EndpointReadings.point piece.fragment) //
    value = PointReadings.ofShared readings.val.readings (fun slot => (lookups.val.get slot).index)
      (EndpointReadings.point piece.fragment) (fun slot => (lookups.val.get slot).coordinate_eq)}

namespace EndpointView

variable (originalLeft : EndpointReadings.Cache piece.assigned shared included)

/-- Complete the actual numerical endpoint suffix on the given retained right-cache prefix. -/
private def onCaches
    (inputs : Inputs (ordinary := ordinary) (piece := piece) (location := location) originalLeft)
    (data : {value : DomainPrimitives ((domains.atRoute location).domain location.sheet) source index
        (numerator := ordinary.numerator) //
      value = (FacePrimitiveBank.atRoute numerics location).atSheet location.sheet})
    (budget : {value : DomainMeshBudget ((domains.atRoute location).domain location.sheet) source points tolerance
        (numerator := ordinary.numerator) //
      value = (MeshWords.FaceMeshBudgets.atRoute budgets location).atSheet location.sheet})
    (readings : {value : DomainMeshReadings budget.val data.val //
      HEq value ((MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet)})
    (locations : {value : Locations (piece := piece) (location := location) //
      value = locateEndpoints (piece := piece) (location := location)}) :
    EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft :=
  let lookups : {value : Lookups (ordinary := ordinary) (piece := piece) (location := location) budget.val //
      value = budget.val.lookupPoints (EndpointReadings.point piece.fragment) locations.val
        (EndpointReadings.point_mem piece.assigned included)} :=
    ⟨budget.val.lookupPoints (EndpointReadings.point piece.fragment) locations.val
      (EndpointReadings.point_mem piece.assigned included), rfl⟩
  let reading := PointReadings.ofShared readings.val.readings (fun slot => (lookups.val.get slot).index)
    (EndpointReadings.point piece.fragment) (fun slot => (lookups.val.get slot).coordinate_eq)
  ⟨inputs, data, budget, readings, locations, lookups, ⟨reading, rfl⟩⟩

/-- Reuse the whole supplied left view and read each actual right bank/cache prefix once before its two real lookups.

Only the route's numerical cell locations, lookups and selected-value view
are newly constructed. The given source piece, route, physical endpoint
cache, root/Entry owners and primitive/shared banks are retained.
-/
def build : EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft :=
  let inputs : Inputs (ordinary := ordinary) (piece := piece) (location := location) originalLeft :=
    ⟨⟨originalLeft, rfl⟩, ⟨(budgets, numerics, shared, ordinary, source, index, piece, location), rfl⟩⟩
  let data : {value : DomainPrimitives ((domains.atRoute location).domain location.sheet) source index
      (numerator := ordinary.numerator) //
      value = (FacePrimitiveBank.atRoute numerics location).atSheet location.sheet} :=
    ⟨(FacePrimitiveBank.atRoute numerics location).atSheet location.sheet, rfl⟩
  let budget : {value : DomainMeshBudget ((domains.atRoute location).domain location.sheet) source points tolerance
      (numerator := ordinary.numerator) //
      value = (MeshWords.FaceMeshBudgets.atRoute budgets location).atSheet location.sheet} :=
    ⟨(MeshWords.FaceMeshBudgets.atRoute budgets location).atSheet location.sheet, rfl⟩
  let readings : {value : DomainMeshReadings budget.val data.val //
      HEq value ((MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet)} :=
    ⟨(MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet, HEq.rfl⟩
  let locations : {value : Locations (piece := piece) (location := location) //
      value = locateEndpoints (piece := piece) (location := location)} :=
    ⟨locateEndpoints (piece := piece) (location := location), rfl⟩
  onCaches (ordinary := ordinary) originalLeft inputs data budget readings locations

variable {originalLeft}
    (kept : EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft)

/-- Read the certified whole original left view and complete same-bank route input product. -/
@[expose] def inputs : Inputs (ordinary := ordinary) (piece := piece) (location := location) originalLeft := kept.1

/-- Read the actual original left endpoint view without another builder or lookup. -/
@[expose] def leftView : EndpointReadings.Cache piece.assigned shared included := kept.1.1.val

/-- Read the SAME actual routed-domain primitive data. -/
@[expose] def data : DomainPrimitives ((domains.atRoute location).domain location.sheet) source index
    (numerator := ordinary.numerator) := kept.2.1.val

/-- Read the SAME actual routed-domain numerical mesh budget. -/
@[expose] def budget : DomainMeshBudget ((domains.atRoute location).domain location.sheet) source points tolerance
    (numerator := ordinary.numerator) := kept.2.2.1.val

/-- Read the actual cached routed-domain mesh values with their whole original input relationship. -/
@[expose] def meshValues : DomainMeshReadings kept.budget kept.data := kept.2.2.2.1.val

/-- Read both actual routed-domain containing cells. -/
@[expose] def locations : Locations (piece := piece) (location := location) := kept.2.2.2.2.1.val

/-- Read both real routed-domain lookup results in their original slot order. -/
@[expose] def lookups : Lookups (ordinary := ordinary) (piece := piece) (location := location) kept.budget :=
  kept.2.2.2.2.2.1.val

/-- Read the original selected-value PointReadings on those two cached lookup indices. -/
@[expose] def reading : PointReadings kept.data.anchors kept.data.offsets (EndpointReadings.point piece.fragment) :=
  kept.2.2.2.2.2.2.val

/-- The whole original left cache is exactly the supplied input. -/
theorem leftView_eq : kept.leftView = originalLeft := kept.1.1.property

/-- The right primitive data is its actual original route/sheet bank getter. -/
theorem data_eq : kept.data = (FacePrimitiveBank.atRoute numerics location).atSheet location.sheet :=
  kept.2.1.property

/-- The right numerical budget is its actual original route/sheet getter. -/
theorem budget_eq : kept.budget = (MeshWords.FaceMeshBudgets.atRoute budgets location).atSheet location.sheet :=
  kept.2.2.1.property

/-- The complete cached right mesh reading retains its actual whole original bank input. -/
theorem meshValues_heq : HEq kept.meshValues
    ((MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet) := kept.2.2.2.1.property

/-- The two actual containing-cell locations retain their single original factory. -/
theorem locations_eq : kept.locations = locateEndpoints (piece := piece) (location := location) :=
  kept.2.2.2.2.1.property

/-- Both actual lookup results retain their original ordered shared worker and point-list memberships. -/
theorem lookups_eq : kept.lookups = kept.budget.lookupPoints (EndpointReadings.point piece.fragment)
    kept.locations (EndpointReadings.point_mem piece.assigned included) := kept.2.2.2.2.2.1.property

/-- The actual point view is the original constructor on the SAME right mesh and two real lookup caches. -/
theorem reading_eq : kept.reading = PointReadings.ofShared kept.meshValues.readings
    (fun slot => (kept.lookups.get slot).index) (EndpointReadings.point piece.fragment)
    (fun slot => (kept.lookups.get slot).coordinate_eq) := kept.2.2.2.2.2.2.property

/-- Every right endpoint slot retains its actual original numerical mesh cell owner. -/
theorem owner_eq (slot : Fin 2) : kept.reading.owners slot =
    kept.budget.mesh.surface.owners (kept.lookups.get slot).index :=
  (congrArg (fun value : PointReadings kept.data.anchors kept.data.offsets (EndpointReadings.point piece.fragment) =>
    value.owners slot) kept.reading_eq).trans (PointReadings.ofShared_owner _ _ _ _ slot)

/-- Each literal right slot reads the same original cached mesh vertex value. -/
theorem value_eq (slot : Fin 2) : kept.reading.values slot =
    kept.meshValues.readings.values (kept.lookups.get slot).index :=
  (congrArg (fun value : PointReadings kept.data.anchors kept.data.offsets (EndpointReadings.point piece.fragment) =>
    value.values slot) kept.reading_eq).trans (PointReadings.ofShared_value _ _ _ _ slot)

/-- Each right slot equals the actual old atPoint reading, by its own lookup coordinate and full cached transports. -/
theorem value_eq_atPoint (slot : Fin 2) : kept.reading.values slot =
    SharedPrimitiveValues.atPoint
      ((MeshWords.FaceSharedMeshes.atRoute shared location).atSheet location.sheet).readings
      (EndpointReadings.point piece.fragment slot) :=
  (kept.value_eq slot).trans
    ((SharedPrimitiveValues.atPoint_coordinate kept.meshValues.readings (kept.lookups.get slot).index).symm.trans
      ((congrArg (SharedPrimitiveValues.atPoint kept.meshValues.readings)
        (kept.lookups.get slot).coordinate_eq).trans
        (DomainMeshReadings.atPoint_congr
          (domain := (domains.atRoute location).domain location.sheet) kept.data_eq kept.budget_eq
          kept.meshValues_heq (EndpointReadings.point piece.fragment slot))))

/-- The same two actual right endpoint readings are precisely the original partial route increment. -/
theorem increment_eq : kept.reading.values 1 - kept.reading.values 0 = routeValue piece location shared :=
  congrArg₂ (· - ·) (kept.value_eq_atPoint 1) (kept.value_eq_atPoint 0)

end EndpointView

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
