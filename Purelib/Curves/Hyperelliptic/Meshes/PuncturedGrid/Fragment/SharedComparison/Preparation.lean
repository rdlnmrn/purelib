module
import Purelib.Riemann.Integration.RectangularSharedPrimitives

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
public import Purelib.Riemann.Readings.RectangularPointReadings.Mesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership

/-! # Numerical preparation on the complete retained fragment split

The mesh request contains every actual analytic-piece endpoint. A genuine
new primitive stage meets that request on the SAME retained domain, while
existing corner readings are reused at matching numerical mesh owners.
The original comparison retains all piece charges and their actual count.
-/

public section

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (DomainMeshBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary
open Purelib.Riemann.Readings
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {axes : PrimitiveAxes base.bank.grid} {parent : CenteredEdge curve source}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {request : LocalRequest parent count target}

/-- Retain one complete mesh request, its matching numerical stage, reused readings and original scalar comparison.

The existing budget fixes the numerical stage before its new polynomials
are built. The existing OnMesh cache retains all corner reuse decisions.
All four complete factory results are stored in original Sigma/Subtype
containers; the source query, Point, Entry and domain are never acquired.
-/
@[expose] def Preparation (assigned : SheetEntry fragment domains request)
    (tolerance : Rational) (positive : 0 < tolerance) : Type :=
  Σ budget : {value : DomainMeshBudget assigned.domain source assigned.split.points tolerance //
    value = DomainMeshBudget.build assigned.domain source assigned.split.points tolerance positive},
  Σ numerics : {value : DomainPrimitives assigned.domain source budget.val.accuracy.index //
    value = DomainPrimitives.build assigned.domain source budget.val.accuracy.index},
  Σ readings : {value : numerics.val.corners.OnMesh budget.val.mesh.surface //
    value = PointReadings.OnMesh.build numerics.val.corners budget.val.mesh.surface},
  {value : SharedComparison (assigned := assigned) (bounds := budget.val.bounds)
      (accuracy := budget.val.accuracy) readings.val.shared //
    value = SharedComparison.build (assigned := assigned) (bounds := budget.val.bounds)
      (accuracy := budget.val.accuracy) readings.val.shared (fun _ member => member)}

namespace Preparation

variable (assigned : SheetEntry fragment domains request) (tolerance : Rational) (positive : 0 < tolerance)

/-- Prepare the complete actual split-point mesh and comparison, evaluating only the new requested numerical stage.

The numerical polynomials, anchors, offsets and corner bank are genuine
new work at the computed stage. The original same-stage corner values are
reused by OnMesh; no earlier arbitrary-stage cut values are retagged.
-/
def build : Preparation assigned tolerance positive :=
  let budget : DomainMeshBudget assigned.domain source assigned.split.points tolerance :=
    DomainMeshBudget.build assigned.domain source assigned.split.points tolerance positive
  let numerics : DomainPrimitives assigned.domain source budget.accuracy.index :=
    DomainPrimitives.build assigned.domain source budget.accuracy.index
  let readings : numerics.corners.OnMesh budget.mesh.surface :=
    PointReadings.OnMesh.build numerics.corners budget.mesh.surface
  let compared : SharedComparison (assigned := assigned) (bounds := budget.bounds)
      (accuracy := budget.accuracy) readings.shared :=
    SharedComparison.build (assigned := assigned) (bounds := budget.bounds) (accuracy := budget.accuracy)
      readings.shared (fun _ member => member)
  ⟨⟨budget, rfl⟩, ⟨numerics, rfl⟩, ⟨readings, rfl⟩, ⟨compared, rfl⟩⟩

variable {assigned tolerance positive}
variable (prepared : Preparation assigned tolerance positive)

/-- Read the complete retained original budget and all-cell mesh request. -/
def budget : DomainMeshBudget assigned.domain source assigned.split.points tolerance := prepared.1.val

/-- Read the genuine original primitive, anchor, offset and corner cache at that budget's exact stage. -/
def numerics : DomainPrimitives assigned.domain source prepared.budget.accuracy.index := prepared.2.1.val

/-- Read the whole original corner-reuse selections and shared reading cache on the same actual mesh. -/
def readings : prepared.numerics.corners.OnMesh prepared.budget.mesh.surface := prepared.2.2.1.val

/-- Read the original scalar comparison on this same complete fragment and mesh. -/
def compared : SharedComparison (assigned := assigned) (bounds := prepared.budget.bounds)
    (accuracy := prepared.budget.accuracy) prepared.readings.shared := prepared.2.2.2.val

/-- The budget is the whole original request on the actual split-point list. -/
theorem budget_eq : prepared.budget =
    DomainMeshBudget.build assigned.domain source assigned.split.points tolerance positive := prepared.1.property

/-- The complete retained mesh is the original constructor on all actual new split points and model cells. -/
theorem mesh_eq : prepared.budget.mesh = RectangularCommonMesh.RectangularInverseModels.CommonMesh.build
    assigned.domain.geometry (RectangularExteriorBoundary.Geometry.allCells assigned.domain.geometry)
      assigned.split.points := by
  have same := congrArg
    (fun value : DomainMeshBudget assigned.domain source assigned.split.points tolerance => value.mesh)
    prepared.budget_eq
  exact same

/-- The numerical cache is the complete original factory at the exact retained requested stage. -/
theorem numerics_eq : prepared.numerics =
    DomainPrimitives.build assigned.domain source prepared.budget.accuracy.index := prepared.2.1.property

/-- The complete original selector and reading cache is built on the same retained corners and mesh. -/
theorem readings_eq : prepared.readings =
    PointReadings.OnMesh.build prepared.numerics.corners prepared.budget.mesh.surface := prepared.2.2.1.property

/-- The scalar comparison is its whole original factory result on these retained readings. -/
theorem compared_eq : prepared.compared =
    SharedComparison.build (assigned := assigned) (bounds := prepared.budget.bounds)
      (accuracy := prepared.budget.accuracy) prepared.readings.shared (fun _ member => member) :=
  prepared.2.2.2.property

/-- Every requested split point is a real vertex of the retained all-cell mesh.

The exact member piece supplies its original column, row and endpoint
containment. Boundary ties and repeated coordinates preserve their actual
piece owners; no off-mesh default value supplies this certificate.
-/
theorem point_on_mesh (point : Canonical) (member : point ∈ assigned.split.points) :
    point ∈ prepared.budget.mesh.surface.mesh.vertices := by
  obtain ⟨piece, present, endpoint⟩ := Flatten.mem_flatMap.mp member
  rcases Membership.mem_cons.mp endpoint with first | last
  · subst point
    exact prepared.budget.mesh.point_mem piece.firstPoint (assigned.split.points_mem present).1
      piece.column piece.row
      (PreparedParentSplitting.Geometry.allCells_mem assigned.domain.geometry _ _) piece.first_inside
  · rcases Membership.mem_cons.mp last with last | impossible
    · subst point
      exact prepared.budget.mesh.point_mem piece.lastPoint (assigned.split.points_mem present).2
        piece.column piece.row
        (PreparedParentSplitting.Geometry.allCells_mem assigned.domain.geometry _ _) piece.last_inside
    · exact (List.not_mem_nil impossible).elim

/-- Both literal fragment endpoints are actual retained mesh vertices, even on a stationary physical parent. -/
theorem endpoints_on_mesh : fragment.located.first ∈ prepared.budget.mesh.surface.mesh.vertices ∧
    fragment.located.last ∈ prepared.budget.mesh.surface.mesh.vertices :=
  ⟨prepared.point_on_mesh _ (WordPoints.SegmentSplit.endpoints_mem assigned.split).1,
    prepared.point_on_mesh _ (WordPoints.SegmentSplit.endpoints_mem assigned.split).2⟩

/-- Every original analytic piece pays the actual ownership allowance and its retained old-request charge. -/
theorem piece_le (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) :
    normSq ((SharedValues.atPoint prepared.readings.shared piece.lastPoint -
      SharedValues.atPoint prepared.readings.shared piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint)) ≤
      32 * prepared.budget.accuracy.globalBound +
        2 * AnalyticComparison.pieceCharge assigned prepared.budget.bounds piece prepared.budget.accuracy.index :=
  SharedComparison.shared_piece_le assigned prepared.budget.bounds prepared.budget.accuracy prepared.budget.mesh
    (fun _ present => present) prepared.readings.shared piece member

/-- The cached scalar is the actual mesh last-minus-first increment of this same complete fragment. -/
theorem value_eq : prepared.compared.value =
    SharedValues.atPoint prepared.readings.shared fragment.located.last -
      SharedValues.atPoint prepared.readings.shared fragment.located.first :=
  prepared.compared.value_eq

/-- The exact bound retains the actual new split count and every original analytic-piece charge. -/
theorem bound_eq : prepared.compared.bound = countCoordinate assigned.split.count *
    (32 * countCoordinate assigned.split.count * prepared.budget.accuracy.globalBound +
      2 * coordinateSum (assigned.split.pieces.map fun piece =>
        AnalyticComparison.pieceCharge assigned prepared.budget.bounds piece prepared.budget.accuracy.index)) :=
  prepared.compared.bound_eq.trans (congrArg
    (fun charge => countCoordinate assigned.split.count *
      (32 * countCoordinate assigned.split.count * prepared.budget.accuracy.globalBound + 2 * charge))
    prepared.compared.analyticCharge_eq)

/-- The actual cached whole-fragment increment pays its computed original comparison bound. -/
theorem accurate : normSq (prepared.compared.value -
    (request.request.model.primitive.value.eval fragment.located.last -
      request.request.model.primitive.value.eval fragment.located.first)) ≤ prepared.compared.bound :=
  prepared.compared.accurate

/-- Only the mesh ownership allowance is forced below the chosen mesh tolerance. -/
theorem ownership_lt : prepared.budget.accuracy.globalBound < tolerance := prepared.budget.accuracy.accurate

/-- The retained finite mesh size uses the actual analytic-piece count, with no fixed RootGrid cut ceiling. -/
theorem mesh_count_le : prepared.budget.mesh.triangleCount ≤
    2 * ((RectangularExteriorBoundary.Geometry.allCells assigned.domain.geometry).length *
      ((2 * assigned.split.count + 1) * (2 * assigned.split.count + 1))) := by
  have bounded := prepared.budget.mesh.count_le
  rewrite [assigned.split.points_length] at bounded
  exact bounded

end Preparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison

end
