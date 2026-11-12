module
import Purelib.Riemann.Integration.RectangularSharedPrimitives

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Data.Gaussian.Norm.Sum.Indexed
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate

/-! # One actual shared reading bank on a retained fragment word

The word may contain different actual partitions, including new partial
leaves and repeated or stationary occurrences. All analytic split points
request ONE original face-domain mesh bank and ONE sufficient numerical
stage above the supplied minimum. A materialized vector retains each
original fragment comparison on that bank. No source, query, Point, Entry or domain is acquired again.
-/

public section

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration
open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}

/-- Every actual analytic-piece endpoint of the retained word, in its original occurrence order. -/
def wordPoints (pieces : List (LiftedFragment axes domains mesh source count target)) : List Canonical :=
  pieces.flatMap (fun piece => piece.assigned.split.points)

/-- The whole selected split-point bank occurs in the actual word request without a coordinate-based selector. -/
theorem wordPoints_included (pieces : List (LiftedFragment axes domains mesh source count target))
    (position : Fin pieces.length) (point : Canonical)
    (member : point ∈ (pieces[position.val]'position.isLt).assigned.split.points) :
    point ∈ wordPoints pieces :=
  Flatten.mem_flatMap.mpr ⟨pieces[position.val]'position.isLt, List.getElem_mem position.isLt, member⟩

/-- Every retained fragment contributes both literal endpoints to the whole-word request in its own occurrence. -/
theorem wordEndpoints_mem (pieces : List (LiftedFragment axes domains mesh source count target)) :
    ∀ piece ∈ pieces, piece.first ∈ wordPoints pieces ∧ piece.last ∈ wordPoints pieces := by
  intro piece member
  have endpoints := WordPoints.SegmentSplit.endpoints_mem piece.assigned.split
  exact ⟨Flatten.mem_flatMap.mpr ⟨piece, member, endpoints.1⟩,
    Flatten.mem_flatMap.mpr ⟨piece, member, endpoints.2⟩⟩

/-- Sum the actual original local polynomial primitive increments without replacing their owners. -/
def modelSum (pieces : List (LiftedFragment axes domains mesh source count target)) : Canonical :=
  sumFin (fun position : Fin pieces.length =>
  (pieces[position.val]'position.isLt).request.request.model.primitive.value.eval
      (pieces[position.val]'position.isLt).last -
    (pieces[position.val]'position.isLt).request.request.model.primitive.value.eval
      (pieces[position.val]'position.isLt).first)

section

variable {tolerance : Rational} {index : Nat}
variable {numerics : FacePrimitiveBank source index domains}

/-- The original actual fragment readings retained at their exact word positions on one supplied shared bank.

The fixed bulk SheetEntries spines use their original axes.parameters.
This existing dependent vector instead indexes the actual retained word,
so arbitrary partial cuts need no second source spine or datatype.
-/
@[expose] def WordReadings (pieces : List (LiftedFragment axes domains mesh source count target))
    {budgets : FaceMeshBudgets source (wordPoints pieces) tolerance domains}
    (shared : FaceSharedMeshes budgets numerics) : Type 1 :=
  DependentVector (fun position : Fin pieces.length =>
    {value : BankReadings.BankReading (pieces[position.val]'position.isLt).assigned shared //
      value = BankReadings.BankReading.build (pieces[position.val]'position.isLt).assigned shared
        (fun point member => wordPoints_included pieces position point member)})

namespace WordReadings

/-- Materialize each actual retained occurrence once on the same supplied original shared bank. -/
def build (pieces : List (LiftedFragment axes domains mesh source count target))
    {budgets : FaceMeshBudgets source (wordPoints pieces) tolerance domains}
    (shared : FaceSharedMeshes budgets numerics) : WordReadings pieces shared :=
  DependentVector.ofFn (fun position =>
    let compared := BankReadings.BankReading.build (pieces[position.val]'position.isLt).assigned shared
      (fun point member => wordPoints_included pieces position point member)
    ⟨compared, rfl⟩)

end WordReadings

end

/-- Retain the original common budgets, matching numerical bank, shared readings and materialized word comparisons.

The maximum actual face/sheet request and explicit minimum fix the stage
before that stage is built. Complete original caches and factory laws are
stored in Sigma/Subtype containers; no alternative mathematical owner or
final comparison premise is introduced.
-/
@[expose] def WordPreparation (pieces : List (LiftedFragment axes domains mesh source count target))
    (tolerance : Rational) (positive : 0 < tolerance) (minimum : Nat) : Type 1 :=
  Σ budgets : {value : FaceMeshBudgets source (wordPoints pieces) tolerance domains //
    value = FaceMeshBudgets.build source (wordPoints pieces) tolerance positive domains},
  Σ numerics : {value : FacePrimitiveBank source (max budgets.val.index minimum) domains //
    value = FacePrimitiveBank.build source (max budgets.val.index minimum) domains},
  Σ shared : {value : FaceSharedMeshes budgets.val numerics.val //
    value = FaceSharedMeshes.build budgets.val numerics.val (Data.Nat.Order.le_max_left _ _)},
  {value : WordReadings pieces shared.val // value = WordReadings.build pieces shared.val}

namespace WordPreparation

variable (pieces : List (LiftedFragment axes domains mesh source count target))
variable (tolerance : Rational) (positive : 0 < tolerance) (minimum : Nat)

/-- Prepare one common whole-word mesh and primitive bank, then read every original occurrence once.

Numerical polynomials, anchors, offsets and mesh readings at the selected
stage are genuine new numerical work. The old requests, Point/Entry
observations, source owners and ordered word remain supplied caches.
-/
def build : WordPreparation pieces tolerance positive minimum :=
  let budgets := FaceMeshBudgets.build source (wordPoints pieces) tolerance positive domains
  let index := max budgets.index minimum
  let numerics := FacePrimitiveBank.build source index domains
  let shared := FaceSharedMeshes.build budgets numerics (Data.Nat.Order.le_max_left _ _)
  let readings := WordReadings.build pieces shared
  ⟨⟨budgets, rfl⟩, ⟨numerics, rfl⟩, ⟨shared, rfl⟩, ⟨readings, rfl⟩⟩

variable {pieces tolerance positive minimum}
variable (prepared : WordPreparation pieces tolerance positive minimum)

/-- Read the whole original face/sheet mesh-budget bank on all actual word split points. -/
def budgets : FaceMeshBudgets source (wordPoints pieces) tolerance domains := prepared.1.val

/-- Read the single original numerical bank at its actual common sufficient stage. -/
def numerics : FacePrimitiveBank source (max prepared.budgets.index minimum) domains := prepared.2.1.val

/-- Read the same retained mesh readings and their original anchors and offsets. -/
def shared : FaceSharedMeshes prepared.budgets prepared.numerics := prepared.2.2.1.val

/-- Read the materialized comparison vector retaining the original exact occurrence indices. -/
def readings : WordReadings pieces prepared.shared := prepared.2.2.2.val

/-- The complete mesh-budget bank is its original whole-word factory result. -/
theorem budgets_eq : prepared.budgets =
    FaceMeshBudgets.build source (wordPoints pieces) tolerance positive domains := prepared.1.property

/-- The selected numerical stage pays the actual additional minimum before any bank evaluation. -/
theorem minimum_le : minimum ≤ max prepared.budgets.index minimum := Data.Nat.Order.le_max_right _ _

/-- The same stage pays the complete original common mesh request. -/
theorem mesh_index_le : prepared.budgets.index ≤ max prepared.budgets.index minimum :=
  Data.Nat.Order.le_max_left _ _

/-- The whole primitive bank is the original factory at the selected common stage. -/
theorem numerics_eq : prepared.numerics =
    FacePrimitiveBank.build source (max prepared.budgets.index minimum) domains :=
  prepared.2.1.property

/-- The whole common reading bank is the original builder on these exact budgets and numerical cache. -/
theorem shared_eq : prepared.shared =
    FaceSharedMeshes.build prepared.budgets prepared.numerics (Data.Nat.Order.le_max_left _ _) :=
  prepared.2.2.1.property

/-- The entire comparison vector is its once-materialized original cached-input construction. -/
theorem readings_eq : prepared.readings = WordReadings.build pieces prepared.shared := prepared.2.2.2.property

/-- Read the complete original comparison at the exact stored word position, without rerunning its builder. -/
def reading (position : Fin pieces.length) :
    BankReadings.BankReading (pieces[position.val]'position.isLt).assigned prepared.shared :=
  (prepared.readings.get position).val

/-- Each retained comparison is the whole original factory on the same supplied cache and literal occurrence. -/
theorem reading_eq (position : Fin pieces.length) : prepared.reading position =
    BankReadings.BankReading.build (pieces[position.val]'position.isLt).assigned prepared.shared
      (fun point member => wordPoints_included pieces position point member) :=
  (prepared.readings.get position).property

/-- The sampled scalar is the last-minus-first increment in this occurrence's actual common-domain mesh readings. -/
theorem value_eq (position : Fin pieces.length) : (prepared.reading position).value =
    SharedValues.atPoint
        (BankReadings.meshReadings (pieces[position.val]'position.isLt).assigned prepared.shared).readings
        (pieces[position.val]'position.isLt).last -
      SharedValues.atPoint
        (BankReadings.meshReadings (pieces[position.val]'position.isLt).assigned prepared.shared).readings
        (pieces[position.val]'position.isLt).first :=
  (prepared.reading position).value_eq

/-- Every actual analytic-piece endpoint is a vertex of its literal retained face/sheet common mesh. -/
theorem point_on_mesh (position : Fin pieces.length) (point : Canonical)
    (member : point ∈ (pieces[position.val]'position.isLt).assigned.split.points) :
    point ∈ (BankReadings.meshBudget (pieces[position.val]'position.isLt).assigned
      prepared.budgets).mesh.surface.mesh.vertices := by
  let assigned := (pieces[position.val]'position.isLt).assigned
  let budget := BankReadings.meshBudget assigned prepared.budgets
  obtain ⟨piece, present, endpoint⟩ := Flatten.mem_flatMap.mp member
  rcases Membership.mem_cons.mp endpoint with first | last
  · subst point
    exact budget.mesh.point_mem piece.firstPoint (wordPoints_included pieces position _ member)
      piece.column piece.row (PreparedParentSplitting.Geometry.allCells_mem assigned.domain.geometry _ _)
      piece.first_inside
  · rcases Membership.mem_cons.mp last with last | impossible
    · subst point
      exact budget.mesh.point_mem piece.lastPoint (wordPoints_included pieces position _ member)
        piece.column piece.row (PreparedParentSplitting.Geometry.allCells_mem assigned.domain.geometry _ _)
        piece.last_inside
    · exact (List.not_mem_nil impossible).elim

/-- Both actual endpoints are sampled vertices, including stationary and repeated physical occurrences. -/
theorem endpoints_on_mesh (position : Fin pieces.length) :
    (pieces[position.val]'position.isLt).first ∈
        (BankReadings.meshBudget (pieces[position.val]'position.isLt).assigned
          prepared.budgets).mesh.surface.mesh.vertices ∧
      (pieces[position.val]'position.isLt).last ∈
        (BankReadings.meshBudget (pieces[position.val]'position.isLt).assigned
          prepared.budgets).mesh.surface.mesh.vertices :=
  ⟨prepared.point_on_mesh position _ (WordPoints.SegmentSplit.endpoints_mem _).1,
    prepared.point_on_mesh position _ (WordPoints.SegmentSplit.endpoints_mem _).2⟩

/-- Each actual fragment retains its computed full-piece payment against its original local request polynomial. -/
theorem accurate (position : Fin pieces.length) : normSq ((prepared.reading position).value -
    ((pieces[position.val]'position.isLt).request.request.model.primitive.value.eval
        (pieces[position.val]'position.isLt).last -
      (pieces[position.val]'position.isLt).request.request.model.primitive.value.eval
        (pieces[position.val]'position.isLt).first)) ≤ (prepared.reading position).bound :=
  (prepared.reading position).accurate

/-- Each bound contains the actual new split count and the original retained analytic charge sum. -/
theorem bound_eq (position : Fin pieces.length) :
    let assigned := (pieces[position.val]'position.isLt).assigned
    let budget := BankReadings.meshBudget assigned prepared.budgets
    let readings := BankReadings.meshReadings assigned prepared.shared
    (prepared.reading position).bound = countCoordinate assigned.split.count *
      (32 * countCoordinate assigned.split.count *
          (GridPrimitiveAccuracy.atIndex budget.accuracy
            (max prepared.budgets.index minimum) readings.later).globalBound +
        2 * (prepared.reading position).analyticCharge) :=
  (prepared.reading position).bound_eq

/-- The analytic cache is the ordered charge of every actual piece at the same common numerical stage. -/
theorem analyticCharge_eq (position : Fin pieces.length) :
    let assigned := (pieces[position.val]'position.isLt).assigned
    let budget := BankReadings.meshBudget assigned prepared.budgets
    (prepared.reading position).analyticCharge = coordinateSum
      (assigned.split.pieces.map (fun piece =>
        AnalyticComparison.pieceCharge assigned budget.bounds piece (max prepared.budgets.index minimum))) := by
  let assigned := (pieces[position.val]'position.isLt).assigned
  let budget := BankReadings.meshBudget assigned prepared.budgets
  let readings := BankReadings.meshReadings assigned prepared.shared
  have stage := GridPrimitiveAccuracy.atIndex_index budget.accuracy
    (max prepared.budgets.index minimum) readings.later
  exact (prepared.reading position).analyticCharge_eq.trans
    (congrArg (fun index => coordinateSum (assigned.split.pieces.map (fun piece =>
      AnalyticComparison.pieceCharge assigned budget.bounds piece index))) stage)

/-- The finite whole-word payment retains every actual fragment and its actual inner analytic-piece count.

The same retained comparisons supply all terms and all bounds. No fixed
RootGrid cut ceiling is applied to newly refined leaves; old source costs
remain in each original comparison bound.
-/
theorem sum_accurate : normSq (sumFin (fun position : Fin pieces.length => (prepared.reading position).value) -
    modelSum pieces) ≤
      (pieces.length : Rational) * sumFin (fun position : Fin pieces.length => (prepared.reading position).bound) :=
  Indexed.normSq_sumFin_sub_le_count_mul_sumFin _ _ _ prepared.accurate

end WordPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

end
