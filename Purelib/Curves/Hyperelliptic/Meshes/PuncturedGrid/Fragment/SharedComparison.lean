module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Shared mesh values for an entire original period fragment

Every analytic subfragment pays both ownership discrepancies and its inverse
residual. Exact telescoping leaves the two shared endpoint values; finite
Cauchy--Schwarz retains the complete analytic-piece count.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularExteriorBoundary

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate countCoordinate_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differential genus}
  {axes : PrimitiveAxes base.bank.grid}
    {parent : CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}
  {assigned :
    SheetEntry fragment
    domains request}

namespace SharedComparison

/-- Read the retained primitive cache through its original face and domain.

The numerical lookup uses the retained face, sheet and domain identities.
It returns the original primitive, anchor, offset and corner caches. -/
@[expose] def sharedPrimitives (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) {index : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank source index domains) :
    PrimitiveData.DomainPrimitives assigned.domain source index :=
  (((numerics.get fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain
    assigned.domain_eq.symm

end SharedComparison

variable
  {bounds : FragmentBounds assigned.domain.patch
    source}
  {globalBounds : PrimitiveOverlapBounds
    fragment.face.located.face.clearance (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator
    source)}
  {tolerance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {accuracy :
    GridPrimitiveAccuracy globalBounds assigned.domain.steps
    tolerance}
  {primitives : Primitives
    (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented (assigned.domain.patch.sheets.refine
    accuracy.index).transitions (assigned.domain.patch.sheets.refine accuracy.index).gauge)
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator source)}
  {anchors : PrimitiveAnchors primitives} {offsets :
    LinearAlgebra.Grid.Offsets anchors.edges}
  {points : List Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {mesh : CommonMesh
    assigned.domain.geometry (Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry.allCells
    assigned.domain.geometry) points}

namespace SharedComparison

/-- Vertex lookups are proved from inclusion in the common mesh's point bank. They do not re-evaluate any primitive or
prepare another root. -/
theorem shared_piece_le (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (bounds : FragmentReadings.FragmentBounds assigned.domain.patch source)
    {globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds fragment.face.located.face.clearance
      (PreparedPrimitiveSamples.differentialNumerator source)}
    {tolerance : InverseRootPolynomial.Coordinate} (accuracy : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy
      globalBounds assigned.domain.steps tolerance)
    {primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine
      accuracy.index).transitions (assigned.domain.patch.sheets.refine accuracy.index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator source)}
    {anchors : RectangularPrimitiveGluing.PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets
      anchors.edges}
    {points : List InverseRootPolynomial.Gaussian} (mesh : RectangularInverseModels.CommonMesh assigned.domain.geometry
      (Geometry.allCells assigned.domain.geometry) points)
    (included : ∀ point ∈ assigned.split.points, point ∈ points)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
    (piece : RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) :
    Data.Gaussian.Norm.Basic.normSq (((SharedPrimitiveValues.atPoint readings) piece.lastPoint -
      (SharedPrimitiveValues.atPoint readings) piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint)) ≤
      32 * accuracy.globalBound + 2 * AnalyticComparison.pieceCharge assigned bounds piece accuracy.index := by
  have ends := assigned.split.points_mem member
  let first := mesh.lookup piece.firstPoint (included _ ends.1) piece.column piece.row
    (Geometry.allCells_mem assigned.domain.geometry _ _) piece.first_inside
  let last := mesh.lookup piece.lastPoint (included _ ends.2) piece.column piece.row
    (Geometry.allCells_mem assigned.domain.geometry _ _) piece.last_inside
  have firstEq : mesh.surface.mesh.coordinate first.index = piece.firstPoint := first.coordinate_eq
  have lastEq : mesh.surface.mesh.coordinate last.index = piece.lastPoint := last.coordinate_eq
  have ownership := GridPrimitiveAccuracy.shared_local_increment_bound
    accuracy readings assigned.domain.patch.cell_refines
    piece.column piece.row first.index last.index (firstEq.symm ▸ piece.first_inside)
    (lastEq.symm ▸ piece.last_inside)
  rw [← SharedPrimitiveValues.atPoint_coordinate readings first.index, ← SharedPrimitiveValues.atPoint_coordinate
    readings last.index,
    firstEq, lastEq] at ownership
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at ownership
  have analytic := AnalyticComparison.piece_increment_le
    assigned bounds piece member primitives
  have identity : ((SharedPrimitiveValues.atPoint readings) piece.lastPoint - (SharedPrimitiveValues.atPoint readings)
    piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint) =
      (((SharedPrimitiveValues.atPoint readings) piece.lastPoint - (SharedPrimitiveValues.atPoint readings)
        piece.firstPoint) -
        (primitives.value piece.column piece.row piece.lastPoint - primitives.value piece.column piece.row
          piece.firstPoint)) +
      ((primitives.value piece.column piece.row piece.lastPoint - primitives.value piece.column piece.row
        piece.firstPoint) -
        (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
          piece.firstPoint)) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add ownership analytic) (by decide)).trans_eq
      (by ring1))

/-- The finite sum of actual Gaussian squared norms is bounded by the sum of the supplied entrywise charges. -/
private theorem normSum_map_le {α : Type} (items : List α) (values : α → InverseRootPolynomial.Gaussian) (charges : α →
  InverseRootPolynomial.Coordinate)
    (bounded : ∀ item ∈ items, Data.Gaussian.Norm.Basic.normSq (values item) ≤ charges item) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (items.map values) ≤ Squares.coordinateSum (items.map charges) := by
  induction items with
  | nil => exact le_rfl
  | cons head tail ih =>
      have headBound := bounded head List.mem_cons_self
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at headBound
      exact add_le_add headBound
        (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

/-- Split the finite charge sum into ownership and analytic contributions.

Each original occurrence contributes the fixed ownership and analytic factors.
The equality separates their complete ordered sum without changing the entries. -/
private theorem charge_sum {α : Type} (items : List α) (charges : α → InverseRootPolynomial.Coordinate) (constant :
  InverseRootPolynomial.Coordinate) :
    Squares.coordinateSum (items.map fun item => 32 * constant + 2 * charges item) =
      32 * Aggregate.countCoordinate items.length * constant + 2 * Squares.coordinateSum (items.map charges) := by
  simp only [Aggregate.countCoordinate_eq]
  induction items with
  | nil => change (0 : InverseRootPolynomial.Coordinate) = 32 * 0 * constant + 2 * 0; ring1
  | cons head tail ih =>
      simp only [List.map_cons, Squares.coordinateSum, List.length_cons, Algebra.NatCast.add, Nat.cast_one, ih]
      ring1

/-- The complete original fragment is compared to the shared values of the supplied mesh. Every analytic-piece and
endpoint-ownership charge remains visible; no closed-path or zero-total cancellation is used. -/
theorem shared_increment_le (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
    (included : ∀ point ∈ assigned.split.points, point ∈ points) :
    Data.Gaussian.Norm.Basic.normSq (((SharedPrimitiveValues.atPoint readings) fragment.located.last -
      (SharedPrimitiveValues.atPoint readings) fragment.located.first) -
      (request.request.model.primitive.value.eval fragment.located.last -
        request.request.model.primitive.value.eval fragment.located.first)) ≤
      Aggregate.countCoordinate assigned.split.count * (32 * Aggregate.countCoordinate assigned.split.count *
        accuracy.globalBound +
        2 * Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge assigned bounds
          piece accuracy.index)) := by
  let error := fun (piece : RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
    fragment.located.last) =>
    ((SharedPrimitiveValues.atPoint readings) piece.lastPoint - request.request.model.primitive.value.eval
      piece.lastPoint) -
      ((SharedPrimitiveValues.atPoint readings) piece.firstPoint - request.request.model.primitive.value.eval
        piece.firstPoint)
  let charges := fun piece => 32 * accuracy.globalBound + 2 * AnalyticComparison.pieceCharge assigned bounds piece
    accuracy.index
  have bounded : ∀ piece ∈ assigned.split.pieces, Data.Gaussian.Norm.Basic.normSq (error piece) ≤ charges piece
    := by
    intro piece member
    have estimate := shared_piece_le assigned bounds
      accuracy mesh included readings piece member
    exact (by congr 1; dsimp only [error]; ring1 : Data.Gaussian.Norm.Basic.normSq (error piece) = _).trans_le
      estimate
  have total := Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (assigned.split.pieces.map error)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at total
  rw [Data.List.Map.length_map] at total
  have paid := total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (normSum_map_le assigned.split.pieces error
      charges bounded)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le assigned.split.pieces.length)))
  have telescope := assigned.split.telescope (fun point => (SharedPrimitiveValues.atPoint readings) point -
    request.request.model.primitive.value.eval point)
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.split.pieces.map error) = _ at telescope
  rw [telescope] at paid
  have identity : ((SharedPrimitiveValues.atPoint readings) fragment.located.last - (SharedPrimitiveValues.atPoint
    readings) fragment.located.first) -
      (request.request.model.primitive.value.eval fragment.located.last - request.request.model.primitive.value.eval
        fragment.located.first) =
      ((SharedPrimitiveValues.atPoint readings) fragment.located.last - request.request.model.primitive.value.eval
        fragment.located.last) -
        ((SharedPrimitiveValues.atPoint readings) fragment.located.first - request.request.model.primitive.value.eval
          fragment.located.first) := by ring1
  rw [identity]
  exact paid.trans_eq (by
    dsimp only [charges]
    rw [charge_sum, assigned.split.count_eq,
      Aggregate.countCoordinate_eq])

end SharedComparison

set_option genInjectivity false in
/-- Cached scalar comparison for an original fragment and shared mesh.

The endpoint difference and ordered analytic-charge sum are retained caches.
Their exact equations and error certificate use the original request and mesh. -/
structure SharedComparison (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
  where
  /-- The cached difference of the two actual shared endpoint readings. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached value is exactly the original fragment's shared last-minus-first reading. -/ value_eq : value =
    (SharedPrimitiveValues.atPoint readings) fragment.located.last - (SharedPrimitiveValues.atPoint readings)
    fragment.located.first
  /-- The cached sum of every original retained analytic-piece charge. -/ analyticCharge :
    InverseRootPolynomial.Coordinate
  /-- The charge cache equals the exact ordered analytic-piece sum at the retained accuracy index. -/ analyticCharge_eq
    : analyticCharge = Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge
    assigned bounds piece accuracy.index)
  /-- The cached complete fragment discrepancy bound, including its original piece count and ownership allowance. -/
    bound : InverseRootPolynomial.Coordinate
  /-- The bound is the exact piece-count payment for both retained ownership and analytic charges. -/ bound_eq : bound =
    Aggregate.countCoordinate assigned.split.count *
    (32 * Aggregate.countCoordinate assigned.split.count * accuracy.globalBound + 2 * analyticCharge)
  /-- The cached shared increment differs from the original prepared primitive increment by at most the retained full
    bound. -/ accurate : Data.Gaussian.Norm.Basic.normSq (value - (request.request.model.primitive.value.eval
    fragment.located.last -
    request.request.model.primitive.value.eval fragment.located.first)) ≤ bound

constructive_injectivity SharedComparison

namespace SharedComparison

/-- Cache the actual shared endpoint difference and complete analytic-piece charge sum, retaining their exact fragment
bound. -/
@[expose] def build (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets
  mesh.surface)
    (included : ∀ point ∈ assigned.split.points, point ∈ points) :
    SharedComparison (bounds := bounds) (accuracy :=
      accuracy) readings :=
  let charge := Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge assigned
    bounds piece accuracy.index)
  ⟨(SharedPrimitiveValues.atPoint readings) fragment.located.last - (SharedPrimitiveValues.atPoint readings)
    fragment.located.first, rfl, charge, rfl,
    Aggregate.countCoordinate assigned.split.count * (32 * Aggregate.countCoordinate assigned.split.count *
      accuracy.globalBound + 2 * charge), rfl,
    shared_increment_le readings included⟩

end SharedComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
