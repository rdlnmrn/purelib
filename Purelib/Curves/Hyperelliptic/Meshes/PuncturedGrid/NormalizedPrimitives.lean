module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Riemann.Integration.RectangularPrimitiveTranslation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

/-! Fix the additive constant using the retained lower-left corner reading. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.Rat
open Purelib.Riemann.Integration.RectangularPrimitiveTranslation
open Purelib.Riemann.Integration.RectangularPrimitiveTranslation.RectangularInverseModels
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace DomainPrimitives
variable {face : RegularFace bank} {models :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet :
  Fin 2}
  {domain : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat}

/-- Shift cached offsets and corners; keep the expensive primitives and anchors. -/
@[expose]
def normalize (cached : PrimitiveData.DomainPrimitives domain differential index) : PrimitiveData.DomainPrimitives
  domain differential index :=
  ⟨cached.primitives, cached.anchors,
    Offsets.translate cached.offsets (-cached.corners.values 0),
    PointReadings.translate
      cached.corners (-cached.corners.values 0)⟩

/-- Normalizing the cached primitive subtracts its retained lower-left value from every corner reading. -/
theorem normalize_corner (cached : PrimitiveData.DomainPrimitives domain differential index) (corner : Fin 4) :
    cached.normalize.corners.values corner = cached.corners.values corner - cached.corners.values 0 := by
  change (PointReadings.translate
    cached.corners (-cached.corners.values 0)).values corner = _
  rw [PointReadings.translate_value]
  rfl

/-- The normalized retained lower-left corner reading is zero. -/
theorem normalize_origin (cached : PrimitiveData.DomainPrimitives domain differential index) :
    cached.normalize.corners.values 0 = 0 := by
  rw [cached.normalize_corner, sub_self]

/-- Normalization preserves every exact retained corner increment. -/
theorem normalize_increment (cached : PrimitiveData.DomainPrimitives domain differential index) (first last : Fin 4) :
    cached.normalize.corners.values last - cached.normalize.corners.values first =
      cached.corners.values last - cached.corners.values first := by
  rw [cached.normalize_corner, cached.normalize_corner]
  ring1

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners
/-- Every normalized aligned primitive value is shifted by the same retained lower-left reading. -/
theorem normalize_alignedValue (cached : PrimitiveData.DomainPrimitives domain differential index)
    (column row : _) (point : Data.Gaussian.Basic.Canonical) :
    cached.normalize.anchors.alignedValue cached.normalize.offsets column row point =
      cached.anchors.alignedValue cached.offsets column row point - cached.corners.values 0 := by
  exact PrimitiveAnchors.alignedValue_translate
    cached.anchors cached.offsets (-cached.corners.values 0) column row point

/-- Each normalized cell reading at the retained anchor is bounded by four times the paid global overlap error.

The original cached anchors, offsets and lower-left reading supply the zero reference. Subtracting that zero transports
the same retained overlap estimate. -/
theorem normalized_anchor_bound
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    {target : InverseRootPolynomial.Coordinate}
    (request : GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    (column row : Fin (domain.steps + 1))
    (inside : (domain.geometry.box column row).Contains (point face.cell.box 0)) :
    Data.Gaussian.Norm.Basic.normSq
      (cached.normalize.anchors.alignedValue cached.normalize.offsets column row (point face.cell.box 0)) ≤
        4 * request.globalBound := by
  let fixed := cached.normalize.corners
  have fixedInside : (domain.geometry.box (fixed.owners 0).column (fixed.owners 0).row).Contains
      (point face.cell.box 0) := by
    rw [← fixed.point_eq 0]
    exact (fixed.owners 0).contains
  have zero : cached.normalize.anchors.alignedValue cached.normalize.offsets
      (fixed.owners 0).column (fixed.owners 0).row (point face.cell.box 0) = 0 := by
    rw [← fixed.point_eq 0, ← fixed.value_eq 0]
    exact cached.normalize_origin
  have estimate := request.overlap_bound cached.normalize.anchors cached.normalize.offsets
    domain.patch.cell_refines column (fixed.owners 0).column row (fixed.owners 0).row inside fixedInside
  rw [zero, Data.Gaussian.Basic.sub_zero, ← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

/-- With unit target, each normalized cell reading at the retained anchor has squared norm at most four. -/
theorem normalized_anchor_le_four
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    (request : GridPrimitiveAccuracy bounds domain.steps 1)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    (column row : Fin (domain.steps + 1))
    (inside : (domain.geometry.box column row).Contains (point face.cell.box 0)) :
    Data.Gaussian.Norm.Basic.normSq
      (cached.normalize.anchors.alignedValue cached.normalize.offsets column row (point face.cell.box 0)) ≤ 4 := by
  have estimate := cached.normalized_anchor_bound request column row inside
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.accurate.le
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq (by ring1))

/-- Any actual normalized point-owner reading at the retained anchor has squared norm at most four under the unit
request. -/
theorem normalized_reading_anchor_le_four
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    (request : GridPrimitiveAccuracy bounds domain.steps 1)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : PointReadings cached.normalize.anchors cached.normalize.offsets points)
    (vertex : Fin count) (equal : points vertex = point face.cell.box 0) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex) ≤ 4 := by
  rw [readings.value_eq, readings.point_eq, equal]
  apply cached.normalized_anchor_le_four request
  rw [← equal, ← readings.point_eq]
  exact (readings.owners vertex).contains

/-- A zero retained anchor reading bounds every other cell's anchor value by the paid overlap error.

The original cached anchors, offsets and lower-left reading supply the zero reference. Subtracting that zero transports
the same retained overlap estimate. -/
theorem anchor_bound_of_zero
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    {target : InverseRootPolynomial.Coordinate}
    (request : GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    (originZero : cached.corners.values 0 = 0)
    (column row : Fin (domain.steps + 1))
    (inside : (domain.geometry.box column row).Contains (point face.cell.box 0)) :
    Data.Gaussian.Norm.Basic.normSq
      (cached.anchors.alignedValue cached.offsets column row (point face.cell.box 0)) ≤
        4 * request.globalBound := by
  let fixed := cached.corners
  have fixedInside : (domain.geometry.box (fixed.owners 0).column (fixed.owners 0).row).Contains
      (point face.cell.box 0) := by
    rw [← fixed.point_eq 0]
    exact (fixed.owners 0).contains
  have zero : cached.anchors.alignedValue cached.offsets
      (fixed.owners 0).column (fixed.owners 0).row (point face.cell.box 0) = 0 := by
    rw [← fixed.point_eq 0, ← fixed.value_eq 0]
    exact originZero
  have estimate := request.overlap_bound cached.anchors cached.offsets
    domain.patch.cell_refines column (fixed.owners 0).column row (fixed.owners 0).row inside fixedInside
  rw [zero, Data.Gaussian.Basic.sub_zero, ← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

/-- A zero retained anchor and a unit accuracy request bound every cell's anchor value by four. -/
theorem anchor_le_four_of_zero
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    (request : GridPrimitiveAccuracy bounds domain.steps 1)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    (originZero : cached.corners.values 0 = 0)
    (column row : Fin (domain.steps + 1))
    (inside : (domain.geometry.box column row).Contains (point face.cell.box 0)) :
    Data.Gaussian.Norm.Basic.normSq
      (cached.anchors.alignedValue cached.offsets column row (point face.cell.box 0)) ≤ 4 := by
  have estimate := cached.anchor_bound_of_zero request originZero column row inside
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.accurate.le
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq (by ring1))

/-- Any actual owner reading at a zero retained anchor has squared norm at most four under the unit request. -/
theorem reading_anchor_le_four_of_zero
    {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    (request : GridPrimitiveAccuracy bounds domain.steps 1)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    (originZero : cached.corners.values 0 = 0)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : PointReadings cached.anchors cached.offsets points)
    (vertex : Fin count) (equal : points vertex = point face.cell.box 0) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex) ≤ 4 := by
  rw [readings.value_eq, readings.point_eq, equal]
  apply cached.anchor_le_four_of_zero request originZero
  rw [← equal, ← readings.point_eq]
  exact (readings.owners vertex).contains

end DomainPrimitives
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
