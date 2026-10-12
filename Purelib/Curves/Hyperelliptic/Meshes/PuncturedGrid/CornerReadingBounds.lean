module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Data.Rat

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Actual point owners compare to the fixed period corner cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace DomainPrimitives
variable {face : RegularFace bank} {models :
  FaceModels frames face} {sheet :
  Fin 2}
  {domain : PeriodDomain models sheet} {differential :
    Differential genus} {index : Nat}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- An actual point reading agrees with the retained fixed corner cache within four times the paid global primitive
bound. -/
theorem reading_corner_bound
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    {target : InverseRootPolynomial.Coordinate}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings cached.anchors cached.offsets points)
    (vertex : Fin count) (corner : Fin 4)
    (equal : points vertex = FaceCorners.point face.cell.box corner) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex - cached.corners.values corner) ≤ 4 *
      request.globalBound := by
  have leftInside := (readings.owners vertex).contains
  have rightInside := (cached.corners.owners corner).contains
  rw [readings.point_eq, equal] at leftInside
  rw [cached.corners.point_eq] at rightInside
  rw [readings.value_eq, cached.corners.value_eq, readings.point_eq, cached.corners.point_eq, equal]
  have scalar := request.overlap_bound cached.anchors cached.offsets domain.patch.cell_refines
    (readings.owners vertex).column (cached.corners.owners corner).column
    (readings.owners vertex).row (cached.corners.owners corner).row leftInside rightInside
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

/-- An actual pair of endpoint readings agrees with its fixed cached corner increment within sixteen times the paid
global bound. -/
theorem reading_corner_increment_bound
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    {target : InverseRootPolynomial.Coordinate}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target)
    (cached : PrimitiveData.DomainPrimitives domain differential request.index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings cached.anchors cached.offsets points)
    (first last : Fin count) (firstCorner lastCorner : Fin 4)
    (firstEq : points first = FaceCorners.point face.cell.box firstCorner)
    (lastEq : points last = FaceCorners.point face.cell.box lastCorner) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      (cached.corners.values lastCorner - cached.corners.values firstCorner)) ≤ 16 * request.globalBound := by
  have equal : (readings.values last - readings.values first) -
      (cached.corners.values lastCorner - cached.corners.values firstCorner) =
      (readings.values last - cached.corners.values lastCorner) -
      (readings.values first - cached.corners.values firstCorner) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add
        (reading_corner_bound
          request cached readings last lastCorner lastEq)
        (reading_corner_bound
          request cached readings first firstCorner firstEq)) (by decide)).trans_eq (by ring1))

end DomainPrimitives
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerReadingBounds
