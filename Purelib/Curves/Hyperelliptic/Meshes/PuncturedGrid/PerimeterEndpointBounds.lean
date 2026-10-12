module
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

public section

/-! Actual normalized perimeter endpoint corrections have a common-stage
bound independent of the number of retained trace edges. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointBounds

open Purelib.Algebra

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
open Purelib.Riemann.Meshes
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary.HandleAreaBounds
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Riemann.Periods
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideEndpoint sideCenteredArea
  side_centered_remainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {position : Fin base.faces.regulars.length} {sheet : Fin 2}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The endpoint-area discrepancy is bounded by the retained corner magnitudes and endpoint error, independently of the
trace length. -/
private theorem endpoint_bound {count : Nat} {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values) {first last : Stokes.PrimitivePoint} {magnitude error :
      Fraction.Rational}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (firstBound : PrimitivePoint.Bounded first magnitude) (lastBound : PrimitivePoint.Bounded last magnitude)
    (firstError : PrimitivePoint.Bounded ((values 0).sub first) error)
    (lastError : PrimitivePoint.Bounded ((values (Fin.last count)).sub last) error) :
    Data.Gaussian.Norm.Basic.normSq (sample.endpoint - Stokes.edgeArea first last) ≤ 32 * (magnitude + 1) *
      error := by
  have equal : sample.endpoint = Stokes.edgeArea (values 0) (values (Fin.last count)) := by
    rw [sample.endpoint_eq]
    simp only [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.sub]
    ring1
  rw [equal]
  exact PrimitivePoint.area_difference_bound nonnegative errorNonnegative small
    firstBound lastBound firstError lastError

variable
    (firstMagnitude : FaceMagnitudeBank domains
      (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i))
    (secondMagnitude : FaceMagnitudeBank domains
      (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {tolerance : Rational} (positive : 0 < tolerance) (small : 4 * tolerance ≤ 1)
    {liBounds : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds
      (base.faces.regulars[position.val]'position.isLt).clearance
      (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator
        (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i))}
    (li : Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy liBounds
      ((domains.get position).domain sheet).steps tolerance) (liLater : li.index ≤ stage)
    {ljBounds : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds
      (base.faces.regulars[position.val]'position.isLt).clearance
      (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator
        (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j))}
    (lj : Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy ljBounds
      ((domains.get position).domain sheet).steps tolerance) (ljLater : lj.index ≤ stage)
    {traces : PerimeterTraces ((request.entries.get
      sheet).meshes.entries.get position)}
    (samples : Centered traces
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position
      sheet))

include firstLater secondLater positive small liLater ljLater

/-- The actual normalized bottom endpoint contribution meets the common corner-error bound at every paid stage. -/
theorem bottom_endpoint_bound :
    Data.Gaussian.Norm.Basic.normSq (samples.bottom.endpoint - Numerics.sideChord cache.normalize i j position
      sheet .bottom) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  apply endpoint_bound samples.bottom (add_nonneg
    firstMagnitude.nonnegative secondMagnitude.nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le) small
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 0)
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 1)
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_bottom_first_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.bottom.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_bottom_first_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.bottom.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_bottom_last_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.bottom.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_bottom_last_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.bottom.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))

/-- The actual normalized top endpoint contribution meets the common corner-error bound at every paid stage. -/
theorem top_endpoint_bound :
    Data.Gaussian.Norm.Basic.normSq (samples.top.endpoint - Numerics.sideChord cache.normalize i j position
      sheet .top) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  apply endpoint_bound samples.top (add_nonneg
    firstMagnitude.nonnegative secondMagnitude.nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le) small
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 3)
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 2)
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_top_first_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.top.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_top_first_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.top.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_top_last_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.top.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_top_last_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.top.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))

/-- The actual normalized left endpoint contribution meets the common corner-error bound at every paid stage. -/
theorem left_endpoint_bound :
    Data.Gaussian.Norm.Basic.normSq (samples.left.endpoint - Numerics.sideChord cache.normalize i j position
      sheet .left) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  apply endpoint_bound samples.left (add_nonneg
    firstMagnitude.nonnegative secondMagnitude.nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le) small
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 0)
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 3)
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_left_first_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.left.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_left_first_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.left.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_left_last_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.left.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_left_last_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.left.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))

/-- The actual normalized right endpoint contribution meets the common corner-error bound at every paid stage. -/
theorem right_endpoint_bound :
    Data.Gaussian.Norm.Basic.normSq (samples.right.endpoint - Numerics.sideChord cache.normalize i j position
      sheet .right) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  apply endpoint_bound samples.right (add_nonneg
    firstMagnitude.nonnegative secondMagnitude.nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le) small
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 1)
    (Numerics.normalized_corner_pair_bound firstMagnitude secondMagnitude firstLater secondLater cache position sheet 2)
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_right_first_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.right.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_right_first_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.right.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  · constructor
    · have estimate := PerimeterCornerReadings.perimeter_right_last_bound
        (GridPrimitiveAccuracy.atIndex li stage liLater) (cache.normalize.atDomain position sheet i) traces
      rw [traces.right.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex li stage liLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · have estimate := PerimeterCornerReadings.perimeter_right_last_bound
        (GridPrimitiveAccuracy.atIndex lj stage ljLater) (cache.normalize.atDomain position sheet j) traces
      rw [traces.right.leftReadings_value] at estimate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
      exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (GridPrimitiveAccuracy.atIndex lj stage ljLater).accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))

/-- Every retained normalized side endpoint contribution satisfies the same original magnitude and primitive-error
bound. -/
theorem side_endpoint_bound (side : GridLiftedDualSteps.GridSide) :
    Data.Gaussian.Norm.Basic.normSq (SideCenteredRemainder.sideEndpoint samples side - Numerics.sideChord
      cache.normalize i j position sheet side) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  cases side with
  | bottom =>
    exact bottom_endpoint_bound firstMagnitude
      secondMagnitude firstLater secondLater
        positive small li liLater lj ljLater samples
  | top =>
    exact top_endpoint_bound firstMagnitude
      secondMagnitude firstLater secondLater
        positive small li liLater lj ljLater samples
  | left =>
    exact left_endpoint_bound firstMagnitude
      secondMagnitude firstLater secondLater
        positive small li liLater lj ljLater samples
  | right =>
    exact right_endpoint_bound firstMagnitude
      secondMagnitude firstLater secondLater
        positive small li liLater lj ljLater samples

/-- The original side-area remainder approximates its actual centered trace area within the retained endpoint-error
budget. -/
theorem side_remainder_centered_bound
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j) (side :
      GridLiftedDualSteps.GridSide) :
    Data.Gaussian.Norm.Basic.normSq (HoleAreaRemainder.sideAreaRemainder perimeters position sheet side -
      SideCenteredRemainder.sideCenteredArea samples side) ≤
      32 * (firstMagnitude.bound + secondMagnitude.bound + 1) * (4 * tolerance) := by
  rw [SideCenteredRemainder.side_centered_remainder samples perimeters side, Group.add_sub_cancel_left]
  exact side_endpoint_bound firstMagnitude
    secondMagnitude firstLater secondLater
    positive small li liLater lj ljLater samples side

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointBounds

end
