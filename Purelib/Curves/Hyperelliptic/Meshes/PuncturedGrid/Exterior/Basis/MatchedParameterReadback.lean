module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularParentTraceSteps
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MatchedFragments
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Paths

@[expose] public section

/-! Exact endpoints, orientation and dyadic bounds for cached physical fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
variable {lc lr rc rr depth : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}

namespace ParentBlock
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence false
    forward (left.partition.x.intervals[column.val]'column.isLt))

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
    (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

local notation "fragment" => block.horizontalFragment (originals := originals) (coefficients := coefficients)
  trace column sourceFirst sourceLast budget owners later original

/-- The cached horizontal physical fragment begins at its original parent block's first parameter. -/
theorem horizontalFragment_first : (fragment).parameters 0 = block.firstParameter :=
  RectangularParentTraceSteps.first_parameter (block.horizontalParameters trace column sourceFirst sourceLast)

/-- The cached horizontal physical fragment ends at its original parent block's last parameter. -/
theorem horizontalFragment_last :
    (fragment).parameters (Fin.last (fragment).vertices) = block.lastParameter :=
  (block.horizontalParameters trace column sourceFirst sourceLast).last_parameter

/-- Read the actual retained dyadic parameter step, with its orientation. -/
theorem horizontalFragment_step (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    (fragment).parameters edge.succ - (fragment).parameters edge.castSucc =
      (1 / 2 : InverseRootPolynomial.Coordinate)^depth * (block.lastParameter - block.firstParameter) :=
  RectangularParentTraceSteps.dyadic_step (block.horizontalParameters trace column sourceFirst sourceLast)
    (trace.segments_eq column) edge

/-- Every original horizontal fragment step follows its retained source orientation. -/
theorem horizontalFragment_ordered (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    if forward then (fragment).parameters edge.castSucc ≤ (fragment).parameters edge.succ
    else (fragment).parameters edge.succ ≤ (fragment).parameters edge.castSucc :=
  (fragment).ordered edge

/-- The physical dyadic depth pays the source mesh-width bound directly. -/
theorem horizontalFragment_sourceWidth : (fragment).sourceWidth ≤ (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  apply SourceSampleResampling.meshWidth_le _ true (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)
  intro edge
  apply RectangularParentTraceSteps.dyadic_step_le (block.horizontalParameters trace column sourceFirst sourceLast)
    (trace.segments_eq column)
  · cases forward with
    | true => exact block.parameters.within.1
    | false => exact block.parameters.within.1.trans block.parameters.range.ordered.le
  · cases forward with
    | true => exact block.parameters.within.2
    | false => exact block.parameters.range.ordered.le.trans block.parameters.within.2

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence true
    forward (left.partition.y.intervals[row.val]'row.isLt))

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
    (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

local notation "fragment" => block.verticalFragment (originals := originals) (coefficients := coefficients)
  trace row sourceFirst sourceLast budget owners later original

/-- The cached vertical physical fragment begins at its original parent block's first parameter. -/
theorem verticalFragment_first : (fragment).parameters 0 = block.firstParameter :=
  RectangularParentTraceSteps.first_parameter (block.verticalParameters trace row sourceFirst sourceLast)

/-- The cached vertical physical fragment ends at its original parent block's last parameter. -/
theorem verticalFragment_last :
    (fragment).parameters (Fin.last (fragment).vertices) = block.lastParameter :=
  (block.verticalParameters trace row sourceFirst sourceLast).last_parameter

/-- Read the actual retained dyadic parameter step, with its orientation. -/
theorem verticalFragment_step (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    (fragment).parameters edge.succ - (fragment).parameters edge.castSucc =
      (1 / 2 : InverseRootPolynomial.Coordinate)^depth * (block.lastParameter - block.firstParameter) :=
  RectangularParentTraceSteps.dyadic_step (block.verticalParameters trace row sourceFirst sourceLast) (trace.segments_eq
    row) edge

/-- Every original vertical fragment step follows its retained source orientation. -/
theorem verticalFragment_ordered (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    if forward then (fragment).parameters edge.castSucc ≤ (fragment).parameters edge.succ
    else (fragment).parameters edge.succ ≤ (fragment).parameters edge.castSucc :=
  (fragment).ordered edge

/-- The physical dyadic depth pays the source mesh-width bound directly. -/
theorem verticalFragment_sourceWidth : (fragment).sourceWidth ≤ (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  apply SourceSampleResampling.meshWidth_le _ true (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)
  intro edge
  apply RectangularParentTraceSteps.dyadic_step_le (block.verticalParameters trace row sourceFirst sourceLast)
    (trace.segments_eq row)
  · cases forward with
    | true => exact block.parameters.within.1
    | false => exact block.parameters.within.1.trans block.parameters.range.ordered.le
  · cases forward with
    | true => exact block.parameters.within.2
    | false => exact block.parameters.range.ordered.le.trans block.parameters.within.2

end Vertical
end ParentBlock
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
