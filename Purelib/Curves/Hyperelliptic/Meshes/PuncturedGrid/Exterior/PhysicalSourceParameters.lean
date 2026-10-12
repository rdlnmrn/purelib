module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
import Purelib.Riemann.Paths.RectangularParentTraceSteps
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularTraceParameterReadings

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! The actual matched-side traces retain their source endpoints and the
mesh-width cap required by complete source-run resampling. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}
  {evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
    sample otherSample fine}
  {lc lr rc rr : Nat} {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts : Paths.RectangularSegmentSplitting.GridCuts rg}
    {leftBox rightBox : Rational.Box}
  {left : Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {depth : Nat} {forward : Bool}

namespace SourceBlockParameters

/-- The selected original block endpoints satisfy the unit parameter bounds in either source orientation. -/
private theorem endpoint_unit {vertical : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated vertical
      forward physical) :
    0 ≤ (SourceBlockParameters.firstParameter block) ∧
      (SourceBlockParameters.lastParameter block) ≤ 1
      := by
  cases forward with
  | true => exact block.parameters.within
  | false => exact ⟨block.parameters.within.1.trans block.parameters.range.ordered.le,
      block.parameters.range.ordered.le.trans block.parameters.within.2⟩

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
    height}
/-- The actual horizontal matched trace retains both source endpoints and the dyadic upper bound on each parameter step.
-/
theorem horizontalParameters_bounds (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (block : SourceBlockParameters evaluated false
      forward (left.partition.x.intervals[column.val]'column.isLt))
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height) :
    let transport :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalParameters
      trace column block sourceFirst sourceLast
    transport.parameters 0 =
      (SourceBlockParameters.firstParameter block) ∧
      transport.parameters (Fin.last (Paths.RectangularDyadicPairedTrace.dyadicCount depth)) =
        (SourceBlockParameters.lastParameter block) ∧
      ∀ edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth),
        transport.parameters edge.succ - transport.parameters edge.castSucc ≤ (1 / 2 :
          Normalization.InverseRootPolynomial.Coordinate)^depth := by
  intro transport
  refine ⟨(Paths.RectangularParentTraceSteps.first_parameter transport), transport.last_parameter, ?_⟩
  intro edge
  exact Paths.RectangularParentTraceSteps.dyadic_step_le transport (trace.segments_eq column)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters.SourceBlockParameters.endpoint_unit block).1
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters.SourceBlockParameters.endpoint_unit block).2
    edge
end Horizontal

section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
    horizontal}
/-- The actual vertical matched trace retains both source endpoints and the dyadic upper bound on each parameter step.
-/
theorem verticalParameters_bounds (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length)
    (block : SourceBlockParameters evaluated true
      forward (left.partition.y.intervals[row.val]'row.isLt))
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal) :
    let transport :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalParameters trace
      row block sourceFirst sourceLast
    transport.parameters 0 =
      (SourceBlockParameters.firstParameter block) ∧
      transport.parameters (Fin.last (Paths.RectangularDyadicPairedTrace.dyadicCount depth)) =
        (SourceBlockParameters.lastParameter block) ∧
      ∀ edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth),
        transport.parameters edge.succ - transport.parameters edge.castSucc ≤ (1 / 2 :
          Normalization.InverseRootPolynomial.Coordinate)^depth := by
  intro transport
  refine ⟨(Paths.RectangularParentTraceSteps.first_parameter transport), transport.last_parameter, ?_⟩
  intro edge
  exact Paths.RectangularParentTraceSteps.dyadic_step_le transport (trace.segments_eq row)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters.SourceBlockParameters.endpoint_unit block).1
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters.SourceBlockParameters.endpoint_unit block).2
    edge
end Vertical

end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters
