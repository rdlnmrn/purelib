module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularParentTraceSteps
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceParameters
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
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Tactic.Ring

public section

/-! Dyadic width bounds for cached source parameters on reversed physical sides. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.ParentParameters

open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Data.Rat.Fraction.Compatibility
variable {lc lr rc rr genus depth : Nat} {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Normalization.RectangularInverseModels.Geometry rc rr}
  {piece : Paths.RectangularPairedSegments.PairedSegmentPiece lg rg} {curve : Hyperelliptic.Basic.HyperellipticCurve
    genus} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {first last :
    Normalization.InverseRootPolynomial.Coordinate}

/-- The original reversed dyadic parameter step is bounded by the retained dyadic mesh width.

The supplied endpoint bounds constrain the original parent span to at most one. -/
theorem dyadic_reverse_step_le {trace : Integration.RectangularPairedPointBanks.Trace piece
  (Paths.RectangularDyadicPairedTrace.dyadicCount depth)}
    (transport : Paths.RectangularTraceParameterReadings.ParentParameters trace parent first last) (retained : trace =
      Paths.RectangularDyadicPairedTrace.dyadic piece depth)
    (lastNonnegative : 0 ≤ last) (firstLe : first ≤ 1) (edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount
      depth)) :
    transport.parameters edge.castSucc - transport.parameters edge.succ ≤ (1 / 2 :
      Normalization.InverseRootPolynomial.Coordinate)^depth := open Purelib.Data.Rat in by
  have step := Paths.RectangularParentTraceSteps.dyadic_step transport retained edge
  have reversed : transport.parameters edge.castSucc - transport.parameters edge.succ =
      (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth * (first - last) := by
    calc
      _ = -(transport.parameters edge.succ - transport.parameters edge.castSucc) := by ring1
      _ = _ := by rw [step]; ring1
  rw [reversed]
  have span : first - last ≤ 1 := (Fraction.Order.Arithmetic.sub_le_sub_direct firstLe lastNonnegative).trans_eq (by
    ring1)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct span (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) depth)).trans_eq (mul_one _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.ParentParameters
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.PairedSourcePlan
namespace SourceBlockParameters

open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

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
  {depth : Nat}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
    height}
/-- A reversed horizontal matched trace retains its original source endpoints and dyadic reverse-step bounds. -/
theorem horizontalParameters_reverse_bounds (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters evaluated false
      false (left.partition.x.intervals[column.val]'column.isLt))
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height) :
    let transport :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalParameters
      trace column block sourceFirst sourceLast
    transport.parameters 0 =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.firstParameter block) ∧
      transport.parameters (Fin.last (Paths.RectangularDyadicPairedTrace.dyadicCount depth)) =
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.lastParameter block) ∧
      ∀ edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth),
        transport.parameters edge.castSucc - transport.parameters edge.succ ≤ (1 / 2 :
          Normalization.InverseRootPolynomial.Coordinate)^depth := by
  intro transport
  refine ⟨(Paths.RectangularParentTraceSteps.first_parameter transport), transport.last_parameter, ?_⟩
  intro edge
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.ParentParameters.dyadic_reverse_step_le
    transport (trace.segments_eq column) block.parameters.within.1 block.parameters.within.2 edge
end Horizontal

section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
    horizontal}
/-- A reversed vertical matched trace retains its original source endpoints and dyadic reverse-step bounds. -/
theorem verticalParameters_reverse_bounds (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length)
    (block : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters evaluated true
      false (left.partition.y.intervals[row.val]'row.isLt))
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal) :
    let transport :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalParameters trace
      row block sourceFirst sourceLast
    transport.parameters 0 =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.firstParameter block) ∧
      transport.parameters (Fin.last (Paths.RectangularDyadicPairedTrace.dyadicCount depth)) =
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.lastParameter block) ∧
      ∀ edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth),
        transport.parameters edge.castSucc - transport.parameters edge.succ ≤ (1 / 2 :
          Normalization.InverseRootPolynomial.Coordinate)^depth := by
  intro transport
  refine ⟨(Paths.RectangularParentTraceSteps.first_parameter transport), transport.last_parameter, ?_⟩
  intro edge
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.ParentParameters.dyadic_reverse_step_le
    transport (trace.segments_eq row) block.parameters.within.1 block.parameters.within.2 edge
end Vertical

end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.PairedSourcePlan

end
