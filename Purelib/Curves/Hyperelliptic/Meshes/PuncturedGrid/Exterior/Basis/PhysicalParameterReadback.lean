module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MatchedParameterReadback
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Read endpoint and mesh certificates from the retained physical side banks. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (blockIndex blockIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs (blockInput)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank (ParentBlockBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis (OwnerRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (horizontalPieces verticalPieces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

variable (retained : CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : Geometry lc lr} {rg :
    Geometry rc rr}
  {leftCuts : GridCuts lg} {rightCuts :
    GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : ObservationMesh leftCuts leftBox} {right :
    ObservationMesh rightCuts rightBox}
  {data : RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Coordinate}
  {side : MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth) {forward : Bool}
  (blocks : ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left false forward)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : Coordinate} (budget :
  LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (column : Fin (left.boundaryColumns + 1))

local notation "fragment" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment.fragment
  (Purelib.Data.Vector.DependentVector.get
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) column)

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
open Purelib.Data.Vector
open Purelib.Riemann.Paths
/-- The retained horizontal physical fragment begins at its original source block's first parameter. -/
theorem horizontalPieces_first : (fragment).parameters 0 =
    (blocks.get (Fin.cast left.boundaryColumns_eq column)).firstParameter := by
  have equal := DependentVector.ofFn_get (fun position : Fin (left.boundaryColumns + 1) =>
    (blocks.get (Fin.cast left.boundaryColumns_eq position)).certifiedHorizontalPiece
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryColumns_eq
        position))).numerical.originals)
      (coefficients := coefficients) trace position sourceFirst sourceLast budget owners later original values readback)
        column
  have firstEq := congrArg (fun sample => (SampledFragment.fragment sample).parameters 0) equal
  exact firstEq.trans (ParentBlock.horizontalFragment_first _ _ _ _ _ _ _ _ _)

/-- The retained horizontal physical fragment ends at its original source block's last parameter. -/
theorem horizontalPieces_last : (fragment).parameters (Fin.last (fragment).vertices) =
    (blocks.get (Fin.cast left.boundaryColumns_eq column)).lastParameter := by
  dsimp only [PhysicalBanks.horizontalPieces]
  rw [DependentVector.ofFn_get]
  exact ParentBlock.horizontalFragment_last _ _ _ _ _ _ _ _ _

/-- The retained horizontal physical fragment retains the original source block's traversal orientation. -/
theorem horizontalPieces_forward : (fragment).forward = forward := by
  dsimp only [PhysicalBanks.horizontalPieces]
  rw [DependentVector.ofFn_get]
  rfl

/-- The retained horizontal physical fragment contains the original physical trace's dyadic number of steps. -/
theorem horizontalPieces_vertices : (fragment).vertices = RectangularDyadicPairedTrace.dyadicCount depth := by
  dsimp only [PhysicalBanks.horizontalPieces]
  rw [DependentVector.ofFn_get]
  rfl

/-- The retained horizontal physical fragment has source mesh width bounded by its actual physical dyadic depth. -/
theorem horizontalPieces_sourceWidth : (fragment).sourceWidth ≤ (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  dsimp only [PhysicalBanks.horizontalPieces]
  rw [DependentVector.ofFn_get]
  exact ParentBlock.horizontalFragment_sourceWidth _ _ _ _ _ _ _ _ _

end

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Coordinate}
  {side : MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth) {forward : Bool}
  (blocks : ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left true forward)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

variable {allowance : Coordinate} (budget :
  LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (row : Fin (left.boundaryRows + 1))

local notation "fragment" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments.SampledFragment.fragment
  (Purelib.Data.Vector.DependentVector.get
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained (coefficients
    := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) row)

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
open Purelib.Data.Vector
open Purelib.Riemann.Paths
/-- The retained vertical physical fragment begins at its original source block's first parameter. -/
theorem verticalPieces_first : (fragment).parameters 0 =
    (blocks.get (Fin.cast left.boundaryRows_eq row)).firstParameter := by
  have equal := DependentVector.ofFn_get (fun position : Fin (left.boundaryRows + 1) =>
    (blocks.get (Fin.cast left.boundaryRows_eq position)).certifiedVerticalPiece
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryRows_eq
        position))).numerical.originals)
      (coefficients := coefficients) trace position sourceFirst sourceLast budget owners later original values readback)
        row
  have firstEq := congrArg (fun sample => (SampledFragment.fragment sample).parameters 0) equal
  exact firstEq.trans (ParentBlock.verticalFragment_first _ _ _ _ _ _ _ _ _)

/-- The retained vertical physical fragment ends at its original source block's last parameter. -/
theorem verticalPieces_last : (fragment).parameters (Fin.last (fragment).vertices) =
    (blocks.get (Fin.cast left.boundaryRows_eq row)).lastParameter := by
  dsimp only [PhysicalBanks.verticalPieces]
  rw [DependentVector.ofFn_get]
  exact ParentBlock.verticalFragment_last _ _ _ _ _ _ _ _ _

/-- The retained vertical physical fragment retains the original source block's traversal orientation. -/
theorem verticalPieces_forward : (fragment).forward = forward := by
  dsimp only [PhysicalBanks.verticalPieces]
  rw [DependentVector.ofFn_get]
  rfl

/-- The retained vertical physical fragment contains the original physical trace's dyadic number of steps. -/
theorem verticalPieces_vertices : (fragment).vertices = RectangularDyadicPairedTrace.dyadicCount depth := by
  dsimp only [PhysicalBanks.verticalPieces]
  rw [DependentVector.ofFn_get]
  rfl

/-- The retained vertical physical fragment has source mesh width bounded by its actual physical dyadic depth. -/
theorem verticalPieces_sourceWidth : (fragment).sourceWidth ≤ (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  dsimp only [PhysicalBanks.verticalPieces]
  rw [DependentVector.ofFn_get]
  exact ParentBlock.verticalFragment_sourceWidth _ _ _ _ _ _ _ _ _

end

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback
