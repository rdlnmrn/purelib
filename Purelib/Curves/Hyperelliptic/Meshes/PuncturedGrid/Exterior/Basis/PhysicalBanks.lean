module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedSideFragments
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
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
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.SourceIntervals
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

public section

/-! Assemble side sample banks on the retained component numerical owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Data.Vector
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Rectangle
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Paths
open Purelib.Topology.Polygon

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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
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
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

/-- A physical sample retains the numerical original selected from the component's common bank at its exact geometric
parent index. -/
@[expose] def BlockSample (retained : Preparation.CommonBasisPreparation prepared) {index : Nat} (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length) {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock (ParentIndices.occurrenceAt prepared.occurrences outer) vertical forward physical)
    {faceIndex : Nat} (data : FragmentQueries.RowData (ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {vertices : Nat}
    (values : Fin (vertices + 1) → Stokes.PrimitivePoint) :=
  JoinedFragments.SampledFragment (originals := (BlockInputs.blockInput retained inputs outer
    block).numerical.originals)
    (coefficients := coefficients) (data := data) values

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

/-- Build all horizontal piece samples using the retained component inputs. -/
@[expose] def horizontalPieces {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
  (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest (ParentIndices.occurrenceAt prepared.occurrences outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    Data.Vector.DependentVector (fun column : Fin (left.boundaryColumns + 1) =>
      BlockSample retained inputs outer
        (blocks.get (Fin.cast left.boundaryColumns_eq column)) data coefficients
        (fun vertex => ((fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow =>
          coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ :
          Stokes.PrimitivePoint))) ((side.pieceVertices depth column).indexed vertex))) :=
  DependentVector.ofFn (fun column =>
    (blocks.get (Fin.cast left.boundaryColumns_eq column)).certifiedHorizontalPiece
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryColumns_eq
        column))).numerical.originals)
      (coefficients := coefficients) trace column sourceFirst sourceLast budget owners later original values readback)

/-- Build all horizontal junction samples using the retained component inputs. -/
@[expose] def horizontalJunctions {allowance : InverseRootPolynomial.Coordinate} (budget :
  NoisyPathArea.LengthErrorBudget (1) allowance)
    (owners : OwnerRequest (ParentIndices.occurrenceAt prepared.occurrences outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    Data.Vector.DependentVector (fun column : Fin left.boundaryColumns =>
      BlockSample retained inputs outer
        (blocks.get (Fin.cast left.boundaryColumns_eq column.castSucc)) data coefficients
        (JoinedSampleBlocks.JunctionValues (fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun
          basisRow => coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
      (side.pieceVertices depth column.castSucc) (side.pieceVertices depth column.succ))) :=
  DependentVector.ofFn (fun column =>
    (blocks.get (Fin.cast left.boundaryColumns_eq column.castSucc)).certifiedHorizontalJunction
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryColumns_eq
        column.castSucc))).numerical.originals)
      (coefficients := coefficients) trace column sourceFirst sourceLast budget owners later original values readback)

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

/-- Build all vertical piece samples using the retained component inputs. -/
@[expose] def verticalPieces {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
  (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest (ParentIndices.occurrenceAt prepared.occurrences outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    Data.Vector.DependentVector (fun row : Fin (left.boundaryRows + 1) =>
      BlockSample retained inputs outer
        (blocks.get (Fin.cast left.boundaryRows_eq row)) data coefficients
        (fun vertex => ((fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow =>
          coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ :
          Stokes.PrimitivePoint))) ((side.pieceVertices depth row).indexed vertex))) :=
  DependentVector.ofFn (fun row =>
    (blocks.get (Fin.cast left.boundaryRows_eq row)).certifiedVerticalPiece
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryRows_eq
        row))).numerical.originals)
      (coefficients := coefficients) trace row sourceFirst sourceLast budget owners later original values readback)

/-- Build all vertical junction samples using the retained component inputs. -/
@[expose] def verticalJunctions {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
  (1) allowance)
    (owners : OwnerRequest (ParentIndices.occurrenceAt prepared.occurrences outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    Data.Vector.DependentVector (fun row : Fin left.boundaryRows =>
      BlockSample retained inputs outer
        (blocks.get (Fin.cast left.boundaryRows_eq row.castSucc)) data coefficients
        (JoinedSampleBlocks.JunctionValues (fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun
          basisRow => coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
      (side.pieceVertices depth row.castSucc) (side.pieceVertices depth row.succ))) :=
  DependentVector.ofFn (fun row =>
    (blocks.get (Fin.cast left.boundaryRows_eq row.castSucc)).certifiedVerticalJunction
      (originals := (BlockInputs.blockInput retained inputs outer (blocks.get (Fin.cast left.boundaryRows_eq
        row.castSucc))).numerical.originals)
      (coefficients := coefficients) trace row sourceFirst sourceLast budget owners later original values readback)

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
