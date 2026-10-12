module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedSourceRun
import Purelib.Riemann.Paths.RectangularParentTraceSteps
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

public section

/-! Carry physical dyadic mesh widths through retained common-source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalWidths
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError
  owned_fragments_area_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (interleaveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : PreparedPatch parent}
  {sourceData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover sourceData}
  {covers : BasisSourceCovers parent} {minimum
    floor index depth : Nat}
  {common : BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {box : Purelib.Geometry.Rational.Box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {originals :
    PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {acquired :
  BasisPreparedCommonRequest.Acquisition
  request polynomials originals cells coefficients depth}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data :
  RowData occurrence faceIndex}

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
namespace OwnedFragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
/-- A retained forward physical dyadic trace has source-parameter width at most its original dyadic width. -/
theorem ofTrace_sourceWidth (member : parent ∈ occurrence.compared.entered.cache.parents)
    {cuts : RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    {split : RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    {interval : PreparedAxisPartitions.Interval} (located : RectangularSegmentRefinement.Subinterval split interval)
    {leftColumns leftRows rightColumns rightRows fineDepth : Nat}
    {leftGeometry : RectangularInverseModels.Geometry leftColumns leftRows}
    {rightGeometry : RectangularInverseModels.Geometry rightColumns rightRows}
    {physical : RectangularPairedSegments.PairedSegmentPiece leftGeometry rightGeometry}
    {trace : RectangularPairedPointBanks.Trace physical (RectangularDyadicPairedTrace.dyadicCount fineDepth)}
    (transport : RectangularTraceParameterReadings.ParentParameters trace parent
      interval.lower interval.upper)
    (increasing : ∀ edge : Fin (RectangularDyadicPairedTrace.dyadicCount fineDepth), trace.parameters edge.castSucc ≤
      trace.parameters edge.succ)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
      (RectangularDyadicPairedTrace.dyadicCount fineDepth) allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (readings : OwnerRequest.OwnedReadings data (fun vertex => trace.points vertex))
    (owned : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        PrimitivePoint)))
    (source : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      (⟨PrimitiveBank.value originals coefficients (transport.parameters vertex), PrimitiveBank.value originals
        coefficients (transport.parameters vertex)⟩ : PrimitivePoint)))
    (retained : trace = RectangularDyadicPairedTrace.dyadic physical fineDepth) :
    (OwnedFragment.ofTrace member located true transport increasing budget owners later readings owned
      source).sourceWidth ≤
      (1 / 2 : InverseRootPolynomial.Coordinate)^fineDepth := by
  apply SourceSampleResampling.meshWidth_le _ true (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) fineDepth)
  intro edge
  exact RectangularParentTraceSteps.dyadic_step_le transport retained (located.piece.within.1.trans located.lower)
    (located.upper.trans located.piece.within.2) edge

/-- The original constant-parameter owner junction has zero source width. -/
theorem atJunction_sourceWidth (member : parent ∈ occurrence.compared.entered.cache.parents)
    {cuts : RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    (split : RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1))
    (parameter : InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget 1 allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (readings : OwnerRequest.OwnedReadings data (fun _ : Fin 2 => parent.edge.point parameter))
    (owned : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        PrimitivePoint)))
    (source : CenteredBilinearPath.Sample (fun _ : Fin 2 => ConjugateIncrementComparison.conjugateFirst
      (⟨PrimitiveBank.value originals coefficients parameter, PrimitiveBank.value originals coefficients parameter⟩ :
        PrimitivePoint))) :
    (OwnedFragment.atJunction member split parameter inside budget owners later readings owned source).sourceWidth ≤ 0
      := by
  apply SourceSampleResampling.meshWidth_le _ true le_rfl
  intro edge
  exact (sub_self parameter).le

end OwnedFragment

/-- Piece and owner-junction bounds propagate in the actual interleaving order used by the whole physical trace. -/
theorem interleave_sourceWidth_le {count : Nat}
    (pieces : Fin (count + 1) → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients)
      data)
    (junctions : Fin count → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data)
    {width : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ width)
    (pieceWidths : ∀ position, (pieces position).sourceWidth ≤ width)
    (junctionWidths : ∀ position, (junctions position).sourceWidth ≤ width) :
    PairedFragmentBlocks.maximum OwnedFragment.sourceWidth (JoinedFragments.interleaveFragments pieces junctions) ≤
      width := by
  induction count with
  | zero => exact Fraction.Order.Basic.max_le (pieceWidths 0) nonnegative
  | succ count ih =>
      exact Fraction.Order.Basic.max_le (pieceWidths 0) (Fraction.Order.Basic.max_le (junctionWidths 0)
        (ih (fun position => pieces position.succ) (fun position => junctions position.succ)
          (fun position => pieceWidths position.succ) (fun position => junctionWidths position.succ)))

/-- The run's cached maximum inherits the physical width cap, including zero-width owner junctions. No source samples
are recomputed. -/
theorem SourceRun.ofChain_width_le
    (fragments : List (OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data))
    (chain : SourceChains.SourceChain fragments 0 1) {width : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤
      width)
    (bounded : ∀ fragment ∈ fragments, fragment.sourceWidth ≤ width) :
    (SourceRun.ofChain (acquired := acquired) fragments chain).width ≤ width := by
  change PairedFragmentBlocks.maximum OwnedFragment.sourceWidth fragments ≤ width
  clear chain
  induction fragments with
  | nil => exact nonnegative
  | cons first rest ih =>
      exact Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
        (ih (fun fragment member => bounded fragment (List.mem_cons_of_mem _ member)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalWidths
