module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOwners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Path.Capacity
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunBudget
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunWidths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunTotalBudget
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Budget.Path

open Purelib.Integration.Path

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon.Stokes

public section

/-! Prepare and certify complete requested common-source runs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea (traceDensity queryScale
  queryScale_nonnegative)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget maximum
  maximum_nonnegative le_maximum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea (traceDensity queryScale)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun sourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns (ReverseSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor
    index depth : Nat}
  {common : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular
    common areaAllowance sourceTarget coefficientTarget floor}
  {box : Geometry.Rational.Box}
  {polynomials : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
    box}
  {originals :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers
    index}
  {cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
  occurrence faceIndex}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep_nonnegative
  parameterSteps_total)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (fragmentLocalTolerance
  fragmentLocalTolerance_positive)

set_option genInjectivity false in
/-- Keep the computed run error alongside the samples and its specification. Subsequent comparisons consume this cached
value and its paid certificate. -/
structure CertifiedReverseRun (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells
  coefficients depth)
    {faceIndex : Nat} (data : FragmentQueries.RowData occurrence faceIndex) (target : InverseRootPolynomial.Coordinate)
      where
  /-- The actual descending physical source run retained by this acquisition. -/ run :
    ReverseSourceRuns.ReverseSourceRun acquired data
  /-- The cached coefficient-independent area error of this reverse run. -/ error : InverseRootPolynomial.Coordinate
  /-- The area-error cache equals the retained reverse run's original error. -/ error_eq : error = run.error
  /-- The retained reverse-run area error is strictly below the requested target. -/ paid : error < target
  /-- The cached displacement error of the same reverse run. -/ totalError : InverseRootPolynomial.Coordinate
  /-- The displacement-error cache equals the original reverse run's total error. -/ totalError_eq : totalError =
    run.totalError
  /-- The retained displacement error is strictly below one quarter of the requested target. -/ totalPaid : totalError <
    target / 4

constructive_injectivity CertifiedReverseRun

namespace RunRequest
variable {fragmentCount runMinimum : Nat} {target : Riemann.Normalization.InverseRootPolynomial.Coordinate}
  (selected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest occurrence covers
    fragmentCount target runMinimum)

/-- Assemble and certify the original reverse source run from paid fragments and a complete descending source chain.

The original count, source and face stages, reversed parameter widths and refinement depth pay both cached area and
displacement errors. -/
@[expose] def acquireReverse {vertices : Fin fragmentCount → Nat}
    (owners : selected.blocks.OwnerPreparation vertices)
    (fragments : List (BlockRequest.BudgetedFragment (originals := originals) (coefficients := coefficients)
      selected.blocks data))
    (countLe : fragments.length ≤ fragmentCount)
    (chain : ReverseSourceChains.ReverseSourceChain (fragments.map BudgetedFragment.fragment) 1 0)
    (sourcePaid : selected.blocks.queries.sourceMinimum ≤ index) (facePaid : owners.faceIndex ≤ faceIndex)
    (widths : ∀ fragment ∈ fragments, fragment.fragment.reverseSourceWidth ≤ selected.refinement.width)
    (depthPaid : selected.refinement.depth ≤ common.depth + acquired.extraDepth) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedReverseRun acquired data target :=
      by
  let retained := fragments.map BudgetedFragment.fragment
  let run := ReverseSourceRun.ofChain (acquired := acquired) retained chain
  have blocks := owners.block_error (acquired := acquired) fragments countLe sourcePaid facePaid
  have widthLe : run.width ≤ selected.refinement.width := by
    apply ReverseSourceRun.ofChain_width_le retained chain selected.refinement.width_positive.le
    intro fragment member
    obtain ⟨certified, present, rfl⟩ := Map.mem_map.mp member
    exact widths certified present
  have totalPaid : run.totalError < target / 4 := by
    apply run.totalError_lt
      (bound := 2 * (1 + (BasisSourceCovers.primitiveSlope covers)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide)
        (BasisSourceCovers.primitiveSlope_nonnegative covers)))
      selected.blocks.positive
    intro fragment member
    obtain ⟨certified, present, rfl⟩ := Map.mem_map.mp member
    have localBound := certified.fragment.totalError_paid (acquired := acquired) selected.blocks.budget
      certified.tolerance_le
      (selected.blocks.fragment_bounds (acquired := acquired) certified.fragment sourcePaid (owners.query_le.trans
        facePaid)).2
    have countRead : run.fragments.length ≤ fragmentCount := (Data.List.Map.length_map ..).trans_le countLe
    have toleranceLe := Capacity.fragmentLocalTolerance_count_antitone countRead
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
          (BasisSourceCovers.primitiveSlope_nonnegative covers))) selected.blocks.positive.le
    exact localBound.trans ((Fraction.Order.Basic.min_le_right ..).trans toleranceLe)
  exact ⟨run, run.error, rfl, run.error_lt selected.refinement blocks.le widthLe depthPaid,
    run.totalError, rfl, totalPaid⟩

end RunRequest
namespace CertifiedReverseRun
variable {target : Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- The descending physical area plus its exact original source area satisfies the certified homogeneous error bound. -/
theorem area_bound (certified :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedReverseRun acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((certified.run.fragments.map
      OwnedFragment.pair).map Prod.fst).flatten +
      weighted.source.area) ≤ certified.error * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw [certified.error_eq]
  exact certified.run.cached_source_area_bound weighted

/-- The descending physical area satisfies the requested homogeneous bound against the negative original source area. -/
theorem area_requested (certified :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedReverseRun acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((certified.run.fragments.map
      OwnedFragment.pair).map Prod.fst).flatten +
      weighted.source.area) ≤ target * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (certified.area_bound weighted).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct certified.paid.le
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The cached endpoint error is paid by the same request as the area error. -/
theorem total_requested (certified :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedReverseRun acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total
      ((certified.run.fragments.map OwnedFragment.pair).map Prod.fst).flatten).sub
        (PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal weighted.source.total)))
          ((target / 4) * PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have bounded := certified.run.cached_source_total_bound weighted
  rw [← certified.totalError_eq] at bounded
  have massNN : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct certified.totalPaid.le massNN
  exact ⟨bounded.1.trans upper, bounded.2.trans upper⟩

end CertifiedReverseRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
