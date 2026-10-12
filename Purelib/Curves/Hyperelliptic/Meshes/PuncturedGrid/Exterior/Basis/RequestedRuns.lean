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
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Budget.Path.Capacity
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOwners
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunBudget
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalWidths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotalBudget
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBudget

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalWidths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Budget.Path

open Purelib.Integration.Path

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

public section

/-! Prepare and certify complete requested common-source runs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns

open Purelib.Data
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

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data :
  RowData occurrence faceIndex}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep_nonnegative
  parameterSteps_total)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (fragmentLocalTolerance
  fragmentLocalTolerance_positive)

set_option genInjectivity false in
/-- Choose block and reference-mesh requirements before acquiring either primitive bank. Fragment counts come from the
retained geometric partition. -/
structure RunRequest (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (covers : SourceLocations.BasisSourceCovers parent) (fragmentCount : Nat)
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained fragment-block request paid from one quarter of the target. -/ blocks : RequestedBlocks.BlockRequest
    occurrence covers fragmentCount (target / 4)
  /-- The source resampling request at the original primitive slope, quarter target and minimum stage. -/ refinement :
    SourceRunRefinement 1 (BasisSourceCovers.primitiveSlope covers) (target / 4) minimum

constructive_injectivity RunRequest

/-- Prepare the original fragment-block and source-refinement requirements before either sample bank is acquired. -/
@[expose] def RunRequest.build (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (covers : SourceLocations.BasisSourceCovers parent) (fragmentCount : Nat)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
    RunRequest occurrence covers fragmentCount
      target minimum :=
  ⟨BlockRequest.build occurrence covers fragmentCount (target / 4) (Fraction.Order.Field.div_pos_direct positive (by
    decide)),
    SourceRuns.sourceRunRefinement covers target positive minimum⟩

set_option genInjectivity false in
/-- Keep the computed run error alongside the samples and its specification. Subsequent comparisons consume this cached
value and its paid certificate. -/
structure CertifiedRun (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells
  coefficients depth)
    {faceIndex : Nat} (data : FragmentQueries.RowData occurrence faceIndex) (target : InverseRootPolynomial.Coordinate)
      where
  /-- The actual retained source run built from the acquired fragments. -/ run : SourceRuns.SourceRun acquired data
  /-- The cached coefficient-independent area error of this exact run. -/ error : InverseRootPolynomial.Coordinate
  /-- The area-error cache equals the retained run's original error. -/ error_eq : error = run.error
  /-- The retained area error is strictly below the requested target. -/ paid : error < target
  /-- The cached displacement error of the same retained run. -/ totalError : InverseRootPolynomial.Coordinate
  /-- The displacement-error cache equals the original run's total error. -/ totalError_eq : totalError = run.totalError
  /-- The retained displacement error is strictly below one quarter of the requested target. -/ totalPaid : totalError <
    target / 4

constructive_injectivity CertifiedRun

namespace RunRequest
variable {fragmentCount runMinimum : Nat} {target : Coordinate}
  (selected : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest occurrence
    covers fragmentCount target runMinimum)

/-- Assemble and certify the original source run from paid retained fragment owners and a complete adjacent source
chain.

The supplied count, source and face stages, parameter widths and refinement depth certify both cached area and
displacement errors. -/
@[expose] def acquire {vertices : Fin fragmentCount → Nat}
    (owners : selected.blocks.OwnerPreparation vertices)
    (fragments : List (BlockRequest.BudgetedFragment (originals := originals) (coefficients := coefficients)
      selected.blocks data))
    (countLe : fragments.length ≤ fragmentCount)
    (chain : SourceChains.SourceChain (fragments.map BudgetedFragment.fragment) 0 1)
    (sourcePaid : selected.blocks.queries.sourceMinimum ≤ index) (facePaid : owners.faceIndex ≤ faceIndex)
    (widths : ∀ fragment ∈ fragments, fragment.fragment.sourceWidth ≤ selected.refinement.width)
    (depthPaid : selected.refinement.depth ≤ common.depth + acquired.extraDepth) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedRun acquired data target := by
  let retained := fragments.map BudgetedFragment.fragment
  let run := SourceRun.ofChain (acquired := acquired) retained chain
  have blocks := owners.block_error (acquired := acquired) fragments countLe sourcePaid facePaid
  have widthLe : run.width ≤ selected.refinement.width := by
    apply SourceRun.ofChain_width_le retained chain selected.refinement.width_positive.le
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
    have countRead : run.fragments.length ≤ fragmentCount := (List.Map.length_map ..).trans_le countLe
    have toleranceLe := Capacity.fragmentLocalTolerance_count_antitone countRead
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
          (BasisSourceCovers.primitiveSlope_nonnegative covers))) selected.blocks.positive.le
    exact localBound.trans ((Fraction.Order.Basic.min_le_right ..).trans toleranceLe)
  exact ⟨run, run.error, rfl, run.error_lt selected.refinement blocks.le widthLe depthPaid,
    run.totalError, rfl, totalPaid⟩

end RunRequest
namespace CertifiedRun
variable {target : Coordinate}

/-- The retained physical area differs from the exact cached source area by at most its certified error times squared
coefficient mass. -/
theorem area_bound (certified : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedRun
  acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((certified.run.fragments.map
      OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area) ≤ certified.error * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw [certified.error_eq]
  exact certified.run.cached_source_area_bound weighted

/-- The retained physical area satisfies the requested homogeneous bound against its exact cached source area. -/
theorem area_requested (certified : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedRun
  acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((certified.run.fragments.map
      OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area) ≤ target * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (certified.area_bound weighted).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct certified.paid.le
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The cached endpoint error is paid by the same request as the area error. -/
theorem total_requested (certified : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.CertifiedRun
  acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total
      ((certified.run.fragments.map OwnedFragment.pair).map Prod.fst).flatten).sub
        (ConjugatePathReadback.conjugateDiagonal weighted.source.total))
          ((target / 4) * PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have bounded := certified.run.cached_source_total_bound weighted
  rw [← certified.totalError_eq] at bounded
  have massNN : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct certified.totalPaid.le massNN
  exact ⟨bounded.1.trans upper, bounded.2.trans upper⟩

end CertifiedRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
