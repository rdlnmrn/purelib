module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedReverseRuns
import Purelib.Integration.Path.PairedReverseBlocks
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunTotals
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
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

@[expose] public section
/-! Normalize descending parent paths and their area, endpoint and magnitude bounds to source orientation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks (BlockRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun sourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns (ReverseSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns (ReverseSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns (CertifiedReverseRun)
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

namespace ReverseSourceRuns.ReverseSourceRun

/-- The same cached physical increments, now traversed in source orientation. -/
def orientedPhysical (run : ReverseSourceRuns.ReverseSourceRun acquired data) : List PrimitivePoint :=
  PairedAreaReversal.reverseIncrements ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten

/-- The original reversed physical increments satisfy the retained homogeneous error bound against the positive source
area. -/
theorem oriented_area (run : ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area run.orientedPhysical - weighted.source.area) ≤
      run.error * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  unfold ReverseSourceRuns.ReverseSourceRun.orientedPhysical
  rw [PairedAreaReversal.area_reverseIncrements]
  rw [show -PairedIncrementArea.area ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area = -(PairedIncrementArea.area
        ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten + weighted.source.area) by ring1,
    Data.Gaussian.Norm.Basic.normSq_neg]
  exact run.cached_source_area_bound weighted

/-- The original reversed physical displacement satisfies the retained error bound against the conjugate source
displacement. -/
theorem oriented_total (run : ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total run.orientedPhysical).sub
      (ConjugatePathReadback.conjugateDiagonal weighted.source.total))
        (run.totalError * PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  PairedReverseBlocks.reversed_total_error _ _ (run.cached_source_total_bound weighted)

/-- The original reversed physical displacement retains its coefficient-scaled magnitude bound. -/
theorem oriented_bounded (run : ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total run.orientedPhysical)
      (2 * (run.totalError + (BasisSourceCovers.primitiveSlope covers)) *
        PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  PairedReverseBlocks.reversed_total_bounded _ (run.owned_total_bounded weighted)

end ReverseSourceRuns.ReverseSourceRun
variable {target : Coordinate}

/-- The original source-oriented physical area satisfies the certified reverse run's requested homogeneous error bound.
-/
theorem
  RequestedRuns.CertifiedReverseRun.oriented_area_requested
  (certified : RequestedRuns.CertifiedReverseRun acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area certified.run.orientedPhysical -
      weighted.source.area) ≤
      target * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bound := certified.run.oriented_area weighted
  rw [← certified.error_eq] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct certified.paid.le
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The original source-oriented physical displacement satisfies the certified reverse run's requested quarter-target
bound. -/
theorem
  RequestedRuns.CertifiedReverseRun.oriented_total_requested
  (certified : RequestedRuns.CertifiedReverseRun acquired data target)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total certified.run.orientedPhysical).sub
      (ConjugatePathReadback.conjugateDiagonal weighted.source.total))
        ((target / 4) * PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  PairedReverseBlocks.reversed_total_error _ _ (certified.total_requested weighted)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
