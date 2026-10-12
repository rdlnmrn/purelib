module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedReverseRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OrientedReverseRuns
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

@[expose] public section

/-! Unit-capped run requests give coefficient-homogeneous magnitudes independent of accuracy. -/
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns (CertifiedRun CertifiedReverseRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns (ReverseSourceRun)
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

/-- An error paid below one quarter of a unit-capped target is at most one. -/
private theorem CertifiedRunMagnitudes.capped_error {error target : InverseRootPolynomial.Coordinate} (paid : error <
  target / 4) (capped :
  target ≤ 1) :
    error ≤ 1 := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct capped (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4⁻¹)
  rw [Fraction.Field.one_mul] at scaled
  rw [Fraction.Field.div_eq_mul_inv_direct] at paid
  exact paid.le.trans (scaled.trans (by decide : (4 : InverseRootPolynomial.Coordinate)⁻¹ ≤ 1))

/-- A paid unit-capped error gives a coefficient-scaled magnitude bound independent of the requested accuracy. -/
private theorem CertifiedRunMagnitudes.capped_magnitude {error target slope mass : InverseRootPolynomial.Coordinate}
    (paid : error < target / 4) (capped : target ≤ 1) (massNN : 0 ≤ mass) :
    2 * (error + slope) * mass ≤ 2 * (1 + slope) * mass :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes.capped_error paid capped) le_rfl)
      (by decide)) massNN

/-- The retained Gaussian coefficient mass is nonnegative. -/
private theorem CertifiedRunMagnitudes.mass_nonnegative (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus) :
    0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
        (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

namespace RequestedRuns.CertifiedRun
variable {target : Coordinate}

/-- This magnitude can be fixed before choosing the requested accuracy. -/
theorem
  total_bounded_requested
  (certified : RequestedRuns.CertifiedRun acquired data target) (capped : target ≤ 1)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total
      ((certified.run.fragments.map OwnedFragment.pair).map Prod.fst).flatten)
        (2 * (1 + (BasisSourceCovers.primitiveSlope covers)) * PreparedObservationCoercivity.coefficientNormSq
          coefficients) := by
  have bounded := certified.run.owned_total_bounded weighted
  rw [← certified.totalError_eq] at bounded
  have paid := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes.capped_magnitude (slope
    := (BasisSourceCovers.primitiveSlope covers)) certified.totalPaid capped
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes.mass_nonnegative coefficients)
  exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩

end RequestedRuns.CertifiedRun
namespace RequestedRuns.CertifiedReverseRun
variable {target : Coordinate}

/-- The certified reverse run's source-oriented displacement has a uniform homogeneous magnitude bound for every
unit-capped target. -/
theorem
  oriented_bounded_requested
  (certified : RequestedRuns.CertifiedReverseRun acquired data target) (capped : target ≤ 1)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total certified.run.orientedPhysical)
      (2 * (1 + (BasisSourceCovers.primitiveSlope covers)) * PreparedObservationCoercivity.coefficientNormSq
        coefficients) := by
  have bounded := certified.run.oriented_bounded weighted
  rw [← certified.totalError_eq] at bounded
  have paid := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes.capped_magnitude (slope
    := (BasisSourceCovers.primitiveSlope covers)) certified.totalPaid capped
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes.mass_nonnegative coefficients)
  exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩

end RequestedRuns.CertifiedReverseRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
