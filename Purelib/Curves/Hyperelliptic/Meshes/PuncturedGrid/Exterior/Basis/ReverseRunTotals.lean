module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Integration.Path.PairedBlockTotals
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon.Stokes

public section

/-! Descending parent-run endpoint bounds for the cross-parent area comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
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

namespace ReverseSourceRun

/-- Squared endpoint error of the complete physical run. -/
@[expose] def totalError (run : ReverseSourceRuns.ReverseSourceRun acquired data) : Coordinate :=
  (run.fragments.length : InverseRootPolynomial.Coordinate)^2 *
    PairedFragmentBlocks.maximum (OwnedFragment.totalError (acquired := acquired)) run.fragments

/-- The endpoint comparison uses the same cached source summary as the area comparison, so it can pay the joining
polygons between complete parent runs. -/
theorem cached_source_total_bound (run : ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total
      ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten).sub
        (PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal weighted.source.total)))
          (run.totalError * PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have massNN : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have bounded := PairedBlockTotals.blocks_total_difference_bound
    (run.fragments.map OwnedFragment.pair)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PairedFragmentBlocks.maximum_nonnegative (OwnedFragment.totalError (acquired := acquired)) run.fragments) massNN)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Map.mem_map.mp member
      have localBound := OwnedFragment.total_accurate (acquired := acquired) fragment
      have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (PairedFragmentBlocks.le_maximum (OwnedFragment.totalError (acquired := acquired)) present) massNN
      exact ⟨localBound.1.trans upper, localBound.2.trans upper⟩)
  rw [run.source_total weighted, Data.List.Map.length_map] at bounded
  have scalar : (run.fragments.length : InverseRootPolynomial.Coordinate)^2 *
      (PairedFragmentBlocks.maximum (OwnedFragment.totalError (acquired := acquired)) run.fragments *
        PreparedObservationCoercivity.coefficientNormSq coefficients) = run.totalError *
          PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold ReverseSourceRuns.ReverseSourceRun.totalError
    ring1
  rw [scalar] at bounded
  exact bounded

/-- The source magnitude comes from its original primitive bank, independently of the number of physical fragments. -/
theorem cached_source_bounded {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      (PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal weighted.source.total))
      (BasisSourceCovers.primitiveSlope covers *
        PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have bounded := SourceRun.cached_source_bounded weighted
  constructor
  · simpa only [PrimitivePoint.zero, PrimitivePoint.sub, zero_sub,
      Data.Gaussian.Basic.Canonical.normSq_neg] using bounded.1
  · simpa only [PrimitivePoint.zero, PrimitivePoint.sub, zero_sub,
      Data.Gaussian.Basic.Canonical.normSq_neg] using bounded.2

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns.ReverseSourceRun in
/-- Uniform whole-parent magnitude needed when bounding cross-parent wedges. -/
theorem owned_total_bounded (run : ReverseSourceRuns.ReverseSourceRun acquired data)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    PrimitivePoint.Bounded
      (PairedIncrementArea.total
      ((run.fragments.map OwnedFragment.pair).map Prod.fst).flatten)
        (2 * (run.totalError + BasisSourceCovers.primitiveSlope covers) *
          PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have errors := run.cached_source_total_bound weighted
  have source :=
    cached_source_bounded
    weighted
  have scalar {a b : InverseRootPolynomial.Gaussian}
      (error : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ run.totalError *
        PreparedObservationCoercivity.coefficientNormSq coefficients)
      (bounded : Data.Gaussian.Norm.Basic.normSq b ≤ BasisSourceCovers.primitiveSlope covers *
        PreparedObservationCoercivity.coefficientNormSq coefficients) :
      Data.Gaussian.Norm.Basic.normSq a ≤ 2 * (run.totalError + BasisSourceCovers.primitiveSlope covers) *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have result := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct error
        bounded)
        (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
    rw [sub_add_cancel] at result
    exact result.trans_eq (by ring1)
  have oldBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  exact ⟨canonicalBound (scalar (oldBound errors.1) (oldBound source.1)),
    canonicalBound (scalar (oldBound errors.2) (oldBound source.2))⟩

end ReverseSourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
