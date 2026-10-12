module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
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
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Integration.Path.PairedBlockTotals
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback.BasisPreparedCommonRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Complete parent-run endpoint bounds for the cross-parent area comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

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
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

namespace SourceRun

/-- Squared endpoint error of the complete physical run. -/
@[expose] def totalError (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data) :
  Coordinate :=
  (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired))
      run.fragments

/-- The endpoint comparison uses the same cached source summary as the area
comparison, so it can pay the joining polygons between complete parent runs. -/
theorem cached_source_total_bound (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired
  data)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Path.PairedIncrementArea.total
        ((run.fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
          Prod.fst).flatten).sub
          (Path.ConjugatePathReadback.conjugateDiagonal weighted.source.total))
      (run.totalError * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Purelib.Algebra
        in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have bounded := Path.PairedBlockTotals.blocks_total_difference_bound
    (run.fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
        acquired)) run.fragments) massNN)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      have localBound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.total_accurate
        (acquired := acquired) fragment
      have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
          acquired)) present) massNN
      exact ⟨localBound.1.trans upper, localBound.2.trans upper⟩)
  rw [run.source_total weighted, List.Map.length_map] at bounded
  have scalar : (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
        acquired)) run.fragments *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) = run.totalError *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun.totalError
    ring1
  rw [scalar] at bounded
  exact bounded

/-- The source magnitude comes from its original primitive bank, independently
of the number of physical fragments. -/
theorem cached_source_bounded {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal weighted.source.total)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.ReciprocalDiskArcOwners.increment_bound
    originals coefficients
    (first := 0) (last := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
  rw [show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct,
    ←
      Acquisition.ChildPairs.Weighted.source_total
      weighted] at bounded
  have canonical : Gaussian.Basic.Canonical.normSq weighted.source.total ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    change Fraction.Order.Basic.LessEqual _ _ at bounded ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bounded
  exact Path.ConjugateIncrementComparison.conjugateFirst_bounded
    (point := ⟨weighted.source.total, weighted.source.total⟩) ⟨canonical, canonical⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun in
/-- Uniform whole-parent magnitude needed when bounding cross-parent wedges. -/
theorem owned_total_bounded (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total
        ((run.fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
          Prod.fst).flatten)
      (2 * (run.totalError +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have errors := run.cached_source_total_bound weighted
  have source := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun.cached_source_bounded weighted
  have scalar {a b : Normalization.InverseRootPolynomial.Gaussian}
      (error : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ run.totalError *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (bounded : Data.Gaussian.Norm.Basic.normSq b ≤
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
      Data.Gaussian.Norm.Basic.normSq a ≤ 2 * (run.totalError +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have result := (Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct error
        bounded)
        (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
    rw [sub_add_cancel] at result
    exact result.trans_eq (by ring1)
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  exact ⟨canonicalBound (scalar (oldBound errors.1) (oldBound source.1)),
    canonicalBound (scalar (oldBound errors.2) (oldBound source.2))⟩

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
