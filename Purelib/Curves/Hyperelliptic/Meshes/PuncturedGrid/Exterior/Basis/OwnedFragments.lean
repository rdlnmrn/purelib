module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints
public import Purelib.Integration.Path.CenteredPathIncrements
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Retain actual common-source fragment paths and their derived errors. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)

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

variable (acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
set_option genInjectivity false in
/-- Geometry and existing readings only; area and total estimates are derived. -/
structure OwnedFragment {faceIndex : Nat} (data :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex) where
  /-- The selected original parent belongs to the occurrence's retained cache. -/ member : parent ∈
    occurrence.compared.entered.cache.parents
  /-- The original common geometric fragment of that retained parent. -/ piece :
    Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
    (parent.edge.point 0) (parent.edge.point 1)
  /-- The actual retained number of sampled increments. -/ vertices : Nat
  /-- The complete original parameter sample, including repeated coordinates. -/ parameters : Fin (vertices + 1) →
    Normalization.InverseRootPolynomial.Coordinate
  /-- Every retained parameter lies inside the original fragment interval. -/ inside : ∀ vertex, piece.interval.lower ≤
    parameters vertex ∧ parameters vertex ≤ piece.interval.upper
  /-- The retained source traversal orientation. -/ forward : Bool
  /-- The original parameter sample follows its retained orientation. -/ ordered : ∀ edge : Fin vertices, if forward
    then parameters edge.castSucc ≤ parameters edge.succ
    else parameters edge.succ ≤ parameters edge.castSucc
  /-- The original finite length-error allowance. -/ allowance : Normalization.InverseRootPolynomial.Coordinate
  /-- The retained length-error budget for the actual increment count. -/ budget : Path.NoisyPathArea.LengthErrorBudget
    vertices allowance
  /-- The original basis-row owner requests at the retained budget tolerance. -/ owners :
    OwnerRequest occurrence budget.tolerance
  /-- The shared face stage pays the retained owner requests. -/ later : owners.index ≤ faceIndex
  /-- The actual original point-owner readings for every basis row and retained vertex. -/ readings :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex => parent.edge.point
    (parameters vertex))
  /-- The retained conjugate sample of the coefficient-weighted owned values. -/ owned :
    Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
    (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
  /-- The retained conjugate sample of the same coefficient-weighted source primitives. -/ source :
    Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
    (⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients (parameters vertex),
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients (parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))

constructive_injectivity OwnedFragment

namespace OwnedFragment
variable {acquired} {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
  occurrence faceIndex}

/-- Both increment lists are retained by their original area samples. -/
@[expose] def pair (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals
  := originals) (coefficients := coefficients) data) :
    List Topology.Polygon.Stokes.PrimitivePoint × List PrimitivePoint := ((Path.CenteredPathIncrements.Sample.increments
      fragment.owned), (Path.CenteredPathIncrements.Sample.increments fragment.source))

/-- The coefficient-independent complete owner and source-query area error for this retained fragment. -/
@[expose] def areaError (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : Coordinate :=
  2 * (40 * fragment.budget.tolerance * (4 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity
    acquired fragment.piece faceIndex + 3) *
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward
        (fragment.parameters 0) (fragment.parameters (Fin.last fragment.vertices)) + fragment.allowance)^2 +
    40 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq) *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece faceIndex *
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward
        (fragment.parameters 0) (fragment.parameters (Fin.last fragment.vertices)))^2)

/-- The coefficient-independent endpoint-total discrepancy from original owner tolerance and query displacement. -/
@[expose] def totalError (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : Coordinate :=
  2 * (fragment.budget.tolerance + Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired
    fragment.piece faceIndex * Data.Gaussian.Norm.Basic.normSq
    (parent.edge.point (fragment.parameters (Fin.last fragment.vertices)) - parent.edge.point (fragment.parameters 0)))

/-- The retained conjugate owned and source areas differ by the computed error times the squared coefficient norm. -/
theorem area_accurate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area fragment.pair.1 - Path.PairedIncrementArea.area
      fragment.pair.2) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError (acquired := acquired)
        fragment * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  change Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
    (Path.CenteredPathIncrements.Sample.increments fragment.owned) -
    Path.PairedIncrementArea.area (Path.CenteredPathIncrements.Sample.increments fragment.source)) ≤ _
  rw [Path.CenteredPathIncrements.Sample.increments_area fragment.owned,
    Path.CenteredPathIncrements.Sample.increments_area fragment.source]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedArea.owned_conjugate_area_bound acquired fragment.piece
    fragment.member data fragment.parameters fragment.inside
    fragment.forward fragment.ordered fragment.budget fragment.owners fragment.later fragment.readings fragment.owned
      fragment.source

/-- Both retained conjugate totals differ by the computed endpoint error times the coefficient norm. -/
theorem total_accurate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total fragment.pair.1).sub
      (Path.PairedIncrementArea.total fragment.pair.2))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
        fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total
    (Path.CenteredPathIncrements.Sample.increments fragment.owned)).sub
    (Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments fragment.source))) _
  rw [Path.CenteredPathIncrements.Sample.increments_total fragment.owned,
    Path.CenteredPathIncrements.Sample.increments_total fragment.source, ←
    Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub, ←
    Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub]
  apply Path.ConjugateIncrementComparison.conjugateFirst_error
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints.owned_increment_error acquired
    fragment.piece fragment.member data fragment.parameters fragment.inside
    fragment.owners fragment.budget.tolerance_positive fragment.later fragment.readings 0 (Fin.last fragment.vertices)
  change Fraction.Order.Basic.LessEqual _ _ at bound
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact ⟨by
    change Fraction.Order.Basic.LessEqual _ _
    convert bound using 1
    · rfl
    · unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError
      rw [Gaussian.Norm.Basic.normSq_eq_canonical],
    by
    change Fraction.Order.Basic.LessEqual _ _
    convert bound using 1
    · rfl
    · unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError
      rw [Gaussian.Norm.Basic.normSq_eq_canonical]⟩

/-- The original basis-source slope weighted by the squared retained endpoint displacement. -/
@[expose] def sourceBound (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : Coordinate :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers *
    (fragment.parameters (Fin.last fragment.vertices) - fragment.parameters 0)^2

/-- The common coefficient-independent magnitude bound for the owned and source totals. -/
@[expose] def totalBound (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) : Coordinate :=
  2 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
    fragment + fragment.sourceBound)

/-- Both original retained source totals meet the source slope bound times the coefficient norm. -/
private theorem source_raw_bound (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total fragment.pair.2)
      (fragment.sourceBound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
    (Path.CenteredPathIncrements.Sample.increments fragment.source)) _
  rw [Path.CenteredPathIncrements.Sample.increments_total fragment.source, ←
    Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub]
  apply Path.ConjugateIncrementComparison.conjugateFirst_bounded
  have unit (vertex : Fin (fragment.vertices + 1)) : 0 ≤ fragment.parameters vertex ∧ fragment.parameters vertex ≤ 1 :=
    ⟨fragment.piece.within.1.trans (fragment.inside vertex).1, (fragment.inside vertex).2.trans fragment.piece.within.2⟩
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.ReciprocalDiskArcOwners.increment_bound
    originals coefficients (unit 0) (unit (Fin.last fragment.vertices))
  have bound : Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
    originals coefficients (fragment.parameters (Fin.last fragment.vertices)) -
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (fragment.parameters 0)) ≤ fragment.sourceBound *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    bounded.trans_eq (by
        unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceBound;
        ring1)
  change Fraction.Order.Basic.LessEqual _ _ at bound
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact ⟨by
    change Fraction.Order.Basic.LessEqual _ _
    convert bound using 1; rfl,
    by
    change Fraction.Order.Basic.LessEqual _ _
    convert bound using 1; rfl⟩

/-- Both original retained source totals meet the common total bound times the coefficient norm. -/
theorem source_bounded (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total fragment.pair.2)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
        fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Purelib.Algebra in by
  have errorNN : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired
    := acquired) fragment :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg fragment.budget.tolerance_positive.le
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale_nonnegative acquired fragment.piece
          faceIndex) (Gaussian.Norm.Basic.normSq_nonneg _)))
  have sourceNN : 0 ≤ fragment.sourceBound :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have paid : fragment.sourceBound ≤
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
    fragment :=
    (le_add_of_nonneg_left errorNN).trans
      ((le_add_of_nonneg_right (add_nonneg errorNN sourceNN)).trans_eq (by
          unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound;
          ring1))
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have raw := fragment.source_raw_bound
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid massNN
  exact ⟨raw.1.trans upper, raw.2.trans upper⟩

/-- Both actual retained owned totals meet that same homogeneous common total bound. -/
theorem owned_bounded (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total fragment.pair.1)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
        fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have errors := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.total_accurate (acquired
    := acquired) fragment
  have source := fragment.source_raw_bound
  have scalar {a b : Normalization.InverseRootPolynomial.Gaussian} (error : Data.Gaussian.Norm.Basic.normSq (a - b)
    ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
    fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (bounded : Data.Gaussian.Norm.Basic.normSq b ≤ fragment.sourceBound *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
      Data.Gaussian.Norm.Basic.normSq a ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
        fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have result := (Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct error
        bounded) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
    rw [sub_add_cancel] at result
    exact result.trans_eq (by
        unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound;
        ring1)
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  exact ⟨canonicalBound (scalar (oldBound errors.1) (oldBound source.1)),
    canonicalBound (scalar (oldBound errors.2) (oldBound source.2))⟩

end OwnedFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
