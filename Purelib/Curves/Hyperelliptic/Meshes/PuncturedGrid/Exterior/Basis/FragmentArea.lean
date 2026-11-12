module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
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
import Purelib.Tactic.Ring

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

public section

/-! Homogeneous conjugate-area comparison on complete common-source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (rowDensity RowData gridValue
  weighted_increment_error)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable (acquired :
  PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)
  (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
    (parent.edge.point 0) (parent.edge.point 1))

/-- Coefficient-independent query scale on this retained physical fragment. -/
@[expose] def queryScale (faceIndex : Nat) : Coordinate :=
  (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row =>
    FragmentQueries.rowDensity acquired piece row faceIndex)

/-- The coefficient-independent query scale is nonnegative at every shared face stage. -/
theorem queryScale_nonnegative (faceIndex : Nat) : 0 ≤
  FragmentArea.queryScale acquired piece faceIndex :=
  Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    (FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row =>
      Face.FragmentQueries.queryDensity_nonnegative
        (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
        piece.column piece.row (acquired.prepared.get row).localRequest faceIndex)))

/-- The coefficient-independent trace density from the original query scale, parent movement and retained basis-source
slope. -/
@[expose] def traceDensity (faceIndex : Nat) : Coordinate :=
  2 * (FragmentArea.queryScale acquired piece faceIndex *
    parent.edge.pointMovement +
    CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)

/-- The original basis-source slope is at most the complete trace density. -/
private theorem source_le_trace (faceIndex : Nat) :
    CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers ≤
      FragmentArea.traceDensity acquired piece faceIndex := by
  have sourceNN :=
    CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative covers
  have extra : 0 ≤ FragmentArea.queryScale acquired piece faceIndex *
    parent.edge.pointMovement := Arithmetic.mul_nonneg_direct
    (FragmentArea.queryScale_nonnegative acquired piece faceIndex)
    (Gaussian.Norm.Basic.normSq_nonneg (parent.edge.point 1 - parent.edge.point 0))
  exact (le_add_of_nonneg_left extra).trans
    ((le_add_of_nonneg_right (add_nonneg extra sourceNN)).trans_eq (by
        unfold FragmentArea.traceDensity;
        ring1))

/-- The squared displacement along the original parent equals its full movement times the squared parameter
displacement. -/
private theorem point_movement (first last : Coordinate) :
    Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) = parent.edge.pointMovement *
      (last - first)^2 := by
  have full := parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0
  have unitSquare : ((1 : Coordinate) - 0)^2 = 1 := rfl
  simp only [-eq_self, -iff_self, unitSquare, Fraction.Field.one_mul] at full
  exact (parent.edge.localSegment.normSq_pointAt_sub_pointAt last first).trans
    ((congrArg (fun value => (last - first)^2 * value) full.symm).trans (Fraction.Field.mul_comm ..))

/-- Every retained fragment parameter lies in the original unit parent interval. -/
private theorem unit_parameter {parameter : Coordinate}
    (inside : piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper) : 0 ≤ parameter ∧ parameter ≤ 1 :=
  ⟨piece.within.1.trans inside.1, inside.2.trans piece.within.2⟩

/-- Every retained fragment parameter maps inside its original indexed domain box. -/
private theorem fragment_contains {parameter : Coordinate}
    (inside : piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper) :
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains (parent.edge.point parameter) :=
      by
  exact (congrArg (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains
    (Integration.PreparedParentSplitting.prepared_point_eq parent parameter)).mpr (piece.contains_query parameter
      inside)

/-- The finite squared Gaussian coefficient norm is nonnegative. -/
private theorem coefficient_nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
  (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients
    row)))

/-- Bound the coefficient-weighted aligned grid increment by the common trace density and coefficient norm.

Both parameters lie in one retained fragment, and the original cached source and grid-query bounds use its actual parent
movement. -/
theorem grid_increment_bound (member : parent ∈ occurrence.compared.entered.cache.parents)
    {faceIndex : Nat} (data : RowData occurrence
      faceIndex) (first last : Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Gaussian.Norm.Basic.normSq (FragmentQueries.gridValue
      (coefficients := coefficients) piece data last -
      FragmentQueries.gridValue (coefficients := coefficients) piece
      data first) ≤
      FragmentArea.traceDensity acquired piece faceIndex *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (last - first)^2 := by
  have error := FragmentQueries.weighted_increment_error acquired
    piece member data first last firstInside lastInside
  rw [FragmentArea.point_movement] at error
  have source := WeightedResampling.ReciprocalDiskArcOwners.increment_bound
    originals coefficients (FragmentArea.unit_parameter piece
    firstInside) (FragmentArea.unit_parameter piece lastInside)
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct error
      source) (by decide : (0 : Coordinate) ≤ 2))
  rw [sub_add_cancel] at bound
  exact bound.trans_eq (by
    unfold FragmentArea.traceDensity
      FragmentArea.queryScale; ring1)

/-- The estimate includes the endpoint discrepancy and every intermediate
vertex. Its error is quadratic in the coefficient norm and has no fine-count factor. -/
theorem conjugate_area_bound (member : parent ∈ occurrence.compared.entered.cache.parents)
    {faceIndex vertices : Nat} (data : RowData
      occurrence faceIndex)
    (parameters : Fin (vertices + 1) → Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin vertices, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨gridValue (coefficients := coefficients) piece data (parameters vertex),
        FragmentQueries.gridValue (coefficients := coefficients) piece
          data (parameters vertex)⟩ : PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex),
        CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex)⟩ : PrimitivePoint))) :
    Gaussian.Norm.Basic.normSq (grid.centeredArea - source.centeredArea) ≤
      40 * (FragmentArea.queryScale acquired piece faceIndex *
        (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq) *
        FragmentArea.traceDensity acquired piece faceIndex *
          (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 *
        (PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last vertices)))^2 := by
  have bounded := Path.WeightedPathComparison.Sample.weighted_full_comparison grid source
    (fun edge : Fin vertices => PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (error := FragmentArea.queryScale acquired piece faceIndex *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq)
    (density := FragmentArea.traceDensity acquired piece faceIndex *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (fun edge => PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
    (fun vertex => by
      rw [grid.centered_eq, source.centered_eq, ←
        Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub, ←
        Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub]
      apply Path.ConjugateIncrementComparison.conjugateFirst_error
      have error := FragmentQueries.weighted_increment_error acquired
        piece member data
        (parameters 0) (parameters vertex) (inside 0) (inside vertex)
      have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
        (FragmentArea.fragment_contains piece (inside vertex))
          (FragmentArea.fragment_contains piece (inside 0))
      have upper := Arithmetic.mul_le_mul_of_nonneg_left_direct distance
        (Arithmetic.mul_nonneg_direct
          (FragmentArea.queryScale_nonnegative acquired piece
          faceIndex) (FragmentArea.coefficient_nonnegative
          (coefficients := coefficients)))
      have h := error.trans upper
      change Basic.LessEqual _ _ at h
      exact ⟨by
          change Basic.LessEqual _ _
          simpa only [PrimitivePoint.sub,
            Gaussian.Norm.Basic.normSq_eq_canonical] using h,
        by
          change Basic.LessEqual _ _
          simpa only [PrimitivePoint.sub,
            Gaussian.Norm.Basic.normSq_eq_canonical] using h⟩)
    (fun edge => by
      rw [PairedFragmentArea.parameterStep_sq]
      apply Path.ConjugateIncrementComparison.conjugateFirst_error
      have bound := FragmentArea.grid_increment_bound acquired piece
        member data _ _ (inside edge.castSucc) (inside edge.succ)
      exact ⟨by simpa only [PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using bound,
        by simpa only [PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using bound⟩)
    (fun edge => by
      rw [PairedFragmentArea.parameterStep_sq]
      apply Path.ConjugateIncrementComparison.conjugateFirst_error
      have source :=
        WeightedResampling.ReciprocalDiskArcOwners.increment_bound originals
        coefficients (FragmentArea.unit_parameter piece (inside
        edge.castSucc))
        (FragmentArea.unit_parameter piece (inside edge.succ))
      have upper := Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct
          (FragmentArea.source_le_trace acquired piece faceIndex)
          (FragmentArea.coefficient_nonnegative (coefficients :=
          coefficients)))
        (Arithmetic.sq_nonneg_direct (parameters edge.succ - parameters edge.castSucc))
      have h := source.trans upper
      change Basic.LessEqual _ _ at h
      exact ⟨by
          change Basic.LessEqual _ _
          simpa only [PrimitivePoint.sub,
            Gaussian.Norm.Basic.normSq_eq_canonical] using h,
        by
          change Basic.LessEqual _ _
          simpa only [PrimitivePoint.sub,
            Gaussian.Norm.Basic.normSq_eq_canonical] using h⟩)
  rw [PairedFragmentArea.parameterSteps_total] at bounded
  exact bounded.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea

end
