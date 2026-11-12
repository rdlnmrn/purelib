module
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugateIncrementComparison
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Integration.Path.HomogeneousOwnedPathComparison
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
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Keep actual point owners in the common-basis conjugate area comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedArea

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData gridValue)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue owned_value_bound)

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
  {areaAllowance sourceTarget coefficientTarget : InverseRootPolynomial.Coordinate}
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- Owner changes and the complete grid/source comparison share one
coefficient vector and retain the full homogeneous area error. -/
theorem owned_conjugate_area_bound (member : parent ∈ occurrence.compared.entered.cache.parents)
    {faceIndex vertices : Nat} (data : RowData
      occurrence faceIndex)
    (parameters : Fin (vertices + 1) → InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin vertices, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    {allowance : InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget vertices
      allowance)
    (owners : OwnerRequest occurrence budget.tolerance)
      (later : owners.index ≤ faceIndex)
    (readings : OwnedReadings data (fun vertex =>
      parent.edge.point (parameters vertex)))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex),
        CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Gaussian.Norm.Basic.normSq (owned.centeredArea - source.centeredArea) ≤
      2 * (40 * budget.tolerance * (4 * FragmentArea.traceDensity
        acquired piece faceIndex + 3) *
          (PairedFragmentArea.parameterStep forward (parameters 0)
            (parameters (Fin.last vertices)) + allowance)^2 +
        40 * (FragmentArea.queryScale acquired piece faceIndex *
          (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq) *
          FragmentArea.traceDensity acquired piece faceIndex *
          (PairedFragmentArea.parameterStep forward (parameters 0)
            (parameters (Fin.last vertices)))^2) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Algebra in by
  let fixed := Periods.CenteredBilinearPath.Sample.build (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
    (⟨gridValue (coefficients := coefficients) piece data (parameters vertex),
      FragmentQueries.gridValue (coefficients := coefficients) piece
        data (parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
  have massNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have movement : 0 ≤ parent.edge.pointMovement := Gaussian.Norm.Basic.normSq_nonneg _
  have densityNonnegative : 0 ≤ FragmentArea.traceDensity acquired
    piece faceIndex :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
        (FragmentArea.queryScale_nonnegative acquired piece faceIndex)
        movement)
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
          covers))
  have ownerError := Path.HomogeneousOwnedPathComparison.LengthErrorBudget.homogeneous_reading_comparison budget
    massNonnegative owned fixed
    (fun edge : Fin vertices => PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    densityNonnegative (fun edge =>
      PairedFragmentArea.parameterStep_nonnegative forward _ _ (ordered
      edge))
    (fun vertex => by
      apply Path.ConjugateIncrementComparison.conjugateFirst_error
      have contained : (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains
          (parent.edge.point (parameters vertex)) :=
        (congrArg (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains
          (Integration.PreparedParentSplitting.prepared_point_eq parent (parameters vertex))).mpr
          (piece.contains_query (parameters vertex) (inside vertex))
      have bound := OwnerRequest.owned_value_bound owners
        budget.tolerance_positive later data readings coefficients
        vertex piece.column piece.row contained
      change Fraction.Order.Basic.LessEqual _ _ at bound
      exact ⟨by
        change Fraction.Order.Basic.LessEqual _ _
        simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
        convert bound using 1; rfl,
        by
        change Fraction.Order.Basic.LessEqual _ _
        simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at bound
        convert bound using 1; rfl⟩)
    (fun edge => by
      rw [PairedFragmentArea.parameterStep_sq]
      apply Path.ConjugateIncrementComparison.conjugateFirst_error
      have bound := FragmentArea.grid_increment_bound acquired piece
        member data _ _ (inside edge.castSucc) (inside edge.succ)
      change Fraction.Order.Basic.LessEqual _ _ at bound
      exact ⟨by
        change Fraction.Order.Basic.LessEqual _ _
        simpa only [Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using bound,
        by
        change Fraction.Order.Basic.LessEqual _ _
        simpa only [Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using bound⟩)
  rw [PairedFragmentArea.parameterSteps_total] at ownerError
  have sourceError := FragmentArea.conjugate_area_bound acquired piece
    member data parameters inside forward ordered fixed source
  rw [show owned.centeredArea - source.centeredArea =
    (owned.centeredArea - fixed.centeredArea) + (fixed.centeredArea - source.centeredArea) by ring1]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ownerError
      sourceError)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedArea
