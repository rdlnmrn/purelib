module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedArea
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
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Endpoint discrepancies for composing the actual owned source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints

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

variable (acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)
  (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
    (parent.edge.point 0) (parent.edge.point 1))

/-- Bound one original coefficient-weighted point-owner reading against its containing cell's aligned value.

The paid positive owner tolerance and common stage retain the same coefficient vector and sample index. -/
private theorem owner_at {faceIndex vertices : Nat} (data :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex)
    (parameters : Fin (vertices + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    {tolerance : Normalization.InverseRootPolynomial.Coordinate} (owners :
      OwnerRequest occurrence tolerance) (positive : 0 <
      tolerance)
    (later : owners.index ≤ faceIndex)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex =>
      parent.edge.point (parameters vertex))) (vertex : Fin (vertices + 1)) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue
      readings coefficients vertex - Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue
      (coefficients := coefficients) piece data (parameters vertex)) ≤
      (tolerance / 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have contained : (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains
      (parent.edge.point (parameters vertex)) :=
    (congrArg (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains
      (Integration.PreparedParentSplitting.prepared_point_eq parent (parameters vertex))).mpr
      (piece.contains_query (parameters vertex) (inside vertex))
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.owned_value_bound owners positive later data
    readings coefficients vertex piece.column piece.row contained

/-- Endpoint error includes owner changes at both ends, even at identical
coordinates. The same estimate pays the total of a retained fragment. -/
theorem owned_increment_error (member : parent ∈ occurrence.compared.entered.cache.parents)
    {faceIndex vertices : Nat} (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
      occurrence faceIndex)
    (parameters : Fin (vertices + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    {tolerance : Normalization.InverseRootPolynomial.Coordinate} (owners :
      OwnerRequest occurrence tolerance) (positive : 0 <
      tolerance)
    (later : owners.index ≤ faceIndex)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex =>
      parent.edge.point (parameters vertex)))
    (start finish : Fin (vertices + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue
      readings coefficients finish - Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings
      coefficients start) -
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters finish) -
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters start))) ≤
      2 * (tolerance + Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired piece
        faceIndex * Data.Gaussian.Norm.Basic.normSq
        (parent.edge.point (parameters finish) - parent.edge.point (parameters start))) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let owned := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings coefficients finish -
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings coefficients start
  let fixed := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients :=
    coefficients) piece data (parameters finish) -
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients := coefficients) piece
      data (parameters start)
  let source :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
    originals coefficients (parameters finish) -
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
    originals coefficients (parameters start)
  have ownerError : Data.Gaussian.Norm.Basic.normSq (owned - fixed) ≤ tolerance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bounded := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints.owner_at (coefficients := coefficients)
          piece data parameters inside owners positive later readings finish)
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints.owner_at (coefficients := coefficients)
            piece data parameters inside owners positive later readings start)) (by
                decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
    have identity : owned - fixed =
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings coefficients finish -
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients := coefficients)
          piece data (parameters finish)) -
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings coefficients start -
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients := coefficients)
          piece data (parameters start)) := by
      dsimp only [owned, fixed]
      ring1
    rw [identity]
    exact bounded.trans_eq (by
      rw [show 2 * ((tolerance / 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients + (tolerance
        / 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
        ((tolerance / 4) * 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1,
          Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)])
  have sourceError := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.weighted_increment_error
    acquired piece member data _ _ (inside start) (inside finish)
  change Data.Gaussian.Norm.Basic.normSq (owned - source) ≤ _
  rw [show owned - source = (owned - fixed) + (fixed - source) by ring1]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ownerError
      sourceError)
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by
          unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale;
          ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentEndpoints
