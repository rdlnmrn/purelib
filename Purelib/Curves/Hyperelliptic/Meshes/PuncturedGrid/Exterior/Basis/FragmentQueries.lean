module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

section

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Compare shared grid queries with the exact common-basis source bank.
Root transport follows the retained occurrence; weighted errors retain the
same coefficient vector as the source-area lower bound. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries

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

variable (acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth)
  (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
    (parent.edge.point 0) (parent.edge.point 1))

/-- The density is computed from the actual retained row request. -/
@[expose] def rowDensity (row : Fin genus) (faceIndex : Nat) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity
    (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
    piece.column piece.row (acquired.prepared.get row).localRequest faceIndex

/-- The retained domain primitive data for every original basis differential at one shared face index. -/
@[expose] def RowData (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (faceIndex : Nat) :=
  (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives
    (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.domain
    (Periods.PeriodMatrix.standardDifferential row) faceIndex

/-- Read the common coefficient-weighted grid primitive at a parameter point of the original retained parent segment. -/
@[expose] def gridValue {faceIndex : Nat} (data :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex) (parameter :
  Normalization.InverseRootPolynomial.Coordinate) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row *
    (data row).anchors.alignedValue (data row).offsets piece.column piece.row (parent.edge.point parameter)

/-- Root transport comes from membership in the occurrence's retained parent
cache; source readback uses the existing acquisition's exact polynomial. -/
theorem row_increment_error (member : parent ∈ occurrence.compared.entered.cache.parents)
    (row : Fin genus) {faceIndex : Nat} (data :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex)
    (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Data.Gaussian.Norm.Basic.normSq (((data row).anchors.alignedValue (data row).offsets piece.column piece.row
      (parent.edge.point last) -
        (data row).anchors.alignedValue (data row).offsets piece.column piece.row (parent.edge.point first)) -
      ((originals.get row).primitive.value.eval (parent.edge.point last) -
        (originals.get row).primitive.value.eval (parent.edge.point first))) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.rowDensity acquired piece row faceIndex *
        Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) := by
  have present : Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
    parent ∈
      occurrence.compared.entered.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge
        (Periods.PeriodMatrix.standardDifferential row)) :=
    Data.List.Map.mem_map_of_mem member
  have reached := (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.reached _
    present
  have bounded := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.query_increment_le
    (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
    (parent := Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
      parent)
    (count := (covers.get row).count) (target := request.sourceTolerance)
    piece (data row).primitives reached (acquired.prepared.get row).localRequest first last firstInside lastInside
  rw [acquired.primitive_eq row] at bounded
  have point_eq (parameter : Normalization.InverseRootPolynomial.Coordinate) :
      (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
        parent).edge.point parameter = parent.edge.point parameter := rfl
  rw [point_eq first, point_eq last] at bounded
  dsimp only [Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue]
  rw [show ((data row).offsets.values piece.column piece.row + (data row).primitives.value piece.column piece.row
    (parent.edge.point last)) -
      ((data row).offsets.values piece.column piece.row + (data row).primitives.value piece.column piece.row
        (parent.edge.point first)) =
      (data row).primitives.value piece.column piece.row (parent.edge.point last) -
        (data row).primitives.value piece.column piece.row (parent.edge.point first) by ring1]
  exact bounded

/-- The grid/source error remains homogeneous in the one coefficient vector
used by the common source-area certificate. -/
theorem weighted_increment_error (member : parent ∈ occurrence.compared.entered.cache.parents)
    {faceIndex : Nat} (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
      faceIndex) (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Data.Gaussian.Norm.Basic.normSq ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue
      (coefficients := coefficients) piece data last -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients := coefficients) piece
      data first) -
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients last -
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients first)) ≤
      (genus : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.rowDensity acquired piece row faceIndex) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * Data.Gaussian.Norm.Basic.normSq
          (parent.edge.point last - parent.edge.point first) := open Purelib.Data.Rat in by
  let errors := fun row =>
    ((data row).anchors.alignedValue (data row).offsets piece.column piece.row (parent.edge.point last) -
      (data row).anchors.alignedValue (data row).offsets piece.column piece.row (parent.edge.point first)) -
    ((originals.get row).primitive.value.eval (parent.edge.point last) -
      (originals.get row).primitive.value.eval (parent.edge.point first))
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build errors
  have paid : budget.scale ≤ (genus : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.rowDensity acquired piece row faceIndex) *
      Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.row_increment_error acquired piece member row
        data first last firstInside lastInside))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.sumFin_mul_right] at bound
    exact bound.trans_eq (by ring1)
  have equal : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue (coefficients :=
    coefficients) piece data last - Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue
    (coefficients := coefficients) piece data first) -
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients last -
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients first) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * errors row) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.gridValue
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
    rw [← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [errors]; ring1)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  rw [equal]
  exact (budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid nonnegative).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries

end
