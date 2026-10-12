module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
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
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Choose common-basis query thresholds before source or face acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

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

namespace QuerySchedule

/-- The coefficient-independent uniform query scale for all basis rows in one original domain cell. -/
def cellQueryScale (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (column height : Fin (occurrence.compared.entered.domain.steps + 1)) : Coordinate :=
  (genus : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
      (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds column height)

set_option genInjectivity false in
/-- Cached source and face thresholds paying one original cell's basis-query target.

The allocated radius, every basis-row refinement threshold and their finite maximum are chosen before acquiring
primitive values. -/
structure CellQuery (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (column height : Fin (occurrence.compared.entered.domain.steps + 1)) (target :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The allocated common source and face radius for this cell. -/ radius :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The radius is the weighted allowance for the original uniform cell-query scale. -/ radius_eq : radius =
    Rational.Budget.Weighted.allowance target (32 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale occurrence column height)
  /-- The cached uniform source-model threshold. -/ sourceMinimum : Nat
  /-- The source threshold is exactly the uniform minimum for the retained radius. -/ source_eq : sourceMinimum =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius
  /-- The retained face-refinement threshold of every original basis row. -/ rowIndices : Data.Vector.DependentVector
    (fun _ : Fin genus => Nat)
  /-- Each row threshold is the geometric search on its exact transported cell model. -/ row_eq : ∀ row, rowIndices.get
    row = Rational.Geometric.Search.firstQuarterBelow
    ((occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.domain.patch.transported.cell
      column height).model.bound 0 radius
  /-- The cached common face-refinement threshold. -/ faceIndex : Nat
  /-- The face threshold is the exact maximum of all retained basis-row thresholds. -/ face_eq : faceIndex =
    rowIndices.maximum (fun _ value => value)

constructive_injectivity CellQuery

end QuerySchedule

namespace QuerySchedule.CellQuery

/-- Cache the weighted radius and all source and basis-row face thresholds for the specified original cell. -/
def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (column height : Fin (occurrence.compared.entered.domain.steps + 1)) (target :
      Normalization.InverseRootPolynomial.Coordinate) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.CellQuery occurrence column height target :=
  let radius := Rational.Budget.Weighted.allowance target (32 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale occurrence column height)
  let rows := Data.Vector.DependentVector.ofFn (fun row : Fin genus => Rational.Geometric.Search.firstQuarterBelow
    ((occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.domain.patch.transported.cell
      column height).model.bound 0 radius)
  ⟨radius, rfl, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceQueryMinimum radius, rfl, rows,
    fun row => Data.Vector.DependentVector.ofFn_get _ row, rows.maximum (fun _ value => value), rfl⟩

/-- A positive cell target bounds the acquired common-basis query scale once both cached thresholds are paid.

The original source-model radius and every basis-row face refinement remain linked to their own retained cell. -/
theorem accurate
    (acquired : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition
      request polynomials originals cells coefficients depth)
    (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
      (parent.edge.point 0) (parent.edge.point 1))
    {target : Normalization.InverseRootPolynomial.Coordinate} (query :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.CellQuery occurrence piece.column piece.row
      target)
    (positive : 0 < target) (sourcePaid : query.sourceMinimum ≤ index)
    {faceIndex : Nat} (facePaid : query.faceIndex ≤ faceIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired piece faceIndex ≤ target := open
      Purelib.Data.Rat in by
  have scaleNonnegative : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale occurrence
    piece.column piece.row :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
      (FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row =>
        (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_nonnegative
          (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
          piece.column piece.row (acquired.prepared.get row).localRequest 0).trans
        (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_uniform_le
          (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
          piece.column piece.row (acquired.prepared.get row).localRequest 0))))
  have weightNonnegative : 0 ≤ 32 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale
    occurrence piece.column piece.row :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) scaleNonnegative
  have radiusPositive : 0 < query.radius := by
    rw [query.radius_eq]
    exact Rational.Budget.Weighted.allowance_positive positive weightNonnegative
  have each (row : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.rowDensity acquired
    piece row faceIndex ≤
      32 * query.radius *
        Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.uniformQueryDensity
          (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds piece.column
            piece.row := by
    let tail := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryTail
      (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.bounds
      piece.column piece.row (acquired.prepared.get row).localRequest query.radius radiusPositive
    have faceLater : tail.index ≤ faceIndex :=
      (query.row_eq row).symm.trans_le
        (((query.rowIndices.get_le_maximum (fun _ value => value) row).trans_eq query.face_eq.symm).trans facePaid)
    have sourceSmall : tail.sourceRadius ≤ query.radius := by
      rw [tail.source_eq, acquired.index_eq row]
      exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_radius_lt
        (acquired.prepared.get row).localRequest.neighborhood.base.model.bound_small radiusPositive
        ((query.source_eq.symm.trans_le sourcePaid).trans (Nat.le_add_left index 2))).le
    exact (tail.accurate faceIndex faceLater).trans (tail.ceiling_le_uniform radiusPositive.le sourceSmall)
  have summed := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
      genus))
  rw [FiniteSum.Fin.sumFin_mul_left] at summed
  have bounded : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired piece faceIndex ≤
      (32 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale occurrence piece.column
        piece.row) * query.radius :=
    summed.trans_eq (by unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.cellQueryScale; ring1)
  rw [query.radius_eq] at bounded
  exact bounded.trans (Rational.Budget.Weighted.mul_allowance_le positive.le weightNonnegative)

end QuerySchedule.CellQuery

namespace QuerySchedule

/-- The dependent row of cell-query schedules at one original column. -/
def QueryRow (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (column : Fin (occurrence.compared.entered.domain.steps + 1)) (target :
      Normalization.InverseRootPolynomial.Coordinate) :=
  Data.Vector.DependentVector (fun height => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.CellQuery
    occurrence column height target)

end QuerySchedule

namespace QuerySchedule.QueryRow

/-- The maximum retained source threshold along this original column. -/
def sourceIndex {column : Fin (occurrence.compared.entered.domain.steps + 1)} {target :
  Normalization.InverseRootPolynomial.Coordinate}
    (row : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow occurrence column target) : Nat :=
      row.maximum (fun _ query => query.sourceMinimum)

/-- The maximum retained face-refinement threshold along this original column. -/
def faceIndex {column : Fin (occurrence.compared.entered.domain.steps + 1)} {target :
  Normalization.InverseRootPolynomial.Coordinate}
    (row : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow occurrence column target) : Nat :=
      row.maximum (fun _ query => query.faceIndex)

end QuerySchedule.QueryRow

set_option genInjectivity false in
/-- Retain all cell thresholds once, before selecting any source or face
polynomial. The same schedule serves every coefficient vector and parent. -/
structure QuerySchedule (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The complete retained cell-query grid in original column and height order. -/ rows : Data.Vector.DependentVector
    (fun column => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow occurrence column target)
  /-- The cached maximum source-model threshold over all original cells. -/ sourceMinimum : Nat
  /-- The source threshold equals the maximum of the retained column source thresholds. -/ source_eq : sourceMinimum =
    rows.maximum (fun _ row => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.sourceIndex row)
  /-- The cached maximum face-refinement threshold over all original cells. -/ faceIndex : Nat
  /-- The face threshold equals the maximum of the retained column face thresholds. -/ face_eq : faceIndex =
    rows.maximum (fun _ row => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.faceIndex row)

constructive_injectivity QuerySchedule

namespace QuerySchedule

/-- Prepare every original cell query and cache their common source and face maxima. -/
def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Normalization.InverseRootPolynomial.Coordinate) :
    QuerySchedule occurrence target :=
  let rows := Data.Vector.DependentVector.ofFn (fun column => Data.Vector.DependentVector.ofFn
    (fun height => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.CellQuery.build occurrence column
      height target))
  ⟨rows, rows.maximum (fun _ row => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.sourceIndex
    row), rfl, rows.maximum (fun _ row =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.faceIndex row), rfl⟩

/-- The complete cached schedule pays the basis-query target on any retained original fragment.

Both source and face stages must reach their separate retained maxima. -/
theorem accurate
    (acquired : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition
      request polynomials originals cells coefficients depth)
    (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
      (parent.edge.point 0) (parent.edge.point 1))
    {target : Normalization.InverseRootPolynomial.Coordinate} (schedule :
      QuerySchedule occurrence target)
    (positive : 0 < target) (sourcePaid : schedule.sourceMinimum ≤ index)
    {faceIndex : Nat} (facePaid : schedule.faceIndex ≤ faceIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired piece faceIndex ≤ target := by
  have sourceLe := ((schedule.rows.get piece.column).get_le_maximum (fun _ query => query.sourceMinimum)
    piece.row).trans
    (((schedule.rows.get_le_maximum (fun _ row =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.sourceIndex row) piece.column).trans_eq
      schedule.source_eq.symm).trans sourcePaid)
  have faceLe := ((schedule.rows.get piece.column).get_le_maximum (fun _ query => query.faceIndex) piece.row).trans
    (((schedule.rows.get_le_maximum (fun _ row =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.QueryRow.faceIndex row) piece.column).trans_eq
      schedule.face_eq.symm).trans facePaid)
  exact ((schedule.rows.get piece.column).get piece.row).accurate acquired piece positive sourceLe faceLe

end QuerySchedule

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
