module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
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
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Choose a complete block comparison request before numerical acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks

open Purelib.Data

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

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

variable {acquired :
  PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

/-- Compute the common block trace-density bound from original parent movement and primitive slope. -/
@[expose] def blockDensity (covers : SourceLocations.BasisSourceCovers
  parent) : Coordinate :=
  2 * (parent.edge.pointMovement +
    (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers))

/-- Choose a local fragment error cap paying the full count-dependent comparison and bounded by one. -/
@[expose] def blockLocalTarget (covers : SourceLocations.BasisSourceCovers
  parent) (count : Nat) (target : Coordinate) : Coordinate :=
  min 1 (PairedFragmentBlocks.fragmentLocalTolerance count (2 * (1 +
    (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers))) target)

/-- Compute the finite row maxima of squared cell diameters for the original occurrence geometry. -/
@[expose] def cellDiagonalRows (occurrence :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) : List Coordinate :=
  List.ofFn (fun column => PairedFragmentBlocks.maximum id (List.ofFn (fun
    height =>
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq)))

set_option genInjectivity false in
/-- A retained local block budget and cell-query schedule paying a complete fragment-path target.

Cached cell-diameter maxima, the original source covers and the supplied fragment capacity determine all query
tolerances. -/
structure BlockRequest (occurrence :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (covers : SourceLocations.BasisSourceCovers parent) (count : Nat) (target
      : Coordinate) where
  /-- The complete fragment-path comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached original row maxima of squared cell diameters. -/ diagonalRows : List
    Coordinate
  /-- The cached rows are exactly those computed from the original occurrence geometry. -/ rows_eq : diagonalRows =
    RequestedBlocks.cellDiagonalRows occurrence
  /-- The cached complete squared-diameter maximum. -/ diagonal : Coordinate
  /-- The cached maximum is exactly the finite maximum of the retained row values. -/ diagonal_eq : diagonal =
    PairedFragmentBlocks.maximum id diagonalRows
  /-- The local area and endpoint budget for the original source density and supplied fragment capacity. -/ budget :
    PairedFragmentBlocks.FragmentAreaBudget
    (RequestedBlocks.blockDensity covers)
    (RequestedBlocks.blockLocalTarget covers count target)
  /-- The retained common cell-query allowance. -/ queryTarget : Coordinate
  /-- The retained query allowance is exactly the diameter-weighted allocation capped by one. -/ query_eq : queryTarget
    = min 1 (Rational.Budget.Weighted.allowance budget.tolerance diagonal)
  /-- The retained common query allowance is strictly positive. -/ query_positive : 0 < queryTarget
  /-- The original occurrence's cell-query schedule at that retained allowance. -/ queries :
    QuerySchedule occurrence queryTarget

constructive_injectivity BlockRequest

/-- Compute and retain the complete block budget, geometry maxima and original cell-query schedule. -/
@[expose] def BlockRequest.build (occurrence :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (covers : SourceLocations.BasisSourceCovers parent) (count : Nat) (target
      : Coordinate)
    (positive : 0 < target) : BlockRequest occurrence
      covers count target := open Data in by
  let rows := RequestedBlocks.cellDiagonalRows occurrence
  let diagonal := PairedFragmentBlocks.maximum id rows
  have slopeNN :=
    (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
    covers)
  have densityNN : 0 ≤ RequestedBlocks.blockDensity covers :=
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg _) slopeNN)
  have localPositive : 0 < RequestedBlocks.blockLocalTarget covers
    count target :=
    Basic.lt_min (by decide)
      (PairedFragmentBlocks.fragmentLocalTolerance_positive count
      (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide) slopeNN)) positive)
  let budget := PairedFragmentBlocks.FragmentAreaBudget.build
    (RequestedBlocks.blockDensity covers) _ densityNN localPositive
  let queryTarget := min 1 (Rational.Budget.Weighted.allowance budget.tolerance diagonal)
  have queryPositive : 0 < queryTarget := Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive budget.tolerance_positive
      (PairedFragmentBlocks.maximum_nonnegative ..))
  exact ⟨positive, rows, rfl, diagonal, rfl, budget, queryTarget, rfl, queryPositive,
    QuerySchedule.build occurrence queryTarget⟩

namespace BlockRequest
variable {count : Nat} {target : Coordinate} (selected :
  BlockRequest occurrence covers count
  target)

/-- Every original cell's squared diameter is bounded by the cached complete maximum. -/
theorem diagonal_bound (column height : Fin (occurrence.compared.entered.domain.steps + 1)) :
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq ≤ selected.diagonal := by
  have row := PairedFragmentBlocks.le_maximum (value := id)
    (List.OfFn.Basic.mem_ofFn.mpr ⟨height, rfl⟩ :
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq ∈
      List.ofFn (fun height => (occurrence.compared.entered.domain.geometry.box column height).diagonalSq))
  have columnBound := PairedFragmentBlocks.le_maximum (value := id)
    (List.OfFn.Basic.mem_ofFn.mpr ⟨column, rfl⟩ :
    PairedFragmentBlocks.maximum id (List.ofFn (fun height =>
      (occurrence.compared.entered.domain.geometry.box column height).diagonalSq)) ∈
      RequestedBlocks.cellDiagonalRows occurrence)
  exact (row.trans columnBound).trans_eq
    ((congrArg (PairedFragmentBlocks.maximum id)
      selected.rows_eq.symm).trans selected.diagonal_eq.symm)

/-- The paid original cell-query schedule bounds both fragment density and diameter-weighted query error. -/
theorem fragment_bounds
    (fragment : OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
    (sourcePaid : selected.queries.sourceMinimum ≤ index) (facePaid : selected.queries.faceIndex ≤ faceIndex) :
    FragmentArea.traceDensity acquired fragment.piece faceIndex ≤
      RequestedBlocks.blockDensity covers ∧
    FragmentArea.queryScale acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq ≤
        selected.budget.tolerance := open Data in by
  have query := selected.queries.accurate acquired fragment.piece selected.query_positive sourcePaid facePaid
  have unit : FragmentArea.queryScale acquired fragment.piece
    faceIndex ≤ 1 :=
    query.trans (selected.query_eq.trans_le (Basic.min_le_left ..))
  have small := query.trans (selected.query_eq.trans_le (Basic.min_le_right ..))
  constructor
  · have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (Arithmetic.mul_le_mul_of_nonneg_right_direct unit
        (Gaussian.Norm.Basic.normSq_nonneg (parent.edge.point 1 - parent.edge.point 0))) (le_refl
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)))
      (by decide : (0 : Coordinate) ≤ 2)
    simpa only [-eq_self, -iff_self, FragmentArea.traceDensity,
      RequestedBlocks.blockDensity,
      Integration.PreparedConstantModels.PreparedEdge.pointMovement,
      Fraction.Field.one_mul] using bound
  · have diameterNN := (occurrence.compared.entered.domain.geometry.box fragment.piece.column
      fragment.piece.row).diagonalSq_nonneg
    have diagonalNN := diameterNN.trans (selected.diagonal_bound fragment.piece.column fragment.piece.row)
    have allowanceNN := (Rational.Budget.Weighted.allowance_positive selected.budget.tolerance_positive diagonalNN).le
    exact ((Arithmetic.mul_le_mul_of_nonneg_right_direct small diameterNN).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (selected.diagonal_bound fragment.piece.column
        fragment.piece.row) allowanceNN)).trans
      ((Fraction.Field.mul_comm ..).trans_le (Rational.Budget.Weighted.mul_allowance_le
        selected.budget.tolerance_positive.le diagonalNN))

/-- The retained block request pays the complete original fragment-path error at the shared paid source and face stages.

The supplied fragment count, padding and owner tolerances must meet the retained finite capacity and local budget. -/
theorem accurate (fragments : List (OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data))
    (countLe : fragments.length ≤ count)
    (sourcePaid : selected.queries.sourceMinimum ≤ index) (facePaid : selected.queries.faceIndex ≤ faceIndex)
    (allowances : ∀ fragment ∈ fragments, fragment.allowance ≤ 1)
    (owners : ∀ fragment ∈ fragments, fragment.budget.tolerance ≤ selected.budget.tolerance) :
    FragmentBlocks.fragmentBlockError (acquired := acquired) fragments
      < target := by
  exact BlockBudget.fragmentBlockError_lt_of_budget fragments countLe
    selected.positive selected.budget allowances
    (fun fragment _ => (selected.fragment_bounds fragment sourcePaid facePaid).1) owners
    (fun fragment _ => (selected.fragment_bounds fragment sourcePaid facePaid).2)

end BlockRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
