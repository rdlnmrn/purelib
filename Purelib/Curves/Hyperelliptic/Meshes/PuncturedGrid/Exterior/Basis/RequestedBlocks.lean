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

/-- Compute the common block trace-density bound from original parent movement and primitive slope. -/
@[expose] def blockDensity (covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  parent) : Coordinate :=
  2 * (parent.edge.pointMovement +
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers))

/-- Choose a local fragment error cap paying the full count-dependent comparison and bounded by one. -/
@[expose] def blockLocalTarget (covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  parent) (count : Nat) (target : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  min 1 (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance count (2 * (1 +
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers))) target)

/-- Compute the finite row maxima of squared cell diameters for the original occurrence geometry. -/
@[expose] def cellDiagonalRows (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) : List Coordinate :=
  List.ofFn (fun column => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id (List.ofFn (fun
    height =>
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq)))

set_option genInjectivity false in
/-- A retained local block budget and cell-query schedule paying a complete fragment-path target.

Cached cell-diameter maxima, the original source covers and the supplied fragment capacity determine all query
tolerances. -/
structure BlockRequest (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent) (count : Nat) (target
      : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The complete fragment-path comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached original row maxima of squared cell diameters. -/ diagonalRows : List
    Normalization.InverseRootPolynomial.Coordinate
  /-- The cached rows are exactly those computed from the original occurrence geometry. -/ rows_eq : diagonalRows =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.cellDiagonalRows occurrence
  /-- The cached complete squared-diameter maximum. -/ diagonal : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached maximum is exactly the finite maximum of the retained row values. -/ diagonal_eq : diagonal =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id diagonalRows
  /-- The local area and endpoint budget for the original source density and supplied fragment capacity. -/ budget :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockDensity covers)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockLocalTarget covers count target)
  /-- The retained common cell-query allowance. -/ queryTarget : Normalization.InverseRootPolynomial.Coordinate
  /-- The retained query allowance is exactly the diameter-weighted allocation capped by one. -/ query_eq : queryTarget
    = min 1 (Rational.Budget.Weighted.allowance budget.tolerance diagonal)
  /-- The retained common query allowance is strictly positive. -/ query_positive : 0 < queryTarget
  /-- The original occurrence's cell-query schedule at that retained allowance. -/ queries :
    QuerySchedule occurrence queryTarget

constructive_injectivity BlockRequest

/-- Compute and retain the complete block budget, geometry maxima and original cell-query schedule. -/
@[expose] def BlockRequest.build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent) (count : Nat) (target
      : Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < target) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest occurrence
      covers count target := open Purelib.Data in by
  let rows := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.cellDiagonalRows occurrence
  let diagonal := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id rows
  have slopeNN :=
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
    covers)
  have densityNN : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockDensity covers :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg _) slopeNN)
  have localPositive : 0 < Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockLocalTarget covers
    count target :=
    Fraction.Order.Basic.lt_min (by decide)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance_positive count
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide) slopeNN)) positive)
  let budget := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget.build
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockDensity covers) _ densityNN localPositive
  let queryTarget := min 1 (Rational.Budget.Weighted.allowance budget.tolerance diagonal)
  have queryPositive : 0 < queryTarget := Fraction.Order.Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive budget.tolerance_positive
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative ..))
  exact ⟨positive, rows, rfl, diagonal, rfl, budget, queryTarget, rfl, queryPositive,
    QuerySchedule.build occurrence queryTarget⟩

namespace BlockRequest
variable {count : Nat} {target : Normalization.InverseRootPolynomial.Coordinate} (selected :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest occurrence covers count
  target)

/-- Every original cell's squared diameter is bounded by the cached complete maximum. -/
theorem diagonal_bound (column height : Fin (occurrence.compared.entered.domain.steps + 1)) :
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq ≤ selected.diagonal := by
  have row := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum (value := id)
    (List.OfFn.Basic.mem_ofFn.mpr ⟨height, rfl⟩ :
    (occurrence.compared.entered.domain.geometry.box column height).diagonalSq ∈
      List.ofFn (fun height => (occurrence.compared.entered.domain.geometry.box column height).diagonalSq))
  have columnBound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum (value := id)
    (List.OfFn.Basic.mem_ofFn.mpr ⟨column, rfl⟩ :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id (List.ofFn (fun height =>
      (occurrence.compared.entered.domain.geometry.box column height).diagonalSq)) ∈
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.cellDiagonalRows occurrence)
  exact (row.trans columnBound).trans_eq
    ((congrArg (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id)
      selected.rows_eq.symm).trans selected.diagonal_eq.symm)

/-- The paid original cell-query schedule bounds both fragment density and diameter-weighted query error. -/
theorem fragment_bounds
    (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
    (sourcePaid : selected.queries.sourceMinimum ≤ index) (facePaid : selected.queries.faceIndex ≤ faceIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece faceIndex ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockDensity covers ∧
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq ≤
        selected.budget.tolerance := open Purelib.Data in by
  have query := selected.queries.accurate acquired fragment.piece selected.query_positive sourcePaid facePaid
  have unit : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece
    faceIndex ≤ 1 :=
    query.trans (selected.query_eq.trans_le (Fraction.Order.Basic.min_le_left ..))
  have small := query.trans (selected.query_eq.trans_le (Fraction.Order.Basic.min_le_right ..))
  constructor
  · have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct unit
        (Gaussian.Norm.Basic.normSq_nonneg (parent.edge.point 1 - parent.edge.point 0))) (le_refl
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)))
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    simpa only [-eq_self, -iff_self, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.blockDensity,
      Integration.PreparedConstantModels.PreparedEdge.pointMovement,
      Fraction.Field.one_mul] using bound
  · have diameterNN := (occurrence.compared.entered.domain.geometry.box fragment.piece.column
      fragment.piece.row).diagonalSq_nonneg
    have diagonalNN := diameterNN.trans (selected.diagonal_bound fragment.piece.column fragment.piece.row)
    have allowanceNN := (Rational.Budget.Weighted.allowance_positive selected.budget.tolerance_positive diagonalNN).le
    exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small diameterNN).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (selected.diagonal_bound fragment.piece.column
        fragment.piece.row) allowanceNN)).trans
      ((Fraction.Field.mul_comm ..).trans_le (Rational.Budget.Weighted.mul_allowance_le
        selected.budget.tolerance_positive.le diagonalNN))

/-- The retained block request pays the complete original fragment-path error at the shared paid source and face stages.

The supplied fragment count, padding and owner tolerances must meet the retained finite capacity and local budget. -/
theorem accurate (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data))
    (countLe : fragments.length ≤ count)
    (sourcePaid : selected.queries.sourceMinimum ≤ index) (facePaid : selected.queries.faceIndex ≤ faceIndex)
    (allowances : ∀ fragment ∈ fragments, fragment.allowance ≤ 1)
    (owners : ∀ fragment ∈ fragments, fragment.budget.tolerance ≤ selected.budget.tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired := acquired) fragments
      < target := by
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget.fragmentBlockError_lt_of_budget fragments countLe
    selected.positive selected.budget allowances
    (fun fragment _ => (selected.fragment_bounds fragment sourcePaid facePaid).1) owners
    (fun fragment _ => (selected.fragment_bounds fragment sourcePaid facePaid).2)

end BlockRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
