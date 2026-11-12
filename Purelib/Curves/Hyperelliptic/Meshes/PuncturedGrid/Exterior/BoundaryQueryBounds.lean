module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-! The pre-owner query requests pay the actual closed bank's source
primitives, not independently prepared reciprocal samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.ClosedBoundaryComparison

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Integration
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open
  Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
  (Piece traceError traceDensity queryDensity queryDensity_nonnegative sourceDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds (CellQuery PreOwnerQueries
  preOwnerCellQuery preOwnerQueryRows cellSourceWeight rowSourceWeight cellFaceWeight rowFaceWeight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (sourceQueryMinimum
  source_radius_lt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget maximum
  maximum_nonnegative le_maximum)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Coordinate} {minimum : Nat}

/-- The original closed-bank primitive pair satisfies one retained cell query's trace-error target at paid source and
face stages. -/
private theorem cell_trace_error (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (occurrence : SurfaceOccurrence regular domains differential) (i : Fin
      comparison.original.plans.length)
    (piece : Piece comparison occurrence i) {target : Coordinate}
    (query : CellQuery occurrence other piece.column piece.row target) (positive : 0 < target)
    (sourcePaid : query.sourceMinimum ≤ minimum) {index : Nat} (facePaid : query.faceIndex ≤ index) :
    ClosedBoundaryComparison.traceError comparison occurrence i piece index ≤ target := by
  let leftSource := (comparison.entries.get i).first
  let rightSource := (comparison.entries.get i).second
  let queryBound := FamilyBounds.preOwnerCellQuery occurrence other piece.column piece.row
  have queryNonnegative : 0 ≤ queryBound :=
    ((FragmentQueries.queryDensity_nonnegative occurrence.compared.entered.bounds
      piece.column piece.row leftSource.localRequest 0).trans
      (FragmentQueries.queryDensity_uniform_le occurrence.compared.entered.bounds
        piece.column piece.row leftSource.localRequest 0)).trans
        (Basic.le_max_left _ _)
  let diagonal := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq
  have diagonalNonnegative : 0 ≤ diagonal :=
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg
  have weightNonnegative := Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
    decide +kernel : (0 : Coordinate) ≤ 32)
    queryNonnegative) diagonalNonnegative
  have radiusPositive : 0 < query.radius := query.radius_eq.trans_gt
    (Weighted.allowance_positive positive weightNonnegative)
  let left := FragmentQueries.queryTail occurrence.compared.entered.bounds
    piece.column piece.row leftSource.localRequest query.radius radiusPositive
  let right := FragmentQueries.queryTail
    (occurrence.recastComparison other).entered.bounds
    piece.column piece.row rightSource.localRequest query.radius radiusPositive
  have sourceMinimum : PairedFragmentValues.sourceQueryMinimum query.radius ≤ minimum := query.source_eq.symm.trans_le
    sourcePaid
  have leftSmall := PairedFragmentValues.source_radius_lt leftSource.localRequest.neighborhood.base.model.bound_small
    radiusPositive
    (sourceMinimum.trans leftSource.index_ge)
  have rightSmall := PairedFragmentValues.source_radius_lt rightSource.localRequest.neighborhood.base.model.bound_small
    radiusPositive
    (sourceMinimum.trans rightSource.index_ge)
  have leftLater : left.index ≤ index := (Data.Nat.Order.le_max_left _ _).trans (query.face_eq.symm.trans_le facePaid)
  have rightLater : right.index ≤ index := (Data.Nat.Order.le_max_right _ _).trans (query.face_eq.symm.trans_le
    facePaid)
  have leftBound := (left.accurate index leftLater).trans
    (left.ceiling_le_uniform radiusPositive.le (left.source_eq.trans_lt leftSmall).le)
  have rightBound := (right.accurate index rightLater).trans
    (right.ceiling_le_uniform radiusPositive.le (right.source_eq.trans_lt rightSmall).le)
  have factor : 0 ≤ 32 * query.radius := Arithmetic.mul_nonneg_direct (by decide +kernel)
    radiusPositive.le
  have paired : ClosedBoundaryComparison.queryDensity comparison occurrence i piece index ≤ 32 * query.radius *
    queryBound :=
    Basic.max_le (leftBound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Basic.le_max_left _ _) factor))
      (rightBound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct (Basic.le_max_right _
        _) factor))
  have paid := Weighted.mul_allowance_le positive.le weightNonnegative
  have radiusEq : query.radius = Weighted.allowance target (32 * queryBound * diagonal) := query.radius_eq
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct paired diagonalNonnegative
  apply scaled.trans
  calc
    32 * query.radius * queryBound * diagonal = (32 * queryBound * diagonal) * query.radius := by ring1
    _ ≤ target := (congrArg (fun radius => (32 * queryBound * diagonal) * radius) radiusEq).trans_le paid

/-- Both the source floor and later face index are taken from the retained pre-owner requests. The source primitives are
those of `comparison` itself. -/
theorem requested_trace_error (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (occurrence : SurfaceOccurrence regular domains differential) (i : Fin
      comparison.original.plans.length)
    (piece : Piece comparison occurrence i) {target : Coordinate}
    (queries : PreOwnerQueries occurrence other target) (positive : 0 < target)
    (sourcePaid : queries.sourceMinimum ≤ minimum) {index : Nat} (facePaid : queries.faceIndex ≤ index) :
    ClosedBoundaryComparison.traceError comparison occurrence i piece index ≤ target := by
  have sourceLe := (DependentVector.get_le_maximum FamilyBounds.cellSourceWeight (queries.rows.get piece.column)
    piece.row).trans
    ((DependentVector.get_le_maximum FamilyBounds.rowSourceWeight queries.rows piece.column).trans
      (queries.source_eq.symm.trans_le sourcePaid))
  have faceLe := (DependentVector.get_le_maximum FamilyBounds.cellFaceWeight (queries.rows.get piece.column)
    piece.row).trans
    ((DependentVector.get_le_maximum FamilyBounds.rowFaceWeight queries.rows piece.column).trans
      (queries.face_eq.symm.trans_le facePaid))
  exact ClosedBoundaryComparison.cell_trace_error
    comparison occurrence i piece ((queries.rows.get piece.column).get piece.row) positive sourceLe faceLe

/-- The retained fragment area budget pays the original owned-area error when density, trace error, owner tolerance and
unit length bounds hold. -/
theorem ownedAreaError_paid (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (occurrence : SurfaceOccurrence regular domains differential) (i : Fin
      comparison.original.plans.length)
    (piece : Piece comparison occurrence i) (index : Nat) {density target length allowance
      tolerance : Coordinate}
    (budget : FragmentAreaBudget density target)
    (densityBound : comparison.traceDensity occurrence i piece index ≤ density)
    (traceBound : comparison.traceError occurrence i piece index ≤ budget.tolerance)
    (ownerNonnegative : 0 ≤ tolerance) (ownerBound : tolerance ≤ budget.tolerance)
    (lengthBound : 0 ≤ length ∧ length ≤ 1) (allowanceBound : 0 ≤ allowance ∧ allowance ≤ 1) :
    comparison.ownedAreaError occurrence i piece index length allowance tolerance ≤ target := by
  let d := comparison.traceDensity occurrence i piece index
  let e := comparison.traceError occurrence i piece index
  have dNonnegative : 0 ≤ d := Arithmetic.mul_nonneg_direct (by
      decide : (0 : Coordinate) ≤ 2)
    (add_nonneg (Arithmetic.mul_nonneg_direct (comparison.queryDensity_nonnegative occurrence i piece
      index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)) (comparison.sourceDensity_nonnegative i))
  have eNonnegative : 0 ≤ e := Arithmetic.mul_nonneg_direct
    (comparison.queryDensity_nonnegative occurrence i piece index)
    (occurrence.compared.entered.domain.geometry.box piece.column piece.row).diagonalSq_nonneg
  have square : length^2 ≤ 1 := (Arithmetic.pow_le_pow_direct lengthBound.1 lengthBound.2 2).trans_eq (by
    ring1)
  have sumLe : length + allowance ≤ 2 := (Arithmetic.add_le_add_direct lengthBound.2
    allowanceBound.2).trans_eq (by ring1)
  have sumSquare : (length + allowance)^2 ≤ 4 :=
    (Arithmetic.pow_le_pow_direct (add_nonneg lengthBound.1 allowanceBound.1) sumLe 2).trans_eq (by
      ring1)
  have firstNonnegative : 0 ≤ 40 * tolerance * (4 * d + 3) :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Coordinate) ≤ 40) ownerNonnegative)
      (add_nonneg (Arithmetic.mul_nonneg_direct (by decide) dNonnegative) (by decide))
  have secondNonnegative : 0 ≤ 40 * e * d :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Coordinate) ≤ 40) eNonnegative) dNonnegative
  have first := Arithmetic.mul_le_mul_of_nonneg_left_direct sumSquare firstNonnegative
  have second := Arithmetic.mul_le_mul_of_nonneg_left_direct square secondNonnegative
  have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct first second) (by decide : (0 : Coordinate) ≤ 2)
  have paid := budget.bound dNonnegative ownerBound densityBound traceBound
  apply bounded.trans
  exact (show 2 * (40 * tolerance * (4 * d + 3) * 4 + 40 * e * d * 1) =
    320 * tolerance * (4 * d + 3) + 80 * e * d by ring1).trans_le paid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.ClosedBoundaryComparison

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.SurfacePreparation

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Integration
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open
  Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
  (Piece traceError traceDensity queryDensity queryDensity_nonnegative sourceDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds (CellQuery PreOwnerQueries
  preOwnerCellQuery preOwnerQueryRows cellSourceWeight rowSourceWeight cellFaceWeight rowFaceWeight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (sourceQueryMinimum
  source_radius_lt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget maximum
  maximum_nonnegative le_maximum)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program}

set_option genInjectivity false in
/-- Cache the covers and uniform coefficients before choosing source indices. The subsequent closed bank consumes these
very covers. -/
structure SourceGeometry (prepared : ExteriorProgram.SurfacePreparation regular domains program) (other :
  Differential genus) where
  /-- The retained source covers for the second differential on the original recast parent list. -/ right :
    ParentCovers
    (program.cache.parents.map (PreparedEdgeRecasting.recastCenteredEdge other))
  /-- The cached common source slope of the original two cover banks. -/ slope : Coordinate
  /-- The source slope is exactly the maximum of the original two bank bounds. -/ slope_eq : slope = max
    (PairedParentRequest.sourceMaximum prepared.sourceCovers)
    (PairedParentRequest.sourceMaximum right)
  /-- The cached query-density maximum for each original surface occurrence. -/ queryRows : List
    Coordinate
  /-- The query rows are exactly the maxima over the retained occurrence cell queries. -/ queryRows_eq : queryRows =
    prepared.occurrences.map (fun occurrence => PairedFragmentBlocks.maximum id (FamilyBounds.preOwnerQueryRows
    occurrence other))
  /-- The cached common query-density maximum over all original occurrences. -/ query : Coordinate
  /-- The common query density is exactly the maximum of the retained row cache. -/ query_eq : query =
    PairedFragmentBlocks.maximum id queryRows
  /-- The cached maximum movement of the original program parents. -/ movement : Coordinate
  /-- The movement cache equals the maximum on the exact original parent list. -/ movement_eq : movement =
    PairedFragmentBlocks.maximum (fun parent => parent.edge.pointMovement) program.cache.parents
  /-- The cached uniform density combining retained query, movement and source slope. -/ density :
    Coordinate
  /-- The density cache equals twice the retained query-movement product plus source slope. -/ density_eq : density = 2
    * (query * movement + slope)
  /-- The cached uniform trace density is nonnegative. -/ density_nonnegative : 0 ≤ density

constructive_injectivity SourceGeometry

/-- Cache the original second source covers, paired source slope and uniform query and movement bounds before selecting
sample stages. -/
@[expose] def SourceGeometry.build (prepared : ExteriorProgram.SurfacePreparation regular domains program) (other :
  Differential genus) :
    SourceGeometry prepared
      other := by
  let right := prepared.otherSourceCovers other
  let slope := max (PairedParentRequest.sourceMaximum prepared.sourceCovers)
    (PairedParentRequest.sourceMaximum right)
  let rows := prepared.occurrences.map (fun occurrence => PairedFragmentBlocks.maximum id
    (FamilyBounds.preOwnerQueryRows occurrence other))
  let query := PairedFragmentBlocks.maximum id rows
  let movement := PairedFragmentBlocks.maximum (fun parent => parent.edge.pointMovement) program.cache.parents
  have slopeNonnegative : 0 ≤ slope :=
    (PairedParentRequest.sourceMaximum_nonnegative prepared.sourceCovers).trans (Basic.le_max_left _ _)
  exact ⟨right, slope, rfl, rows, rfl, query, rfl, movement, rfl, 2 * (query * movement + slope), rfl,
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Arithmetic.mul_nonneg_direct (PairedFragmentBlocks.maximum_nonnegative _ _)
        (PairedFragmentBlocks.maximum_nonnegative _ _)) slopeNonnegative)⟩

/-- The cached uniform trace density bounds the original common source slope. -/
theorem SourceGeometry.slope_le_density (geometry :
  SourceGeometry prepared
  other) : geometry.slope ≤ geometry.density := by
  have queryNonnegative : 0 ≤ geometry.query := by
    rw [geometry.query_eq]
    exact PairedFragmentBlocks.maximum_nonnegative _ _
  have movementNonnegative : 0 ≤ geometry.movement := by
    rw [geometry.movement_eq]
    exact PairedFragmentBlocks.maximum_nonnegative _ _
  have slopeNonnegative : 0 ≤ geometry.slope := by
    rw [geometry.slope_eq]
    exact (PairedParentRequest.sourceMaximum_nonnegative prepared.sourceCovers).trans (Basic.le_max_left
      _ _)
  have extra := Arithmetic.mul_nonneg_direct queryNonnegative movementNonnegative
  exact (le_add_of_nonneg_left extra).trans
    ((le_add_of_nonneg_right (add_nonneg extra slopeNonnegative)).trans_eq (by rw [geometry.density_eq]; ring1))

/-- The cached source geometry bounds every original closed-bank fragment trace density when the bank retains its exact
slope. -/
theorem SourceGeometry.density_bound (geometry :
  SourceGeometry prepared
  other)
    {requested : Coordinate} {minimum : Nat} (comparison : prepared.ClosedBoundaryComparison other
      requested minimum)
    (slope : comparison.original.slope = geometry.slope)
    (occurrence : SurfaceOccurrence regular domains differential) (member : occurrence ∈
      prepared.occurrences)
    (i : Fin comparison.original.plans.length) (piece : Piece comparison occurrence i) (index :
      Nat) :
    comparison.traceDensity occurrence i piece index ≤ geometry.density := by
  have row := PairedFragmentBlocks.le_maximum (value := id) (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨piece.row, rfl⟩ :
    FamilyBounds.preOwnerCellQuery occurrence other piece.column piece.row ∈ List.ofFn (FamilyBounds.preOwnerCellQuery
      occurrence other piece.column))
  have column := PairedFragmentBlocks.le_maximum (value := id) (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨piece.column, rfl⟩ :
    PairedFragmentBlocks.maximum id (List.ofFn (FamilyBounds.preOwnerCellQuery occurrence other piece.column)) ∈
      FamilyBounds.preOwnerQueryRows occurrence other)
  have occurrenceLe := PairedFragmentBlocks.le_maximum (value := id)
    (Map.mem_map_of_mem (f := fun occurrence => PairedFragmentBlocks.maximum id (FamilyBounds.preOwnerQueryRows
      occurrence other)) member)
  have queryLe : FamilyBounds.preOwnerCellQuery occurrence other piece.column piece.row ≤ geometry.query :=
    ((row.trans column).trans occurrenceLe).trans_eq
      ((congrArg (PairedFragmentBlocks.maximum id) geometry.queryRows_eq.symm).trans geometry.query_eq.symm)
  have uniform : comparison.queryDensity occurrence i piece index ≤ FamilyBounds.preOwnerCellQuery occurrence other
    piece.column piece.row :=
    Basic.max_le
      ((FragmentQueries.queryDensity_uniform_le occurrence.compared.entered.bounds
        piece.column piece.row (comparison.entries.get i).first.localRequest index).trans
          (Basic.le_max_left _ _))
      ((FragmentQueries.queryDensity_uniform_le
        (occurrence.recastComparison other).entered.bounds piece.column piece.row
        (comparison.entries.get i).second.localRequest index).trans (Basic.le_max_right _ _))
  have queryBound := uniform.trans queryLe
  have parentMember := Map.mem_map_of_mem
    (f := Plan.parent)
    (List.getElem_mem i.isLt : PairedParentCharts.ChartParent comparison.original i ∈ comparison.original.plans)
  have parentPresent := Eq.mp (congrArg (fun parents => comparison.Parent i ∈ parents)
    comparison.original.parents_eq) parentMember
  have movementBound : (comparison.Parent i).edge.pointMovement ≤ geometry.movement :=
    (PairedFragmentBlocks.le_maximum (value := fun parent => parent.edge.pointMovement) parentPresent).trans_eq
      geometry.movement_eq.symm
  have source := comparison.original.plan_bounds
    (PairedParentCharts.ChartParent comparison.original i) (List.getElem_mem i.isLt)
  have sourceBound : comparison.sourceDensity i ≤ geometry.slope := (Basic.max_le source.1
    source.2).trans_eq slope
  have weighted := (Arithmetic.mul_le_mul_of_nonneg_right_direct queryBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct movementBound
      ((comparison.queryDensity_nonnegative occurrence i piece index).trans queryBound))
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
    weighted sourceBound) (by decide : (0 : Coordinate) ≤ 2)).trans_eq
    geometry.density_eq.symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.SurfacePreparation
