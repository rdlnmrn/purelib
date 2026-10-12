module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
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
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib
open Purelib.Riemann

/-! Pay local common-source area and endpoint errors with finite budgets. -/
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

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

section OwnedFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment

/-- A retained parameter in the original fragment interval lies in its actual containing cell. -/
private theorem FragmentBudget.OwnedFragment.contains (fragment : OwnedFragments.OwnedFragment
  (originals := originals) (coefficients := coefficients) data)
    (parameter : Normalization.InverseRootPolynomial.Coordinate) (inside : fragment.piece.interval.lower ≤ parameter ∧
      parameter ≤ fragment.piece.interval.upper) :
    (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).Contains
      (parent.edge.point parameter) :=
  (congrArg (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).Contains
    (Integration.PreparedParentSplitting.prepared_point_eq parent parameter)).mpr (fragment.piece.contains_query
      parameter inside)

/-- Compute the original sampled parameter displacement in its retained traversal orientation. -/
@[expose] def OwnedFragments.OwnedFragment.width
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward (fragment.parameters 0)
    (fragment.parameters (Fin.last fragment.vertices))

/-- The original ordered parameter sample has nonnegative oriented width. -/
theorem
  OwnedFragments.OwnedFragment.width_nonnegative
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) : 0 ≤ fragment.width := open Purelib.Algebra in by
  have sumNonnegative {n : Nat} (values : Fin n → Normalization.InverseRootPolynomial.Coordinate) (nonnegative : ∀ i, 0
    ≤ values i) :
      0 ≤ FiniteSum.Fin.sumFin values := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact add_nonneg (nonnegative 0) (ih _ (fun i => nonnegative i.succ))
  have bound := sumNonnegative
    (fun edge : Fin fragment.vertices => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep
      fragment.forward (fragment.parameters edge.castSucc) (fragment.parameters edge.succ))
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative
      fragment.forward _ _ (fragment.ordered edge))
  exact bound.trans_eq (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total
    fragment.forward fragment.parameters)

/-- The original unit-interval parameter sample has oriented width at most one. -/
theorem
  OwnedFragments.OwnedFragment.width_le_one
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) : fragment.width ≤ 1 := by
  have unit (vertex : Fin (fragment.vertices + 1)) : 0 ≤ fragment.parameters vertex ∧ fragment.parameters vertex ≤ 1 :=
    ⟨fragment.piece.within.1.trans (fragment.inside vertex).1, (fragment.inside vertex).2.trans fragment.piece.within.2⟩
  cases direction : fragment.forward with
  | true =>
    have bound := Fraction.Order.Arithmetic.sub_le_sub_direct (unit (Fin.last fragment.vertices)).2 (unit 0).1
    rw [show (1 : Fraction.Rational) - 0 = 1 by ring1] at bound
    simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.width,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep, direction, if_pos (Eq.refl true),
      -eq_self, -iff_self] using bound
  | false =>
    have bound := Fraction.Order.Arithmetic.sub_le_sub_direct (unit 0).2 (unit (Fin.last fragment.vertices)).1
    rw [show (1 : Fraction.Rational) - 0 = 1 by ring1] at bound
    simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.width,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep, direction, if_neg (by
          decide : ¬ false = true), if_pos (Eq.refl true), -eq_self, -iff_self] using bound

/-- The retained common-source fragment trace density is nonnegative. -/
theorem
  OwnedFragments.OwnedFragment.density_nonnegative
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece faceIndex :=
  open Purelib.Data in Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale_nonnegative acquired fragment.piece
      faceIndex) (Gaussian.Norm.Basic.normSq_nonneg _))
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers))

/-- Bound the scalar area rate using the unit width and padded-width estimates.

The owner tolerance, source discrepancy and trace density must all be nonnegative. -/
private theorem FragmentBudget.OwnedFragment.area_rate_scalar {t d e w a :
  Normalization.InverseRootPolynomial.Coordinate}
    (ht : 0 ≤ t) (hd : 0 ≤ d) (he : 0 ≤ e) (hw : w ^ 2 ≤ 1) (ha : (w + a) ^ 2 ≤ 4) :
    2 * (40 * t * (4 * d + 3) * (w + a) ^ 2 + 40 * e * d * w ^ 2) ≤
      320 * t * (4 * d + 3) + 80 * e * d := by
  have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ha
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 40) ht)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) hd) (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 3)))
  have second := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct hw
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 40) he) hd)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
    second) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1)

/-- Eliminate the sampled parameter width from the error rate using its
retained unit-interval containment, in either source orientation. -/
theorem
  OwnedFragments.OwnedFragment.areaError_rate
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) (allowanceLe : fragment.allowance ≤ 1) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError (acquired := acquired)
      fragment) ≤ 320 * fragment.budget.tolerance * (4 *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece faceIndex + 3)
      +
      80 * (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece faceIndex
        * (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq) *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece faceIndex :=
        by
  have densityNonnegative :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.density_nonnegative (acquired :=
    acquired) fragment)
  have errorNonnegative : 0 ≤ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired
    fragment.piece faceIndex * (occurrence.compared.entered.domain.geometry.box fragment.piece.column
    fragment.piece.row).diagonalSq) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale_nonnegative acquired fragment.piece
      faceIndex) (occurrence.compared.entered.domain.geometry.box fragment.piece.column
      fragment.piece.row).diagonalSq_nonneg
  have allowanceNonnegative : 0 ≤ fragment.allowance :=
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le fragment.vertices))
      fragment.budget.padding_positive.le).trans fragment.budget.paid
  have widthSquare : fragment.width ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct fragment.width_nonnegative fragment.width_le_one 2).trans_eq (by
      decide)
  have paddedSquare : (fragment.width + fragment.allowance) ^ 2 ≤ 4 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (add_nonneg fragment.width_nonnegative allowanceNonnegative)
      (Fraction.Order.Arithmetic.add_le_add_direct fragment.width_le_one allowanceLe) 2).trans_eq (by decide)
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBudget.OwnedFragment.area_rate_scalar
    fragment.budget.tolerance_positive.le densityNonnegative errorNonnegative widthSquare paddedSquare

/-- The retained finite area budget pays the actual fragment area error under its density, owner and cell-query bounds.
-/
theorem
  OwnedFragments.OwnedFragment.areaError_paid
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) {density target : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
      (allowanceLe : fragment.allowance ≤ 1)
    (densityLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece
      faceIndex ≤ density)
    (ownerLe : fragment.budget.tolerance ≤ budget.tolerance)
    (errorLe : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece
      faceIndex * (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq)
      ≤ budget.tolerance) : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError
      (acquired := acquired) fragment) ≤ target :=
  ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError_rate (acquired := acquired)
    fragment) allowanceLe).trans (budget.bound
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.density_nonnegative (acquired :=
    acquired) fragment) ownerLe densityLe errorLe)

/-- Bound the original endpoint-total discrepancy by owner tolerance and the actual containing cell's squared diameter.
-/
theorem
  OwnedFragments.OwnedFragment.totalError_rate
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
      fragment) ≤ 2 * (fragment.budget.tolerance +
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq)) := by
  have displacement := Rational.Box.normSq_sub_le_diagonalSq
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBudget.OwnedFragment.contains fragment _ (fragment.inside
      (Fin.last fragment.vertices)))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBudget.OwnedFragment.contains fragment _ (fragment.inside
      0))
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      displacement (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale_nonnegative acquired
      fragment.piece faceIndex))) (by decide)

/-- The retained finite area budget also pays the original endpoint-total discrepancy. -/
theorem
  OwnedFragments.OwnedFragment.totalError_paid
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) {density target : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
      (ownerLe : fragment.budget.tolerance ≤ budget.tolerance)
    (errorLe : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece
      faceIndex * (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq)
      ≤ budget.tolerance) : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError
      (acquired := acquired) fragment) ≤ target := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    ownerLe errorLe) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have bounded : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
    acquired) fragment) ≤ 4 * budget.tolerance :=
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError_rate (acquired :=
      acquired) fragment).trans scaled).trans_eq (by ring1)
  exact bounded.trans budget.four_tolerance_le

/-- The original source-total bound is at most the retained common primitive slope. -/
theorem
  OwnedFragments.OwnedFragment.sourceBound_uniform
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) :
    fragment.sourceBound ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers := by
  have widthSquare : fragment.width ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct fragment.width_nonnegative fragment.width_le_one 2).trans_eq (by
      decide)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.width,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq] at widthSquare
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
    covers)).trans_eq (mul_one _)

/-- A paid endpoint discrepancy and the common source slope give the displayed uniform total bound. -/
theorem
  OwnedFragments.OwnedFragment.totalBound_uniform
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data) {target : Normalization.InverseRootPolynomial.Coordinate}
    (errorLe : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
      acquired) fragment) ≤ target) :
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
      fragment) ≤ 2 * (target +
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers) :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct errorLe
    fragment.sourceBound_uniform) (by decide)

/-- Pay both local errors using the pre-acquisition cell query. The cell
square diameter is charged explicitly when selecting its query target. -/
theorem
  OwnedFragments.OwnedFragment.errors_paid_of_query
  (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
  (coefficients := coefficients) data)
    {density target : Normalization.InverseRootPolynomial.Coordinate} (budget :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
    (allowanceLe : fragment.allowance ≤ 1)
    (densityLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity acquired fragment.piece
      faceIndex ≤ density)
    (ownerLe : fragment.budget.tolerance ≤ budget.tolerance)
    (query : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule.CellQuery occurrence fragment.piece.column
      fragment.piece.row
      (Rational.Budget.Weighted.allowance budget.tolerance
        (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq))
    (sourcePaid : query.sourceMinimum ≤ index) (facePaid : query.faceIndex ≤ faceIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError (acquired := acquired)
      fragment ≤ target ∧ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError
      (acquired := acquired) fragment ≤ target := by
  have diameterNonnegative := (occurrence.compared.entered.domain.geometry.box fragment.piece.column
    fragment.piece.row).diagonalSq_nonneg
  have queryBound := query.accurate acquired fragment.piece
    (Rational.Budget.Weighted.allowance_positive budget.tolerance_positive diameterNonnegative) sourcePaid facePaid
  have errorLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale acquired fragment.piece
    faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq ≤
        budget.tolerance :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct queryBound diameterNonnegative).trans
      ((Fraction.Field.mul_comm ..).trans_le (Rational.Budget.Weighted.mul_allowance_le budget.tolerance_positive.le
        diameterNonnegative))
  exact ⟨areaError_paid fragment budget allowanceLe densityLe ownerLe errorLe,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError_paid fragment budget
      ownerLe errorLe⟩

end OwnedFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
