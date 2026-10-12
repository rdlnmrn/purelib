module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Integration.Budget.Path.Capacity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBudget
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
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

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Pay the entire common-source fragment polygon from local finite budgets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget

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

/-- The full count-dependent fragment comparison coefficient is nonnegative when its total bound is nonnegative. -/
private theorem fragmentCoefficient_nonnegative (count : Nat) {bound : Normalization.InverseRootPolynomial.Coordinate}
  (nonnegative : 0 ≤ bound) :
    0 ≤ 2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (count :
      Normalization.InverseRootPolynomial.Coordinate)^4 * bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
      nonnegative))

/-- Local area and endpoint tolerances pay the entire fragment-path comparison error.

The actual fragment count and common total bound pay both internal areas and the full cross-fragment polygon. -/
theorem fragmentBlockError_lt
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data)) {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target)
    (areas : ∀ fragment ∈ fragments,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError (acquired := acquired)
      fragment) ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance
      fragments.length bound target)
    (errors : ∀ fragment ∈ fragments,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
      fragment) ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance
      fragments.length bound target)
    (totals : ∀ fragment ∈ fragments,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
      fragment) ≤ bound) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired
      := acquired) fragments < target := by
  let tolerance := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance
    fragments.length bound target
  have tolerancePositive : 0 < tolerance :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance_positive _ nonnegative
    positive
  have areaMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.areaError (acquired := acquired))
    fragments tolerancePositive.le areas
  have errorMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired))
    fragments tolerancePositive.le errors
  have totalMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired))
    fragments nonnegative totals
  have fourth : 0 ≤ 16 * (fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have cross := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorMax fourth)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalBound (acquired := acquired))
      fragments)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalMax (Fraction.Order.Arithmetic.mul_nonneg_direct
        fourth tolerancePositive.le))
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaMax
      (Fraction.Order.Arithmetic.sq_nonneg_direct (fragments.length : Normalization.InverseRootPolynomial.Coordinate)))
      cross)
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have bounded : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired :=
    acquired) fragments ≤
      (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
        Normalization.InverseRootPolynomial.Coordinate)^4 * bound)) * tolerance :=
    estimate.trans_eq (by ring1)
  have denominatorPositive : 0 < 2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 *
    (fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget.fragmentCoefficient_nonnegative _ nonnegative) (by
      decide)
  have paid : (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
    Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have strict := Fraction.Order.Arithmetic.add_lt_add_left_direct tolerancePositive
    (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
      Normalization.InverseRootPolynomial.Coordinate)^4 * bound) * tolerance)
  rw [Fraction.Field.add_comm _ 0, Fraction.Field.zero_add] at strict
  exact bounded.trans_lt (strict.trans_eq ((by ring1 :
    2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
      Normalization.InverseRootPolynomial.Coordinate)^4 * bound) * tolerance + tolerance =
      (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
        Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance).trans paid))

/-- One positive local cap pays areas, endpoint discrepancies and the
cross-fragment polygon. The common source slope also bounds every block. -/
theorem fragmentBlockError_lt_of_budget
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data))
    {capacity : Nat} (countLe : fragments.length ≤ capacity)
    {density target : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target)
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density (min 1
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance capacity
      (2 * (1 + Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        covers)) target)))
    (allowances : ∀ fragment ∈ fragments, fragment.allowance ≤ 1)
    (densities : ∀ fragment ∈ fragments, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.traceDensity
      acquired fragment.piece faceIndex ≤ density)
    (owners : ∀ fragment ∈ fragments, fragment.budget.tolerance ≤ budget.tolerance)
    (queries : ∀ fragment ∈ fragments, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentArea.queryScale
      acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq ≤
        budget.tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired := acquired) fragments
      < target := open Purelib.Integration in by
  have boundNN : 0 ≤ 2 * (1 +
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers))
  have toleranceLe := Budget.Path.Capacity.fragmentLocalTolerance_count_antitone countLe boundNN positive.le
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget.fragmentBlockError_lt fragments boundNN positive
  · intro fragment member
    exact (fragment.areaError_paid (acquired := acquired) budget (allowances fragment member) (densities fragment
      member)
      (owners fragment member) (queries fragment member)).trans ((Fraction.Order.Basic.min_le_right ..).trans
        toleranceLe)
  · intro fragment member
    exact (fragment.totalError_paid (acquired := acquired) budget (owners fragment member) (queries fragment
      member)).trans ((Fraction.Order.Basic.min_le_right ..).trans toleranceLe)
  · intro fragment member
    have localBound := fragment.totalError_paid (acquired := acquired) budget (owners fragment member) (queries fragment
      member)
    exact (fragment.totalBound_uniform (acquired := acquired) localBound).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.min_le_left ..) le_rfl) (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget
