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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Pay the entire common-source fragment polygon from local finite budgets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget

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

variable {acquired :
  PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

/-- The full count-dependent fragment comparison coefficient is nonnegative when its total bound is nonnegative. -/
private theorem fragmentCoefficient_nonnegative (count : Nat) {bound : InverseRootPolynomial.Coordinate}
  (nonnegative : 0 ≤ bound) :
    0 ≤ 2 * ((count : InverseRootPolynomial.Coordinate)^2 + 16 * (count :
      InverseRootPolynomial.Coordinate)^4 * bound) :=
  Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Arithmetic.sq_nonneg_direct _)
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
      nonnegative))

/-- Local area and endpoint tolerances pay the entire fragment-path comparison error.

The actual fragment count and common total bound pay both internal areas and the full cross-fragment polygon. -/
theorem fragmentBlockError_lt
    (fragments : List (OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data)) {bound target : InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target)
    (areas : ∀ fragment ∈ fragments,
      (OwnedFragments.OwnedFragment.areaError (acquired := acquired)
      fragment) ≤ PairedFragmentBlocks.fragmentLocalTolerance
      fragments.length bound target)
    (errors : ∀ fragment ∈ fragments,
      (OwnedFragments.OwnedFragment.totalError (acquired := acquired)
      fragment) ≤ PairedFragmentBlocks.fragmentLocalTolerance
      fragments.length bound target)
    (totals : ∀ fragment ∈ fragments,
      (OwnedFragments.OwnedFragment.totalBound (acquired := acquired)
      fragment) ≤ bound) : FragmentBlocks.fragmentBlockError (acquired
      := acquired) fragments < target := by
  let tolerance := PairedFragmentBlocks.fragmentLocalTolerance
    fragments.length bound target
  have tolerancePositive : 0 < tolerance :=
    PairedFragmentBlocks.fragmentLocalTolerance_positive _ nonnegative
    positive
  have areaMax := PairedFragmentBlocks.maximum_le
    (OwnedFragments.OwnedFragment.areaError (acquired := acquired))
    fragments tolerancePositive.le areas
  have errorMax := PairedFragmentBlocks.maximum_le
    (OwnedFragments.OwnedFragment.totalError (acquired := acquired))
    fragments tolerancePositive.le errors
  have totalMax := PairedFragmentBlocks.maximum_le
    (OwnedFragments.OwnedFragment.totalBound (acquired := acquired))
    fragments nonnegative totals
  have fourth : 0 ≤ 16 * (fragments.length : InverseRootPolynomial.Coordinate)^4 :=
    Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have cross := (Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct errorMax fourth)
      (PairedFragmentBlocks.maximum_nonnegative
      (OwnedFragments.OwnedFragment.totalBound (acquired := acquired))
      fragments)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct totalMax (Arithmetic.mul_nonneg_direct
        fourth tolerancePositive.le))
  have estimate := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Arithmetic.mul_le_mul_of_nonneg_left_direct areaMax
      (Arithmetic.sq_nonneg_direct (fragments.length : InverseRootPolynomial.Coordinate)))
      cross)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  have bounded : FragmentBlocks.fragmentBlockError (acquired :=
    acquired) fragments ≤
      (2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
        InverseRootPolynomial.Coordinate)^4 * bound)) * tolerance :=
    estimate.trans_eq (by ring1)
  have denominatorPositive : 0 < 2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 *
    (fragments.length : InverseRootPolynomial.Coordinate)^4 * bound) + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct
      (BlockBudget.fragmentCoefficient_nonnegative _ nonnegative) (by
      decide)
  have paid : (2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
    InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have strict := Arithmetic.add_lt_add_left_direct tolerancePositive
    (2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
      InverseRootPolynomial.Coordinate)^4 * bound) * tolerance)
  rw [Fraction.Field.add_comm _ 0, Fraction.Field.zero_add] at strict
  exact bounded.trans_lt (strict.trans_eq ((by ring1 :
    2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
      InverseRootPolynomial.Coordinate)^4 * bound) * tolerance + tolerance =
      (2 * ((fragments.length : InverseRootPolynomial.Coordinate)^2 + 16 * (fragments.length :
        InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance).trans paid))

/-- One positive local cap pays areas, endpoint discrepancies and the
cross-fragment polygon. The common source slope also bounds every block. -/
theorem fragmentBlockError_lt_of_budget
    (fragments : List (OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data))
    {capacity : Nat} (countLe : fragments.length ≤ capacity)
    {density target : InverseRootPolynomial.Coordinate} (positive : 0 < target)
    (budget : PairedFragmentBlocks.FragmentAreaBudget density (min 1
      (PairedFragmentBlocks.fragmentLocalTolerance capacity
      (2 * (1 + CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        covers)) target)))
    (allowances : ∀ fragment ∈ fragments, fragment.allowance ≤ 1)
    (densities : ∀ fragment ∈ fragments, FragmentArea.traceDensity
      acquired fragment.piece faceIndex ≤ density)
    (owners : ∀ fragment ∈ fragments, fragment.budget.tolerance ≤ budget.tolerance)
    (queries : ∀ fragment ∈ fragments, FragmentArea.queryScale
      acquired fragment.piece faceIndex *
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq ≤
        budget.tolerance) :
    FragmentBlocks.fragmentBlockError (acquired := acquired) fragments
      < target := open Purelib.Integration in by
  have boundNN : 0 ≤ 2 * (1 +
    CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers) :=
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide)
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers))
  have toleranceLe := Budget.Path.Capacity.fragmentLocalTolerance_count_antitone countLe boundNN positive.le
  apply BlockBudget.fragmentBlockError_lt fragments boundNN positive
  · intro fragment member
    exact (fragment.areaError_paid (acquired := acquired) budget (allowances fragment member) (densities fragment
      member)
      (owners fragment member) (queries fragment member)).trans ((Basic.min_le_right ..).trans
        toleranceLe)
  · intro fragment member
    exact (fragment.totalError_paid (acquired := acquired) budget (owners fragment member) (queries fragment
      member)).trans ((Basic.min_le_right ..).trans toleranceLe)
  · intro fragment member
    have localBound := fragment.totalError_paid (acquired := acquired) budget (owners fragment member) (queries fragment
      member)
    exact (fragment.totalBound_uniform (acquired := acquired) localBound).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
        (Basic.min_le_left ..) le_rfl) (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget
