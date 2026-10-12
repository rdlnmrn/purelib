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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockBudget
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Pay complete-run endpoint errors from the existing fragment request. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns

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

namespace SourceRun

/-- The existing local fragment tolerance also pays the whole-run endpoint
error; no additional numerical acquisition is required. -/
theorem totalError_lt (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data)
  {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target)
    (errors : ∀ fragment ∈ run.fragments,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired)
        fragment ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance run.fragments.length
          bound target) :
    run.totalError < target := open Purelib.Data.Rat in by
  let tolerance := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance
    run.fragments.length bound target
  have tolerancePos : 0 < tolerance :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance_positive _ boundNN positive
  have maxBound : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired := acquired))
    run.fragments ≤ tolerance := by
    have general (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment
      (originals := originals) (coefficients := coefficients) data))
        (bounded : ∀ fragment ∈ fragments,
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
          acquired) fragment ≤ tolerance) :
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.totalError (acquired :=
          acquired)) fragments ≤ tolerance := by
      induction fragments with
      | nil => exact tolerancePos.le
      | cons first rest ih =>
        exact Purelib.Data.Rat.Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
          (ih (fun fragment member => bounded fragment (List.mem_cons_of_mem _ member)))
    exact general run.fragments errors
  have squareNN := Fraction.Order.Arithmetic.sq_nonneg_direct (run.fragments.length :
    Normalization.InverseRootPolynomial.Coordinate)
  have crossNN : 0 ≤ 32 * (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 * bound :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)) boundNN
  have restPos : 0 < (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 +
      32 * (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 * bound + 1 :=
    Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.add_le_add_direct squareNN crossNN) (by decide)
  have denomPos : 0 < 2 * ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 +
      16 * (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1 := by
    have positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct squareNN restPos
    exact positive.trans_eq (by ring1)
  have paid : (2 * ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 +
      16 * (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance = target
        := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denomPos.ne'
  have strict : (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance <
      (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance +
        ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 32 * (run.fragments.length :
          Normalization.InverseRootPolynomial.Coordinate)^4 * bound + 1) * tolerance := by
    have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (Fraction.Order.Arithmetic.mul_pos_direct restPos tolerancePos)
      ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance)
    simpa only [-eq_self, -iff_self, AddZeroClass.add_zero] using translated
  have strictPaid : (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance < target :=
    strict.trans_eq ((show
      (run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance +
        ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 32 * (run.fragments.length :
          Normalization.InverseRootPolynomial.Coordinate)^4 * bound + 1) * tolerance =
      (2 * ((run.fragments.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (run.fragments.length :
        Normalization.InverseRootPolynomial.Coordinate)^4 * bound) + 1) * tolerance by ring1).trans paid)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct maxBound squareNN).trans_lt strictPaid

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
