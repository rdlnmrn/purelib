module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Readings

public section

/-! Select a finite source resampling depth and pay the complete run error. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains (ReverseSourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError
  owned_fragments_area_bound)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunScale)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : PreparedPatch parent}
  {sourceData : Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover sourceData}
  {covers : Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor
    index depth : Nat}
  {common : BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest regular
    common areaAllowance sourceTarget coefficientTarget floor}
  {box : Geometry.Rational.Box}
  {polynomials : RegularBasisPolynomials cap index
    box}
  {originals :
    PrimitiveBank covers
    index}
  {cells : BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {acquired :
  BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data : RowData
  occurrence faceIndex}

namespace ReverseSourceRun

/-- The retained reverse source run's resampling cost fits its requested refinement target once the actual width and
depth are paid. -/
theorem resampling_paid (run : ReverseSourceRun acquired data) {requested :
  Coordinate} {minimum : Nat}
    (refinement : SourceRunRefinement 1 (BasisSourceCovers.primitiveSlope covers) requested minimum)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth) :
    16 * (BasisSourceCovers.primitiveSlope covers)^2 *
      (max run.width ((1 / 2 : Coordinate)^(common.depth + acquired.extraDepth)))^2 < requested :=
        by
  have maxNonnegative : 0 ≤ max run.width ((1 / 2 : Coordinate)^(common.depth +
    acquired.extraDepth)) :=
    (Arithmetic.pow_nonneg_direct (by decide) _).trans (Basic.le_max_right ..)
  have depthWidth : (1 / 2 : Coordinate)^(common.depth + acquired.extraDepth) ≤
      (1 / 2 : Coordinate)^refinement.depth := by
    have split := Data.Nat.Subtraction.add_sub_of_le later
    rw [← split, pow_add]
    have bounded := Arithmetic.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 2)
      (by decide : (1 / 2 : Coordinate) ≤ 1)
      (common.depth + acquired.extraDepth - refinement.depth)
    rw [one_pow] at bounded
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
      (Arithmetic.pow_nonneg_direct (by decide) refinement.depth)).trans_eq (mul_one _)
  have upper := Basic.max_le widthLe (depthWidth.trans_eq refinement.width_eq.symm)
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.pow_le_pow_direct
    maxNonnegative upper 2)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 16)
      (Arithmetic.sq_nonneg_direct (BasisSourceCovers.primitiveSlope covers)))
  have equal : 16 * (BasisSourceCovers.primitiveSlope covers)^2 * refinement.width^2 =
      Geometric.Basic.quarterRadius
        (SourceRunRefinement.sourceRunScale 1 (BasisSourceCovers.primitiveSlope covers)) refinement.depth := by
    have widthSquare : ((1 / 2 : Coordinate)^refinement.depth)^2 =
        (1 / 4 : Coordinate)^refinement.depth := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      exact congrArg (fun value : Coordinate => value^refinement.depth)
        (by decide : (1 / 2 : Coordinate)^2 = 1 / 4)
    rw [refinement.width_eq, widthSquare, Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold SourceRunRefinement.sourceRunScale
    simp only [Nat.cast_one, one_pow, mul_one, -eq_self, -iff_self]
    rfl
  exact (bound.trans_eq equal).trans_lt refinement.accurate

/-- Both whole-path errors are charged; no equality of total increments is used as a replacement for area comparison. -/
theorem error_lt (run : ReverseSourceRun acquired data) {requested : Coordinate}
  {minimum : Nat}
    (refinement : SourceRunRefinement 1 (BasisSourceCovers.primitiveSlope covers) (requested / 4)
      minimum)
    (blocks : FragmentBlocks.fragmentBlockError (acquired := acquired) run.fragments ≤ requested / 4)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth) :
    run.error < requested := by
  have source := run.resampling_paid refinement widthLe later
  have summed := (Arithmetic.add_le_add_direct blocks (le_refl _)).trans_lt
    (Arithmetic.add_lt_add_left_direct source (requested / 4))
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : Coordinate) < 2) summed
  apply scaled.trans_eq
  calc
    2 * (requested / 4 + requested / 4) = requested / 4 * 4 := by ring1
    _ = requested := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The complete descending physical area approximates its signed cached source area with the requested homogeneous
bound.

Both the original fragment-block error and the retained source-resampling width and depth must be paid. -/
theorem cached_source_area_requested (run : ReverseSourceRun acquired data) {requested :
  Coordinate} {minimum : Nat}
    (refinement : SourceRunRefinement 1 (BasisSourceCovers.primitiveSlope covers) (requested / 4)
      minimum)
    (blocks : FragmentBlocks.fragmentBlockError (acquired := acquired) run.fragments ≤ requested / 4)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth)
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((run.fragments.map OwnedFragment.pair).map
      Prod.fst).flatten +
      weighted.source.area) ≤ requested * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (run.cached_source_area_bound weighted).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (run.error_lt refinement blocks widthLe later).le
      (Arithmetic.sq_nonneg_direct _))

end ReverseSourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
