module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Mathlib.Algebra.Ring.Defs
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Select a finite source resampling depth and pay the complete run error. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns

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

/-- Increasing a natural depth decreases its rational dyadic width. -/
private theorem half_antitone {first last : Nat} (later : first ≤ last) :
    (1 / 2 : InverseRootPolynomial.Coordinate)^last ≤ (1 / 2 :
      InverseRootPolynomial.Coordinate)^first := by
  let extra := last - first
  have equal : last = first + extra := (Nat.Subtraction.add_sub_of_le later).symm
  rw [equal, pow_add]
  have bounded := Arithmetic.pow_le_pow_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 2)
    (by decide : (1 / 2 : InverseRootPolynomial.Coordinate) ≤ 1) extra
  rw [one_pow] at bounded
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Arithmetic.pow_nonneg_direct
    (by decide) first)).trans_eq (mul_one _)

/-- The squared dyadic width is the corresponding rational quarter power. -/
private theorem half_square (depth : Nat) :
    ((1 / 2 : InverseRootPolynomial.Coordinate)^depth)^2 = (1 / 4 :
      InverseRootPolynomial.Coordinate)^depth := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact congrArg (fun value : InverseRootPolynomial.Coordinate => value^depth) (by
      decide : (1 / 2 : InverseRootPolynomial.Coordinate)^2 = 1 / 4)

/-- Select the reference depth from the retained source covers alone. -/
@[expose] def sourceRunRefinement (covers : SourceLocations.BasisSourceCovers
  parent)
    (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) (minimum : Nat) :
    SourceRunRefinement 1
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)
      (requested / 4) minimum :=
  SourceRunRefinement.build 1 _ _
    (Field.div_pos_direct positive (by decide)) minimum

namespace SourceRun

/-- The retained physical width and paid reference depth bound the original common-source resampling cost strictly. -/
theorem resampling_paid (run : SourceRun acquired data)
  {requested : InverseRootPolynomial.Coordinate} {minimum : Nat}
    (refinement : SourceRunRefinement 1
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)
      requested minimum)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth) :
    16 * (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)^2 *
      (max run.width ((1 / 2 : InverseRootPolynomial.Coordinate)^(common.depth + acquired.extraDepth)))^2
        < requested := open Approximation in by
  have maxNonnegative : 0 ≤ max run.width ((1 / 2 : InverseRootPolynomial.Coordinate)^(common.depth +
    acquired.extraDepth)) :=
    (Arithmetic.pow_nonneg_direct (by decide) _).trans (Basic.le_max_right ..)
  have upper := Basic.max_le widthLe
    ((SourceRuns.half_antitone later).trans_eq
    refinement.width_eq.symm)
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.pow_le_pow_direct
    maxNonnegative upper 2)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
      (Arithmetic.sq_nonneg_direct
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)))
  have equal : 16 * (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    covers)^2 * refinement.width^2 =
      Rational.Geometric.Basic.quarterRadius
        (SourceRunRefinement.sourceRunScale 1
          (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers))
          refinement.depth := by
    rw [refinement.width_eq, SourceRuns.half_square,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold SourceRunRefinement.sourceRunScale
    simp only [-eq_self, -iff_self, Nat.cast_one, one_pow, mul_one]
    rfl
  exact (bound.trans_eq equal).trans_lt refinement.accurate

/-- Both whole-path errors are charged; no equality of total increments is
used as a replacement for area comparison. -/
theorem error_lt (run : SourceRun acquired data) {requested
  : InverseRootPolynomial.Coordinate} {minimum : Nat}
    (refinement : SourceRunRefinement 1
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)
      (requested / 4) minimum)
    (blocks : FragmentBlocks.fragmentBlockError (acquired := acquired)
      run.fragments ≤ requested / 4)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth) :
    run.error < requested := by
  have source := run.resampling_paid refinement widthLe later
  have summed := (Arithmetic.add_le_add_direct blocks (le_refl _)).trans_lt
    (Arithmetic.add_lt_add_left_direct source (requested / 4))
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2) summed
  apply scaled.trans_eq
  calc
    2 * (requested / 4 + requested / 4) = requested / 4 * 4 := by ring1
    _ = requested := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The paid fragment and resampling requests bound the complete run against its original cached source area.

The retained physical width and reference depth supply the geometric conditions, with the common coefficient norm
scaling the requested error. -/
theorem cached_source_area_requested (run : SourceRun
  acquired data) {requested : InverseRootPolynomial.Coordinate} {minimum : Nat}
    (refinement : SourceRunRefinement 1
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers)
      (requested / 4) minimum)
    (blocks : FragmentBlocks.fragmentBlockError (acquired := acquired)
      run.fragments ≤ requested / 4)
    (widthLe : run.width ≤ refinement.width) (later : refinement.depth ≤ common.depth + acquired.extraDepth)
    {pairs :
      PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((run.fragments.map
      OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten -
      weighted.source.area) ≤ requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (run.cached_source_area_bound weighted).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (run.error_lt refinement blocks widthLe later).le
      (Arithmetic.sq_nonneg_direct _))

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
