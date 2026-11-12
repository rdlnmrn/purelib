module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Bound the full common-source fragment path, including its joining polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : UniformReciprocalModels.Data patch count} {cover :
    UniformReciprocalCover.Cover sourceData}
  {covers : Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

/-- Compute the complete fragment-path area error, including the cross-fragment polygon.

The original fragment count and maxima of local area, endpoint and total bounds determine the coefficient-independent
error. -/
@[expose] def fragmentBlockError (fragments : List
  (OwnedFragments.OwnedFragment (originals := originals) (coefficients
  := coefficients) data)) : Coordinate :=
  2 * ((fragments.length : Coordinate)^2 *
    PairedFragmentBlocks.maximum
    (OwnedFragments.OwnedFragment.areaError (acquired := acquired))
    fragments +
    16 * (fragments.length : Coordinate)^4 *
      PairedFragmentBlocks.maximum
      (OwnedFragments.OwnedFragment.totalError (acquired := acquired))
      fragments *
      PairedFragmentBlocks.maximum
        (OwnedFragments.OwnedFragment.totalBound (acquired :=
        acquired)) fragments)

/-- This compares flattened paths rather than just the sum of their internal
areas. The cross-fragment polygon is bounded using retained endpoint errors. -/
theorem owned_fragments_area_bound
    (fragments : List (OwnedFragments.OwnedFragment (originals :=
      originals) (coefficients := coefficients) data)) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((fragments.map
      OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten -
      Path.PairedIncrementArea.area ((fragments.map
        OwnedFragments.OwnedFragment.pair).map Prod.snd).flatten) ≤
      FragmentBlocks.fragmentBlockError (acquired := acquired)
        fragments * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Algebra in
        open Purelib.Data.Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have upper {value : OwnedFragments.OwnedFragment (originals :=
    originals) (coefficients := coefficients) data → Coordinate}
      {fragment} (present : fragment ∈ fragments) :
      value fragment * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        PairedFragmentBlocks.maximum value fragments *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (PairedFragmentBlocks.le_maximum value present) massNN
  have bounded := Path.PairedBlockComparison.blocks_area_difference_bound (fragments.map
    OwnedFragments.OwnedFragment.pair)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PairedFragmentBlocks.maximum_nonnegative
      (OwnedFragments.OwnedFragment.totalError (acquired := acquired))
      fragments) massNN)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PairedFragmentBlocks.maximum_nonnegative
      (OwnedFragments.OwnedFragment.totalBound (acquired := acquired))
      fragments) massNN)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact (OwnedFragments.OwnedFragment.area_accurate (acquired :=
        acquired) fragment).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (PairedFragmentBlocks.le_maximum _ present)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := OwnedFragments.OwnedFragment.total_accurate
        (acquired := acquired) fragment
      exact ⟨bound.1.trans (upper present), bound.2.trans (upper present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := OwnedFragments.OwnedFragment.owned_bounded
        (acquired := acquired) fragment
      exact ⟨bound.1.trans (upper present), bound.2.trans (upper present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      have bound := OwnedFragments.OwnedFragment.source_bounded
        (acquired := acquired) fragment
      exact ⟨bound.1.trans (upper present), bound.2.trans (upper present)⟩)
  rw [List.Map.length_map] at bounded
  exact bounded.trans_eq (by
      unfold FragmentBlocks.fragmentBlockError;
      ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
