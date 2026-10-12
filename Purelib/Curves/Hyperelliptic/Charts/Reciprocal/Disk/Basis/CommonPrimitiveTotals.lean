module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Total errors on the same complete paths as the parent area comparison.
The endpoint error is retained for later concatenation between parents. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveTotals

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility

variable {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum}

/-- The finite sum of original block-total differences equals the difference of the complete flattened path totals. -/
private theorem sum_differences (paths : List (List Normalization.InverseRootPolynomial.Gaussian × List
  Normalization.InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map Prod.fst).flatten - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (paths.map Prod.snd).flatten := by
  induction paths with
  | nil => change (0 : Normalization.InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair paths ih =>
      change (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1
          - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pair.1 ++ (paths.map Prod.fst).flatten) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pair.2 ++ (paths.map Prod.snd).flatten)
      rw [ih, Path.IncrementArea.sum_append, Path.IncrementArea.sum_append]
      ring1

namespace CommonPrimitivePlans.Blocks

variable {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The original source and pullback totals satisfy a homogeneous bound using the squared actual interval count and
retained primitive target. -/
theorem total_error {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers)} {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
  target floor intervals}
    (blocks : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals cells coefficients depth plans) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.paths.map Prod.fst).flatten -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.paths.map Prod.snd).flatten) ≤
      (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * target *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (blocks.paths.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) (by
      intro value member
      obtain ⟨pair, belongs, rfl⟩ := Data.List.Map.mem_map.mp member
      exact
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.CommonPrimitivePlans.Blocks.paths_bounded
        blocks pair belongs).2.1)
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveTotals.sum_differences, List.Map.length_map,
    blocks.paths_count] at bound
  exact bound.trans_eq (by ring1)

end CommonPrimitivePlans.Blocks

namespace BasisPreparedCommonRequest.Acquisition.ChildPairs

variable {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}
  {acquired : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition
    request polynomials originals cells coefficients depth}

/-- No endpoint closure is assumed or inferred from the area comparison. -/
theorem Weighted.integral_pullback_total_bound {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.total - acquired.area.pullback.total) ≤
      2 * (sourceTarget + (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
        request.comparison.tolerance) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Data.Rat in by
  have source :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveTotals.CommonPrimitivePlans.Blocks.total_error
    acquired.area.blocks
  rw [← acquired.area.source.total_eq, ← acquired.area.pullback.total_eq] at source
  have sourceEqual : weighted.source.total = acquired.area.source.total := by
    rw [weighted.source.total_eq,

        PreparedPathReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_path
        weighted,
      acquired.area.source.total_eq,
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.CommonPrimitivePlans.Blocks.source_parent_path
        acquired.area.blocks]
  rw [← sourceEqual] at source
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (weighted.source.total - acquired.area.pullback.total)
    (weighted.source.total - weighted.integral.total)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source

        (PreparedIntegralReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.total_error
        weighted)) (by decide))
  rw [show weighted.source.total - acquired.area.pullback.total - (weighted.source.total - weighted.integral.total) =
    weighted.integral.total - acquired.area.pullback.total by ring1] at bound
  exact bound.trans_eq (by ring1)

end BasisPreparedCommonRequest.Acquisition.ChildPairs
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveTotals
