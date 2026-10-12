module
import Purelib.Data.List.Map
import Purelib.Data.List.GetD
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Integration.Path.DyadicPrimitiveLinearReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Identify the combined prepared polynomial path with the original parent
path used by the common-interval area comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback

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

namespace BasisPreparedCommonRequest.Acquisition

variable {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

namespace ChildPairs

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

/-- Each retained child-pair source entry equals the corresponding original parent dyadic primitive increment. -/
private theorem source_read (pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus)
    (column : Fin (2 ^ (common.depth + acquired.extraDepth))) :
    (pairs.read row column).1 =
      (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements
        (fun parameter => (originals.get row).primitive.value.eval (parent.edge.point parameter))
        (common.depth + acquired.extraDepth) 0 1)[column.val]'(
          (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ column.isLt) := by
  have equal := pairs.source_path row
  have inside : column.val < ((pairs.values row).map Prod.fst).length := by
    rw [Purelib.Data.List.Map.length_map, pairs.count_eq]
    exact column.isLt
  have sourceInside : column.val < (pairs.values row).length :=
    (Purelib.Data.List.Map.length_map Prod.fst (pairs.values row)) ▸ inside
  have readback := congrArg (fun values : List Normalization.InverseRootPolynomial.Gaussian =>
    Purelib.Data.List.getElem? values column.val) equal
  rw [Purelib.Data.List.getElem?_eq_getElem _ _ inside,
    Purelib.Data.List.getElem?_eq_getElem _ _ ((Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸
      column.isLt)] at readback
  have scalar := Option.some.inj readback
  rw [Purelib.Data.List.Map.getElem_map Prod.fst (pairs.values row) column.val sourceInside inside] at scalar
  exact scalar

/-- The weighted original source entries form exactly the dyadic increment path of the retained finite primitive
combination. -/
theorem Weighted.source_path {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    weighted.values.map Prod.fst = Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients) (common.depth + acquired.extraDepth) 0 1 := open Purelib.Algebra in by
  rw [weighted.values_eq, Data.List.OfFn.Basic.map_ofFn]
  calc
    _ = List.ofFn (fun column : Fin (2 ^ (common.depth + acquired.extraDepth)) =>
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements
          (fun parameter => (originals.get row).primitive.value.eval (parent.edge.point parameter))
          (common.depth + acquired.extraDepth) 0 1)[column.val]'(
            (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ column.isLt))) := by
      apply Data.List.OfFn.Basic.ofFn_congr
      intro column
      change FiniteSum.Fin.sumFin _ = FiniteSum.Fin.sumFin _
      exact FiniteSum.Fin.sumFin_congr (fun row => congrArg (fun value => coefficients row * value)
        (source_read
        pairs row column))
    _ = _ := Path.DyadicPrimitiveLinearReadback.dyadicIncrements_linear _ _ _ _ _

/-- The retained weighted child-pair source area equals the same cached source area used by the common primitive
acquisition. -/
theorem Weighted.source_area {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    weighted.source.area = acquired.area.source.area := by
  rw [weighted.source.area_eq,
    Weighted.source_path
    weighted,
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.CommonPrimitiveRequest.Acquisition.source_area
    acquired.area]

/-- Both comparisons now share the exact cached source area. -/
theorem Weighted.integral_pullback_bound {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.area - acquired.area.pullback.area) ≤
      2 * (32 * sourceTarget *
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers +
        sourceTarget) + areaAllowance^2) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Data.Rat in by
  have source := acquired.area.bounded
  rw [acquired.area.difference_eq, ←
    Weighted.source_area
    weighted] at source
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (weighted.source.area - acquired.area.pullback.area) weighted.difference).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
      weighted.area_error) (by decide))
  rw [weighted.difference_eq,
    show weighted.source.area - acquired.area.pullback.area - (weighted.source.area - weighted.integral.area) =
      weighted.integral.area - acquired.area.pullback.area by ring1] at bound
  exact bound.trans_eq (by ring1)

end ChildPairs
end BasisPreparedCommonRequest.Acquisition
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback
