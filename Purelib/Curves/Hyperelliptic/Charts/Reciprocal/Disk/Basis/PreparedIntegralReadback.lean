module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
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
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Paths.PreparedPrimitivePathArea
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Exact ownership of the weighted prepared child-integral path and total.
These are the acquired children, not another sampler's refinement schedule. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback

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

/-- The Gaussian sum of a finite function's ordered list equals its finite indexed sum. -/
private theorem sum_ofFn {size : Nat} (values : Fin size → Normalization.InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn values) = FiniteSum.Fin.sumFin values := by
  induction size with
  | zero => rfl
  | succ size ih =>
      rw [Data.List.OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      exact congrArg (fun tail => values 0 + tail) (ih (fun index => values index.succ))

/-- Reading a retained list through its certified finite indices reconstructs exactly that list. -/
private theorem ofFn_readback (values : List (Normalization.InverseRootPolynomial.Gaussian ×
  Normalization.InverseRootPolynomial.Gaussian)) (size : Nat) (length_eq : values.length = size) :
    List.ofFn (fun column : Fin size => values[column.val]'(length_eq.symm ▸ column.isLt)) = values := by
  subst size
  exact Data.List.OfFn.Basic.ofFn_getElem values

/-- Each row reads the actual retained child integrals in their original order. -/
theorem integral_path (pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) :
    List.ofFn (fun column : Fin (2 ^ (common.depth + acquired.extraDepth)) => (pairs.read row column).2) =
      Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((acquired.prepared.get row).localRequest.request.block.children.map
          Integration.PreparedSubdivisionModelCore.CenteredEdge.model)) := by
  calc
    _ = (List.ofFn (pairs.read row)).map Prod.snd := Data.List.OfFn.Basic.map_ofFn.symm
    _ = (pairs.values row).map Prod.snd := congrArg (List.map Prod.snd)
      (ofFn_readback
      _ _ (pairs.count_eq row))
    _ = _ := by
      rw [pairs.values_eq]
      exact Paths.PreparedPrimitivePathArea.LocalRequest.areaPairs_right (acquired.prepared.get row).localRequest

/-- The combined path retains one weighted integral for each spatial child. -/
theorem Weighted.integral_path {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    weighted.values.map Prod.snd = List.ofFn (fun column : Fin (2 ^ (common.depth + acquired.extraDepth)) =>
      FiniteSum.Fin.sumFin (fun row => coefficients row * (pairs.read row column).2)) := by
  rw [weighted.values_eq, Data.List.OfFn.Basic.map_ofFn]
  rfl

/-- The cached weighted integral total equals the original acquisition's retained integral value. -/
theorem Weighted.integral_total {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    weighted.integral.total = acquired.integralValue := by
  rw [weighted.integral.total_eq,
    Weighted.integral_path
    weighted,
    sum_ofFn,
    FiniteSum.Fin.sumFin_swap]
  unfold
    PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition.integralValue
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [FiniteSum.Fin.sumFin_mul_left, ←
    sum_ofFn,

      ChildPairs.integral_path
      pairs row,
    Paths.PathArea.increments_sum]

/-- The cached weighted source total is exactly the original primitive bank's endpoint difference. -/
theorem Weighted.source_total {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    weighted.source.total =
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients 1 -
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients 0 := by
  rw [weighted.source.total_eq,

      PreparedPathReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_path
      weighted,
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum]

/-- The area and endpoint comparisons refer to the same pair of cached paths. -/
theorem Weighted.total_error {pairs :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired} (weighted :
  PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
  pairs) :
    Data.Gaussian.Norm.Basic.normSq (weighted.source.total - weighted.integral.total) ≤ sourceTarget *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  rw
    [Weighted.source_total
    weighted,
    Weighted.integral_total
    weighted]
  exact acquired.integral_error

end ChildPairs
end BasisPreparedCommonRequest.Acquisition
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
