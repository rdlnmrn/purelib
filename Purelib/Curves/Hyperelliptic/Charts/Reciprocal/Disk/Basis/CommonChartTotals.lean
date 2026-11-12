module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Total-increment comparison on the same cached common chart and pullback
paths as the area estimate. No endpoint closure is assumed. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals

open Purelib.Data.Rat

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor : Nat}
  {covers : SourceLocations.BasisSourceCovers parent}

variable {cover : UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate}

variable {minimum : Nat} {common : CommonCover.BasisCommonCover cover covers
  minimum}

variable {index readingMinimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box} {polynomials :
    Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
    {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}

/-- The sum of finite block-total differences is the difference of the two complete flattened path totals. -/
private theorem sum_differences (paths : List (List Normalization.InverseRootPolynomial.Gaussian × List
  Normalization.InverseRootPolynomial.Gaussian)) :
    Gaussian.Norm.Sum.Basic.gaussianSum (paths.map (fun pair =>
      Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Gaussian.Norm.Sum.Basic.gaussianSum (paths.map Prod.fst).flatten -
        Gaussian.Norm.Sum.Basic.gaussianSum (paths.map Prod.snd).flatten := by
  induction paths with
  | nil => change (0 : Normalization.InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair paths ih =>
      change (Gaussian.Norm.Sum.Basic.gaussianSum pair.1 - Gaussian.Norm.Sum.Basic.gaussianSum pair.2) +
        Gaussian.Norm.Sum.Basic.gaussianSum (paths.map (fun pair => Gaussian.Norm.Sum.Basic.gaussianSum pair.1
          - Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
        Gaussian.Norm.Sum.Basic.gaussianSum (pair.1 ++ (paths.map Prod.fst).flatten) -
        Gaussian.Norm.Sum.Basic.gaussianSum (pair.2 ++ (paths.map Prod.snd).flatten)
      rw [ih, Path.IncrementArea.sum_append, Path.IncrementArea.sum_append]
      ring1

namespace BasisCommonChartBudget

/-- The retained pullback and common chart totals meet the paid homogeneous parent bound on the same cached paths used
by the area comparison. -/
theorem acquisition_total_bounded (budget :
  CommonChartBudget.BasisCommonChartBudget common regular depth target
  allowance floor sourceFloor)
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials readingMinimum budget.requests}
    {readings : CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage budget.requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients budget.requests plans readings)
    {areaAllowance : Normalization.InverseRootPolynomial.Coordinate} {request :
      CommonPrimitiveRequest regular common
      areaAllowance primitiveFloor}
    (acquired : request.Acquisition polynomials originals bank coefficients depth) :
    Gaussian.Norm.Basic.normSq (acquired.pullback.total - paths.chartSummary.total) ≤ allowance^2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in open
      Purelib.Data.Rat in by
  have small : request.tolerance ≤ 1 := by rw [request.tolerance_eq]; exact Basic.min_le_left _ _
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (paths.pairs.map (fun pair => Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Gaussian.Norm.Sum.Basic.gaussianSum pair.2))
    (budget.localAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) (by
      intro value member
      obtain ⟨pair, belongs, rfl⟩ := Data.List.Map.mem_map.mp member
      exact
        (CommonChartArea.BasisCommonChartRequests.Plans.Paths.block_bounds
        small paths acquired.blocks pair belongs).2.1)
  rw [sum_differences, List.Map.length_map, paths.count_eq,
    CommonChartPaths.BasisCommonChartRequests.Plans.Paths.source_paths paths
    acquired.blocks,
    ← acquired.pullback.total_eq, ← paths.chartSummary.total_eq] at bound
  have extraNonnegative : 0 ≤ 64 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
    budget.localAllowance^2 *
      (2 * (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers +
        1) + budget.localAllowance^2) :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        (Arithmetic.sq_nonneg_direct _))
      (add_nonneg (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
        covers) (by decide)))
        (Arithmetic.sq_nonneg_direct _))
  have first : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 ≤
      2 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 :=
    (show (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 =
      1 * ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2) by
        ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
        (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
          (Arithmetic.sq_nonneg_direct _))).trans_eq (by ring1))
  have paid := first.trans ((le_add_of_nonneg_right extraNonnegative).trans budget.paid)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg
      (coefficients row)))
  exact (bound.trans_eq (show (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    (budget.localAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) =
      ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1)).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct paid nonnegative)

end BasisCommonChartBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals
