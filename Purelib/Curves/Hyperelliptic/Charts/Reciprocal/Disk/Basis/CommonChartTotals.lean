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

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor : Nat}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

variable {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate}

variable {minimum : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum}

variable {index readingMinimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}

/-- The sum of finite block-total differences is the difference of the two complete flattened path totals. -/
private theorem sum_differences (paths : List (List Normalization.InverseRootPolynomial.Gaussian × List
  Normalization.InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map (fun pair =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map Prod.fst).flatten -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (paths.map Prod.snd).flatten := by
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

namespace BasisCommonChartBudget

/-- The retained pullback and common chart totals meet the paid homogeneous parent bound on the same cached paths used
by the area comparison. -/
theorem acquisition_total_bounded (budget :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget common regular depth target
  allowance floor sourceFloor)
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials readingMinimum budget.requests}
    {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage budget.requests plans}
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients budget.requests plans readings)
    {areaAllowance : Normalization.InverseRootPolynomial.Coordinate} {request :
      CommonPrimitiveRequest regular common
      areaAllowance primitiveFloor}
    (acquired : request.Acquisition polynomials originals bank coefficients depth) :
    Data.Gaussian.Norm.Basic.normSq (acquired.pullback.total - paths.chartSummary.total) ≤ allowance^2 *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in open
      Purelib.Data.Rat in by
  have small : request.tolerance ≤ 1 := by rw [request.tolerance_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (paths.pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))
    (budget.localAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) (by
      intro value member
      obtain ⟨pair, belongs, rfl⟩ := Data.List.Map.mem_map.mp member
      exact
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea.BasisCommonChartRequests.Plans.Paths.block_bounds
        small paths acquired.blocks pair belongs).2.1)
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals.sum_differences, List.Map.length_map, paths.count_eq,
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths.source_paths paths
    acquired.blocks,
    ← acquired.pullback.total_eq, ← paths.chartSummary.total_eq] at bound
  have extraNonnegative : 0 ≤ 64 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
    budget.localAllowance^2 *
      (2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers +
        1) + budget.localAllowance^2) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
        covers) (by decide)))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have first : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 ≤
      2 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 :=
    (show (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2 =
      1 * ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2) by
        ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))).trans_eq (by ring1))
  have paid := first.trans ((le_add_of_nonneg_right extraNonnegative).trans budget.paid)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact (bound.trans_eq (show (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    (budget.localAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) =
      ((common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * budget.localAllowance^2) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid nonnegative)

end BasisCommonChartBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals
