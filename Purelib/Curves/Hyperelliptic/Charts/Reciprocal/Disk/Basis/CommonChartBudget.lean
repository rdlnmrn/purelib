module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
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
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! One parent allowance pays every interval polygon and the complete
joining polygon before any polynomial or reading stage is selected. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget

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

set_option genInjectivity false in
/-- A paid whole-parent chart-area request for the original common interval cover.

It includes every interval error and the complete joining polygon through a cached count-and-slope weight and a positive
local allowance. -/
structure BasisCommonChartBudget (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover
  covers minimum)
    (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (depth : Nat) (target allowance :
      Normalization.InverseRootPolynomial.Coordinate) (floor sourceFloor : Nat) where
  /-- The cached weight for all original interval and joining-polygon errors. -/ weight :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The weight uses the original interval count and retained primitive slope. -/ weight_eq : weight = 2 *
    (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 +
    64 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * (2 *
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
      1)
  /-- The retained common local chart allowance. -/ localAllowance : Normalization.InverseRootPolynomial.Coordinate
  /-- The local allowance is the minimum of one and the weighted allowance for the squared parent target. -/ local_eq :
    localAllowance = min 1 (Rational.Budget.Weighted.allowance (allowance^2) weight)
  /-- The common local allowance is positive. -/ local_positive : 0 < localAllowance
  /-- The original interval chart requests at that same paid local allowance. -/ requests :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth target
    localAllowance floor sourceFloor common.intervals
  /-- The complete interval and joining-polygon bound is paid by the squared parent allowance. -/ paid : 2 *
    (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * localAllowance^2 +
    64 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * localAllowance^2 *
      (2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers +
        1) + localAllowance^2) ≤ allowance^2

constructive_injectivity BasisCommonChartBudget

namespace BasisCommonChartBudget

/-- Prepare every original interval chart request and certify the whole-parent area payment before selecting any
numerical readings. -/
@[expose] def build (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum) (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (depth : Nat) (target allowance : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target)
      (allowancePositive : 0 < allowance)
    (floor sourceFloor : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget
      common regular depth target allowance floor sourceFloor := by
  let first := 2 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2
  let last := 64 * (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4
  let slope := 2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    covers + 1)
  have firstNonnegative : 0 ≤ first := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have lastNonnegative : 0 ≤ last := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have slopeNonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers) (by decide))
  let weight := first + last * (slope + 1)
  have weightNonnegative : 0 ≤ weight := add_nonneg firstNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct lastNonnegative (add_nonneg slopeNonnegative (by decide)))
  let localAllowance := min 1 (Rational.Budget.Weighted.allowance (allowance^2) weight)
  have localPositive : 0 < localAllowance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive (Fraction.Order.Arithmetic.pow_pos_direct allowancePositive 2)
      weightNonnegative)
  have small : localAllowance ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have squareLe : localAllowance^2 ≤ localAllowance := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small localPositive.le
    exact (show localAllowance^2 = localAllowance * localAllowance by ring1).trans_le
      (scaled.trans_eq (Fraction.Field.mul_one_direct _))
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show localAllowance ≤ Rational.Budget.Weighted.allowance (allowance^2) weight from
      Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _) weightNonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct allowance) weightNonnegative)
  have term := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    (le_rfl : slope ≤ slope) (squareLe.trans small))
    (Fraction.Order.Arithmetic.mul_nonneg_direct lastNonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct
      localAllowance))
  have bound := Fraction.Order.Arithmetic.add_le_add_direct (le_rfl : first * localAllowance^2 ≤ first *
    localAllowance^2) term
  have scaled := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe weightNonnegative).trans paid
  let requests := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.build regular
    depth target localAllowance positive localPositive floor sourceFloor common.intervals
  refine ⟨weight, rfl, localAllowance, rfl, localPositive, requests, ?_⟩
  exact bound.trans ((show first * localAllowance^2 + last * localAllowance^2 * (slope + 1) = weight * localAllowance^2
    by ring1).trans_le scaled)

variable {index readingMinimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}

/-- The error is for the complete parent path, including the polygon of totals. -/
theorem bounded (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget common
  regular depth target allowance floor sourceFloor)
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials readingMinimum budget.requests}
    {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage budget.requests plans}
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients budget.requests plans readings)
    {primitivePlans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor common.intervals}
    (blocks : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans)
    (small : primitiveTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (paths.sourceSummary.area - paths.chartSummary.area) ≤ allowance^2 *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea.BasisCommonChartRequests.Plans.Paths.area_bound paths
    blocks small).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Transport to the previously retained pullback acquisition by literal
path readback, without acquiring its numerical bank or summaries again. -/
theorem acquisition_bounded (budget :
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
    Data.Gaussian.Norm.Basic.normSq (acquired.pullback.area - paths.chartSummary.area) ≤ allowance^2 *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have small : request.tolerance ≤ 1 := by rw [request.tolerance_eq]; exact
    Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have bound := budget.bounded paths acquired.blocks small
  rw [paths.sourceSummary.area_eq,
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths.source_paths paths
    acquired.blocks, ← acquired.pullback.area_eq] at bound
  exact bound

end BasisCommonChartBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
