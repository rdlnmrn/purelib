module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArea.BasisIntervalChartRequest.Plan.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Pay both the complete interval polygon and its endpoint discrepancy
before sampling, using the preselected depth and retained source slope. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
    Nat}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

set_option genInjectivity false in
/-- A source-reading budget paying both the complete interval polygon and its endpoint discrepancy.

The weight uses the selected dyadic depth and retained source slope before sampling. -/
structure BasisIntervalChartBudget (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap) (depth : Nat) (target allowance : InverseRootPolynomial.Coordinate) (floor
      sourceFloor : Nat) where
  /-- The cached combined polygon and endpoint error weight. -/ weight : InverseRootPolynomial.Coordinate
  /-- The weight uses the fourth power of the dyadic count, retained primitive slope and endpoint constant. -/ weight_eq
    : weight = 1280 * (((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate)^4) * (40 + 2 *
    (BasisSourceCovers.primitiveSlope covers + 1)) + 40
  /-- The retained positive source-reading allowance capped at one. -/ sourceTarget : InverseRootPolynomial.Coordinate
  /-- The source allowance is the unit-capped weighted share of the squared target allowance. -/ source_eq :
    sourceTarget = min 1 (Weighted.allowance (allowance^2) weight)
  /-- The actual interval chart request using that same retained source allowance. -/ request :
    IntervalChartRequest.BasisIntervalChartRequest interval regular depth target sourceTarget floor sourceFloor
  /-- The complete polygon discrepancy coefficient fits the squared allowance. -/ area_paid : 1280 * (((2 ^ depth : Nat)
    : InverseRootPolynomial.Coordinate)^4) * sourceTarget *
    (40 * sourceTarget + 2 * (BasisSourceCovers.primitiveSlope covers + 1)) ≤ allowance^2
  /-- The endpoint discrepancy coefficient fits the squared allowance. -/ total_paid : 40 * sourceTarget ≤ allowance^2

constructive_injectivity BasisIntervalChartBudget

namespace BasisIntervalChartBudget

/-- Allocate a positive source tolerance paying both interval discrepancies and prepare its chart request. -/
@[expose] def build (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data cap)
    (depth : Nat) (target allowance : InverseRootPolynomial.Coordinate) (positive : 0 < target) (allowancePositive : 0 <
      allowance)
    (floor sourceFloor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget.BasisIntervalChartBudget interval regular
      depth target allowance floor sourceFloor := by
  let slope := BasisSourceCovers.primitiveSlope covers
  have slopeNonnegative : 0 ≤ slope := BasisSourceCovers.primitiveSlope_nonnegative covers
  let factor := 1280 * (((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate)^4)
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  let areaWeight := factor * (40 + 2 * (slope + 1))
  have areaNonnegative : 0 ≤ areaWeight := Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (add_nonneg (by decide +kernel) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      slopeNonnegative (by decide))))
  let weight := areaWeight + 40
  have weightNonnegative : 0 ≤ weight := add_nonneg areaNonnegative (by decide +kernel)
  let sourceTarget := min 1 (Weighted.allowance (allowance^2) weight)
  have sourcePositive : 0 < sourceTarget := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Weighted.allowance_positive (Fraction.Order.Arithmetic.pow_pos_direct allowancePositive 2) weightNonnegative)
  have small : sourceTarget ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show sourceTarget ≤ Weighted.allowance (allowance^2) weight from Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _) weightNonnegative).trans
    (Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct allowance) weightNonnegative)
  have term := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 40)
  rw [Fraction.Field.mul_one_direct] at term
  have area := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    term (le_rfl : 2 * (slope + 1) ≤ 2 * (slope + 1)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative sourcePositive.le)
  have areaLe : areaWeight * sourceTarget ≤ weight * sourceTarget :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide +kernel))
      sourcePositive.le
  have totalLe : 40 * sourceTarget ≤ weight * sourceTarget :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_left areaNonnegative)
      sourcePositive.le
  let request := BasisIntervalChartRequest.build interval regular depth target sourceTarget positive sourcePositive
    floor sourceFloor
  refine ⟨weight, rfl, sourceTarget, rfl, request, ?_, totalLe.trans paid⟩
  exact area.trans ((show factor * sourceTarget * (40 + 2 * (slope + 1)) = areaWeight * sourceTarget by ring1).trans_le
    (areaLe.trans paid))

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers} {depth index minimum stage : Nat}
  {allowance primitiveTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}
    {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    covers index} {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The actual source/chart area discrepancy fits the squared allowance with the squared homogeneous coefficient norm
once the primitive request is paid and unit bounded. -/
theorem area_bounded (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget.BasisIntervalChartBudget interval regular depth
  target allowance floor sourceFloor)
    {plan : BasisIntervalChartRequest.Plan budget.request capSample polynomials minimum} {evaluated : plan.Evaluation
      sample bank stage}
    (path : Evaluation.PathData evaluated originals coefficients)
    (primitive : BasisCommonInterval.PrimitiveRequest interval regular primitiveTarget primitiveFloor) (later :
      primitive.index ≤ index)
    (small : primitiveTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (path.paired.source.area - path.chart.area) ≤ allowance^2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have term : 40 * budget.sourceTarget + 2 * (BasisSourceCovers.primitiveSlope covers + primitiveTarget) ≤
      40 * budget.sourceTarget + 2 * (BasisSourceCovers.primitiveSlope covers + 1) :=
        Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (le_rfl :
      BasisSourceCovers.primitiveSlope covers ≤ _) small) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct term
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 1280)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (2 ^ depth))) 4))
        budget.request.source_positive.le)
  exact (PathData.area_bound path primitive later).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (paid.trans budget.area_paid)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The actual source/chart endpoint-total discrepancy fits the squared allowance with its homogeneous coefficient norm.
-/
theorem total_bounded (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget.BasisIntervalChartBudget interval regular depth
  target allowance floor sourceFloor)
    {plan : BasisIntervalChartRequest.Plan budget.request capSample polynomials minimum} {evaluated : plan.Evaluation
      sample bank stage}
    (path : Evaluation.PathData evaluated originals coefficients) :
    Data.Gaussian.Norm.Basic.normSq (path.paired.source.total - path.chart.total) ≤ allowance^2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  exact (PathData.total_bound path).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.total_paid
    nonnegative)

end BasisIntervalChartBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
