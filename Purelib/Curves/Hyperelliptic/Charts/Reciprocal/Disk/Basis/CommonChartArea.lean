module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
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
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea
import Mathlib.Algebra.Ring.Defs
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

/-! Complete parent source/chart area comparison, including the signed
polygon of interval totals. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea

open Purelib.Data.Rat.Fraction.Order

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

variable {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace BasisCommonChartRequests.Plans

variable {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index
  cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Paths

variable {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}

/-- The squared norm of the retained finite coefficient vector is nonnegative. -/
private theorem norm_nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
  Purelib.Algebra in FiniteSum.Fin.sumFin_zero.symm.trans_le
  (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg (coefficients
    row)))

/-- Each original interval retains its homogeneous area error, total-increment error and both source/chart magnitude
bounds.

The bounds use the same acquired primitive blocks and coefficient vector, with the retained primitive target at most
one. -/
theorem block_bounds (small : primitiveTarget ≤ 1) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    {primitivePlans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor intervals} →
    (blocks : CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans) →
    ∀ pair ∈ paths.pairs,
      Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea pair.1 - Path.IncrementArea.pathArea pair.2) ≤
        allowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 ∧
      Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ allowance^2 *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ∧
      Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 * (2 *
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
        allowance^2) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ∧
      Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 * (2 *
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
        allowance^2) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, .nil, _, _, _, _, .nil, _, member => False.elim (List.not_mem_nil member)
  | _, .cons head _, _, _, paths, _, .cons (request := primitive) block later remaining, pair, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have area := head.area_bounded paths.1 primitive later small
        have error := head.total_bounded paths.1
        have source :=
          (CommonPrimitiveParentArea.BasisCommonInterval.PrimitiveSample.Block.parent_bounds
          block primitive later).2.2.2
        have sourceLe := Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct (le_rfl :
            CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers ≤
            _) small)
            (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
              (norm_nonnegative
              (coefficients := coefficients))
        have sourceBound := source.trans sourceLe
        rw [←
          IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.PathData.source_total
          _ paths.1 block] at sourceBound
        let slope := 2 *
          (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1)
        have slopeNonnegative : 0 ≤ slope := Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
            covers) (by decide))
        have enlarged : slope ≤ 2 * (slope + allowance^2) :=
          (show slope = slope + 0 by ring1).trans_le
            ((Arithmetic.add_le_add_direct le_rfl (add_nonneg slopeNonnegative
              (Arithmetic.mul_nonneg_direct (by decide : (0 :
                Normalization.InverseRootPolynomial.Coordinate) ≤ 2) (Arithmetic.sq_nonneg_direct
                allowance)))).trans_eq (by ring1))
        have leftBound := sourceBound.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged
          norm_nonnegative)
        have rightBound := (Gaussian.Norm.Bounds.normSq_sub_le_two paths.1.paired.source.total
          (paths.1.paired.source.total - paths.1.chart.total)).trans
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct sourceBound error) (by decide))
        rw [show paths.1.paired.source.total - (paths.1.paired.source.total - paths.1.chart.total) = paths.1.chart.total
          by ring1] at rightBound
        have rightFinal : Gaussian.Norm.Basic.normSq paths.1.chart.total ≤ 2 * (slope + allowance^2) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
          rightBound.trans_eq (by dsimp only [slope]; ring1)
        rw [paths.1.paired.source.area_eq, paths.1.chart.area_eq] at area
        rw [paths.1.paired.source.total_eq, paths.1.chart.total_eq] at error
        rw [paths.1.paired.source.total_eq] at leftBound
        rw [paths.1.chart.total_eq] at rightFinal
        exact ⟨area, error, leftBound, rightFinal⟩
      · exact
          block_bounds
          small paths.2 remaining pair member

/-- Cached summary readback includes every interval and the intervening
coarse polygon, with a homogeneous error for arbitrary coefficients. -/
theorem area_bound {intervals : List (CommonCover.BasisCommonInterval cover
  covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    {primitivePlans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor intervals}
    (blocks : CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans)
    (small : primitiveTarget ≤ 1) :
    Gaussian.Norm.Basic.normSq (paths.sourceSummary.area - paths.chartSummary.area) ≤
      (2 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * allowance^2 + 64 * (intervals.length
        : Normalization.InverseRootPolynomial.Coordinate)^4 * allowance^2 *
        (2 * (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers +
          1) + allowance^2)) * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open
          Purelib.Data.Rat in by
  have bounds :=
    block_bounds small
    paths blocks
  have commonNonnegative : 0 ≤ 2 * (2 *
    (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
    allowance^2) :=
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
        covers) (by decide)))
      (Arithmetic.sq_nonneg_direct allowance))
  have bound := Path.IncrementAreaComparison.blocks_area_difference_bound paths.pairs
    (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct allowance)
      norm_nonnegative)
      (Arithmetic.mul_nonneg_direct commonNonnegative
      norm_nonnegative)
    (fun pair member => (bounds pair member).1) (fun pair member => (bounds pair member).2.1)
    (fun pair member => (bounds pair member).2.2.1) (fun pair member => (bounds pair member).2.2.2)
  rw [paths.count_eq, ← paths.sourceSummary.area_eq, ← paths.chartSummary.area_eq] at bound
  exact bound.trans_eq (by ring1)

end Paths
end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea
