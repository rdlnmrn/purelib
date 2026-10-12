module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
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
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Bound the complete acquired source/chart polygon using the same pullback
slope and the certified endpoint transports. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation
  (PathData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace BasisIntervalChartRequest

variable {interval : BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {request : BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace Plan.Evaluation

variable {plan :
  Plan
  request capSample polynomials minimum}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero)

variable {evaluated :
  IntervalChartAcquisition.BasisIntervalChartRequest.Plan.Evaluation
  plan sample bank stage}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {primitiveTarget : Coordinate} {primitiveFloor : Nat}

/-- The squared coefficient norm of the retained finite Gaussian vector is nonnegative. -/
private theorem norm_nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
  (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
    Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

namespace PathData

/-- Each retained source-path increment obeys the common primitive slope bound with the actual coefficient norm. -/
theorem source_increment (path : Evaluation.PathData evaluated originals coefficients)
    (primitive : BasisCommonInterval.PrimitiveRequest interval regular primitiveTarget primitiveFloor) (later :
      primitive.index ≤ index)
    (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈ path.paired.pairs) :
    Data.Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (BasisSourceCovers.primitiveSlope covers + primitiveTarget) *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let pullback := BasisCommonInterval.primitiveSample interval regular polynomials originals bank
  have present : pair.1 ∈ path.paired.pairs.map Prod.fst := Map.mem_map.mpr ⟨pair, member, rfl⟩
  rw [path.source_path] at present
  have slopeNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers) primitive.positive.le))

      (norm_nonnegative
      (coefficients := coefficients))
  have bound := DyadicAreaRefinement.dyadicIncrements_bounded (pullback.pullbackValue coefficients)
    (slope := 2 * (BasisSourceCovers.primitiveSlope covers + primitiveTarget) *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (fun _ _ firstInside lastInside => (PrimitiveSample.pullback_increment_bound pullback primitive later coefficients
      firstInside lastInside).trans_eq (by ring1))
    depth ⟨le_rfl, interval.ordered⟩ ⟨interval.ordered, le_rfl⟩ interval.ordered pair.1 present
  have width : interval.edge.right.parameter - interval.edge.left.parameter ≤ 1 :=
    (Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
      ((show (1 : Purelib.Data.Rat.Fraction.Rational) - 0 = 1 by ring1))
  have square := (Fraction.Order.Arithmetic.pow_le_pow_direct
    (Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct interval.ordered) width 2).trans_eq (_root_.one_pow _)
  have clipped := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (Geometric.Basic.quarterRadius_nonneg slopeNonnegative depth)
  rw [Fraction.Field.mul_one_direct] at clipped
  exact bound.trans (clipped.trans (Geometric.Basic.quarterRadius_le_scale slopeNonnegative depth))

/-- The actual source/chart polygon discrepancy obeys the retained dyadic count, primitive slope and endpoint-error
bound.

Both complete polygon summaries use the same acquired path and retain the homogeneous squared coefficient-norm factor.
-/
theorem area_bound (path : Evaluation.PathData evaluated originals coefficients)
    (primitive : BasisCommonInterval.PrimitiveRequest interval regular primitiveTarget primitiveFloor) (later :
      primitive.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (path.paired.source.area - path.chart.area) ≤
      1280 * (((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate)^4) * sourceTarget *
        (40 * sourceTarget + 2 * (BasisSourceCovers.primitiveSlope covers + primitiveTarget)) *
          (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  let slope := 2 * (BasisSourceCovers.primitiveSlope covers + primitiveTarget)
  let error := 40 * sourceTarget
  have slopeNonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers) primitive.positive.le)
  have errorNonnegative : 0 ≤ error := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    request.source_positive.le
  have commonNonnegative : 0 ≤ 2 * (slope + error) := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg slopeNonnegative errorNonnegative)
  have slopeLe : slope ≤ 2 * (slope + error) :=
    (show slope = slope + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl (add_nonneg slopeNonnegative
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        errorNonnegative))).trans_eq (by ring1))
  have sourceBound (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
    path.paired.pairs) :
      Data.Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (slope + error) *
        PreparedObservationCoercivity.coefficientNormSq coefficients :=

      (source_increment
      path primitive later pair member).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct slopeLe
      norm_nonnegative)
  have chartBound (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
    path.paired.pairs) :
      Data.Gaussian.Norm.Basic.normSq pair.2 ≤ 2 * (slope + error) *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two pair.1 (pair.1 - pair.2)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (source_increment
        path primitive later pair member) (path.paired.errors pair member)) (by decide))
    rw [show pair.1 - (pair.1 - pair.2) = pair.2 by ring1] at bound
    exact bound.trans_eq (by dsimp only [slope, error]; ring1)
  have bound := IncrementAreaComparison.pathArea_difference_bound path.paired.pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct errorNonnegative
      norm_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct commonNonnegative
      norm_nonnegative)
    path.paired.errors sourceBound chartBound
  have counted : path.paired.pairs.length = 2 ^ depth := by
    have equal := congrArg List.length path.source_path
    rw [Purelib.Data.List.Map.length_map, DyadicPrimitivePaths.dyadicIncrements_length] at equal
    exact equal
  rw [counted, ← path.paired.source.area_eq, ← path.chart.area_eq] at bound
  exact bound.trans_eq (by dsimp only [slope, error]; ring1)

/-- The endpoint error uses the two retained extremes, so it has no segment count multiplier when these polygons are
joined across intervals. -/
theorem total_bound (path : Evaluation.PathData evaluated originals coefficients) :
    Data.Gaussian.Norm.Basic.normSq (path.paired.source.total - path.chart.total) ≤ 40 * sourceTarget *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have first := evaluated.firstSources.evaluated.accurate coefficients
  have last := evaluated.lastSources.evaluated.accurate coefficients
  change Data.Gaussian.Norm.Basic.normSq (Evaluation.firstValue evaluated coefficients - polynomials.value
    coefficients evaluated.first.root.coordinate) ≤ _ at first
  change Data.Gaussian.Norm.Basic.normSq (Evaluation.lastValue evaluated coefficients - polynomials.value
    coefficients evaluated.last.root.coordinate) ≤ _ at last
  rw [← path.first_eq] at first
  rw [← path.last_eq] at last
  have chartTotal := Segment.value_total (polynomials.value coefficients) (Evaluation.path evaluated).segments
    (Evaluation.path evaluated).chain
  rw [path.paired.source_total, path.chart.total_eq, path.paired.chart_eq, chartTotal]
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (path.lastSource - polynomials.value coefficients evaluated.last.root.coordinate)
    (path.firstSource - polynomials.value coefficients evaluated.first.root.coordinate)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct last first)
      (by decide))
  rw [show (path.lastSource - polynomials.value coefficients evaluated.last.root.coordinate) -
    (path.firstSource - polynomials.value coefficients evaluated.first.root.coordinate) =
    path.lastSource - path.firstSource - (polynomials.value coefficients evaluated.last.root.coordinate -
      polynomials.value coefficients evaluated.first.root.coordinate) by ring1] at bound
  exact bound.trans_eq (by ring1)

end PathData
end Plan.Evaluation
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArea
