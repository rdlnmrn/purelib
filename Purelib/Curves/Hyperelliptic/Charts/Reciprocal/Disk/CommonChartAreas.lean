module
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! Count-paid full pullback/chart areas. The source tolerance and model
stage are selected from retained endpoint bounds before sampling either cap
polynomial. No endpoint cancellation or closed-path hypothesis is used. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
variable {genus count otherCount depth : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {interval : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval cover otherCover}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth}

namespace SourceVertexRequest
variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {i : Fin (geometry.tail.length + 1)}

/-- Bound both original primitive readings using their retained denominator sample bounds and coefficient ceilings. -/
@[expose] def magnitude (vertex : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceVertexRequest regular
  geometry target floor i) : Coordinate :=
  (Gaussian.Name.Sampling.approximation (geometry.vertices.get
    i).first.coordinates.coordinate.prepared.denominator.name).centerBound *
      vertex.firstBounds.coefficientUpper +
    (Gaussian.Name.Sampling.approximation (geometry.vertices.get
      i).second.coordinates.coordinate.prepared.denominator.name).centerBound *
      vertex.secondBounds.coefficientUpper

/-- The retained paired primitive-reading magnitude is nonnegative. -/
theorem magnitude_nonnegative (vertex : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceVertexRequest
  regular geometry target floor i) : 0 ≤
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude vertex :=
  add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
    vertex.firstBounds.coefficientUpper_nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
      vertex.secondBounds.coefficientUpper_nonnegative)

/-- Reissue both endpoint comparisons at the supplied positive target while retaining the original coefficient bounds
and stage floor. -/
@[expose] def withTarget (vertex : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceVertexRequest regular
  geometry target floor i)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceVertexRequest regular geometry requested floor i :=
  ⟨vertex.firstBounds, vertex.secondBounds,
    Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request.build vertex.firstBounds requested positive floor,
    Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request.build vertex.secondBounds requested positive floor⟩

end SourceVertexRequest

namespace SourceChartRequest
variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Sum the original paired-reading magnitude bounds over all retained chart vertices. -/
@[expose] def magnitude (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor) : Coordinate :=
  FiniteSum.Fin.sumFin (fun i => (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude
    (prepared.vertices.get i)))

/-- The common magnitude bound summed over the retained chart vertices is nonnegative. -/
theorem magnitude_nonnegative (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor) : 0 ≤
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) :=
  FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun i =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude_nonnegative
    (prepared.vertices.get i)))

/-- Retarget every original vertex comparison and recompute the shared model and reading stage maxima. -/
@[expose] def withTarget (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry requested floor :=
  let vertices := Data.Vector.DependentVector.ofFn (fun i =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.withTarget (prepared.vertices.get i)
    requested positive))
  ⟨vertices, vertices.maximum (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceModelWeight regular
    geometry), rfl,
    vertices.maximum (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceReadingWeight regular geometry),
      rfl⟩

/-- Retargeting the original vertex comparisons preserves their retained magnitude bound. -/
theorem withTarget_magnitude (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget prepared requested positive)
      = (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) := by
  apply FiniteSum.Fin.sumFin_congr
  intro i
  change Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude
    ((Data.Vector.DependentVector.ofFn (fun j =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.withTarget (prepared.vertices.get j)
    requested positive))).get i) = _
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

variable {index : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}

/-- Both original primitive values at every retained chart vertex satisfy the prepared common magnitude bound. -/
theorem original_bounded (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor)
    {chartTarget : Normalization.InverseRootPolynomial.Coordinate} {chartFloor stage : Nat}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest interval sample otherSample geometry
      chartTarget chartFloor}
    (i : Fin (geometry.tail.length + 1))
    (reading : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (request.entries.get i) stage) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (reading.originalPoint)
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) := by
  let vertex := prepared.vertices.get i
  have firstBound : Data.Gaussian.Norm.Basic.normSq reading.first.value ≤
      (Gaussian.Name.Sampling.approximation (geometry.vertices.get
        i).first.coordinates.coordinate.prepared.denominator.name).centerBound *
        vertex.firstBounds.coefficientUpper := by
    rw [reading.first.value_eq, Gaussian.Norm.Basic.normSq_mul, reading.first.coordinate_eq]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct ((Gaussian.Name.Sampling.approximation _).sample_bounded stage)
      (vertex.firstBounds.coefficient_le (request.entries.get i).first)
      (Gaussian.Norm.Basic.normSq_nonneg _) (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
  have secondBound : Data.Gaussian.Norm.Basic.normSq reading.originalOther.value ≤
      (Gaussian.Name.Sampling.approximation (geometry.vertices.get
        i).second.coordinates.coordinate.prepared.denominator.name).centerBound *
        vertex.secondBounds.coefficientUpper := by
    rw [reading.originalOther.value_eq, Gaussian.Norm.Basic.normSq_mul, reading.originalOther.coordinate_eq]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct ((Gaussian.Name.Sampling.approximation _).sample_bounded stage)
      (vertex.secondBounds.coefficient_le (request.entries.get i).originalOther)
      (Gaussian.Norm.Basic.normSq_nonneg _) (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
  have sumBound : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude vertex ≤
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) :=
    FiniteSum.Fin.Rational.entry_le_sum _ (fun j =>
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceVertexRequest.magnitude_nonnegative
      (prepared.vertices.get j))) i
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstBound secondBound
  exact ⟨firstBound.trans ((le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
      vertex.secondBounds.coefficientUpper_nonnegative)).trans sumBound),
    secondBound.trans ((le_add_of_nonneg_left
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Name.Sampling.approximation _).centerBound_nonneg
      vertex.firstBounds.coefficientUpper_nonnegative)).trans sumBound)⟩

variable {firstComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell}
  {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
  {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor}
    {requested : Normalization.InverseRootPolynomial.Coordinate}

/-- Read the original paired pullback polynomial values from the retained vertex evaluations. -/
@[expose] def Evaluation.pullbackValues (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (i : Fin (geometry.tail.length + 1)) : PrimitivePoint :=
  ⟨(evaluated.pullbacks.get i).firstValue, (evaluated.pullbacks.get i).secondValue⟩

/-- The centered finite polygon sample over the original retained pullback vertex values. -/
@[expose] def Evaluation.PullbackSample (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
  :=
  Periods.CenteredBilinearPath.Sample
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated)

/-- Evaluate the original pair of pullback polynomials at the inverse original parent-edge coordinate. -/
@[expose] def pullbackPolynomialValues (first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison
  sample)
    (second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample) (parameter :
      Normalization.InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  ⟨first.pullback.value.eval (parent.edge.point parameter)⁻¹,
    second.pullback.value.eval (parent.edge.point parameter)⁻¹⟩

/-- Scalar readbacks identify the cached polygon with the complete original
dyadic polynomial trace, including every intermediate vertex. -/
theorem Evaluation.pullback_area_eq (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (pullback : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample
      evaluated) :
    pullback.originalArea = Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second)
      depth interval.edge.left.parameter interval.edge.right.parameter := by
  have pointEq (i : Fin (geometry.tail.length + 1)) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated i =
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i)
        :=
    congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (evaluated.pullbacks.get i).first_eq (evaluated.pullbacks.get
      i).second_eq
  rw [pullback.originalArea_eq]
  have indexedEq : Periods.CenteredBilinearPath.area
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated) =
      Periods.CenteredBilinearPath.area (fun i =>
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i))
        :=
    FiniteSum.Fin.sumFin_congr (fun edge =>
      congrArg₂ Topology.Polygon.Stokes.edgeArea (pointEq edge.castSucc) (pointEq edge.succ))
  exact indexedEq.trans ((Path.Dyadic.DyadicTrace.indexed_area
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second)
      interval.edge.left.parameter geometry.tail).trans
      ((congrArg (Path.Dyadic.DyadicTrace.areaFrom
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second)
          interval.edge.left.parameter) geometry.tail_eq).trans
          (Path.Dyadic.DyadicTrace.tail_area
            (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first
              second) depth interval.edge.left.parameter interval.edge.right.parameter)))

/-- The cached centered pullback area equals the complete original dyadic polynomial trace centered at its initial
vertex. -/
theorem Evaluation.pullback_centered_eq (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (pullback : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample
      evaluated) :
    pullback.centeredArea = Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (fun parameter =>
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        parameter).sub
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
          interval.edge.left.parameter))
      depth interval.edge.left.parameter interval.edge.right.parameter := by
  let values := fun parameter =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
    parameter).sub
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
      interval.edge.left.parameter)
  have pointEq (i : Fin (geometry.tail.length + 1)) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated i =
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i)
        :=
    congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (evaluated.pullbacks.get i).first_eq (evaluated.pullbacks.get
      i).second_eq
  have centeredEq (i : Fin (geometry.tail.length + 1)) : pullback.centered i = values
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i) :=
    (pullback.centered_eq i).trans (congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.sub (pointEq i) (pointEq 0))
  rw [pullback.centeredArea_eq]
  have indexedEq : Periods.CenteredBilinearPath.area (fun i => pullback.centered i) =
      Periods.CenteredBilinearPath.area (fun i => values
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i))
        :=
    FiniteSum.Fin.sumFin_congr (fun edge =>
      congrArg₂ Topology.Polygon.Stokes.edgeArea (centeredEq edge.castSucc) (centeredEq edge.succ))
  exact indexedEq.trans ((Path.Dyadic.DyadicTrace.indexed_area
    values interval.edge.left.parameter geometry.tail).trans
      ((congrArg (Path.Dyadic.DyadicTrace.areaFrom values interval.edge.left.parameter)
        geometry.tail_eq).trans
          (Path.Dyadic.DyadicTrace.tail_area values depth interval.edge.left.parameter interval.edge.right.parameter)))

/-- The retained vertex comparisons bound the complete pullback-area error with its exact edge-count-squared factor. -/
theorem Evaluation.pullback_area_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (pullback : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample
      evaluated) (small : 16 * target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (pullback.originalArea - evaluated.area.evaluated.original.originalArea) ≤
      (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (32 * (4 *
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1) * (16 *
        target)) := by
  have positive : 0 < target := (prepared.vertices.get 0).first.positive
  have magnitudeLe : (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) ≤ 4 *
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) :=
    (by ring1 : (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) = 1 *
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared)).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide)
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative prepared))
  have errorLe : target ≤ 16 * target :=
    (by ring1 : target = 1 * target).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) positive.le)
  have bounded (i : Fin (geometry.tail.length + 1)) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
        evaluated.area.evaluated.readings i)) (4 *
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared)) := by
    have original := (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.original_bounded
      prepared) i (evaluated.area.evaluated.readings.get i)
    exact ⟨original.1.trans magnitudeLe, original.2.trans magnitudeLe⟩
  have accurate (i : Fin (geometry.tail.length + 1)) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
        i).sub
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
          evaluated.area.evaluated.readings i))) (16 * target) :=
    by
      have left := (evaluated.pullbacks.get i).first_close.le
      have right := (evaluated.pullbacks.get i).second_close.le
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
      exact ⟨left.trans errorLe, right.trans errorLe⟩
  rw [pullback.originalArea_eq, evaluated.area.evaluated.original.originalArea_eq]
  unfold Periods.CenteredBilinearPath.area
  rw [← FiniteSum.Fin.sumFin_sub]
  exact Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ _ (fun edge =>
    Topology.Surface.Boundary.HandleAreaBounds.PrimitivePoint.area_difference_bound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative prepared))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small
      (bounded edge.castSucc) (bounded edge.succ) (accurate edge.castSucc) (accurate edge.succ))

/-- Subtracting two paired readings with a common squared-norm bound gives four times that bound. -/
private theorem bounded_sub {first last : Topology.Polygon.Stokes.PrimitivePoint} {bound :
  Normalization.InverseRootPolynomial.Coordinate}
    (left : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (first) bound) (right :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (last) bound) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((first.sub last)) (4 * bound) := by
  have firstScalar := Gaussian.Norm.Bounds.normSq_sub_le_two first.left last.left
  have secondScalar := Gaussian.Norm.Bounds.normSq_sub_le_two first.right last.right
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at firstScalar secondScalar
  exact ⟨firstScalar.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left.1
      right.1) (by decide)).trans_eq (by ring1)),
    secondScalar.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left.2
      right.2) (by decide)).trans_eq (by ring1))⟩

/-- The original centered pullback-area error satisfies the retained edge-count-squared bound. -/
theorem Evaluation.pullback_centered_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (pullback : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample
      evaluated) (small : 16 * target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (pullback.centeredArea - evaluated.area.evaluated.original.centeredArea) ≤
      (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (32 * (4 *
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1) * (16 *
        target)) := by
  have positive : 0 < target := (prepared.vertices.get 0).first.positive
  have errorLe : 4 * target ≤ 16 * target := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel) positive.le
  have pointError (i : Fin (geometry.tail.length + 1)) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
        i).sub
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
          evaluated.area.evaluated.readings i))) target :=
    by
      have left := (evaluated.pullbacks.get i).first_close.le
      have right := (evaluated.pullbacks.get i).second_close.le
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
      exact ⟨left, right⟩
  have bound := pullback.comparison evaluated.area.evaluated.original
    (magnitude := 4 * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared))
      (error := 16 * target)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative prepared))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) small (fun i => by
      rw [evaluated.area.evaluated.original.centered_eq]
      exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.bounded_sub
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.original_bounded prepared) i
        (evaluated.area.evaluated.readings.get i))
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.original_bounded prepared) 0
          (evaluated.area.evaluated.readings.get 0))) (fun i => by
      rw [pullback.centered_eq, evaluated.area.evaluated.original.centered_eq]
      have identity :
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
        i).sub (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues
        evaluated 0)).sub
          ((Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
            evaluated.area.evaluated.readings i).sub
            (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
              evaluated.area.evaluated.readings 0)) =
          ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
            i).sub (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
            evaluated.area.evaluated.readings i)).sub
            ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues
              evaluated 0).sub (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.originalValues
              evaluated.area.evaluated.readings 0)) := by
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> simp only
          [Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1
      rw [identity]
      have difference := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.bounded_sub
        (pointError i) (pointError 0)
      exact ⟨difference.1.trans errorLe, difference.2.trans errorLe⟩)
  have identity : (pullback.originalArea - evaluated.area.evaluated.original.originalArea) -
      (pullback.endpoint - evaluated.area.evaluated.original.endpoint) =
      pullback.centeredArea - evaluated.area.evaluated.original.centeredArea := by
    rw [pullback.decomposition, evaluated.area.evaluated.original.decomposition]; ring1
  rw [identity] at bound
  exact bound

/-- The same retained vertex comparisons control increments from the first
vertex, including the terminal increment used when joining chart blocks. -/
theorem Evaluation.centered_point_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (pullback : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample
      evaluated) (i : Fin (geometry.tail.length + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (((pullback.centered i).sub
      (evaluated.area.evaluated.chart.centered i)))
      (8 * (target + 4 * evaluated.area.budget.tolerance)) := by
  rw [pullback.centered_eq, evaluated.area.evaluated.chart.centered_eq]
  have identity : ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues
    evaluated i).sub (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues
    evaluated 0)).sub
      ((Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.chartValues
        evaluated.area.evaluated.readings i).sub
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.chartValues
          evaluated.area.evaluated.readings 0)) =
      ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
        i).sub (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.chartValues
        evaluated.area.evaluated.readings i)).sub
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues evaluated
          0).sub (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.chartValues
          evaluated.area.evaluated.readings 0)) := by
    apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> simp only [Topology.Polygon.Stokes.PrimitivePoint.sub,
      -eq_self, -iff_self] <;> ring1
  rw [identity]
  have bound := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.bounded_sub
    (evaluated.pullbacks.get i).chart_bound (evaluated.pullbacks.get 0).chart_bound
  exact ⟨bound.1.trans_eq (by ring1), bound.2.trans_eq (by ring1)⟩

/-- Every retained centered chart point is bounded by the prepared original magnitude and chart tolerance. -/
theorem Evaluation.centered_chart_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (i : Fin (geometry.tail.length + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((evaluated.area.evaluated.chart.centered i))
      (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 4 *
        evaluated.area.budget.tolerance)) := by
  have scalar (original changed : Normalization.InverseRootPolynomial.Gaussian) (left : Gaussian.Basic.Canonical.normSq
    original ≤ (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared))
      (right : Gaussian.Basic.Canonical.normSq (original - changed) ≤ 4 * evaluated.area.budget.tolerance) :
      Gaussian.Basic.Canonical.normSq changed ≤ 2 *
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 4 *
        evaluated.area.budget.tolerance) := by
    rw [show changed = original - (original - changed) by ring1]
    have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two original (original - changed)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
    exact estimate.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left
        right) (by decide))
  have point (j : Fin (geometry.tail.length + 1)) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.chartValues
        evaluated.area.evaluated.readings j))
        (2 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 4 *
          evaluated.area.budget.tolerance)) := by
    have original := (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.original_bounded
      prepared) j (evaluated.area.evaluated.readings.get j)
    have error := (evaluated.area.evaluated.readings.get j).point_error
    exact ⟨scalar _ _ original.1 error.1, scalar _ _ original.2 error.2⟩
  rw [evaluated.area.evaluated.chart.centered_eq]
  have bound := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.bounded_sub (point i) (point 0)
  exact ⟨bound.1.trans_eq (by ring1), bound.2.trans_eq (by ring1)⟩

end SourceChartRequest

variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Exact identity between the refined request and retargeting the original prepared vertices at the retained budget
tolerance. -/
@[expose] def SourceRetargetReadback (prepared :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor)
    {magnitude requested : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.AreaBudget geometry.tail.length
      magnitude (requested / 4))
    (refined : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry
      budget.tolerance floor) : Prop :=
  refined = Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget prepared
    budget.tolerance budget.positive

set_option genInjectivity false in
/-- A count-paid comparison request for the full original pullback and chart areas.

Retain the prepared magnitude, positive requested tolerance and exact retargeted vertex request before acquiring either
polynomial sample. -/
structure SourceAreaRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor) (requested : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original requested area tolerance is strictly positive. -/ positive : 0 < requested
  /-- The retained common bound on both original primitive-reading components. -/ magnitude :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The retained magnitude is exactly the original prepared vertex-bound sum. -/ magnitude_eq : magnitude =
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared)
  /-- The edge-count-paid area budget for one quarter of the original request. -/ budget :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.AreaBudget geometry.tail.length magnitude
    (requested / 4)
  /-- The original vertex requests retargeted to the retained paid tolerance. -/ refined :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry budget.tolerance floor
  /-- The retained refined request is exactly the original request's checked retargeting. -/ refined_eq :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceRetargetReadback prepared budget refined

constructive_injectivity SourceAreaRequest

namespace SourceAreaRequest

/-- Prepare the original vertex comparisons at a count-paid tolerance covering one quarter of the requested area error.
-/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared requested :=
  let magnitude := (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared)
  let budget := Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.AreaBudget.build
    geometry.tail.length magnitude (requested / 4)
    ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative prepared))
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  ⟨positive, magnitude, rfl, budget, Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget
    prepared budget.tolerance budget.positive, rfl⟩

variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target
  floor} {requested : Normalization.InverseRootPolynomial.Coordinate}
  {index : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {firstComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell}

set_option genInjectivity false in
/-- The original retained pullback polygon and chart evaluation with full and centered area-error certificates. -/
structure Evaluation (request : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared
  requested)
    (first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample)
    (second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample) where
  /-- The actual retained evaluation of the original refined source and paired chart requests. -/ retained :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation request.refined first second
    (requested / 4)
  /-- The centered polygon over the exact retained pullback values. -/ pullback :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.PullbackSample retained
  /-- The original pullback and original-reading polygon areas differ by less than one quarter of the request. -/
    pullback_close : Data.Gaussian.Norm.Basic.normSq (pullback.originalArea -
    retained.area.evaluated.original.originalArea) < requested / 4
  /-- The original full pullback and chart polygon areas differ by less than the requested tolerance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (pullback.originalArea - retained.area.evaluated.chart.originalArea) < requested
  /-- The original centered pullback and chart polygon areas differ by less than the requested tolerance. -/
    centered_bounded : Data.Gaussian.Norm.Basic.normSq (pullback.centeredArea -
    retained.area.evaluated.chart.centeredArea) < requested

constructive_injectivity Evaluation

/-- Keep the original dyadic pullback polygon and its endpoint term, and
certify its full area against the paired chart polygon at the requested error. -/
@[expose] def evaluate (request : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared
  requested)
    (first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample)
    (second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample)
    (modelLater : request.refined.index ≤ index) (readingFloor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second := by
  let retained := request.refined.evaluate first second modelLater (requested / 4)
    (Fraction.Order.Field.div_pos_direct request.positive (by decide)) readingFloor
  let pullback := Periods.CenteredBilinearPath.Sample.build
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues retained)
  have magnitudeEq : (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
    request.refined) = request.magnitude := by
    rw [show request.refined = Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget
      prepared request.budget.tolerance request.budget.positive from request.refined_eq]
    exact (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget_magnitude prepared _
      _).trans request.magnitude_eq.symm
  have pullbackClose : Data.Gaussian.Norm.Basic.normSq (pullback.originalArea -
    retained.area.evaluated.original.originalArea) < requested / 4 := by
    have bound :=
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_area_bound retained)
      pullback request.budget.small
    rw [magnitudeEq] at bound
    exact bound.trans_lt request.budget.paid
  have chartClose : Data.Gaussian.Norm.Basic.normSq (retained.area.evaluated.original.originalArea -
    retained.area.evaluated.chart.originalArea) < requested / 4 := by
    rw [show retained.area.evaluated.original.originalArea - retained.area.evaluated.chart.originalArea =
      -(retained.area.evaluated.chart.originalArea - retained.area.evaluated.original.originalArea) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    exact retained.area.bounded
  have close := (Gaussian.Norm.Bounds.normSq_sub_le_via pullback.originalArea
    retained.area.evaluated.original.originalArea
    retained.area.evaluated.chart.originalArea).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct pullbackClose chartClose))
  have paid : 2 * (requested / 4 + requested / 4) = requested :=
    (by ring1 : 2 * (requested / 4 + requested / 4) = requested / 4 * 4).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have centeredPullback : Data.Gaussian.Norm.Basic.normSq (pullback.centeredArea -
    retained.area.evaluated.original.centeredArea) < requested / 4 := by
    have bound :=
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_centered_bound
      retained) pullback request.budget.small
    rw [magnitudeEq] at bound
    exact bound.trans_lt request.budget.paid
  have centeredChart : Data.Gaussian.Norm.Basic.normSq (retained.area.evaluated.original.centeredArea -
    retained.area.evaluated.chart.centeredArea) < requested / 4 := by
    have bound := retained.area.corrected_bounded
    have identity : (retained.area.evaluated.chart.originalArea - retained.area.evaluated.original.originalArea) -
        (retained.area.evaluated.chart.endpoint - retained.area.evaluated.original.endpoint) =
        -(retained.area.evaluated.original.centeredArea - retained.area.evaluated.chart.centeredArea) := by
      rw [retained.area.evaluated.chart.decomposition, retained.area.evaluated.original.decomposition]; ring1
    rw [identity, Gaussian.Norm.Basic.normSq_neg] at bound
    exact bound
  have centeredClose := (Gaussian.Norm.Bounds.normSq_sub_le_via pullback.centeredArea
    retained.area.evaluated.original.centeredArea
    retained.area.evaluated.chart.centeredArea).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct centeredPullback centeredChart))
  exact ⟨retained, pullback, pullbackClose, close.trans_eq paid, centeredClose.trans_eq paid⟩

/-- The complete original dyadic pullback trace is within the requested error of the retained full chart polygon. -/
theorem Evaluation.dyadic_bounded {request : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest
  prepared requested}
    {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
    {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first
      second) :
    Data.Gaussian.Norm.Basic.normSq (Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second)
      depth interval.edge.left.parameter interval.edge.right.parameter -
        evaluated.retained.area.evaluated.chart.originalArea) < requested := by
  rw [← (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_area_eq
    evaluated.retained) evaluated.pullback]
  exact evaluated.bounded

/-- The centered original dyadic pullback trace is within the requested error of the retained centered chart polygon. -/
theorem Evaluation.centered_dyadic_bounded {request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared requested}
    {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
    {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first
      second) :
    Data.Gaussian.Norm.Basic.normSq (Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (fun parameter =>
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        parameter).sub
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
          interval.edge.left.parameter))
      depth interval.edge.left.parameter interval.edge.right.parameter -
        evaluated.retained.area.evaluated.chart.centeredArea) < requested := by
  rw [← (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_centered_eq
    evaluated.retained) evaluated.pullback]
  exact evaluated.centered_bounded

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared
  requested}
  {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
  {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}

set_option genInjectivity false in
/-- Endpoint data for joining the actual paired chart path. Both increments
are read from cached centered vectors; no root or polynomial is resampled. -/
structure Evaluation.Increments (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second) where
  /-- The original terminal centered pullback increment. -/ pullback : Topology.Polygon.Stokes.PrimitivePoint
  /-- The retained pullback increment is the exact last cached centered pullback vertex. -/ pullback_eq : pullback =
    evaluated.pullback.centered (Fin.last geometry.tail.length)
  /-- The original terminal centered chart increment. -/ chart : Topology.Polygon.Stokes.PrimitivePoint
  /-- The retained chart increment is the exact last cached centered chart vertex. -/ chart_eq : chart =
    evaluated.retained.area.evaluated.chart.centered (Fin.last geometry.tail.length)
  /-- The retained squared-norm error for the original endpoint increment difference. -/ error :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The retained error is exactly eight times the source tolerance plus four chart tolerances. -/ error_eq : error = 8
    * (request.budget.tolerance + 4 * evaluated.retained.area.budget.tolerance)
  /-- The original pullback-minus-chart increment satisfies the retained paired squared-norm error. -/ bounded :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((pullback.sub chart)) error

constructive_injectivity Evaluation.Increments

/-- Read the original terminal pullback and chart increments with their retained comparison bound. -/
@[expose] def Evaluation.increments (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second) :
  evaluated.Increments :=
  ⟨evaluated.pullback.centered (Fin.last geometry.tail.length), rfl,
    evaluated.retained.area.evaluated.chart.centered (Fin.last geometry.tail.length), rfl,
    8 * (request.budget.tolerance + 4 * evaluated.retained.area.budget.tolerance), rfl,
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.centered_point_bound
      evaluated.retained) evaluated.pullback (Fin.last geometry.tail.length)⟩

/-- The retained pullback increment is exactly the original polynomial endpoint value minus its initial value. -/
theorem Evaluation.Increments.pullback_readback (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second)
    (increments : evaluated.Increments) :
    increments.pullback =
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
      interval.edge.right.parameter).sub
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        interval.edge.left.parameter) := by
  rw [increments.pullback_eq, evaluated.pullback.centered_eq]
  have pointEq (i : Fin (geometry.tail.length + 1)) :
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullbackValues
    evaluated.retained) i =
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i)
        :=
    congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (evaluated.retained.pullbacks.get i).first_eq
      (evaluated.retained.pullbacks.get i).second_eq
  rw [pointEq, pointEq]
  dsimp only [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter, -eq_self, -iff_self]
  rw [Path.Dyadic.DyadicTrace.indexed_first,
    Path.Dyadic.DyadicTrace.indexed_last, geometry.tail_eq,
    Path.Dyadic.DyadicTrace.tail_terminal]

/-- Appending this actual correction vector restores the pullback total. -/
@[expose] def Evaluation.Increments.connector {evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second}
    (increments : evaluated.Increments) : PrimitivePoint := increments.pullback.sub increments.chart

/-- Appending the original correction vector to the chart increment restores the retained pullback increment. -/
theorem Evaluation.Increments.restored {evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second}
    (increments : evaluated.Increments) : increments.chart.add increments.connector = increments.pullback := by
  apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> simp only [Increments.connector,
    Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1

/-- The exact bilinear edge area between the retained chart and pullback endpoint increments. -/
@[expose] def Evaluation.Increments.connectorArea {evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second}
    (increments : evaluated.Increments) : Gaussian := Topology.Polygon.Stokes.edgeArea increments.chart
      increments.pullback

/-- The endpoint-restoring edge has a computed bound from retained reading
tolerances and the preselected magnitude, independent of any new root read. -/
theorem Evaluation.Increments.connectorArea_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second)
    (increments : evaluated.Increments) :
    Data.Gaussian.Norm.Basic.normSq increments.connectorArea ≤
      4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude request.refined) + 4
        * evaluated.retained.area.budget.tolerance)) * increments.error := by
  have identity : increments.connectorArea = Topology.Polygon.Stokes.edgeArea increments.chart increments.connector :=
    by
    simp only [Increments.connectorArea, Increments.connector, Topology.Polygon.Stokes.edgeArea,
      Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self]
    ring1
  rw [identity]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  apply Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
  · rw [increments.chart_eq]
    exact (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.centered_chart_bound
      evaluated.retained) (Fin.last geometry.tail.length)
  · exact increments.bounded

/-- The retained endpoint increment error is bounded using only the original preparation request. -/
theorem Evaluation.Increments.error_prepared (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second)
    (increments : evaluated.Increments) : increments.error ≤ 40 * ((requested / 4) / 2) := by
  have magnitudeNonnegative : 0 ≤ request.magnitude :=
    ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative prepared)).trans_eq
    request.magnitude_eq.symm
  have source := request.budget.tolerance_le magnitudeNonnegative (Fraction.Order.Field.div_pos_direct request.positive
    (by decide))
  have chartMagnitude : 0 ≤ evaluated.retained.area.magnitude :=
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.magnitude_nonnegative
      evaluated.retained.request).trans_eq
      evaluated.retained.area.magnitude_eq.symm
  have chart := evaluated.retained.area.budget.tolerance_le chartMagnitude (Fraction.Order.Field.div_pos_direct
    request.positive (by decide))
  rw [increments.error_eq]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct source (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      chart (by decide))) (by decide)).trans_eq (by ring1)

/-- The chart-restoring edge is paid using preparation magnitude and the
requested tolerance; neither coefficient depends on the sampled endpoints. -/
theorem Evaluation.Increments.connectorArea_prepared (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation request first second)
    (increments : evaluated.Increments) :
    Data.Gaussian.Norm.Basic.normSq increments.connectorArea ≤
      4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude request.refined) +
        1)) * (40 * ((requested / 4) / 2)) := by
  have small : 4 * evaluated.retained.area.budget.tolerance ≤ 1 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (4 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      evaluated.retained.area.budget.positive.le).trans evaluated.retained.area.budget.small
  have errorNonnegative : 0 ≤ increments.error :=
    (Gaussian.Basic.Canonical.normSq_nonneg _).trans increments.bounded.1
  have magnitude := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (le_refl
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude request.refined)) small) (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8))
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
  have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct magnitude errorNonnegative
  have second := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Increments.error_prepared evaluated
    increments)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8)
      (add_nonneg (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative
        request.refined) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1))))
  exact (Increments.connectorArea_bound evaluated increments).trans (first.trans second)

end SourceAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
