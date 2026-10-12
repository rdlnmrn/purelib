module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

/-! Adjacent common-cover charts retain their actual endpoint owners. The
junction is prepared from cached source bounds before either chart is read. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

variable {genus count otherCount depth nextDepth : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
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
  {interval nextInterval : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval cover otherCover}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth}
  {next : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) nextInterval nextDepth}
  {sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {sourceFloor : Nat}

namespace SourceChartRequest

/-- Read the original denominator-name approximation at the last retained chart vertex. -/
@[expose] def lastCoordinateApproximation (geometry :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :=
  Gaussian.Name.Sampling.approximation
    (geometry.vertices.get (Fin.last geometry.tail.length)).first.coordinates.coordinate.prepared.denominator.name

/-- Read the original denominator-name approximation at the first retained chart vertex. -/
@[expose] def firstCoordinateApproximation (geometry :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :=
  Gaussian.Name.Sampling.approximation
    (geometry.vertices.get 0).first.coordinates.coordinate.prepared.denominator.name

set_option genInjectivity false in
/-- A paid radial junction comparison between the original retained neighbouring chart coordinates.

The two-polynomial coefficient bound fixes the scale and comparison budget before either endpoint is read. -/
structure RadialRequest (bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded)
    (owners : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry.Junction geometry next) (target :
      Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained squared-coefficient scale for the original paired radial comparison. -/ scale :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The scale is exactly 512 times the square of the larger original polynomial coefficient bound. -/ scale_eq : scale
    = 512 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)) ^ 2
  /-- The retained radial comparison scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The retained coordinate-comparison tolerance paid by the radial target. -/ budget :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The budget equals the original target divided by the retained scale plus one. -/ budget_eq : budget = target /
    (scale + 1)
  /-- The original two-sided coordinate approximation comparison at the retained floors and paid budget. -/ comparison :
    Gaussian.Equivalence.Comparison
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.lastCoordinateApproximation geometry)
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.firstCoordinateApproximation next)
      floor floor budget
  /-- The common sufficient reading stage of the retained radial comparison. -/ index : Nat
  /-- The stage is exactly the maximum of the original comparison's two retained indices. -/ index_eq : index = max
    comparison.leftIndex comparison.rightIndex

constructive_injectivity RadialRequest

/-- Prepare the radial comparison from the retained original owner equivalence, coefficient bounds and positive target.
-/
@[expose] def RadialRequest.build (bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds
  regular.padded)
    (owners : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry.Junction geometry next) (target :
      Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.RadialRequest bounds owners target
      floor :=
  let scale : Coordinate := 512 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)) ^ 2
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let budget : Coordinate := target / (scale + 1)
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide))
  let comparison := owners.first.coordinate.compare floor floor budget budgetPositive
  ⟨scale, rfl, nonnegative, budget, rfl, comparison, max comparison.leftIndex comparison.rightIndex, rfl⟩

set_option genInjectivity false in
/-- The original paired endpoint owners and three paid comparisons joining neighbouring common-cover charts. -/
structure JunctionRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry sourceTarget sourceFloor)
    (next : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) nextInterval nextDepth)
      (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The actual retained owner junction between the original neighbouring chart geometries. -/ owners :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry.Junction geometry next
  /-- The original first-differential endpoint comparison request. -/ first :
    Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request (prepared.vertices.get (Fin.last
    geometry.tail.length)).firstBounds owners.first target floor
  /-- The original second-differential endpoint comparison request. -/ second :
    Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request (prepared.vertices.get (Fin.last
    geometry.tail.length)).secondBounds owners.second target floor
  /-- The paid radial comparison using the original retained polynomial coefficient bounds. -/ radial :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.RadialRequest first.energyBounds owners
    target floor
  /-- The sufficient common stage for both primitive comparisons and their radial comparison. -/ index : Nat
  /-- The retained stage is exactly the maximum of the three original request stages. -/ index_eq : index = max (max
    first.index second.index) radial.index

constructive_injectivity JunctionRequest

namespace JunctionRequest

/-- Prepare both original primitive comparisons and their radial comparison before selecting the shared maximum stage.
-/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry sourceTarget sourceFloor)
    (next : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) nextInterval nextDepth)
    (adjacent : interval.edge.right.parameter = nextInterval.edge.left.parameter)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
      floor :=
  let owners := geometry.junction next adjacent
  let vertex := prepared.vertices.get (Fin.last geometry.tail.length)
  let first := Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request.build vertex.firstBounds owners.first
    target positive floor
  let second := Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request.build vertex.secondBounds owners.second
    target positive floor
  let radial := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.RadialRequest.build
    first.energyBounds owners target positive floor
  ⟨owners, first, second, radial, max (max first.index second.index) radial.index, rfl⟩

variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry
  sourceTarget sourceFloor}
  {target leftTarget rightTarget : Normalization.InverseRootPolynomial.Coordinate} {floor leftFloor rightFloor index
    leftStage rightStage : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {leftRequest : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest interval sample otherSample geometry
    leftTarget leftFloor}
  {rightRequest : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest nextInterval sample otherSample
    next rightTarget rightFloor}

/-- The paired original values are the readings already owned by the two
paths, even when their area allocators selected different reading stages. -/
theorem original_accurate (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (left : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (leftRequest.entries.get (Fin.last geometry.tail.length)) leftStage)
    (right : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (rightRequest.entries.get 0) rightStage)
    (leftLater : request.index ≤ leftStage) (rightLater : request.index ≤ rightStage) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (right.originalPoint.sub left.originalPoint) target := by
  have firstLeft := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
    (request.index_eq.ge.trans leftLater))
  have firstRight := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
    (request.index_eq.ge.trans rightLater))
  have secondLeft := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
    (request.index_eq.ge.trans leftLater))
  have secondRight := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
    (request.index_eq.ge.trans rightLater))
  constructor
  · change Gaussian.Basic.Canonical.normSq (right.first.value - left.first.value) ≤ target
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    rw [right.first.sample_eq, left.first.sample_eq]
    exact (request.first.accurate _ _ firstLeft firstRight).le
  · change Gaussian.Basic.Canonical.normSq (right.originalOther.value - left.originalOther.value) ≤ target
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    rw [right.originalOther.sample_eq, left.originalOther.sample_eq]
    exact (request.second.accurate _ _ secondLeft secondRight).le

/-- The two original retained endpoint coordinates differ by less than one sixty-fourth of the collar coordinate bound.
-/
theorem coordinate_accurate (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (left : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (leftRequest.entries.get (Fin.last geometry.tail.length)) leftStage)
    (right : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (rightRequest.entries.get 0) rightStage)
    (leftLater : request.index ≤ leftStage) (rightLater : request.index ≤ rightStage) :
    Data.Gaussian.Norm.Basic.normSq (right.first.coordinate - left.first.coordinate) < collar.coordinateBound / 64
      := by
  rw [right.first.coordinate_eq, left.first.coordinate_eq]
  exact request.first.coordinate_accurate
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq.ge.trans
      leftLater)))
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq.ge.trans
      rightLater)))

/-- Three retained Gaussian gap bounds give the original nested two-term squared-norm estimate. -/
private theorem chart_gap {a b c d : Normalization.InverseRootPolynomial.Gaussian} {x y z :
  Normalization.InverseRootPolynomial.Coordinate}
    (first : Data.Gaussian.Norm.Basic.normSq (b - a) ≤ x) (middle : Data.Gaussian.Norm.Basic.normSq (b - c) ≤ y)
    (last : Data.Gaussian.Norm.Basic.normSq (c - d) ≤ z) : Data.Gaussian.Norm.Basic.normSq (a - d) ≤ 2 * (x + 2
      * (y + z)) := by
  have reverse : Data.Gaussian.Norm.Basic.normSq (a - b) = Data.Gaussian.Norm.Basic.normSq (b - a) := by
    rw [show a - b = -(b - a) by ring1, Gaussian.Norm.Basic.normSq_neg]
  have tail := (Gaussian.Norm.Bounds.normSq_sub_le_via b c d).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct middle last) (by decide))
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via a b d).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (reverse.trans_le first) tail) (by decide))

/-- The prepared two-polynomial scale pays the radial cancellation at every
depth, using the original cached coordinates at their independent stages. -/
theorem radial_accurate (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (left : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (leftRequest.entries.get (Fin.last geometry.tail.length)) leftStage)
    (right : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (rightRequest.entries.get 0) rightStage)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (left.first.coordinate * left.first.coordinate))
    (rightInside : regular.padded.Contains (right.first.coordinate * right.first.coordinate))
    (leftLater : request.index ≤ leftStage) (rightLater : request.index ≤ rightStage) (depth : Nat) :
    let values := fun point => (⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.Bilinear.radialArea values depth
      right.first.coordinate -
      RootContinuation.RootRadialGeometry.Bilinear.radialArea values depth left.first.coordinate -
      Topology.Polygon.Stokes.edgeArea (values left.first.coordinate) (values right.first.coordinate)) < target := by
  intro values
  have bound := request.first.energyBounds.paired_radial_connector_bound sample otherSample branch leftInside
    rightInside depth
  rw [← request.radial.scale_eq] at bound
  have leftFloor := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq.ge.trans leftLater)
  have rightFloor := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq.ge.trans rightLater)
  have close : Data.Gaussian.Norm.Basic.normSq (right.first.coordinate - left.first.coordinate) <
    request.radial.budget := by
    rw [show right.first.coordinate - left.first.coordinate = -(left.first.coordinate - right.first.coordinate) by
      ring1,
      Gaussian.Norm.Basic.normSq_neg, left.first.coordinate_eq, right.first.coordinate_eq]
    exact request.radial.comparison.close
      ((Data.Nat.Order.le_max_left _ _).trans (request.radial.index_eq.ge.trans leftFloor))
      ((Data.Nat.Order.le_max_right _ _).trans (request.radial.index_eq.ge.trans rightFloor))
  have positive : 0 < request.radial.scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    request.radial.nonnegative (by decide)
  apply bound.trans_lt
  calc
    _ ≤ (request.radial.scale + 1) * Data.Gaussian.Norm.Basic.normSq (right.first.coordinate -
      left.first.coordinate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
        (Gaussian.Norm.Basic.normSq_nonneg _)
    _ < (request.radial.scale + 1) * request.radial.budget :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    _ = target := by
      rw [request.radial.budget_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- Pay the actual chart connector, including both polynomial-reading
errors and the root-owner gap. -/
theorem chart_accurate (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (left : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (leftRequest.entries.get (Fin.last geometry.tail.length)) leftStage)
    (right : Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest.Evaluation
      (rightRequest.entries.get 0) rightStage)
    (leftLater : request.index ≤ leftStage) (rightLater : request.index ≤ rightStage) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (right.chartPoint.sub left.chartPoint) (2 * (4 * rightTarget + 2 * (target + 4 * leftTarget))) := by
  have gap := request.original_accurate left right leftLater rightLater
  have rightError := right.point_error
  have leftError := left.point_error
  have firstRight := rightError.1
  have secondRight := rightError.2
  have firstLeft := leftError.1
  have secondLeft := leftError.2
  have firstGap := gap.1
  have secondGap := gap.2
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at firstRight secondRight firstLeft secondLeft firstGap secondGap
  have firstScalar := chart_gap firstRight firstGap firstLeft
  have secondScalar := chart_gap secondRight secondGap secondLeft
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
  exact ⟨firstScalar, secondScalar⟩

set_option genInjectivity false in
/-- Both complete original chart acquisitions and their retained primitive, coordinate and chart junction bounds. -/
structure Acquisition (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox) (requested :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original left chart request prepared at the retained junction stage floor. -/ leftRequest :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest interval sample otherSample geometry requested
    request.index
  /-- The original right chart request prepared at the retained junction stage floor. -/ rightRequest :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest nextInterval sample otherSample next requested
    request.index
  /-- The actual acquired left chart area and its retained readings. -/ left :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.RequestedArea leftRequest requested
  /-- The actual acquired right chart area and its retained readings. -/ right :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.RequestedArea rightRequest requested
  /-- The retained original primitive endpoint readings satisfy the paid junction tolerance. -/ original_gap :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
    ((right.evaluated.readings.get 0).originalPoint.sub
      (left.evaluated.readings.get (Fin.last geometry.tail.length)).originalPoint) target
  /-- The retained original coordinate readings satisfy the collar-scaled junction bound. -/ coordinate_gap :
    Data.Gaussian.Norm.Basic.normSq ((right.evaluated.readings.get 0).first.coordinate -
    (left.evaluated.readings.get (Fin.last geometry.tail.length)).first.coordinate) < collar.coordinateBound / 64
  /-- The actual retained chart connector is bounded by its root junction and both polynomial-reading errors. -/
    chart_gap : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
    ((right.evaluated.readings.get 0).chartPoint.sub
      (left.evaluated.readings.get (Fin.last geometry.tail.length)).chartPoint)
      (2 * (4 * right.budget.tolerance + 2 * (target + 4 * left.budget.tolerance)))

constructive_injectivity Acquisition

/-- Acquire each complete chart exactly once, after the root junction floor
has been selected. Each area allocator may independently refine that floor. -/
@[expose] def acquire (request :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest prepared next target
  floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest.JunctionRequest.Acquisition request
      sample otherSample requested := by
  let leftRequest := Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.build geometry.joins
    sample otherSample requested positive request.index
  let rightRequest := Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.ChartPathRequest.build next.joins sample
    otherSample requested positive request.index
  let left := leftRequest.acquireRequestedArea requested positive
  let right := rightRequest.acquireRequestedArea requested positive
  let first := left.evaluated.readings.get (Fin.last geometry.tail.length)
  let last := right.evaluated.readings.get 0
  exact ⟨leftRequest, rightRequest, left, right,
    request.original_accurate first last left.refined.floor_le right.refined.floor_le,
    request.coordinate_accurate first last left.refined.floor_le right.refined.floor_le,
    request.chart_accurate first last left.refined.floor_le right.refined.floor_le⟩

end JunctionRequest
end SourceChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions
