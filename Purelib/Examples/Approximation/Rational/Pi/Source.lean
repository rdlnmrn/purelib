module

public import Purelib.Approximation.Rational.Pi.Source
public import Purelib.Approximation.Gaussian.Pi.Integral
public import Purelib.Approximation.Gaussian.Pi.Polygon
public import Purelib.Approximation.Gaussian.Pi.Comparison
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Examples.Approximation.Rational.Pi.Source

open Purelib.Approximation.Rational.Pi
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Pi
open Purelib.Integration
open Purelib.Data.Rat

/-- A coarse positive-width request, retaining its actual circle-source frontier. -/
@[expose] public def coarse : SourceFrontier.Continuous.Result Source.modulus :=
  Source.producer.request ⟨16, by decide⟩

/-- The source points retained by the original coarse frontier, in cell order. -/
@[expose] public def retainedReadings := coarse.frontier.cells.map (fun cell => cell.item)

/-- A second request uses the retained coarse readings in the original cached producer. -/
@[expose] public def cached : SourceFrontier.Continuous.Result Source.modulus :=
  Source.producer.requestCached retainedReadings ⟨8, by decide⟩

/-- The two actual answers satisfy the common-refinement comparison. -/
public theorem answers_close : Fraction.abs (coarse.answer - cached.answer) <
    coarse.preparation.request.tolerance + cached.preparation.request.tolerance :=
  Purelib.Approximation.Rational.Pi.Source.answers_close coarse cached

/-- The original initial source-frontier history used by the coherent Gaussian name. -/
@[expose] public def initialHistory : Source.boundProcess.State := Source.boundProcess.initial

/-- A positive squared request refines the retained initial source history. -/
@[expose] public def firstHistory : Source.boundProcess.State :=
  Integral.process.refine initialHistory 4 (by decide)

/-- A second independent squared request starts from the same original history. -/
@[expose] public def secondHistory : Source.boundProcess.State :=
  Integral.process.refine initialHistory 2 (by decide)

/-- The two actual histories have overlapping source-linked integral bounds. -/
public theorem history_overlap :
    (Source.boundProcess.bound firstHistory).Overlaps (Source.boundProcess.bound secondHistory) :=
  Integral.bounds_overlap firstHistory secondHistory

/-- The two-cell uniform frontier with exact circle-source endpoint bounds. -/
@[expose] public def endpointFrontier : SourceFrontier Source.value := Endpoint.frontier 1

/-- The first history and a reading from the two-cell frontier pay both actual widths. -/
public theorem endpoint_answer_close (reading : Fraction.Rational)
    (inside : (integralBound endpointFrontier.cells).Contains reading) :
    Fraction.abs (Integral.answer firstHistory - reading) ≤
      (Source.boundProcess.bound firstHistory).width + (integralBound endpointFrontier.cells).width :=
  Integral.answer_endpoint_difference_le firstHistory 1 reading inside

/-- The actual first-quarter polygon sample at the first dyadic stage. -/
@[expose] public def polygonFirst := Gaussian.Pi.Polygon.sample 0

/-- A finite squared request starting at the third polygon stage. -/
@[expose] public def polygonRefinedStage : Nat :=
  Gaussian.Pi.Polygon.approximation.refineIndex 3 4 (by decide)

/-- The polygon refinement retains its requested starting floor. -/
public theorem polygonRefinedStage_floor : 3 ≤ polygonRefinedStage :=
  Gaussian.Pi.Polygon.approximation.refineIndex_ge 3 4 (by decide)

/-- The selected polygon stage pays the original positive squared request. -/
public theorem polygonRefinedStage_accurate :
    Gaussian.Pi.Polygon.approximation.radiusSq polygonRefinedStage < 4 :=
  Gaussian.Pi.Polygon.approximation.refineIndex_accurate 3 4 (by decide)

/-- Compare the two original pi names after unequal, already-late sampling floors.

The positive squared request is four; the returned certificate retains the
polygon floor five and integral floor three and covers every later pair. -/
@[expose] public def polygonIntegralComparison :=
  Gaussian.Pi.Comparison.polygon_equivalent_integral.compare 5 3 4 (by decide)

/-- The computed polygon comparison index is no earlier than its original floor. -/
public theorem polygonIntegral_left_floor : 5 ≤ polygonIntegralComparison.leftIndex :=
  polygonIntegralComparison.left_ge

/-- The computed integral comparison index is no earlier than its original floor. -/
public theorem polygonIntegral_right_floor : 3 ≤ polygonIntegralComparison.rightIndex :=
  polygonIntegralComparison.right_ge

end Purelib.Examples.Approximation.Rational.Pi.Source
