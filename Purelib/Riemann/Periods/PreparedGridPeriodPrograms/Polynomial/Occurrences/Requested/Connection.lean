module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Requested.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Endpoint.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Connection
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Sampling
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid
import Purelib.Curves.Legendre.Periods.Jets.Connection.Matrix
import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Calculus.Linear.Euler
import Purelib.Calculus.Linear.Euler.Blocks
import Purelib.Algebra.Recurrence.Affine.Constant
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

/-! # Canonical-initial connection transport on the retained source endpoint cache

One original source endpoint computation keeps its actual initial vector,
trace and all six-channel caches. A canonical model-selection floor precedes
that computation. Its actual common index then supplies one canonical
vector and one independent canonical-initial trace on the SAME coefficient
grid. Two quarter payments derive the requested final endpoint quadrance.
-/

public section

universe u

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialValues

open Purelib.Data.Nat

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (ParameterRange)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows
  (referenceEulerFactor referenceEulerFactor_nonnegative)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (zipWith_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.LinearAlgebra.Gaussian
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {polynomialFloor : Nat}
    (values : PolynomialValues walk polynomialFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (roots : RootChain (parent :: parents) (ownerName owner) (ownerName owner))
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- Retain the original source endpoint callback and append the actual canonical readings and independent trace.

The shared dependent-tail alias preserves every original source argument
without another callback telescope or context record. Both initial vectors
and traces remain actual independent values with their own factories;
finite inequalities never identify either pair by equality.
-/
abbrev ConnectionEndpointConsumer (direction : Canonical) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart comparisonStart minimum : Nat) (Result : Type u) : Type _ :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  let ceilingNonnegative := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  let amplification := Affine.iterate (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
  (quarter : AccuracyRequest) → quarter.tolerance = request.tolerance / 4 →
  (paid : Selection (2 * amplification * PolynomialWork.errorScale values.1.parents) minimum quarter.tolerance) →
  paid = Selection.build (2 * amplification * PolynomialWork.errorScale values.1.parents)
    paid.scaleNonnegative minimum quarter.tolerance paid.targetPositive →
  Requested.SourceConnectionEndpointConsumerWith.{u}
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (count := 1) (parent := parent) (parents := parents)
    (covered := values.1.sourceCovered same) (chain := values.1.sourceChain same)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := requested) (ranges := ranges) (allocation := allocation) (root := ownerName owner) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) direction quarter spatial
    firstStart lastStart freshStart residualStart comparisonStart paid.stage
    (fun _forcing selection index sourceInitial sourceTrace memberEndpoint =>
      let refinement := 4 ^ selection.stage
      let intervals := coarse * refinement
      let offsets := fun vertex : Fin (intervals + 1) => Sampling.gridOffset intervals vertex direction
      let boundedIndex := fun position : Nat => (⟨min position intervals,
        Nat.lt_succ_of_le (Nat.min_le_right position intervals)⟩ : Fin (intervals + 1))
      let coefficients := fun position =>
        Connection.alongMatrix (parameter + offsets (boundedIndex position)) direction
      (canonical : { vector : Vec Canonical 2 // vector = values.sampleValues index ∧
        amplification * Norm.vector (zipWith (fun first last => first - last) vector sourceInitial) <
          quarter.tolerance }) →
      (canonicalTrace : Vec Canonical 2) →
      canonicalTrace = Euler.trace coefficients (fun _ => 1 / (intervals : Rational)) canonical.val intervals →
      Norm.vector (zipWith (fun first last => first - last) canonicalTrace sourceTrace) ≤
        amplification * Norm.vector (zipWith (fun first last => first - last) canonical.val sourceInitial) →
      Norm.vector (zipWith (fun first last => first - last) canonicalTrace sourceTrace) < quarter.tolerance →
      Norm.vector (zipWith (fun first last => first - last) memberEndpoint canonicalTrace) < request.tolerance → Result)

/-- Compute the requested canonical-initial endpoint while retaining the SAME original source endpoint construction.

The original model Selection pays a quarter-target initial comparison
before its stage is supplied as the original source constructor's minimum.
That constructor independently pays its quarter-target endpoint request.
At the actual common index, one canonical read and one new Euler trace
keep the original source trace untouched. The original strip bounds every
coefficient; finite trace stability and the vector triangle inequality
derive the final strict target without a growth, defect or error premise.
-/
def withConnectionEndpoint (direction : Canonical) (moving : direction ≠ 0)
    (directionAdmitted : Norm.Basic.normSq direction ≤ allocation.bound) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart comparisonStart minimum : Nat) {Result : Type u}
    (consume : values.ConnectionEndpointConsumer same requested ranges allocation roots widths
      targetCurrent targetFloor targetRootStage direction request spatial
      firstStart lastStart freshStart residualStart comparisonStart minimum Result) : Result :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  have ceilingNonnegative : 0 ≤ ceiling := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  let amplification := Affine.iterate (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
  have amplificationNonnegative : 0 ≤ amplification :=
    Affine.iterate_nonnegative (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
      (by decide +kernel) (fun _ _ => by decide +kernel) (fun _ _ => by decide +kernel)
  let quarter : AccuracyRequest := ⟨request.tolerance / 4, Data.Rat.Bounds.Quarter.quarter_pos request.positive⟩
  let paid := values.sourceModelSelection amplification amplificationNonnegative minimum quarter
  Requested.withSourceConnectionEndpoint
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (count := 1) (parent := parent) (parents := parents)
    (covered := values.1.sourceCovered same) (chain := values.1.sourceChain same)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := requested) (ranges := ranges) (allocation := allocation) (root := ownerName owner) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage)
    direction moving directionAdmitted quarter spatial
    firstStart lastStart freshStart residualStart comparisonStart paid.val.stage
    (fun completed completedFactory actual actualFactory jetFactory forcing forcingTolerance
        comparison comparisonFactory selection selectionFactory positiveCount admitted members membersFactory
        unit nonzero scaled origin positive edges edgesFactory index indexFactory sampled sampledFactory
        sourceInitial initialFactory sourceTrace sourceTraceFactory blockBound initialBound sourcePaid =>
      let refinement := 4 ^ selection.stage
      have refinementPositive : 0 < refinement := Nat.pow_pos (by decide +kernel)
      let intervals := coarse * refinement
      let offsets := fun vertex : Fin (intervals + 1) => Sampling.gridOffset intervals vertex direction
      let boundedIndex := fun position : Nat => (⟨min position intervals,
        Nat.lt_succ_of_le (Nat.min_le_right position intervals)⟩ : Fin (intervals + 1))
      let coefficients := fun position =>
        Connection.alongMatrix (parameter + offsets (boundedIndex position)) direction
      have after : paid.val.stage ≤ index :=
        ((Order.le_max_left paid.val.stage comparison.stage).trans
          (Order.le_max_left (Nat.max paid.val.stage comparison.stage)
            (Requested.samplingFloor (parameter := parameter) (frame := frame)
              (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
              (parent := parent) (parents := parents)
              (covered := values.1.sourceCovered same) (chain := values.1.sourceChain same)
              (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
              (source := requested) (ranges := ranges) (allocation := allocation)
              (root := ownerName owner) (roots := roots)
              (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
              (targetRootStage := targetRootStage) (intervals := intervals) (residualStart := residualStart)
              offsets admitted members (fun _ => 1 / (intervals : Rational)) edges))).trans_eq
          indexFactory.symm
      let canonical := values.readSource (parameter := parameter) (frame := frame) (walk := walk)
        (parent := parent) (parents := parents) same requested completed actual.1 jetFactory
        amplification amplificationNonnegative quarter paid.val index after sourceInitial initialFactory
      let canonicalTrace := Euler.trace coefficients (fun _ => 1 / (intervals : Rational)) canonical.val intervals
      have canonicalTraceFactory : canonicalTrace =
          Euler.trace coefficients (fun _ => 1 / (intervals : Rational)) canonical.val intervals := rfl
      have bounded (position : Nat) (_before : position < intervals) :
          Norm.matrix (coefficients position) ≤ ceiling :=
        Connection.alongMatrix_le (ParameterClearance.ofFrame frame) (offsets (boundedIndex position)) direction
          (allocation.parameter_admitted _ (admitted (boundedIndex position)))
      have originalDifference := Euler.trace_difference_blocks_le (size := 2)
        coefficients canonical.val sourceInitial
        ceiling ceilingNonnegative refinement refinementPositive bounded
      have difference : Norm.vector (zipWith (fun first last => first - last) canonicalTrace sourceTrace) ≤
          amplification * Norm.vector (zipWith (fun first last => first - last) canonical.val sourceInitial) :=
        (congrArg₂ (fun first last : Vec Canonical 2 =>
          Norm.vector (zipWith (fun first last => first - last) first last))
          canonicalTraceFactory sourceTraceFactory).trans_le
          originalDifference
      have differencePaid := difference.trans_lt canonical.property.2
      have reversed : Norm.vector (zipWith (fun first last => first - last) sourceTrace canonicalTrace) =
          Norm.vector (zipWith (fun first last => first - last) canonicalTrace sourceTrace) := by
        unfold Norm.vector
        apply sumFin_congr
        intro coordinate
        have negated : sourceTrace coordinate - canonicalTrace coordinate =
            -(canonicalTrace coordinate - sourceTrace coordinate) := by ring1
        exact (congrArg Norm.Basic.normSq (zipWith_apply _ _ _ coordinate)).trans
          (((congrArg Norm.Basic.normSq negated).trans (Norm.Basic.normSq_neg _)).trans
            (congrArg Norm.Basic.normSq (zipWith_apply _ _ _ coordinate)).symm)
      let memberEndpoint := sampled ⟨intervals, Nat.lt_succ_self intervals⟩
      let firstError := zipWith (fun first last => first - last) memberEndpoint sourceTrace
      let lastError := zipWith (fun first last => first - last) sourceTrace canonicalTrace
      have combined : Norm.vector (zipWith (fun first last => first - last) memberEndpoint canonicalTrace) =
          Norm.vector (zipWith (fun first last => first + last) firstError lastError) :=
        Norm.vector_congr _ _ (fun coordinate =>
          (zipWith_apply _ _ _ coordinate).trans ((show memberEndpoint coordinate - canonicalTrace coordinate =
              (memberEndpoint coordinate - sourceTrace coordinate) +
                (sourceTrace coordinate - canonicalTrace coordinate) by ring1).trans
            ((zipWith_apply _ _ _ coordinate).trans
              (congrArg₂ (fun first last : Canonical => first + last)
                (zipWith_apply _ _ _ coordinate) (zipWith_apply _ _ _ coordinate))).symm))
      have triangle := Norm.vector_add_le_parameter 1 (by decide +kernel) firstError lastError
      have doubled : ((1 : Rational) + 1) * Norm.vector firstError +
          (((1 : Rational) + 1) / 1) * Norm.vector lastError =
            2 * Norm.vector firstError + 2 * Norm.vector lastError :=
        congrArg₂ (fun first last : Rational => first * Norm.vector firstError + last * Norm.vector lastError)
          (show (1 : Rational) + 1 = 2 by decide +kernel)
          (show ((1 : Rational) + 1) / 1 = 2 by decide +kernel)
      have small := Order.Arithmetic.add_lt_add_direct
        (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (show (0 : Rational) < 2 by decide +kernel) sourcePaid)
        (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (show (0 : Rational) < 2 by decide +kernel)
          (reversed.trans_lt differencePaid))
      have budget : 2 * quarter.tolerance + 2 * quarter.tolerance = request.tolerance :=
        (show 2 * (request.tolerance / 4) + 2 * (request.tolerance / 4) =
          (request.tolerance / 4 + request.tolerance / 4) * 2 by ring1).trans
          ((congrArg (fun value : Rational => value * 2) (Data.Rat.Bounds.Quarter.two_quarters request.tolerance)).trans
            (Data.Rat.Bounds.Quarter.half_mul_two request.tolerance))
      have endpoint := (combined.trans_le (triangle.trans_eq doubled)).trans_lt (small.trans_eq budget)
      consume quarter rfl paid.val paid.property
        completed completedFactory actual actualFactory jetFactory forcing forcingTolerance comparison comparisonFactory
        selection selectionFactory positiveCount admitted members membersFactory unit nonzero scaled origin
        positive edges edgesFactory index indexFactory sampled sampledFactory sourceInitial initialFactory
        sourceTrace sourceTraceFactory blockBound initialBound sourcePaid
        canonical canonicalTrace canonicalTraceFactory difference differencePaid endpoint)

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialValues

end
