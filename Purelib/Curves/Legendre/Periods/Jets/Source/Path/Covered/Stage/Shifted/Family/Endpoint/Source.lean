module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Endpoint
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Algebra.Recurrence.Affine.Constant
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Calculus.Linear.Euler.Schedule
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # Requested connection transport initialized by actual original source readings

One original occurrence family and its six-channel jet precede numerical
endpoint requests. An original comparison selection pays the propagated
source/zero-member discrepancy before the common sample stage is chosen.
The trace consumes that SAME once-read source vector, while its geometric
member, zero-member Frame and all samples retain their independent owners.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib.Data.Nat

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows
  (referenceEulerFactor referenceEulerFactor_nonnegative)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (DependentVector zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply zipWith_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.LinearAlgebra.Gaussian
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- The exact dependent result family for an original source endpoint's retained grid and three actual vectors.

Only the actual forcing, selection, model index, source initial vector,
source trace and member endpoint parameterize the tail. All original
source-family, jet, member, sample and factory arguments remain in the
shared consumer telescope rather than a copied context record.
-/
abbrev SourceConnectionEndpointTail (direction : Canonical) : Type (u + 1) :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  let ceilingNonnegative := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  let factor := referenceEulerFactor (covered := covered) direction
  (forcing : AccuracyRequest) → Selection (Euler.endpointScale coarse factor) 0 forcing.tolerance →
    Nat → Vec Canonical 2 → Vec Canonical 2 → Vec Canonical 2 → Type u

/-- Retain the original source endpoint telescope with an exact dependent result on its actual final cache values. -/
abbrev SourceConnectionEndpointConsumerWith (direction : Canonical) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart comparisonStart minimum : Nat)
    (Finish : SourceConnectionEndpointTail.{u}
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) direction) : Type _ :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  let ceilingNonnegative := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  let factor := referenceEulerFactor (covered := covered) direction
  let amplification := Affine.iterate (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
  let comparisonScale := 2 * amplification * errorScale (parent :: parents)
  (completed : source.attempt.OccurrenceFamily) →
  (_completed_factory : completed = source.attempt.completeOccurrenceFamily roots) →
  (actual : (jet : SynchronizedPeriodJet frame) ×
    Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) →
  (_actual_factory : actual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
    covered chain (fun stage => (completed stage).val)) →
  (_jet_factory : actual.1 = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
    covered chain (fun stage => (completed stage).val)) →
  (forcing : AccuracyRequest) → (_forcing_tolerance : forcing.tolerance = request.tolerance / 2) →
  (comparison : Selection comparisonScale comparisonStart (request.tolerance / 4)) →
  (_comparison_factory : comparison = Selection.build comparisonScale comparison.scaleNonnegative comparisonStart
    (request.tolerance / 4) comparison.targetPositive) →
  (selection : Selection (Euler.endpointScale coarse factor) 0 forcing.tolerance) →
  (_selection_factory : selection = Euler.endpointSelection coarse factor
    (referenceEulerFactor_nonnegative (covered := covered) direction) forcing) →
  let refinement := 4 ^ selection.stage
  let intervals := coarse * refinement
  let offsets := fun vertex : Fin (intervals + 1) => Sampling.gridOffset intervals vertex direction
  let steps := fun _ : Fin intervals => 1 / (intervals : Rational)
  let boundedIndex := fun index : Nat => (⟨min index intervals,
    Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
  let coefficients := fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction
  (_positiveCount : 0 < intervals) →
  (admitted : ∀ vertex, Norm.Basic.normSq (offsets vertex) ≤ allocation.bound) →
  (members : DependentVector (fun vertex => LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage (offsets vertex) (admitted vertex))) →
  (_members_factory : members = localMembers source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offsets admitted) →
  (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1) →
  (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) →
  (_scaled : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc = scale (steps edge) direction) →
  (_origin : offsets 0 = 0) →
  (positive : 0 < 1 / (intervals : Rational)) →
  (edges : DependentVector (EdgeSampling offsets admitted members steps residualStart)) →
  (_edges_factory : edges = edgeSampling offsets admitted members steps (fun _ => positive)
    firstStart lastStart freshStart residualStart unit nonzero spatial) →
  (index : Nat) →
  (_index_factory : index = Nat.max (Nat.max minimum comparison.stage)
    (samplingFloor offsets admitted members steps edges)) →
  (values : Vec (Vec Canonical 2) (intervals + 1)) →
  (_values_factory : values = sampleValues offsets admitted members index) →
  (initialValue : Vec Canonical 2) →
  (_initial_factory : initialValue = vectorOfFn (fun coordinate =>
    ((actual.1.value coordinate).integral.model index).integralSample)) →
  (transported : Vec Canonical 2) →
  (_transport_factory : transported = Euler.trace coefficients (fun _ => 1 / (intervals : Rational))
    initialValue intervals) →
  (_block_bound : ConnectionBlockBound (covered := covered) direction refinement initialValue values transported) →
  (_initial_bound : Norm.vector (zipWith (fun first last => first - last) (values 0) initialValue) ≤
    2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents)) comparison.stage) →
  Norm.vector (zipWith (fun first last => first - last)
    (values ⟨intervals, Nat.lt_succ_self intervals⟩) transported) < request.tolerance →
    Finish forcing selection index initialValue transported (values ⟨intervals, Nat.lt_succ_self intervals⟩)

/-- The actual source realization, paid stages, once-bound initial vector and requested connection endpoint.

Source and zero-member Frames are separate retained owners. Scalar zero
offset reindexing supplies no Frame equality. The final two inequalities
are derived outputs on the actual vectors and independently computed trace.
-/
abbrev SourceConnectionEndpointConsumer (direction : Canonical) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart comparisonStart minimum : Nat) (Result : Type u) : Type _ :=
  SourceConnectionEndpointConsumerWith.{u} (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage direction request spatial
    firstStart lastStart freshStart residualStart comparisonStart minimum (fun _ _ _ _ _ _ => Result)

/-- Construct requested connection transport from the actual original source vector at the SAME paid common index.

The original family/jet are constructed once. Both endpoint refinement and
source-comparison stages precede all member sampling. Their maximum pays
every requested original reading before the index-aware initial selector
constructs its one actual source vector. Original Origin comparisons and
finite affine response derive the endpoint bound without an initial-error,
ODE, Frame identity, canonical attachment or final accuracy premise.
-/
def withSourceConnectionEndpoint (direction : Canonical) (moving : direction ≠ 0)
    (directionAdmitted : Norm.Basic.normSq direction ≤ allocation.bound) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart comparisonStart minimum : Nat) {Result : Type u}
    (consume : SourceConnectionEndpointConsumer source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage direction request spatial
      firstStart lastStart freshStart residualStart comparisonStart minimum Result) : Result :=
  let completed := source.attempt.completeOccurrenceFamily (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (covered := covered) (chain := chain)
    (index := source.selected.stage) (floor := floor) (rootStage := rootStage) roots
  let actual := OccurrenceCompletion.build (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
    covered chain (fun stage => (completed stage).val)
  have jetFactory := OccurrenceCompletion.build_jet (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
    covered chain (fun stage => (completed stage).val)
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  have ceilingNonnegative : 0 ≤ ceiling := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  have coarsePositive : 0 < coarse := Euler.intervalCount_positive 2 ceiling ceilingNonnegative
  let factor := referenceEulerFactor (covered := covered) direction
  have factorNonnegative := referenceEulerFactor_nonnegative (covered := covered) direction
  let amplification := Affine.iterate (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
  have amplificationNonnegative : 0 ≤ amplification :=
    Affine.iterate_nonnegative (fun _ => (2 : Rational)) (fun _ => 0) 1 coarse
      (by decide +kernel) (fun _ _ => by decide +kernel) (fun _ _ => by decide +kernel)
  let comparisonScale := 2 * amplification * errorScale (parent :: parents)
  have comparisonNonnegative : 0 ≤ comparisonScale := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 2 by decide +kernel) amplificationNonnegative)
    (errorScale_nonnegative (parameter := parameter) (frame := frame) (basis := basis) (parent :: parents))
  let comparison := Selection.build comparisonScale comparisonNonnegative comparisonStart
    (request.tolerance / 4) (Data.Rat.Bounds.Quarter.quarter_pos request.positive)
  let forcing : AccuracyRequest := ⟨request.tolerance / 2,
    Order.Field.div_pos_direct request.positive (show (0 : Rational) < 2 by decide +kernel)⟩
  let selection := Euler.endpointSelection coarse factor factorNonnegative forcing
  let refinement := 4 ^ selection.stage
  have refinementPositive : 0 < refinement := Nat.pow_pos (by decide +kernel)
  let intervals := coarse * refinement
  have positiveCount : 0 < intervals := Nat.mul_pos coarsePositive refinementPositive
  let offsets := fun vertex : Fin (intervals + 1) => Sampling.gridOffset intervals vertex direction
  have admitted (vertex : Fin (intervals + 1)) : Norm.Basic.normSq (offsets vertex) ≤ allocation.bound :=
    (Sampling.gridOffset_normSq_le intervals positiveCount vertex direction).trans directionAdmitted
  let members := localMembers source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offsets admitted
  have capped : (ranges.entry 0).bound ≤ 1 := by
    change min 1 _ ≤ 1
    exact Order.Basic.min_le_left _ _
  have directionUnit : Norm.Basic.normSq direction ≤ 1 :=
    directionAdmitted.trans (allocation.bound_le_bound.trans ((ranges.bound_le_entry 0).trans capped))
  have unit (edge : Fin intervals) : Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1 :=
    (congrArg Norm.Basic.normSq (Sampling.gridOffset_difference intervals edge direction)).trans_le
      (((Sampling.gridIncrement_normSq_le intervals positiveCount edge direction).trans
        (Sampling.gridOffset_normSq_le intervals positiveCount edge.succ direction)).trans directionUnit)
  have nonzero (edge : Fin intervals) : offsets edge.succ - offsets edge.castSucc ≠ 0 :=
    fun zero => Sampling.gridIncrement_nonzero intervals positiveCount direction moving
      ((Sampling.gridOffset_difference intervals edge direction).symm.trans zero)
  have scaled (edge : Fin intervals) :
      offsets edge.succ - offsets edge.castSucc = scale (1 / (intervals : Rational)) direction :=
    Sampling.gridOffset_difference intervals edge direction
  have origin : offsets 0 = 0 := Sampling.gridOffset_zero intervals direction
  withConnectionBlocks (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (intervals := intervals)
    offsets admitted members direction refinement refinementPositive rfl
    firstStart lastStart freshStart residualStart unit nonzero spatial (Nat.max minimum comparison.stage) scaled
    (fun index _ => vectorOfFn (fun coordinate => ((actual.1.value coordinate).integral.model index).integralSample))
    (fun positive edges edgesFactory index indexFactory values valuesFactory initialValue initialFactory
        transported transportFactory bounded =>
      have after : comparison.stage ≤ index :=
        ((Order.le_max_right minimum comparison.stage).trans
          (Order.le_max_left (Nat.max minimum comparison.stage)
            (samplingFloor offsets admitted members (fun _ => 1 / (intervals : Rational)) edges))).trans_eq
          indexFactory.symm
      have sourceValues (coordinate : Fin 2) : initialValue coordinate =
          ((actual.1.value coordinate).integral.model index).integralSample :=
        (congrArg (fun value : Vec Canonical 2 => value coordinate) initialFactory).trans
          (vectorOfFn_apply _ coordinate)
      have zeroValues (coordinate : Fin 2) : values 0 coordinate =
          (((members.get 0).jet.value coordinate).integral.model index).integralSample :=
        (congrArg (fun value : Vec (Vec Canonical 2) (intervals + 1) => value 0 coordinate) valuesFactory).trans
          (sampleValues_apply offsets admitted members index 0 coordinate)
      have compared := (members.get 0).sourceValues_difference_le
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
        (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) (offset := offsets 0) (admitted := admitted 0)
        origin completed actual.1 jetFactory
        comparison.stage index index after after initialValue (values 0) sourceValues zeroValues
      have reversed : Norm.vector (zipWith (fun first last => first - last) (values 0) initialValue) =
          Norm.vector (zipWith (fun first last => first - last) initialValue (values 0)) := by
        unfold Norm.vector
        apply sumFin_congr
        intro coordinate
        have negated : values 0 coordinate - initialValue coordinate =
            -(initialValue coordinate - values 0 coordinate) := by ring1
        exact (congrArg Norm.Basic.normSq (zipWith_apply _ _ _ coordinate)).trans
          (((congrArg Norm.Basic.normSq negated).trans (Norm.Basic.normSq_neg _)).trans
            (congrArg Norm.Basic.normSq (zipWith_apply _ _ _ coordinate)).symm)
      have initialBound := reversed.trans_le compared
      have radius : amplification * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
          comparison.stage) = Geometric.Basic.quarterRadius comparisonScale comparison.stage := by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      have initialPaid := (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct initialBound
        amplificationNonnegative).trans_lt
          (radius.trans_lt (comparison.allowance_eq.symm.trans_lt comparison.accurate))
      have forcingPaid := Euler.blockBound_lt coarse coarsePositive factor factorNonnegative forcing selection
      have split := Affine.iterate_initial (fun _ => (2 : Rational))
        (fun _ => 2 * ((refinement : Rational) *
          (factor * ((1 / (intervals : Rational)) + 1) * (1 / (intervals : Rational)) ^ 3)))
        (Norm.vector (zipWith (fun first last => first - last) (values 0) initialValue)) coarse
      have small := Order.Arithmetic.add_lt_add_direct initialPaid forcingPaid
      have endpoint : Norm.vector (zipWith (fun first last => first - last)
          (values ⟨intervals, Nat.lt_succ_self intervals⟩) transported) < request.tolerance :=
        (bounded.trans_eq split).trans_lt
          (small.trans ((Field.add_comm _ _).trans_lt (Data.Rat.Bounds.Quarter.half_add_quarter_lt request.positive)))
      consume completed rfl actual rfl jetFactory forcing rfl comparison rfl selection rfl
        positiveCount admitted members rfl unit nonzero scaled origin positive edges edgesFactory
        index indexFactory values valuesFactory initialValue initialFactory transported transportFactory bounded
        initialBound endpoint)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
