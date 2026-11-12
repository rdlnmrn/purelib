module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid
public import Purelib.Calculus.Linear.Euler.Schedule
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Requested connection endpoints from the original affine strip

The original covered geometry and direction fix the endpoint scale before
any grid member is constructed. Its finite selection fixes a positive
uniform partition. All vertex admissions and unit/nonzero increments are
derived from the same strip; one retained member vector then drives the
common-stage samples and independent connection trace.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr sumFin_zero)
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows
  (referenceEulerFactor referenceEulerFactor_nonnegative)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (DependentVector zipWith)
open Purelib.Data.Vector.Basic (zipWith_apply)
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

/-- The computed refinement, original grid members and same-stage connection endpoint with its requested error.

Every factory names the actual retained data. The trace starts from the
first cached sample vector and is computed independently from the final
sample. Its strict endpoint bound is additional to the original block
bound; neither identifies a canonical period or another initial owner.
-/
@[expose] def ConnectionEndpointConsumer (direction : Canonical) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart minimum : Nat) (Result : Type u) :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  let ceilingNonnegative := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  let factor := referenceEulerFactor (covered := covered) direction
  (selection : Selection (Euler.endpointScale coarse factor) 0 request.tolerance) →
  selection = Euler.endpointSelection coarse factor
    (referenceEulerFactor_nonnegative (covered := covered) direction) request →
  let refinement := 4 ^ selection.stage
  let intervals := coarse * refinement
  let offsets := fun vertex : Fin (intervals + 1) => Sampling.gridOffset intervals vertex direction
  let steps := fun _ : Fin intervals => 1 / (intervals : Rational)
  let boundedIndex := fun index : Nat => (⟨min index intervals,
    Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
  let coefficients := fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction
  (positiveCount : 0 < intervals) →
  (admitted : ∀ vertex, Norm.Basic.normSq (offsets vertex) ≤ allocation.bound) →
  (members : DependentVector (fun vertex => LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage (offsets vertex) (admitted vertex))) →
  members = localMembers source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offsets admitted →
  (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1) →
  (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) →
  (∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc = scale (steps edge) direction) →
  (positive : 0 < 1 / (intervals : Rational)) →
  (edges : DependentVector (EdgeSampling offsets admitted members steps residualStart)) →
  edges = edgeSampling offsets admitted members steps (fun _ => positive)
    firstStart lastStart freshStart residualStart unit nonzero spatial →
  (index : Nat) → index = Nat.max minimum (samplingFloor offsets admitted members steps edges) →
  (values : Vec (Vec Canonical 2) (intervals + 1)) → values = sampleValues offsets admitted members index →
  (transported : Vec Canonical 2) →
  transported = Euler.trace coefficients (fun _ => 1 / (intervals : Rational)) (values 0) intervals →
  ConnectionBlockBound (covered := covered) direction refinement (values 0) values transported →
  Norm.vector (zipWith (fun first last => first - last)
    (values ⟨intervals, Nat.lt_succ_self intervals⟩) transported) < request.tolerance → Result

/-- Select a finite refinement before constructing the same grid members and pay their actual connection endpoint error.

The admitted direction lies in the original common strip. Its retained
first range supplies the unit cap, so each actual uniform grid increment
is admitted without a new geometric hypothesis. Original endpoint search,
member construction, common sampling and block stability execute in that
order. The conclusion compares samples on this same source family; source
base identification and canonical geometric transport remain separate.
-/
def withConnectionEndpoint (direction : Canonical) (moving : direction ≠ 0)
    (directionAdmitted : Norm.Basic.normSq direction ≤ allocation.bound) (request spatial : AccuracyRequest)
    (firstStart lastStart freshStart residualStart minimum : Nat) {Result : Type u}
    (consume : ConnectionEndpointConsumer source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage direction request spatial
      firstStart lastStart freshStart residualStart minimum Result) : Result :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  have ceilingNonnegative : 0 ≤ ceiling := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling ceilingNonnegative
  have coarsePositive : 0 < coarse := Euler.intervalCount_positive 2 ceiling ceilingNonnegative
  let factor := referenceEulerFactor (covered := covered) direction
  have factorNonnegative := referenceEulerFactor_nonnegative (covered := covered) direction
  let selection := Euler.endpointSelection coarse factor factorNonnegative request
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
  withConnectionBlocks offsets admitted members direction refinement refinementPositive rfl
    firstStart lastStart freshStart residualStart unit nonzero spatial minimum scaled (fun _ values => values 0)
    (fun positive edges edgesFactory index indexFactory values valuesFactory initialValue initialFactory
        transported transportFactory bounded =>
      have initialError : Norm.vector (zipWith (fun first last => first - last) (values 0) (values 0)) = 0 := by
        have coordinates (coordinate : Fin 2) : Norm.Basic.normSq
            (zipWith (fun first last => first - last) (values 0) (values 0) coordinate) = 0 :=
          (congrArg Norm.Basic.normSq ((zipWith_apply _ _ _ coordinate).trans
            (Basic.sub_self (values 0 coordinate)))).trans Norm.Basic.normSq_zero
        exact (sumFin_congr coordinates).trans sumFin_zero
      have initialSame := congrArg (fun value : Vec Canonical 2 => Norm.vector
        (zipWith (fun first last => first - last) (values 0) value)) initialFactory
      have actualInitial := initialSame.trans initialError
      have zeroed := congrArg (fun value : Rational => Affine.iterate (fun _ => 2)
        (fun _ => 2 * ((refinement : Rational) *
          (factor * ((1 / (intervals : Rational)) + 1) * (1 / (intervals : Rational)) ^ 3))) value coarse) actualInitial
      have paid := Euler.blockBound_lt coarse coarsePositive factor factorNonnegative request selection
      have endpoint : Norm.vector (zipWith (fun first last => first - last)
          (values ⟨intervals, Nat.lt_succ_self intervals⟩) transported) < request.tolerance :=
        (bounded.trans_eq zeroed).trans_lt paid
      have transportReadback := transportFactory.trans (congrArg (fun value : Vec Canonical 2 =>
        Euler.trace
          (fun index => Connection.alongMatrix (parameter + offsets (⟨min index intervals,
            Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))) direction)
          (fun _ => 1 / (intervals : Rational)) value intervals) initialFactory)
      have boundReadback := bounded.trans_eq (congrArg (fun value : Rational => Affine.iterate (fun _ => 2)
        (fun _ => 2 * ((refinement : Rational) *
          (factor * ((1 / (intervals : Rational)) + 1) * (1 / (intervals : Rational)) ^ 3))) value coarse) initialSame)
      consume selection rfl positiveCount admitted members rfl unit nonzero scaled
        positive edges edgesFactory index indexFactory values valuesFactory
        transported transportReadback boundReadback endpoint)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
