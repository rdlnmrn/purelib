module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Sampling
public import Purelib.Calculus.Linear.Euler.Blocks
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Connection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Independent connection transport on the retained local-member samples

One common sample stage pays all adjacent reference comparisons. The
original parameter strip bounds the independent connection matrices;
computed coarse intervals discharge growth inside finite Euler stability.
The resulting bound retains the actual initial discrepancy and supplies
neither canonical-period attachment nor geometric monodromy agreement.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows
  (referenceEulerFactor referenceEulerFactor_nonnegative)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (DependentVector zipWith)
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
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage intervals : Nat}
    (offsets : Fin (intervals + 1) → Canonical)
    (admitted : ∀ vertex, Norm.Basic.normSq (offsets vertex) ≤ allocation.bound)
    (members : DependentVector (fun vertex => LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage (offsets vertex) (admitted vertex)))

/-- The original block recurrence bounds the same endpoint readings and independent connection result.

The coefficient ceiling and coarse count depend only on the original
Frame and direction. The local forcing uses the retained reference
Taylor factor; the initial discrepancy remains explicit.
-/
@[expose] def ConnectionBlockBound (direction : Canonical) (refinement : Nat)
    (initial : Vec Canonical 2) (values : Vec (Vec Canonical 2) (intervals + 1))
    (transported : Vec Canonical 2) : Prop :=
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  let nonnegative := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling nonnegative
  let width : Rational := 1 / (intervals : Rational)
  Norm.vector (zipWith (fun first last => first - last)
    (values ⟨intervals, Nat.lt_succ_self intervals⟩) transported) ≤
      Affine.iterate (fun _ => 2)
        (fun _ => 2 * ((refinement : Rational) *
          (referenceEulerFactor (covered := covered) direction * (width + 1) * width ^ 3)))
        (Norm.vector (zipWith (fun first last => first - last) (values 0) initial)) coarse

include admitted in
/-- Original adjacent sample defects and the same strip derive the finite block bound internally. -/
private theorem connection_blocks_le (direction : Canonical) (refinement : Nat) (positive : 0 < refinement)
    (partition : intervals = Euler.intervalCount 2
      (Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame))
      (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
        (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))) * refinement)
    (values : Vec (Vec Canonical 2) (intervals + 1)) (initial : Vec Canonical 2)
    (remainders : ∀ edge : Fin intervals,
      Norm.vector (Euler.defect (Connection.alongMatrix (parameter + offsets edge.castSucc) direction)
        (1 / (intervals : Rational)) (values edge.castSucc) (values edge.succ)) ≤
          referenceEulerFactor (covered := covered) direction * (1 / (intervals : Rational)) ^ 4) :
    let boundedIndex := fun index : Nat => (⟨min index intervals,
      Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
    ConnectionBlockBound (covered := covered) direction refinement initial values
      (Euler.trace (fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction)
        (fun _ => 1 / (intervals : Rational)) initial intervals) := by
  cases partition
  let ceiling := Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)
  have nonnegative : 0 ≤ ceiling := Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))
  let coarse := Euler.intervalCount 2 ceiling nonnegative
  let fineCount := coarse * refinement
  let boundedIndex := fun index : Nat => (⟨min index fineCount,
    Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
  let coefficients := fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction
  let samples := fun index => values (boundedIndex index)
  let width : Rational := 1 / (fineCount : Rational)
  have bounded (index : Nat) (_before : index < fineCount) : Norm.matrix (coefficients index) ≤ ceiling :=
    Connection.alongMatrix_le (ParameterClearance.ofFrame frame) (offsets (boundedIndex index)) direction
      (allocation.parameter_admitted _ (admitted (boundedIndex index)))
  have localBounds (index : Nat) (before : index < fineCount) :
      Norm.vector (Euler.defect (coefficients index) width (samples index) (samples (index + 1))) ≤
        referenceEulerFactor (covered := covered) direction * width ^ 4 := by
    let edge : Fin fineCount := ⟨index, before⟩
    have first : boundedIndex index = edge.castSucc := Fin.ext (Nat.min_eq_left (Nat.le_of_lt before))
    have last : boundedIndex (index + 1) = edge.succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt before))
    have start := congrArg₂ (fun position value => Norm.vector
      (Euler.defect (Connection.alongMatrix (parameter + offsets position) direction) width value
        (samples (index + 1)))) first (congrArg values first)
    have finish := congrArg (fun value => Norm.vector
      (Euler.defect (Connection.alongMatrix (parameter + offsets edge.castSucc) direction) width
        (values edge.castSucc) value)) (congrArg values last)
    exact (start.trans finish).trans_le (remainders edge)
  have finite := Euler.stability_blocks coefficients samples initial ceiling nonnegative refinement positive
    (referenceEulerFactor (covered := covered) direction)
    (referenceEulerFactor_nonnegative (covered := covered) direction) bounded localBounds
  have first : boundedIndex 0 = (0 : Fin (fineCount + 1)) := Fin.ext (Nat.min_eq_left (Nat.zero_le fineCount))
  have last : boundedIndex fineCount = (⟨fineCount, Nat.lt_succ_self fineCount⟩ : Fin (fineCount + 1)) :=
    Fin.ext (Nat.min_eq_left (Nat.le_refl fineCount))
  have initialError := congrArg (fun value : Vec Canonical 2 => Norm.vector
    (zipWith (fun first last => first - last) value initial)) (congrArg values first)
  have endpoint := congrArg (fun value : Vec Canonical 2 => Norm.vector
    (zipWith (fun first last => first - last) value
      (Euler.trace coefficients (fun _ => width) initial fineCount))) (congrArg values last)
  have bound := congrArg (fun value : Rational => Affine.iterate (fun _ => 2)
    (fun _ => 2 * ((refinement : Rational) *
      (referenceEulerFactor (covered := covered) direction * (width + 1) * width ^ 3))) value coarse) initialError
  exact endpoint.symm.trans_le (finite.trans_eq bound)

/-- Retain the paid samples and the independently computed connection endpoint with its derived block bound. -/
@[expose] def ConnectionBlockConsumer
    (firstStart lastStart freshStart residualStart : Nat)
    (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1)
    (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) (spatial : AccuracyRequest)
    (minimum : Nat) (direction : Canonical) (refinement : Nat)
    (initial : Nat → Vec (Vec Canonical 2) (intervals + 1) → Vec Canonical 2) (Result : Type u) :=
  let steps := fun _ : Fin intervals => 1 / (intervals : Rational)
  let boundedIndex := fun index : Nat => (⟨min index intervals,
    Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
  let coefficients := fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction
  (positive : 0 < 1 / (intervals : Rational)) →
  (edges : DependentVector (EdgeSampling offsets admitted members steps residualStart)) →
  edges = edgeSampling offsets admitted members steps (fun _ => positive)
    firstStart lastStart freshStart residualStart unit nonzero spatial →
  (index : Nat) → index = Nat.max minimum (samplingFloor offsets admitted members steps edges) →
  (values : Vec (Vec Canonical 2) (intervals + 1)) → values = sampleValues offsets admitted members index →
  (initialValue : Vec Canonical 2) → initialValue = initial index values →
  (transported : Vec Canonical 2) →
  transported = Euler.trace coefficients (fun _ => 1 / (intervals : Rational)) initialValue intervals →
  ConnectionBlockBound (covered := covered) direction refinement initialValue values transported → Result

/-- Construct independent finite connection transport and compare it with the same actual retained sample family.

The input partition is the exact count of computed coarse intervals and
a positive refinement. Original strip admission bounds all coefficients;
the sample constructor derives every defect before block stability is
applied. No growth estimate, ODE identity or endpoint comparison is input.
The initial-vector function receives the actual common index and retained
sample cache once. Its SAME bound value and factory are forwarded before
the trace, so a client never rebuilds its initial readings for a proof.
-/
def withConnectionBlocks (direction : Canonical) (refinement : Nat) (positiveRefinement : 0 < refinement)
    (partition : intervals = Euler.intervalCount 2
      (Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame))
      (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
        (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))) * refinement)
    (firstStart lastStart freshStart residualStart : Nat)
    (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1)
    (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) (spatial : AccuracyRequest)
    (minimum : Nat)
    (scaled : ∀ edge : Fin intervals,
      offsets edge.succ - offsets edge.castSucc = scale (1 / (intervals : Rational)) direction)
    (initial : Nat → Vec (Vec Canonical 2) (intervals + 1) → Vec Canonical 2) {Result : Type u}
    (consume : ConnectionBlockConsumer offsets admitted members firstStart lastStart freshStart residualStart
      unit nonzero spatial minimum direction refinement initial Result) : Result :=
  have positiveCount : 0 < intervals := partition.symm ▸
    Nat.mul_pos (Euler.intervalCount_positive 2 _ _) positiveRefinement
  have positive : 0 < 1 / (intervals : Rational) :=
    Order.Field.div_pos_direct (by decide +kernel) (Cast.Order.natCast_pos_direct positiveCount)
  withConnectionSamples offsets admitted members (fun _ => 1 / (intervals : Rational))
    (fun _ => positive) firstStart lastStart freshStart residualStart unit nonzero spatial minimum direction scaled
    (fun edges edgesFactory index indexFactory values valuesFactory localBounds =>
      let boundedIndex := fun index : Nat => (⟨min index intervals,
        Nat.lt_succ_of_le (Nat.min_le_right index intervals)⟩ : Fin (intervals + 1))
      let initialValue := initial index values
      let transported := Euler.trace
        (fun index => Connection.alongMatrix (parameter + offsets (boundedIndex index)) direction)
        (fun _ => 1 / (intervals : Rational)) initialValue intervals
      consume positive edges edgesFactory index indexFactory values valuesFactory initialValue rfl transported rfl
        (connection_blocks_le offsets admitted direction refinement positiveRefinement partition
          values initialValue localBounds))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
