module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order

/-! # Original root observations after retained comparison stages

An additional stage floor is combined with the existing radius minimum
before invoking the same square comparison. The original residual observation
retains its actual selected state and spread. Semantic allowance stages are
computed from the same coherent input's original finite refinement request.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

open Purelib
open Purelib.Data
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Request the same paid original-root observation after an additional retained comparison stage. -/
def requestAfter {parameter : Canonical} (root : Certificate parameter) (accuracy : AccuracyRequest) (stage : Nat) :
    { sample : ResidualObservation root accuracy // stage ≤ sample.comparison.leftIndex } := by
  let minimum := Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root accuracy).tolerance
  let start := max minimum stage
  let actual := (squareComparison root).compare start 0 (squareRequest accuracy).tolerance
    (squareRequest accuracy).positive
  let comparison : Comparison (squareApproximation root) (Name.Sampling.approximation (Named.exact parameter))
      minimum 0 (squareRequest accuracy).tolerance :=
    { leftIndex := actual.leftIndex
      rightIndex := actual.rightIndex
      left_ge := (show minimum ≤ start by
        change minimum ≤ max minimum stage
        rewrite [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _).trans actual.left_ge
      right_ge := actual.right_ge
      close := actual.close }
  let state := Process.Sampling.stateAt root.value.name.process root.value.name.state comparison.leftIndex
  let observation := root.value.name.process.observation state
  let sample : ResidualObservation root accuracy :=
    { minimumIndex := minimum
      minimumIndex_eq := rfl
      comparison := comparison
      state := state
      state_eq := rfl
      observation := observation
      observation_eq := rfl
      residual_lt := candidate_residual_lt root accuracy comparison }
  exact ⟨sample, (show stage ≤ start by
    change stage ≤ max minimum stage
    rewrite [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_right _ _).trans actual.left_ge⟩

namespace ResidualObservation

open Purelib.Data.Gaussian

/-- Every candidate of an actual later observation preserves an earlier paid residual comparison on the same root.

The earlier and later observations, comparison owners and selected states
remain independent. The earlier comparison tail and radius floor apply to
the actual later index; no old displayed witness is assigned a new payment.
-/
theorem residual_lt_after {parameter : Canonical} {root : Certificate parameter}
    {earlierAccuracy laterAccuracy : AccuracyRequest}
    (earlier : ResidualObservation root earlierAccuracy) (later : ResidualObservation root laterAccuracy)
    (after : earlier.comparison.leftIndex ≤ later.comparison.leftIndex) {candidate : Canonical}
    (possible : later.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - parameter) < earlierAccuracy.tolerance := by
  let comparison : Comparison (squareApproximation root) (Name.Sampling.approximation (Named.exact parameter))
      (Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root earlierAccuracy).tolerance) 0
      (squareRequest earlierAccuracy).tolerance :=
    { leftIndex := later.comparison.leftIndex
      rightIndex := earlier.comparison.rightIndex
      left_ge := by
        rewrite [← earlier.minimumIndex_eq]
        exact earlier.comparison.left_ge.trans after
      right_ge := earlier.comparison.right_ge
      close := fun {_ _} leftGe rightGe => earlier.comparison.close (after.trans leftGe) rightGe }
  have actualPossible : root.value.name.process.Possible later.state candidate := by
    rewrite [later.observation_eq] at possible
    exact possible
  rewrite [later.state_eq] at actualPossible
  exact candidate_residual_lt root earlierAccuracy comparison actualPossible

/-- The actual later retained witness preserves the same earlier residual payment. -/
theorem reading_residual_lt_after {parameter : Canonical} {root : Certificate parameter}
    {earlierAccuracy laterAccuracy : AccuracyRequest}
    (earlier : ResidualObservation root earlierAccuracy) (later : ResidualObservation root laterAccuracy)
    (after : earlier.comparison.leftIndex ≤ later.comparison.leftIndex) :
    Norm.Basic.normSq (later.reading * later.reading - parameter) < earlierAccuracy.tolerance :=
  earlier.residual_lt_after later after later.observation.witness_possible

end ResidualObservation

/-- Two original requests and the actual selected-index ordering retain both independent residual payments. -/
@[expose] def JointRequest {parameter : Canonical} (root : Certificate parameter)
    (primary additional : AccuracyRequest) :=
  (paid : ResidualObservation root additional) ×
    { selected : ResidualObservation root primary // paid.comparison.leftIndex ≤ selected.comparison.leftIndex }

/-- Retain both an additional paid root observation and an actual primary observation selected after its stage.

The first request pays the independent additional residual tolerance. The
primary request keeps its own original tolerance and is made after that
actual comparison index. Both observations and both original comparisons
remain stored. residual_lt_after derives both payments on the selected
primary candidates without changing any old witness, state or request.
-/
def requestJoint {parameter : Canonical} (root : Certificate parameter)
    (primary additional : AccuracyRequest) : JointRequest root primary additional :=
  let paid := request root additional
  let selected := requestAfter root primary paid.comparison.leftIndex
  ⟨paid, selected⟩

/-- Compute the finite canonical sampling stage paying the original coherent input's semantic allowance request. -/
@[expose] def allowanceMinimum (value : CoherentNamed) (target : Fraction.Rational) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 (value.coherent.accuracyRequest target)

/-- Every canonical state after the computed stage pays the same positive semantic allowance target. -/
theorem allowance_lt_after (value : CoherentNamed) (target : Fraction.Rational) (positive : 0 < target)
    {index : Nat} (after : allowanceMinimum value target ≤ index) :
    value.coherent.allowance (Process.Sampling.stateAt value.name.process value.name.state index) < target := by
  have minimum := Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0
    (value.coherent.accuracyRequest target) (value.coherent.accuracyRequest_pos positive)
  apply value.coherent.stateAt_allowance_lt value.name.state index target positive
  exact (Geometric.Basic.quarterRadius_antitone
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1) after).trans_lt minimum

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
