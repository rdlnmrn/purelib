module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Name.Bounds
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Paid observations of an original certified square-root process

The existing square comparison is transported through the existing coherent
product bridge. A spread request determines the minimum sampling index
before that comparison chooses its actual index. The returned state and
observation belong to the original cached process, and every admitted reading
pays the requested square residual. No root isolation or replacement root
process is performed.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data
open Purelib.Data.Rat

/-- The existing equal-index product approximation of the original certified root name. -/
@[expose] def squareApproximation {parameter : Canonical} (root : Certificate parameter) :
    Sequence.ApproximationData :=
  Sequence.Arithmetic.Product.sampledProductApproximation root.value.name root.value.name

/-- The original square certificate compares its equal-index square samples with the original exact radicand. -/
@[expose] def squareComparison {parameter : Canonical} (root : Certificate parameter) :
    Equivalent (squareApproximation root) (Name.Sampling.approximation (Named.exact parameter)) :=
  Equivalent.trans
    (Equivalent.symm (Name.Coherent.Arithmetic.Product.Bridge.coherentMul_toSampled root.value root.value))
    root.square

/-- The retained centre bound gives a common magnitude bound after every canonical sampling stage. -/
@[expose] def candidateBound {parameter : Canonical} (root : Certificate parameter) : Fraction.Rational :=
  2 * (1 + root.value.name.process.centerBound)

/-- The computed magnitude bound is strictly positive. -/
theorem candidateBound_pos {parameter : Canonical} (root : Certificate parameter) :
    0 < candidateBound root := by
  unfold candidateBound
  exact Arithmetic.mul_pos_direct (by decide +kernel)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel)
      root.value.name.process.centerBound_nonneg)

/-- Every candidate of an actual sampled state satisfies the computed common magnitude bound. -/
theorem candidate_normSq_le {parameter : Canonical} (root : Certificate parameter) (index : Nat)
    {candidate : Canonical}
    (possible : root.value.name.process.Possible
      (Process.Sampling.stateAt root.value.name.process root.value.name.state index) candidate) :
    Norm.Basic.normSq candidate ≤ candidateBound root := by
  let process := root.value.name.process
  let state := Process.Sampling.stateAt process root.value.name.state index
  have radius : (process.ball state).radiusSq ≤ 1 :=
    (Process.Sampling.stateAt_accurate process root.value.name.state index).le.trans
      (Process.Sampling.refinementTarget_le_one index)
  have bound := Name.Bounds.possible_normSq_le_inputBound
    (show Named from { process := process, state := state }) possible
  apply bound.trans
  unfold Name.Bounds.inputBound candidateBound
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide +kernel)
  calc
    _ ≤ 1 + process.centerBound := Arithmetic.add_le_add_direct radius (process.center_bounded state)
    _ = _ := by ring1

/-- One quarter of the original residual request is the square-comparison request. -/
@[expose] def squareRequest (request : AccuracyRequest) : AccuracyRequest :=
  ⟨request.tolerance / 4, Rat.Bounds.Quarter.quarter_pos request.positive⟩

/-- The computed sensitivity denominator converting square residual tolerance into ball-radius tolerance. -/
@[expose] def radiusDenominator {parameter : Canonical} (root : Certificate parameter) : Fraction.Rational :=
  64 * candidateBound root

/-- The square-sensitivity denominator is strictly positive. -/
theorem radiusDenominator_pos {parameter : Canonical} (root : Certificate parameter) :
    0 < radiusDenominator root := by
  have constantPositive : (0 : Fraction.Rational) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide +kernel)
  exact Arithmetic.mul_pos_direct
    (left := (64 : Fraction.Rational)) (right := candidateBound root) constantPositive (candidateBound_pos root)

/-- The original residual request pays square sensitivity through a distinct ball-radius request. -/
@[expose] def radiusRequest {parameter : Canonical} (root : Certificate parameter)
    (request : AccuracyRequest) : AccuracyRequest :=
  ⟨request.tolerance / radiusDenominator root,
    Fraction.Order.Field.div_pos_direct (numerator := request.tolerance) (denominator := radiusDenominator root)
      request.positive (radiusDenominator_pos root)⟩

/-- The actual square-sensitivity radius request never exceeds the original positive residual allowance. -/
theorem radiusRequest_le {parameter : Canonical} (root : Certificate parameter) (request : AccuracyRequest) :
    (radiusRequest root request).tolerance ≤ request.tolerance := by
  have extra := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (le_add_of_nonneg_right root.value.name.process.centerBound_nonneg :
      (1 : Fraction.Rational) ≤ 1 + root.value.name.process.centerBound)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have larger := Arithmetic.mul_le_mul_of_nonneg_left_direct extra
    (by decide +kernel : (0 : Fraction.Rational) ≤ 64)
  have denominator : (1 : Fraction.Rational) ≤ radiusDenominator root :=
    (show (1 : Fraction.Rational) ≤ 64 * (2 * 1) by decide +kernel).trans larger
  exact Fraction.Order.Field.divide_le_self request.positive.le denominator

/-- Sixteen times the magnitude bound pays exactly one quarter of the residual request. -/
private theorem radius_payment {parameter : Canonical} (root : Certificate parameter)
    (request : AccuracyRequest) :
    16 * candidateBound root * (radiusRequest root request).tolerance = (squareRequest request).tolerance := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := (4 : Fraction.Rational)) (by decide +kernel)
  calc
    _ = (radiusRequest root request).tolerance * (64 * candidateBound root) := by ring1
    _ = request.tolerance := Fraction.Field.div_mul_cancel_of_ne _ _ (radiusDenominator_pos root).ne'
    _ = (squareRequest request).tolerance * 4 :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (4 : Fraction.Rational) ≠ 0)).symm

/-- The canonical spread is small enough to pay square movement at and after the computed minimum index. -/
private theorem sampled_radius_lt {parameter : Canonical} (root : Certificate parameter)
    (request : AccuracyRequest) {index : Nat}
    (minimum : Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root request).tolerance ≤ index) :
    (root.value.name.process.ball
      (Process.Sampling.stateAt root.value.name.process root.value.name.state index)).radiusSq <
      (radiusRequest root request).tolerance := by
  have selected := Geometric.Search.firstQuarterBelow_accurate
    1 (by decide +kernel) 0 (radiusRequest root request).tolerance (radiusRequest root request).positive
  exact (Process.Sampling.stateAt_accurate root.value.name.process root.value.name.state index).trans_le
    (Geometric.Basic.quarterRadius_antitone (by decide +kernel) minimum) |>.trans selected

/-- The actual sampled witness square is within the original square-comparison request. -/
private theorem compared_witness_residual_lt {parameter : Canonical} (root : Certificate parameter)
    (request : AccuracyRequest) (minimum : Nat)
    (comparison : Comparison (squareApproximation root)
      (Name.Sampling.approximation (Named.exact parameter)) minimum 0 (squareRequest request).tolerance) :
    Norm.Basic.normSq
      (Process.Sampling.witnessAt root.value.name.process root.value.name.state comparison.leftIndex *
        Process.Sampling.witnessAt root.value.name.process root.value.name.state comparison.leftIndex - parameter) <
      (squareRequest request).tolerance := by
  have close := comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  rewrite [Sequence.Name.Exact.exactNamedSample] at close
  exact close

/-- Every possible reading of the same retained sampled state inherits the paid square residual. -/
theorem candidate_residual_lt {parameter : Canonical} (root : Certificate parameter)
    (request : AccuracyRequest)
    (comparison : Comparison (squareApproximation root)
      (Name.Sampling.approximation (Named.exact parameter))
      (Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root request).tolerance) 0
      (squareRequest request).tolerance)
    {candidate : Canonical}
    (possible : root.value.name.process.Possible
      (Process.Sampling.stateAt root.value.name.process root.value.name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate * candidate - parameter) < request.tolerance := by
  let process := root.value.name.process
  let index := comparison.leftIndex
  let state := Process.Sampling.stateAt process root.value.name.state index
  let witness := Process.Sampling.witnessAt process root.value.name.state index
  let radius := (process.ball state).radiusSq
  have radiusSmall : radius < (radiusRequest root request).tolerance :=
    sampled_radius_lt root request comparison.left_ge
  have witnessPossible := Process.Sampling.witnessAt_possible process root.value.name.state index
  have candidateBound' := candidate_normSq_le root index possible
  have witnessBound := candidate_normSq_le root index witnessPossible
  have sumBound : Norm.Basic.normSq (candidate + witness) ≤ 4 * candidateBound root := by
    exact ((Norm.Bounds.normSq_add_le_two _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct candidateBound' witnessBound) (by decide +kernel))).trans_eq
          (by ring1)
  have distance : Norm.Basic.normSq (candidate - witness) ≤ 4 * radius :=
    (process.observation state).pairwise possible witnessPossible
  have factorization : candidate * candidate - witness * witness =
      (candidate - witness) * (candidate + witness) := by ring1
  have squareMovement : Norm.Basic.normSq (candidate * candidate - witness * witness) <
      (squareRequest request).tolerance := by
    rewrite [factorization, Norm.Basic.normSq_mul]
    calc
      _ ≤ (4 * radius) * (4 * candidateBound root) :=
        Arithmetic.mul_le_mul_direct distance sumBound (Norm.Basic.normSq_nonneg _)
          (Arithmetic.mul_nonneg_direct (by decide +kernel) (process.ball state).radiusSq_nonneg)
      _ = 16 * candidateBound root * radius := by ring1
      _ < 16 * candidateBound root * (radiusRequest root request).tolerance :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          (Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide +kernel)) (candidateBound_pos root))
          radiusSmall
      _ = _ := radius_payment root request
  have witnessResidual := compared_witness_residual_lt root request _ comparison
  have identity : candidate * candidate - parameter =
      (candidate * candidate - witness * witness) + (witness * witness - parameter) := by ring1
  rewrite [identity]
  calc
    _ ≤ 2 * (Norm.Basic.normSq (candidate * candidate - witness * witness) +
        Norm.Basic.normSq (witness * witness - parameter)) := Norm.Bounds.normSq_add_le_two _ _
    _ < 2 * ((squareRequest request).tolerance + (squareRequest request).tolerance) :=
      Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Arithmetic.add_lt_add_direct squareMovement witnessResidual)
    _ = request.tolerance := by
      apply Fraction.Field.mul_right_cancel_of_ne (c := (4 : Fraction.Rational)) (by decide +kernel)
      change (2 * (request.tolerance / 4 + request.tolerance / 4)) * 4 = request.tolerance * 4
      calc
        _ = 4 * ((request.tolerance / 4) * 4) := by ring1
        _ = _ := by rewrite [Fraction.Field.div_mul_cancel_of_ne _ _
          (by decide +kernel : (4 : Fraction.Rational) ≠ 0)]; ring1

set_option genInjectivity false in
/-- A paid original-process observation retaining the actual comparison and selected state.

The minimum index pays ball spread before the square comparison selects its
left index. Both comparison approximation owners are retained by the existing
Comparison type. The cached state and observation are exactly those at the
chosen original-name index, and every admitted reading pays the residual request.
-/
structure ResidualObservation {parameter : Canonical}
    (root : Certificate parameter) (request : AccuracyRequest) where
  /-- The retained minimum canonical sampling index paying square sensitivity. -/ minimumIndex : Nat
  /-- The minimum is computed from the actual radius request. -/ minimumIndex_eq : minimumIndex =
    Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root request).tolerance
  /-- The actual existing comparison of original equal-index squares and exact radicand. -/ comparison :
    Comparison (squareApproximation root) (Name.Sampling.approximation (Named.exact parameter))
      minimumIndex 0 (squareRequest request).tolerance
  /-- The cached actual state of the original root process. -/ state : root.value.name.process.State
  /-- The state is the original canonical sample state at the retained comparison's selected index. -/ state_eq :
    state = Process.Sampling.stateAt root.value.name.process root.value.name.state comparison.leftIndex
  /-- The cached generic observation of that same retained process state. -/ observation :
    Observation Canonical (fun first last => Norm.Basic.normSq (first - last))
  /-- The cached observation is the actual original process observation. -/ observation_eq :
    observation = root.value.name.process.observation state
  /-- Every reading possible in the retained observation pays the original square-residual request. -/ residual_lt :
    ∀ {candidate : Canonical}, observation.Possible candidate →
      Norm.Basic.normSq (candidate * candidate - parameter) < request.tolerance

constructive_injectivity ResidualObservation

/-- Request a paid observation from the original certificate without replacing its cached process.

The radius minimum is computed before the existing comparison is invoked.
The comparison's returned left index selects both the state and actual
witness; the same cached observation proves residual payment for all candidates.
-/
@[expose] def request {parameter : Canonical} (root : Certificate parameter)
    (accuracy : AccuracyRequest) : ResidualObservation root accuracy := by
  let minimum := Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root accuracy).tolerance
  let comparison := (squareComparison root).compare minimum 0 (squareRequest accuracy).tolerance
    (squareRequest accuracy).positive
  let state := Process.Sampling.stateAt root.value.name.process root.value.name.state comparison.leftIndex
  let observation := root.value.name.process.observation state
  exact
    { minimumIndex := minimum
      minimumIndex_eq := rfl
      comparison := comparison
      state := state
      state_eq := rfl
      observation := observation
      observation_eq := rfl
      residual_lt := candidate_residual_lt root accuracy comparison }

/-- An original-owner cache equality transports every actual candidate into that owner's initial box.

The complete certificate equality identifies the process. Its existing state
transport moves the retained state and possibility proof to the original
owner, whose certificate then supplies the initial-box containment.
-/
theorem candidate_in_initial_box {parameter : Canonical} {root : Certificate parameter}
    (owner : Topology.SquareRootContinuationChain.Owner parameter)
    (cache_eq : root = owner.certificate owner.parameterNonzero)
    {state : root.value.name.process.State} {candidate : Canonical}
    (possible : root.value.name.process.Possible state candidate) :
    owner.track.initial.box.Contains candidate := by
  have process_eq : root.value.name.process = (owner.certificate owner.parameterNonzero).value.name.process :=
    congrArg (fun certificate : Certificate parameter => certificate.value.name.process) cache_eq
  let ownerState := Process.Sampling.castState process_eq state
  have ownerPossible := Process.Sampling.possible_castState process_eq state possible
  exact owner.certificate_candidate_in_initial_box owner.parameterNonzero ownerState ownerPossible

namespace ResidualObservation

/-- Read the actual cached witness of the retained original-process observation. -/
@[expose] def reading {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) : Canonical := sample.observation.witness

/-- The retained witness satisfies the exact original process possibility predicate. -/
theorem reading_possible {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) : root.value.name.process.Possible sample.state sample.reading := by
  have possible : sample.observation.Possible sample.reading := sample.observation.witness_possible
  rewrite [sample.observation_eq] at possible
  exact possible

/-- The same actual retained observation state pays its originally computed square-sensitivity radius request. -/
theorem radius_lt {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    (root.value.name.process.ball sample.state).radiusSq < (radiusRequest root accuracy).tolerance := by
  rewrite [sample.state_eq]
  exact sampled_radius_lt root accuracy (sample.minimumIndex_eq.symm.trans_le sample.comparison.left_ge)

/-- The actual later root-state ball retains an earlier observation's independently paid radius request.

The original comparison indices supply the additional stage floor. The
same original canonical-radius theorem consumes that computed payment for
the exact later selected state; neither observation nor root is rebuilt.
-/
theorem radius_lt_after {parameter : Canonical} {root : Certificate parameter}
    {earlierAccuracy laterAccuracy : AccuracyRequest}
    (earlier : ResidualObservation root earlierAccuracy) (later : ResidualObservation root laterAccuracy)
    (after : earlier.comparison.leftIndex ≤ later.comparison.leftIndex) :
    (root.value.name.process.ball later.state).radiusSq < (radiusRequest root earlierAccuracy).tolerance := by
  have minimum : Geometric.Search.firstQuarterBelow 1 0 (radiusRequest root earlierAccuracy).tolerance ≤
      earlier.comparison.leftIndex := earlier.minimumIndex_eq.symm.trans_le earlier.comparison.left_ge
  rewrite [later.state_eq]
  exact sampled_radius_lt root earlierAccuracy (minimum.trans after)

/-- The actual cached state radius is strictly below its original residual-accuracy allowance. -/
theorem radius_lt_accuracy {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    (root.value.name.process.ball sample.state).radiusSq < accuracy.tolerance :=
  sample.radius_lt.trans_le (radiusRequest_le root accuracy)

/-- The actual paid witness preserves the original certificate's quantitative denominator clearance. -/
theorem reading_normSq_lower {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    root.apart.certificate.lowerSq ≤ Norm.Basic.normSq sample.reading :=
  root.apart.certificate.lower sample.state
    (root.value.name.process.possible_inside sample.reading_possible)

/-- The actual paid witness is nonzero by the original certificate's retained apartness. -/
theorem reading_nonzero {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) : sample.reading ≠ 0 := by
  have lower := sample.reading_normSq_lower
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt root.apart.certificate.positive) lower

/-- The same actual witness pays the exact indexed square-residual request. -/
theorem reading_residual_lt {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    Norm.Basic.normSq (sample.reading * sample.reading - parameter) < accuracy.tolerance :=
  sample.residual_lt sample.observation.witness_possible

/-- The paid witness remains possible at the original cached name's initial state. -/
theorem reading_possible_start {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    root.value.name.process.Possible root.value.name.state sample.reading := by
  have possible := sample.reading_possible
  rewrite [sample.state_eq] at possible
  exact Process.Sampling.stateAt_possible_at_start root.value.name.process root.value.name.state
    sample.comparison.leftIndex possible

/-- A cached certificate of an original tracked owner retains that owner's initial-box membership.

Complete certificate equality transports the actual selected state and its
possibility proof to the original owner's process. The original owner then
supplies initial-box containment without another isolation or sample selection.
-/
theorem reading_in_initial_box {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) (owner : Topology.SquareRootContinuationChain.Owner parameter)
    (cache_eq : root = owner.certificate owner.parameterNonzero) :
    owner.track.initial.box.Contains sample.reading :=
  candidate_in_initial_box owner cache_eq sample.reading_possible

end ResidualObservation

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
