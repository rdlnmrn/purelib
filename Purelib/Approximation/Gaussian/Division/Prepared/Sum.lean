module

public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
public import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Process.Conjugation
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Preparing sums and selecting apart summands

Two retained original source enclosures supply one cached sum ball. Its
checked sufficient separation prepares the original sum without another
starting refinement; a failed test retains both input caches and remains
inconclusive. Actual conjugated source histories remain distinct.

A comparison with a nonzero exact point computes one common sampling stage
and a positive radius budget for both original summands. Their cached readings
cannot both be small. The selected reading gives apartness throughout the
future of its same original state, without deciding whether the other summand
is zero.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared.Sum

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- An actual source presentation, comparison, retained state and certified cached enclosure of one original channel.

This dependent tuple retains the original owners directly. It performs no
sampling, changes no parent identity and asserts no nonzero sum.
-/
abbrev Source (channel : CoherentNamed) :=
  (presentation : CoherentNamed) ×
  (_equivalent : NamedEquivalent channel.name presentation.name) ×
  (state : Refinement.State presentation) ×
    {ball : Enclosure.Ball // ball = presentation.name.process.ball state.source}

namespace Source

/-- Read the original retained numerical presentation. -/
@[expose] def presentation {channel : CoherentNamed} (source : Source channel) : CoherentNamed := source.1

/-- Read the retained original-channel comparison. -/
@[expose] def equivalent {channel : CoherentNamed} (source : Source channel) :
    NamedEquivalent channel.name source.presentation.name := source.2.1

/-- Read the exact original state and its independent retry position. -/
@[expose] def state {channel : CoherentNamed} (source : Source channel) :
    Refinement.State source.presentation := source.2.2.1

/-- Read the stored actual ball without querying its process. -/
@[expose] def ball {channel : CoherentNamed} (source : Source channel) : Enclosure.Ball := source.2.2.2.val

/-- The stored ball is the original observation at its exact retained state. -/
theorem readback {channel : CoherentNamed} (source : Source channel) :
    source.ball = source.presentation.name.process.ball source.state.source := source.2.2.2.property

/-- Retain the supplied source, comparison, state and complete cached enclosure literally. -/
@[expose] def ofBall {channel : CoherentNamed} (presentation : CoherentNamed)
    (equivalent : NamedEquivalent channel.name presentation.name) (state : Refinement.State presentation)
    (ball : Enclosure.Ball) (readback : ball = presentation.name.process.ball state.source) : Source channel :=
  ⟨presentation, equivalent, state, ⟨ball, readback⟩⟩

/-- Conjugate the retained source and cached enclosure while preserving the full channel history. -/
@[expose] def conj {channel : CoherentNamed} (source : Source channel) : Source (CoherentNamed.conj channel) :=
  let state : Refinement.State (CoherentNamed.conj source.presentation) :=
    { source := source.state.source
      nextIndex := source.state.nextIndex
      persists := by
        rintro value ⟨original, possible, rfl⟩
        exact ⟨original, source.state.persists possible, rfl⟩ }
  ⟨CoherentNamed.conj source.presentation, CoherentNamed.conj_respects source.equivalent,
    state, ⟨source.ball.conj, congrArg Enclosure.Ball.conj source.readback⟩⟩

/-- Actual conjugation retains the original retry position. -/
theorem conj_nextIndex {channel : CoherentNamed} (source : Source channel) :
    source.conj.state.nextIndex = source.state.nextIndex := rfl

/-- Actual conjugation computes only the original cached ball's conjugate. -/
theorem conj_ball {channel : CoherentNamed} (source : Source channel) :
    source.conj.ball = source.ball.conj := rfl

/-- Twice conjugating the actual sources recovers only the cached ball, without replacing either channel parent. -/
theorem conj_conj_ball {channel : CoherentNamed} (source : Source channel) :
    source.conj.conj.ball = source.ball := Enclosure.Ball.conj_conj source.ball

end Source

/-- Pair the two actual retained operand states as a new sum request, without refining either operand.

Both supplied states retain their own retry positions in the source tuple.
The new sum request begins at retry zero and claims no canonical transition
from the original sum's initial state.
-/
@[expose] def pairedState {left right : CoherentNamed} (sources : Source left × Source right) :
    Refinement.State (CoherentNamed.add sources.1.presentation sources.2.presentation) where
  source := (sources.1.state.source, sources.2.state.source)
  nextIndex := 0
  persists := by
    rintro value ⟨first, second, firstPossible, secondPossible, rfl⟩
    exact ⟨first, second, sources.1.state.persists firstPossible,
      sources.2.state.persists secondPossible, rfl⟩

/-- The combined cached enclosure is the actual ball of the paired original source states. -/
theorem paired_readback {left right : CoherentNamed} (sources : Source left × Source right) :
    sources.1.ball.add sources.2.ball =
      (CoherentNamed.add sources.1.presentation sources.2.presentation).name.process.ball
        (pairedState sources).source :=
  congrArg₂ Enclosure.Ball.add sources.1.readback sources.2.readback

/-- Prepare the actual original sum from a certified separated combination of both retained input enclosures.

The original apartification consumes a whole-ball apart state at the same
paired source. No new starting refinement is needed; cancelling or currently
wide enclosures supply no such preparation.
-/
@[expose] def fromBalls {left right : CoherentNamed} (sources : Source left × Source right)
    (ball : Enclosure.Ball) (readback : ball = sources.1.ball.add sources.2.ball)
    (separated : ball.Separated) : Prepared (CoherentNamed.add left right) :=
  let actual := Prepared.ofBall (pairedState sources) ball (readback.trans (paired_readback sources))
    (Enclosure.Residual.apartOfCenter ball separated)
  let equivalent := Arithmetic.Sum.Congruence.coherentAdd_respects left sources.1.presentation
    right sources.2.presentation sources.1.equivalent sources.2.equivalent
  actual.transport equivalent.symm

/-- Cached-sum preparation uses exactly the original pair of source states as its initial apart state. -/
theorem fromBalls_source {left right : CoherentNamed} (sources : Source left × Source right)
    (ball : Enclosure.Ball) (readback : ball = sources.1.ball.add sources.2.ball)
    (separated : ball.Separated) :
    (fromBalls sources ball readback separated).denominator.name.state.source.source =
      (sources.1.state.source, sources.2.state.source) := rfl

/-- A typed successful sum preparation or current failed sufficient test on the same actual combined cached ball. -/
abbrev Result {left right : CoherentNamed} (sources : Source left × Source right)
    (ball : Enclosure.Ball) (readback : ball = sources.1.ball.add sources.2.ball) :=
  Sum {prepared : Prepared (CoherentNamed.add left right) //
    ∃ separated : ball.Separated, prepared = fromBalls sources ball readback separated}
    (PLift (¬ ball.Separated))

/-- Both original source/cache parents, the once-combined ball and the actual finite sum-preparation result. -/
abbrev Attempt (left right : CoherentNamed) :=
  (sources : Source left × Source right) ×
  (ball : {actual : Enclosure.Ball // actual = sources.1.ball.add sources.2.ball}) ×
    Result sources ball.val ball.property

/-- Check the actual combined cached ball once and retain its computed success or current inconclusivity. -/
@[expose] def inspect {left right : CoherentNamed} (sources : Source left × Source right) : Attempt left right :=
  let ball := sources.1.ball.add sources.2.ball
  let result : Result sources ball rfl :=
    if separated : ball.Separated then
      .inl ⟨fromBalls sources ball rfl separated, ⟨separated, rfl⟩⟩
    else .inr ⟨separated⟩
  ⟨sources, ⟨ball, rfl⟩, result⟩

namespace Attempt

/-- Read the same complete original input source/cache tuple retained by this finite attempt. -/
@[expose] def sources {left right : CoherentNamed} (attempt : Attempt left right) : Source left × Source right :=
  attempt.1

/-- Read this attempt's stored combined ball without combining either source again. -/
@[expose] def ball {left right : CoherentNamed} (attempt : Attempt left right) : Enclosure.Ball := attempt.2.1.val

/-- Read a successful retained preparation, leaving a failed finite sufficient test inconclusive. -/
@[expose] def prepared {left right : CoherentNamed} (attempt : Attempt left right) :
    Option (Prepared (CoherentNamed.add left right)) :=
  match attempt.2.2 with
  | .inl prepared => some prepared.val
  | .inr _ => none

end Attempt

/-- Inspection retains both complete original source/cache entries in their input order. -/
theorem inspect_sources {left right : CoherentNamed} (sources : Source left × Source right) :
    (inspect sources).sources = sources := rfl

/-- Inspection combines the two stored original balls without reading either input process. -/
theorem inspect_ball {left right : CoherentNamed} (sources : Source left × Source right) :
    (inspect sources).ball = sources.1.ball.add sources.2.ball := rfl

/-- A separated inspection stores the complete original cached-ball preparation. -/
theorem inspect_prepared {left right : CoherentNamed} (sources : Source left × Source right)
    (separated : (sources.1.ball.add sources.2.ball).Separated) :
    (inspect sources).prepared =
      some (fromBalls sources (sources.1.ball.add sources.2.ball) rfl separated) := by
  unfold inspect Attempt.prepared
  dsimp only
  rewrite [dif_pos separated]
  rfl

/-- A currently nonseparating combined enclosure returns no preparation and retains its failed finite test. -/
theorem inspect_inconclusive {left right : CoherentNamed} (sources : Source left × Source right)
    (failed : ¬ (sources.1.ball.add sources.2.ball).Separated) :
    (inspect sources).prepared = none := by
  unfold inspect Attempt.prepared
  dsimp only
  rewrite [dif_neg failed]
  rfl

set_option genInjectivity false in
/-- Original sum observations and explicit budgets certifying at least one apart summand. -/
structure Observation (left right : CoherentNamed) (point : Basic.Canonical) where
  /-- The entire original first summand. -/
  first : CoherentNamed
  /-- The retained first summand is the original input. -/
  first_eq : first = left
  /-- The entire original second summand. -/
  second : CoherentNamed
  /-- The retained second summand is the original input. -/
  second_eq : second = right
  /-- The actual exact point specified by the sum comparison. -/
  value : Basic.Canonical
  /-- The retained point is the original request. -/
  value_eq : value = point
  /-- The original sum's supplied operational identity. -/
  identity : NamedEquivalent (CoherentNamed.add left right).name (Coherence.exact point).name
  /-- The cached squared norm of the original point. -/
  norm : Rational
  /-- The norm is computed from that same point. -/
  norm_eq : norm = Norm.Basic.normSq point
  /-- The exact sum point is nonzero. -/
  norm_positive : 0 < norm
  /-- The comparison's actual positive squared tolerance. -/
  target : Rational
  /-- The comparison pays one sixteenth of the original point norm. -/
  target_eq : target = norm / 4 / 4
  /-- The comparison tolerance is positive. -/
  target_positive : 0 < target
  /-- The common original operand radius request. -/
  precision : Rational
  /-- The operand request pays one 256th of the original point norm. -/
  precision_eq : precision = norm / 4 / 4 / 4 / 4
  /-- The original operand radius request is positive. -/
  precision_positive : 0 < precision
  /-- The actual equal-index original sum approximation. -/
  sum : ApproximationData
  /-- The cached approximation uses both original summands. -/
  sum_eq : sum = Arithmetic.Sum.sampledSumApproximation left.name right.name
  /-- The actual finite comparison at the retained original sum and budget. -/
  comparison : Comparison sum (Name.Sampling.approximation (Coherence.exact point).name) 0 0 target
  /-- The same computed canonical sampling stage for both summands. -/
  index : Nat
  /-- The stage is computed after the actual sum comparison. -/
  index_eq : index = Search.firstQuarterBelow 1 comparison.leftIndex precision
  /-- The stage meets the retained comparison's original request. -/
  index_ge : comparison.leftIndex ≤ index
  /-- The actual first summand's cached original sampling state. -/
  firstSource : Refinement.State left
  /-- The first state is sampled at the same computed stage. -/
  first_source_eq : firstSource.source = Process.Sampling.stateAt left.name.process left.name.state index
  /-- The first state's canonical retry position follows the performed work. -/
  first_next_eq : firstSource.nextIndex = index + 1
  /-- The actual second summand's cached original sampling state. -/
  secondSource : Refinement.State right
  /-- The second state is sampled at the same computed stage. -/
  second_source_eq : secondSource.source = Process.Sampling.stateAt right.name.process right.name.state index
  /-- The second state's canonical retry position follows the performed work. -/
  second_next_eq : secondSource.nextIndex = index + 1
  /-- The cached original first summand reading. -/
  firstWitness : Basic.Canonical
  /-- The first reading is the witness of its actual cached state. -/
  first_witness_eq : firstWitness = (left.name.process.witness firstSource.source).val
  /-- The cached first reading is possible at that exact original state. -/
  first_possible : left.name.process.Possible firstSource.source firstWitness
  /-- The cached original second summand reading. -/
  secondWitness : Basic.Canonical
  /-- The second reading is the witness of its actual cached state. -/
  second_witness_eq : secondWitness = (right.name.process.witness secondSource.source).val
  /-- The cached second reading is possible at that exact original state. -/
  second_possible : right.name.process.Possible secondSource.source secondWitness
  /-- The first original enclosure meets the computed common radius request. -/
  first_radius_lt : (left.name.process.ball firstSource.source).radiusSq < precision
  /-- The second original enclosure meets the computed common radius request. -/
  second_radius_lt : (right.name.process.ball secondSource.source).radiusSq < precision
  /-- The sum of the same cached original readings meets the retained comparison. -/
  sum_close : Norm.Basic.normSq (firstWitness + secondWitness - point) < target

constructive_injectivity Observation

namespace Observation

/-- Construct the original sampled observation from its retained budgets and comparison.

The exact input caches and their readback equalities are parameters. The
construction computes one common stage, samples each original summand once,
and keeps the supplied comparison without another comparison call. -/
@[noinline, nospecialize] private def ofComparison
    (left right : CoherentNamed) (point : Basic.Canonical)
    (identity : NamedEquivalent (CoherentNamed.add left right).name (Coherence.exact point).name)
    (norm : Rational) (normEq : norm = Norm.Basic.normSq point) (normPositive : 0 < norm)
    (target : Rational) (targetEq : target = norm / 4 / 4) (targetPositive : 0 < target)
    (precision : Rational) (precisionEq : precision = norm / 4 / 4 / 4 / 4)
    (precisionPositive : 0 < precision)
    (sum : ApproximationData) (sumEq : sum = Arithmetic.Sum.sampledSumApproximation left.name right.name)
    (comparison : Comparison sum (Name.Sampling.approximation (Coherence.exact point).name)
      0 0 target) : Observation left right point := by
  let index := Search.firstQuarterBelow 1 comparison.leftIndex precision
  have indexGe : comparison.leftIndex ≤ index := Search.firstQuarterBelow_ge 1 comparison.leftIndex precision
  have accurate : Process.Sampling.refinementTarget index < precision :=
    Search.firstQuarterBelow_accurate 1 (by decide) comparison.leftIndex precision precisionPositive
  let firstSource := Refinement.State.sampled left index
  let secondSource := Refinement.State.sampled right index
  let firstState := firstSource.source
  let secondState := secondSource.source
  let firstWitness := (left.name.process.witness firstState).val
  let secondWitness := (right.name.process.witness secondState).val
  have close := comparison.close indexGe (Nat.le_refl comparison.rightIndex)
  have firstReading : (Name.Sampling.approximation left.name).sample index = firstWitness := rfl
  have secondReading : (Name.Sampling.approximation right.name).sample index = secondWitness := rfl
  have sumReading : sum.sample index = firstWitness + secondWitness :=
    (congrArg (fun approximation : ApproximationData => approximation.sample index) sumEq).trans
      ((Arithmetic.Sum.sampledSumApproximation_sample left.name right.name index).trans
        (congrArg₂ (fun first second : Basic.Canonical => first + second) firstReading secondReading))
  have differenceReading := congrArg₂ (fun first second : Basic.Canonical => first - second)
    sumReading (Exact.exactNamedSample point comparison.rightIndex)
  have normReading := congrArg Norm.Basic.normSq differenceReading
  have sumClose : Norm.Basic.normSq (firstWitness + secondWitness - point) < target :=
    (congrArg (fun squared : Rational => squared < target) normReading).mp close
  have firstRadius : (left.name.process.ball firstSource.source).radiusSq < precision :=
    (Refinement.State.sampled_accurate left index).trans accurate
  have secondRadius : (right.name.process.ball secondSource.source).radiusSq < precision :=
    (Refinement.State.sampled_accurate right index).trans accurate
  exact
    { first := left
      first_eq := rfl
      second := right
      second_eq := rfl
      value := point
      value_eq := rfl
      identity := identity
      norm := norm
      norm_eq := normEq
      norm_positive := normPositive
      target := target
      target_eq := targetEq
      target_positive := targetPositive
      precision := precision
      precision_eq := precisionEq
      precision_positive := precisionPositive
      sum := sum
      sum_eq := sumEq
      comparison := comparison
      index := index
      index_eq := rfl
      index_ge := indexGe
      firstSource := firstSource
      first_source_eq := Refinement.State.sampled_source left index
      first_next_eq := Refinement.State.sampled_nextIndex left index
      secondSource := secondSource
      second_source_eq := Refinement.State.sampled_source right index
      second_next_eq := Refinement.State.sampled_nextIndex right index
      firstWitness := firstWitness
      first_witness_eq := rfl
      first_possible := (left.name.process.witness firstState).property
      secondWitness := secondWitness
      second_witness_eq := rfl
      second_possible := (right.name.process.witness secondState).property
      first_radius_lt := firstRadius
      second_radius_lt := secondRadius
      sum_close := sumClose }

end Observation

/-- Compute one finite observation of both original summands at the same stage and retained budgets. -/
@[noinline, nospecialize] def observe (left right : CoherentNamed) (point : Basic.Canonical)
    (nonzero : point ≠ 0)
    (identity : NamedEquivalent (CoherentNamed.add left right).name (Coherence.exact point).name) :
    Observation left right point := by
  let norm := Norm.Basic.normSq point
  have normPositive : 0 < norm := Norm.Basic.normSq_pos nonzero
  let target := norm / 4 / 4
  have targetPositive : 0 < target := Order.Field.div_pos_direct
    (Order.Field.div_pos_direct normPositive (by decide)) (by decide)
  let precision := norm / 4 / 4 / 4 / 4
  have precisionPositive : 0 < precision := Order.Field.div_pos_direct
    (Order.Field.div_pos_direct targetPositive (by decide)) (by decide)
  let sum := Arithmetic.Sum.sampledSumApproximation left.name right.name
  let bridge : NamedEquivalent (CoherentNamed.add left right).name sum.toNamed :=
    Arithmetic.Sum.Bridge.coherentAdd_toNamed left right
  let sumIdentity : Equivalent sum (Name.Sampling.approximation (Coherence.exact point).name) :=
    Equivalent.trans (Equivalent.symm (Equivalent.toNamed_sampling sum))
      (NamedEquivalent.trans (NamedEquivalent.symm bridge) identity)
  let comparison : Comparison sum (Name.Sampling.approximation (Coherence.exact point).name)
      0 0 target := sumIdentity.compare 0 0 target targetPositive
  exact Observation.ofComparison left right point identity norm rfl normPositive
    target rfl targetPositive precision rfl precisionPositive sum rfl comparison

/-- The same observed sum retains a quarter of its original nonzero comparison point's squared norm. -/
theorem Observation.sum_lower {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) :
    observation.norm / 4 ≤ Norm.Basic.normSq (observation.firstWitness + observation.secondWitness) := by
  have budget : observation.target ≤ observation.norm / 4 := by
    rewrite [observation.target_eq]
    have quarterNonnegative :=
      (Order.Field.div_pos_direct observation.norm_positive (by decide : (0 : Rational) < 4)).le
    apply (Order.Field.div_le_iff_pos (by decide : (0 : Rational) < 4)).mpr
    have ordered := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide : (1 : Rational) ≤ 4) quarterNonnegative
    rewrite [mul_one] at ordered
    exact ordered
  have close : Norm.Basic.normSq (point - (observation.firstWitness + observation.secondWitness)) ≤
      Norm.Basic.normSq point / 4 := by
    rewrite [Norm.Bounds.normSq_sub_symm, ← observation.norm_eq]
    exact observation.sum_close.le.trans budget
  rewrite [observation.norm_eq]
  exact Norm.Bounds.quarter_normSq_le_of_close point _ close

/-- If the cached first summand is too small, the same observed sum certifies the cached second summand's lower norm. -/
theorem Observation.second_lower {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point)
    (small : ¬ observation.norm / 4 / 4 ≤ Norm.Basic.normSq observation.firstWitness) :
    observation.norm / 4 / 4 ≤ Norm.Basic.normSq observation.secondWitness := by
  have firstUpper : Norm.Basic.normSq observation.firstWitness ≤ observation.norm / 4 / 4 := by
    cases Order.Basic.le_total (Norm.Basic.normSq observation.firstWitness) (observation.norm / 4 / 4) with
    | inl ordered => exact ordered
    | inr ordered => exact False.elim (small ordered)
  have sumLower : 4 * (observation.norm / 4 / 4) ≤
      Norm.Basic.normSq (observation.firstWitness + observation.secondWitness) := by
    have same : 4 * (observation.norm / 4 / 4) = observation.norm / 4 :=
      (mul_comm _ _).trans (Field.div_mul_cancel_of_ne _ _ (by decide))
    rewrite [same]
    exact observation.sum_lower
  exact Norm.Bounds.other_normSq_lower_of_sum _ _ _ sumLower firstUpper

/-- A candidate at the original observed summand state retains a quarter of that summand's lower norm. -/
private theorem candidate_lower (channel : CoherentNamed) (source : Refinement.State channel)
    (witness : Basic.Canonical) (witnessPossible : channel.name.process.Possible source.source witness)
    (norm : Rational) (large : norm / 4 / 4 ≤ Norm.Basic.normSq witness)
    (accurate : (channel.name.process.ball source.source).radiusSq < norm / 4 / 4 / 4 / 4)
    {value : Basic.Canonical} (possible : channel.name.process.Possible source.source value) :
    norm / 4 / 4 / 4 ≤ Norm.Basic.normSq value := by
  let center := (channel.name.process.ball source.source).center
  let radius := (channel.name.process.ball source.source).radiusSq
  have inside := channel.name.process.possible_inside possible
  have witnessInside := channel.name.process.possible_inside witnessPossible
  change Norm.Basic.normSq (value - center) ≤ radius at inside
  change Norm.Basic.normSq (witness - center) ≤ radius at witnessInside
  have reverse : Norm.Basic.normSq (center - witness) ≤ radius := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact witnessInside
  have deviation : Norm.Basic.normSq (value - witness) ≤ 4 * radius := by
    calc
      Norm.Basic.normSq (value - witness) ≤
          2 * (Norm.Basic.normSq (value - center) + Norm.Basic.normSq (center - witness)) :=
        Norm.Bounds.normSq_sub_le_via value center witness
      _ ≤ 2 * (radius + radius) := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct inside reverse) (by decide)
      _ = 4 * radius := by ring1
  have movement : Norm.Basic.normSq (witness - value) ≤ Norm.Basic.normSq witness / 4 := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    calc
      Norm.Basic.normSq (value - witness) ≤ 4 * radius := deviation
      _ ≤ 4 * (norm / 4 / 4 / 4 / 4) := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate.le (by decide)
      _ = (norm / 4 / 4) / 4 :=
        (mul_comm _ _).trans (Field.div_mul_cancel_of_ne _ _ (by decide))
      _ ≤ Norm.Basic.normSq witness / 4 :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct large (by decide)
  calc
    norm / 4 / 4 / 4 = (norm / 4 / 4) / 4 := rfl
    _ ≤ Norm.Basic.normSq witness / 4 :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct large (by decide)
    _ ≤ Norm.Basic.normSq value := Norm.Bounds.quarter_normSq_le_of_close witness value movement

/-- Prepare the original selected summand using its same cached state, reading and explicit lower norm. -/
private def prepareSummand (channel : CoherentNamed) (source : Refinement.State channel)
    (witness : Basic.Canonical) (witnessPossible : channel.name.process.Possible source.source witness)
    (norm : Rational) (positive : 0 < norm) (large : norm / 4 / 4 ≤ Norm.Basic.normSq witness)
    (accurate : (channel.name.process.ball source.source).radiusSq < norm / 4 / 4 / 4 / 4) : Prepared channel := by
  have lowerPositive : 0 < norm / 4 / 4 / 4 := Order.Field.div_pos_direct
    (Order.Field.div_pos_direct (Order.Field.div_pos_direct positive (by decide)) (by decide)) (by decide)
  exact ofEvidence source
    { lowerSq := norm / 4 / 4 / 4
      positive := lowerPositive
      lower := fun state _ possible => candidate_lower channel source witness witnessPossible norm large accurate
        (state.persists possible) }

/-- Select and prepare an original summand from the retained common observation without sampling either input again. -/
@[noinline, nospecialize] def Observation.prepare {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) : Sum (Prepared left) (Prepared right) :=
  if first : observation.norm / 4 / 4 ≤ Norm.Basic.normSq observation.firstWitness then
    .inl (prepareSummand left observation.firstSource observation.firstWitness observation.first_possible
      observation.norm observation.norm_positive first (by
        have accurate := observation.first_radius_lt
        rewrite [observation.precision_eq] at accurate
        exact accurate))
  else
    .inr (prepareSummand right observation.secondSource observation.secondWitness observation.second_possible
      observation.norm observation.norm_positive (observation.second_lower first) (by
        have accurate := observation.second_radius_lt
        rewrite [observation.precision_eq] at accurate
        exact accurate))

set_option genInjectivity false in
/-- A selected original summand retaining its complete common observation and the exact cached preparation outcome. -/
structure Selection (left right : CoherentNamed) (point : Basic.Canonical) where
  /-- The complete original sum observation, including both states and computed budgets. -/
  observation : Observation left right point
  /-- The actual successful preparation of one original summand. -/
  prepared : Sum (Prepared left) (Prepared right)
  /-- Selection consumes this same observation without another sampling call. -/
  prepared_eq : prepared = observation.prepare

constructive_injectivity Selection

/-- Observe the original nonzero sum once and retain the selected preparation with the same complete observation. -/
@[noinline, nospecialize] def select (left right : CoherentNamed) (point : Basic.Canonical)
    (nonzero : point ≠ 0)
    (identity : NamedEquivalent (CoherentNamed.add left right).name (Coherence.exact point).name) :
    Selection left right point :=
  let observation := observe left right point nonzero identity
  let prepared := observation.prepare
  ⟨observation, prepared, rfl⟩

end Purelib.Approximation.Gaussian.Division.Prepared.Sum

end
