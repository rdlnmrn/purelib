module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
public import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Cached original geometric observations in finite denominator preparation -/

public section
namespace Purelib.Approximation.Gaussian.Geometric.Preparation

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.Gaussian

/-- The coherent numerical presentation of the same retained geometric sample program. -/
@[expose] def sampledChannel (source : GeometricApproximation) : CoherentNamed :=
  CoherentNamed.ofApproximation source.toApproximation

/-- The actual refinement-state type of that same retained sample presentation. -/
abbrev State (source : GeometricApproximation) := Refinement.State (sampledChannel source)

/-- The cached observation is exactly the displayed ball at the same retained original source state. -/
abbrev Readback (source : GeometricApproximation) (state : State source) (ball : Ball) :=
  ball = (sampledChannel source).name.process.ball state.source

/-- The original observation's rational centre certifies whole-ball separation by the quantitative sufficient test. -/
abbrev Separated (ball : Ball) := ball.Separated

/-- Consume the cached actual ball to prepare the original channel through its retained sample-program comparison. -/
@[expose] def fromBall (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (state : State source) (ball : Ball) (readback : Readback source state ball) (separated : Separated ball) :
    Division.Prepared channel :=
  let apart := Enclosure.Residual.apartOfCenter ball separated
  let actual : Ball.Apart ((sampledChannel source).name.process.ball state.source) := readback ▸ apart
  let evidence := Process.Apart.Based.possibleApartOfBall (sampledChannel source).name.process state.source actual
  let prepared := Division.Prepared.ofEvidence state evidence
  prepared.transport equivalent.symm

/-- The same retained geometric observation preparation preserves its original common center bound. -/
theorem fromBall_centerBound (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (state : State source) (ball : Ball) (readback : Readback source state ball) (separated : Separated ball) :
    (fromBall source channel equivalent state ball readback separated).denominator.name.process.centerBound =
      source.centerBound := (rfl)

/-- The same actual cached-ball preparation retains the original explicit whole-ball lower floor.

The original ball's center-separation estimate supplies its positive
possible-value floor. Apartification divides that retained floor by eight;
transport changes the original channel index without replacing the ball.
-/
theorem fromBall_lowerSq (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (state : State source) (ball : Ball) (readback : Readback source state ball) (separated : Separated ball) :
    (fromBall source channel equivalent state ball readback separated).apart.certificate.lowerSq =
      (Purelib.Data.Gaussian.Norm.Basic.normSq ball.center / 2 - ball.radiusSq) / 8 := by
  cases readback
  rfl

set_option genInjectivity false in
/-- A successful actual cached-ball preparation or the failed sufficient test on this same finite observation. -/
inductive Outcome (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (state : State source) (ball : Ball) (readback : Readback source state ball) where
  /-- The actual observation's separation supplies the same computed original-channel preparation. -/
  | prepared (separated : Separated ball) (result : Division.Prepared channel)
      (result_eq : result = fromBall source channel equivalent state ball readback separated)
  /-- The actual finite observation does not certify separation; this asserts no operational zero. -/
  | inconclusive (failed : ¬ Separated ball)

constructive_injectivity Outcome

set_option genInjectivity false in
/-- One supplied original geometric state, its cached actual ball and its typed preparation outcome. -/
structure Observation (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (original : State source := Refinement.State.initial (sampledChannel source)) where
  /-- The actual retained supplied state of the same geometric sample presentation. -/
  state : State source
  /-- The complete cached state, including its original retry index, is the supplied state. -/
  state_eq : state = original
  /-- The once read actual ball at the supplied original state. -/
  ball : Ball
  /-- The cached ball is the same observation of this exact original source state. -/
  readback : Readback source state ball
  /-- Success or current inconclusivity retains that same cached original observation. -/
  outcome : Outcome source channel equivalent state ball readback

constructive_injectivity Observation

/-- Inspect the actual supplied original state once, retaining its complete ball and typed sufficient-test outcome.

The procedure consumes this same state and reads its ball once. Current
inconclusivity is a failed finite sufficient test, with no operational-zero
claim and no hidden advancement or replacement of the supplied state.
-/
@[expose] def inspectAt (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) (state : State source) :
    Observation source channel equivalent state :=
  let ball := (sampledChannel source).name.process.ball state.source
  let outcome := if separated : Separated ball then
      Outcome.prepared separated (fromBall source channel equivalent state ball rfl separated) rfl
    else .inconclusive separated
  ⟨state, rfl, ball, rfl, outcome⟩

/-- Read and cache the unchanged original initial observation through the same finite inspection procedure. -/
@[expose] def inspectInitial (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    Observation source channel equivalent :=
  inspectAt source channel equivalent (Refinement.State.initial (sampledChannel source))

/-- Initial inspection preserves the complete original state, retry index, ball and sufficient-test branch. -/
theorem inspectInitial_eq (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    inspectInitial source channel equivalent =
      (let state := Refinement.State.initial (sampledChannel source)
       let ball := (sampledChannel source).name.process.ball state.source
       let outcome := if separated : Separated ball then
           Outcome.prepared separated (fromBall source channel equivalent state ball rfl separated) rfl
         else .inconclusive separated
       ⟨state, rfl, ball, rfl, outcome⟩) := rfl

/-- Inspection retains the complete supplied original state without another refinement. -/
theorem inspectAt_state (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) (state : State source) :
    (inspectAt source channel equivalent state).state = state := rfl

/-- Initial inspection keeps the original zero retry index. -/
theorem inspectInitial_nextIndex (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    (inspectInitial source channel equivalent).state.nextIndex = 0 := rfl

/-- The stored initial observation's centre is the same original geometric sample at index zero. -/
theorem inspectInitial_center (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    (inspectInitial source channel equivalent).ball.center = source.sample 0 := rfl

/-- The stored initial observation's radius is the same original geometric allowance at index zero. -/
theorem inspectInitial_radius (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed) :
    (inspectInitial source channel equivalent).ball.radiusSq =
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius source.errorScale 0 := rfl

set_option genInjectivity false in
/-- A paid original geometric observation and its retained denominator preparation.

The positive lower bound applies to all actual source samples. The retained
bounded search starts at the supplied original state, pays half that lower
bound, and separates the cached observed ball. Preparation consumes that same
state and ball through the original sample-program comparison.
-/
structure Paid (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (initial : State source) (lowerSq : Fraction.Rational) where
  /-- The original sample lower quadrance is strictly positive. -/
  positive : 0 < lowerSq
  /-- Every actual original source sample meets the same lower quadrance. -/
  lower : ∀ index, lowerSq ≤ Norm.Basic.normSq (source.sample index)
  /-- The retained finite observation request. -/
  target : Fraction.Rational
  /-- The request is half the original lower quadrance. -/
  target_eq : target = lowerSq / 2
  /-- The cached finite search consumes the original scale and current source index. -/
  selection : Geometric.Search.Selection source.errorScale initial.source target
  /-- The actual paid state of the original sampled process. -/
  state : State source
  /-- The paid process state uses exactly the retained search index. -/
  source_eq : state.source = selection.stage
  /-- The paid state is the original process's refinement at the retained request. -/
  refined : state.source = (sampledChannel source).name.process.refine
    initial.source target selection.targetPositive
  /-- This supplied request leaves the next canonical automatic request unchanged. -/
  nextIndex_eq : state.nextIndex = initial.nextIndex
  /-- The cached actual observed original process ball. -/
  ball : Ball
  /-- The cached ball is the observation of exactly the retained paid source state. -/
  readback : Readback source state ball
  /-- The cached allowance is the attained allowance of that same bounded search. -/
  radius_eq : ball.radiusSq = selection.allowance
  /-- The actual observed ball satisfies the existing sufficient separation test. -/
  separated : Separated ball
  /-- The once constructed preparation retains the unchanged original channel. -/
  prepared : Division.Prepared channel
  /-- Preparation consumes exactly the retained original state, cached ball and bridge. -/
  prepared_eq : prepared = fromBall source channel equivalent state ball readback separated

constructive_injectivity Paid

/-- A retained geometric selection is the original sample process's exact refinement index. -/
theorem selection_refined (source : GeometricApproximation) (initial : State source)
    (target : Fraction.Rational)
    (selection : Geometric.Search.Selection source.errorScale initial.source target) :
    selection.stage = (sampledChannel source).name.process.refine
      initial.source target selection.targetPositive := by
  change selection.stage = Geometric.Search.firstQuarterBelow source.errorScale initial.source target
  unfold Geometric.Search.firstQuarterBelow
  rewrite [selection.stage_eq, selection.fuel_eq, selection.ceiling_eq, selection.quotient_eq]
  rfl

/-- Pay one original observation request derived from an all-index positive sample lower bound.

The finite search reuses the current source index. Its attained allowance and
the original sample are cached together as the actual observed process ball.
The lower bound proves separation directly, so no inconclusive branch or
caller-supplied successful search is needed under these hypotheses.
-/
@[expose] def fromLower (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (initial : State source) (lowerSq : Fraction.Rational) (positive : 0 < lowerSq)
    (lower : ∀ index, lowerSq ≤ Norm.Basic.normSq (source.sample index)) :
    Paid source channel equivalent initial lowerSq :=
  let target := lowerSq / 2
  let targetPositive := Fraction.Order.Field.div_pos_direct positive
    (by decide : (0 : Fraction.Rational) < 2)
  let selection := Geometric.Search.Selection.build source.errorScale source.errorScale_nonneg
    initial.source target targetPositive
  let state : State source :=
    { source := selection.stage
      nextIndex := initial.nextIndex
      persists := fun possible => initial.persists
        (source.toApproximation.possible_persists selection.lower possible) }
  let ball : Ball :=
    { center := source.sample selection.stage
      radiusSq := selection.allowance
      radiusSq_nonneg := selection.allowance_eq.symm ▸
        Geometric.Basic.quarterRadius_nonneg source.errorScale_nonneg selection.stage }
  have readback : Readback source state ball := by
    apply (Ball.mk.injEq _ _ _ _ _ _).mpr
    exact ⟨rfl, selection.allowance_eq⟩
  have separated : Separated ball := by
    change 2 * selection.allowance < Norm.Basic.normSq (source.sample selection.stage)
    have small : selection.allowance * 2 < lowerSq :=
      (Fraction.Order.Field.lt_div_iff_pos
        (by decide : (0 : Fraction.Rational) < 2)).mp selection.accurate
    rewrite [Fraction.Field.mul_comm] at small
    exact small.trans_le (lower selection.stage)
  let prepared := fromBall source channel equivalent state ball readback separated
  ⟨positive, lower, target, rfl, selection, state, rfl,
    selection_refined source initial target selection, rfl,
    ball, readback, rfl, separated, prepared, rfl⟩

/-- The paid cached ball's center is the original source sample at its retained index. -/
theorem Paid.center {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) :
    paid.ball.center = source.sample paid.selection.stage := by
  have same := congrArg Ball.center paid.readback
  change paid.ball.center = source.sample paid.state.source at same
  rewrite [paid.source_eq] at same
  exact same

/-- The original observed ball pays the retained positive finite request. -/
theorem Paid.accurate {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) : paid.ball.radiusSq < paid.target := by
  rewrite [paid.radius_eq]
  exact paid.selection.accurate

/-- The paid observed ball contains every later actual original sample. -/
theorem Paid.contains_later {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) {later : Nat}
    (order : paid.selection.stage ≤ later) : paid.ball.Contains (source.sample later) := by
  change Norm.Basic.normSq (source.sample later - paid.ball.center) ≤ paid.ball.radiusSq
  rewrite [paid.center, paid.radius_eq, paid.selection.allowance_eq]
  exact source.later_close order

/-- Every candidate in the paid original observed ball meets its retained apartness lower bound. -/
theorem Paid.lower_bound {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) {value : Purelib.Data.Gaussian.Basic.Canonical}
    (inside : paid.ball.Contains value) :
    (Enclosure.Residual.apartOfCenter paid.ball paid.separated).lowerSq ≤ Norm.Basic.normSq value :=
  (Enclosure.Residual.apartOfCenter paid.ball paid.separated).lower inside

end Purelib.Approximation.Gaussian.Geometric.Preparation
end
