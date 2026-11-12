module

public import Purelib.Computation.Machine.Halting
public import Purelib.Approximation.Gaussian.Sequence.Process
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Process.Based
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Dyadic.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-!
# Total coherent shadows of finite machine computations

The finite description retains the original program, input and initial
configuration. Every sample uses an inclusive bounded first-stage scan.
A detected first halt fixes a positive rational amplitude forever; before
that halt the sample is zero. Quarter-power allowances pay every newly
observed jump and support total finite refinement without deciding halting.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.HaltingShadow

open Purelib
open Purelib.Computation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Approximation.Rational

set_option genInjectivity false in
/-- A finite shadow description retains the original program, input and exact cached initial machine configuration. -/
structure Code where
  /-- The original finite instruction-list program. -/ program : Machine.Program
  /-- Its original finite encoded input. -/ input : Machine.Value
  /-- The same initial machine configuration, cached once. -/ initial : Machine.Configuration
  /-- The configuration belongs to that exact original program and input. -/ initialEq :
    initial = Machine.Configuration.initial program input

namespace Code

/-- Construct the original shadow description, computing its finite initial configuration once. -/
@[expose] def ofProgram (program : Machine.Program) (input : Machine.Value) : Code :=
  ⟨program, input, Machine.Configuration.initial program input, rfl⟩

/-- Display finite program and input data for the fixed bounded-simulation shadow algorithm. -/
@[expose] def description (code : Code) : Machine.Value :=
  .pair (.number 0) (.pair (Machine.Value.encode code.program) code.input)

/-- Read the first halt through the displayed inclusive bound on the same original cached configuration. -/
@[expose] def firstHalt (code : Code) (bound : Nat) : Option Nat := Machine.Halting.firstHalt code.initial bound

end Code

/-- The fixed positive rational amplitude paid by a first halt at the displayed stage. -/
@[expose] def amplitude (stage : Nat) : Fraction.Rational := (1 / 2 : Fraction.Rational) ^ (stage + 1)

/-- Read the same amplitude in the real axis of the Gaussian-rational chart. -/
@[expose] def point (stage : Nat) : Gaussian.Basic.Canonical := ⟨amplitude stage, 0⟩

/-- The shadow's displayed squared allowance is the quarter power at the successor stage. -/
@[expose] def radiusSq (index : Nat) : Fraction.Rational := Geometric.Basic.quarterRadius 1 (index + 1)

/-- Every halting amplitude is strictly positive. -/
theorem amplitude_pos (stage : Nat) : 0 < amplitude stage :=
  Fraction.Order.Arithmetic.pow_pos_direct (by decide) _

/-- The squared norm of a halting point is exactly its same successor quarter-power allowance. -/
theorem point_normSq (stage : Nat) : Gaussian.Norm.Basic.normSq (point stage) = radiusSq stage := by
  rewrite [Gaussian.Norm.Basic.normSq_eq_canonical]
  change amplitude stage * amplitude stage + 0 * 0 = _
  have square : amplitude stage ^ 2 = (1 / 4 : Fraction.Rational) ^ (stage + 1) := by
    unfold amplitude
    rewrite [← pow_mul, Nat.mul_comm (stage + 1) 2, pow_mul,
      show ((1 / 2 : Fraction.Rational) ^ 2) = 1 / 4 by decide]
    rfl
  calc
    amplitude stage * amplitude stage + 0 * 0 = amplitude stage ^ 2 := by ring1
    _ = (1 / 4 : Fraction.Rational) ^ (stage + 1) := square
    _ = radiusSq stage := by
      unfold radiusSq
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Fraction.Field.one_mul]
      rfl

/-- Every displayed shadow allowance is positive at its finite stage. -/
theorem radiusSq_pos (index : Nat) : 0 < radiusSq index := Geometric.Basic.quarterRadius_pos (by decide) _

/-- Advancing the stage weakly decreases the original squared allowance. -/
theorem radiusSq_antitone {earlier later : Nat} (order : earlier ≤ later) : radiusSq later ≤ radiusSq earlier :=
  Geometric.Basic.quarterRadius_antitone (by decide) (Nat.succ_le_succ order)

namespace Code

/-- Compute a bounded shadow sample, returning zero until the original first halt has actually been observed. -/
@[expose] def sample (code : Code) (index : Nat) : Gaussian.Basic.Canonical :=
  match code.firstHalt index with
  | none => 0
  | some stage => point stage

/-- Once a first halt is observed, every later original sample is the same retained positive rational point. -/
theorem sample_after {code : Code} {bound stage : Nat} (observed : code.firstHalt bound = some stage)
    {later : Nat} (order : bound ≤ later) : code.sample later = point stage := by
  have observedLater : code.firstHalt later = some stage := Machine.Halting.firstHalt_persists order observed
  unfold sample
  rewrite [observedLater]
  rfl

/-- Every later sample remains inside the earlier sample's exact displayed squared allowance. -/
theorem later_close (code : Code) {earlier later : Nat} (order : earlier ≤ later) :
    Gaussian.Norm.Basic.normSq (code.sample later - code.sample earlier) ≤ radiusSq earlier := by
  cases earlierHalt : code.firstHalt earlier with
  | some stage =>
      have laterEq := code.sample_after earlierHalt order
      have earlierEq := code.sample_after earlierHalt (Nat.le_refl earlier)
      rewrite [laterEq, earlierEq, Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
      exact (radiusSq_pos earlier).le
  | none =>
      have earlierEq : code.sample earlier = 0 := by unfold sample; rewrite [earlierHalt]; rfl
      rewrite [earlierEq, Gaussian.Basic.sub_zero]
      cases laterHalt : code.firstHalt later with
      | none =>
          have laterEq : code.sample later = 0 := by unfold sample; rewrite [laterHalt]; rfl
          rewrite [laterEq, Gaussian.Norm.Basic.normSq_zero]
          exact (radiusSq_pos earlier).le
      | some stage =>
          have laterEq := code.sample_after laterHalt (Nat.le_refl later)
          rewrite [laterEq, point_normSq]
          exact radiusSq_antitone (Nat.le_of_lt (Machine.Halting.firstHalt_after_none earlierHalt laterHalt))

/-- Every original shadow sample meets the same fixed squared-norm bound one. -/
theorem sample_bounded (code : Code) (index : Nat) : Gaussian.Norm.Basic.normSq (code.sample index) ≤ 1 := by
  cases observed : code.firstHalt index with
  | none =>
      have equal : code.sample index = 0 := by unfold sample; rewrite [observed]; rfl
      rewrite [equal, Gaussian.Norm.Basic.normSq_zero]
      decide
  | some stage =>
      have equal := code.sample_after observed (Nat.le_refl index)
      rewrite [equal, point_normSq]
      exact Geometric.Basic.quarterRadius_le_scale (by decide) _

/-- Compute a finite refinement stage from the owned quarter-power search and the original current-stage floor. -/
@[expose] def refineIndex (current : Nat) (target : Fraction.Rational) : Nat :=
  max current (Geometric.Search.firstQuarterBelow 1 0 target)

/-- The retained refinement stage is no earlier than its actual original current stage. -/
theorem refineIndex_ge (current : Nat) (target : Fraction.Rational) : current ≤ refineIndex current target := by
  rewrite [refineIndex, Data.Nat.Order.max_eq_natMax]
  exact Data.Nat.Order.le_max_left _ _

/-- Every positive request is met strictly by the same computed refinement stage and successor allowance. -/
theorem refineIndex_accurate (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    radiusSq (refineIndex current target) < target := by
  have requestedLe : Geometric.Search.firstQuarterBelow 1 0 target ≤ refineIndex current target := by
    rewrite [refineIndex, Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_right _ _
  have successorLe := Nat.le_trans requestedLe (Nat.le_succ (refineIndex current target))
  exact (Geometric.Basic.quarterRadius_antitone (by decide) successorLe).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate 1 (by decide) 0 target positive)

/-- Package the original bounded simulation as total finite Gaussian approximation data with its proved allowances. -/
@[expose] def approximation (code : Code) : ApproximationData where
  sample := code.sample
  radiusSq := radiusSq
  radiusSq_nonneg index := (radiusSq_pos index).le
  later_close := code.later_close
  refineIndex current target _ := refineIndex current target
  refineIndex_ge current target _ := refineIndex_ge current target
  refineIndex_accurate := refineIndex_accurate
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := code.sample_bounded

/-- Translate the same retained approximation to its original finite-index persistent process. -/
@[expose] def process (code : Code) : Process := code.approximation.toProcess

/-- Name the same retained shadow process with the original constructive coherence certificate. -/
@[expose] def named (code : Code) : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation code.approximation

/-- Absence of any finite halting witness gives bounded absence at every displayed scan bound. -/
theorem firstHalt_of_noHalt (code : Code) (noHalt : ¬ Machine.Halting.Halts code.initial) (bound : Nat) :
    code.firstHalt bound = none := by
  cases observed : code.firstHalt bound with
  | none => rfl
  | some stage => exact (noHalt (Machine.Halting.halts_of_firstHalt observed)).elim

/-- Every original shadow sample is zero when no finite halt exists. -/
theorem sample_of_noHalt (code : Code) (noHalt : ¬ Machine.Halting.Halts code.initial) (index : Nat) :
    code.sample index = 0 := by
  unfold sample
  rewrite [code.firstHalt_of_noHalt noHalt index]
  rfl

/-- A shadow with no finite halt is operationally equivalent to the exact zero name. -/
def zero_of_noHalt (code : Code) (noHalt : ¬ Machine.Halting.Halts code.initial) :
    Equivalence.NamedEquivalent code.named.name (Name.Basic.Named.exact 0) :=
  let comparison := Equivalence.Equivalent.of_constant_samples code.approximation
    (Constant.constantApproximation 0) 0 (code.sample_of_noHalt noHalt) (fun _ => rfl)
  Equivalence.NamedEquivalent.trans
    (Name.Equivalence.approximationEquivalent_toNamed comparison)
    (Equivalence.NamedEquivalent.symm (Name.Exact.exact_toConstantNamed 0))

/-- Operational equivalence of the original shadow to zero excludes every actual finite halt. -/
theorem noHalt_of_zero (code : Code)
    (zero : Equivalence.NamedEquivalent code.named.name (Name.Basic.Named.exact 0)) :
    ¬ Machine.Halting.Halts code.initial := by
  intro halted
  rcases halted with ⟨bound, value, reached⟩
  rcases Machine.Halting.firstHalt_of_halted reached with ⟨stage, observed⟩
  let agreement := Equivalence.Equivalent.trans
    (Equivalence.Equivalent.symm (Equivalence.Equivalent.toNamed_sampling code.approximation)) zero
  let comparison := agreement.compare bound 0 (radiusSq stage) (radiusSq_pos stage)
  have close := comparison.close (leftLater := comparison.leftIndex) (rightLater := comparison.rightIndex)
    (Nat.le_refl _) (Nat.le_refl _)
  have leftEq := code.sample_after observed comparison.left_ge
  change Gaussian.Norm.Basic.normSq (code.sample comparison.leftIndex -
    (Name.Sampling.approximation (Name.Basic.Named.exact 0)).sample comparison.rightIndex) <
      radiusSq stage at close
  rewrite [leftEq, Name.Exact.exactNamedSample, Gaussian.Basic.sub_zero, point_normSq] at close
  exact lt_irrefl (radiusSq stage) close

/-- Read the actual index reached by the original canonical finite refinement trajectory. -/
@[expose] def reachedIndex (code : Code) (bound : Nat) : Nat :=
  Process.Sampling.stateAt code.process (show code.process.State from (0 : Nat)) bound

/-- The actual canonical trajectory at a supplied bound has reached at least that original machine-simulation index. -/
theorem reachedIndex_ge (code : Code) (bound : Nat) : bound ≤ code.reachedIndex bound := by
  have accurate := Process.Sampling.stateAt_accurate code.process
    (show code.process.State from (0 : Nat)) bound
  change radiusSq (code.reachedIndex bound) < Geometric.Basic.quarterRadius 1 bound at accurate
  apply Nat.le_of_not_gt
  intro earlier
  have order : code.reachedIndex bound + 1 ≤ bound := Nat.succ_le_of_lt earlier
  have reverse := Geometric.Basic.quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 1) order
  exact (not_lt_of_ge reverse) accurate

set_option genInjectivity false in
/-- Apartness retains an actual finite trajectory bound and its same reached source state as the base owner. -/
structure ReachedApart (code : Code) where
  /-- The supplied finite canonical refinement trajectory bound. -/ bound : Nat
  /-- The exact original source state reached by that trajectory. -/ state : code.process.State
  /-- The retained state is the original finite trajectory's actual output. -/ stateEq :
    state = code.reachedIndex bound
  /-- The positive candidate bound belongs to this same reached and based process. -/ apart :
    Process.Apart.Possible.PossibleApart (Process.Based.based code.process state)

/-- A bounded observed halt constructs apartness at an actually reached state with its same constant post-halt tail. -/
def apart_of_observed (code : Code) {bound stage : Nat} (observed : code.firstHalt bound = some stage) :
    ReachedApart code := by
  let state := code.reachedIndex bound
  have boundLe : bound ≤ state := code.reachedIndex_ge bound
  exact
    { bound := bound
      state := state
      stateEq := rfl
      apart :=
        { lowerSq := radiusSq stage
          positive := radiusSq_pos stage
          lower := by
            intro basedState value possible
            have atBase := Process.Based.based_initial_persists code.process state possible
            change ∃ later : Nat, state ≤ later ∧ value = code.sample later at atBase
            rcases atBase with ⟨later, stateLe, valueEq⟩
            have sampleEq := code.sample_after observed (Nat.le_trans boundLe stateLe)
            rewrite [valueEq, sampleEq, point_normSq]
            exact Fraction.Order.Basic.le_refl _ } }

/-- Apartness of an explicitly reached shadow state supplies a finite halting witness for its original machine. -/
theorem halts_of_apart (code : Code) (reached : ReachedApart code) : Machine.Halting.Halts code.initial := by
  let value := code.sample reached.state
  let basedState := Process.Based.BasedState.initial code.process reached.state
  have possible : (Process.Based.based code.process reached.state).Possible basedState value :=
    ⟨reached.state, Nat.le_refl _, rfl⟩
  have lower := reached.apart.lower basedState possible
  cases observed : code.firstHalt reached.state with
  | some stage => exact Machine.Halting.halts_of_firstHalt observed
  | none =>
      have valueEq : value = 0 := by unfold value sample; rewrite [observed]; rfl
      rewrite [valueEq, Gaussian.Norm.Basic.normSq_zero] at lower
      exact ((not_le_of_gt reached.apart.positive) lower).elim

/-- An unobserved initial halt excludes apartness asserted uniformly at all original source states. -/
theorem excludes_initial_apart (code : Code) (absent : code.firstHalt 0 = none) :
    Process.Apart.Possible.PossibleApart code.process → False := by
  intro apart
  let state : code.process.State := (0 : Nat)
  have possible : code.process.Possible state (code.sample 0) := ⟨0, Nat.le_refl 0, rfl⟩
  have lower := apart.lower state possible
  have equal : code.sample 0 = 0 := by unfold sample; rewrite [absent]; rfl
  rewrite [equal, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt apart.positive) lower

end Code

end Purelib.Approximation.Gaussian.Sequence.HaltingShadow

end
