module

public import Purelib.Computation.Machine.Simulation

/-!
# Certified first halting stages in bounded execution

The scan inspects stage zero and advances the actual cached configuration
once per inspected stage. A found result retains the first stage, its exact
output and exclusion of every earlier halt. Exhaustion retains the actual
last configuration and proves only absence through the supplied bound.
-/

public section

namespace Purelib.Computation.Machine.Halting

/-- Every displayed stage strictly before the supplied stage has no outermost halt output. -/
@[expose] def NoHaltBefore (initial : Configuration) (stage : Nat) : Prop :=
  ∀ earlier, earlier < stage → (Simulation.run initial earlier).output = none

/-- Every displayed stage through the supplied inclusive bound has no outermost halt output. -/
@[expose] def NoHaltThrough (initial : Configuration) (bound : Nat) : Prop :=
  ∀ stage, stage ≤ bound → (Simulation.run initial stage).output = none

set_option genInjectivity false in
/-- A retained first halt binds its exact stage and value to the same original bounded simulation. -/
structure First (initial : Configuration) (bound : Nat) where
  /-- The actual first successful halting stage. -/ stage : Nat
  /-- The original outermost returned value at that stage. -/ value : Value
  /-- The found stage lies within the original inclusive bound. -/ within : stage ≤ bound
  /-- The actual original simulation reaches this exact halt value at that stage. -/ reaches :
    Simulation.run initial stage = .halted value
  /-- Every preceding stage has no successful output. -/ before : NoHaltBefore initial stage

namespace First

/-- A first-halt certificate retains its actual successful output at the same stage. -/
theorem output {initial : Configuration} {bound : Nat} (first : First initial bound) :
    (Simulation.run initial first.stage).output = some first.value := congrArg Configuration.output first.reaches

/-- Two first-halt certificates for the same original configuration retain the same first stage. -/
theorem stage_unique {initial : Configuration} {leftBound rightBound : Nat}
    (left : First initial leftBound) (right : First initial rightBound) : left.stage = right.stage := by
  cases Nat.lt_trichotomy left.stage right.stage with
  | inl earlier =>
      have impossible := left.output.symm.trans (right.before left.stage earlier)
      nomatch impossible
  | inr alternatives =>
      cases alternatives with
      | inl equal => exact equal
      | inr earlier =>
          have impossible := right.output.symm.trans (left.before right.stage earlier)
          nomatch impossible

/-- Two first-halt certificates for the same original configuration retain the same exact returned value. -/
theorem value_unique {initial : Configuration} {leftBound rightBound : Nat}
    (left : First initial leftBound) (right : First initial rightBound) : left.value = right.value := by
  have sameStage := left.stage_unique right
  have sameOutput := left.output.symm.trans
    ((congrArg (fun stage => (Simulation.run initial stage).output) sameStage).trans right.output)
  exact Option.some.inj sameOutput

end First

set_option genInjectivity false in
/-- A bounded inspection either retains its actual first halt or the exact last state and complete bounded absence. -/
inductive Result (initial : Configuration) (bound : Nat) where
  /-- The same original bounded simulation has its retained first halt. -/ | found (first : First initial bound)
  /-- The finite scan exhausted its original inclusive bound. -/ | pending (current : Configuration)
      (currentEq : current = Simulation.run initial bound) (absent : NoHaltThrough initial bound)

/-- Extend the retained earlier absence with the same current nonhalting configuration's output. -/
private theorem through_of_current {initial current : Configuration} {stage : Nat}
    (currentEq : Simulation.run initial stage = current) (before : NoHaltBefore initial stage)
    (absent : current.output = none) : NoHaltThrough initial stage := by
  intro earlier order
  cases Nat.lt_or_eq_of_le order with
  | inl strict => exact before earlier strict
  | inr equal =>
      exact (congrArg (fun index => (Simulation.run initial index).output) equal).trans
        ((congrArg Configuration.output currentEq).trans absent)

/-- Scan actual successive cached configurations with structural finite fuel and retained earlier-stage certificates. -/
private def scan (initial : Configuration) (stage : Nat) (current : Configuration)
    (currentEq : Simulation.run initial stage = current) (before : NoHaltBefore initial stage)
    (fuel : Nat) : Result initial (stage + fuel) :=
  match fuel with
  | 0 =>
      match observed : current.output with
      | some value => .found ⟨stage, value, Nat.le_refl stage,
          currentEq.trans (Configuration.output_some observed), before⟩
      | none => .pending current currentEq.symm (through_of_current currentEq before observed)
  | fuel + 1 =>
      match observed : current.output with
      | some value => .found ⟨stage, value, Nat.le_add_right stage (fuel + 1),
          currentEq.trans (Configuration.output_some observed), before⟩
      | none =>
          have through := through_of_current currentEq before observed
          have nextEq : Simulation.run initial (stage + 1) = current.step := congrArg Configuration.step currentEq
          have nextBefore : NoHaltBefore initial (stage + 1) :=
            fun earlier order => through earlier (Nat.le_of_lt_succ order)
          let next := scan initial (stage + 1) current.step nextEq nextBefore fuel
          have boundEq : (stage + 1) + fuel = stage + (fuel + 1) :=
            (Nat.succ_add stage fuel).trans (Nat.add_succ stage fuel).symm
          boundEq ▸ next
termination_by structural fuel

/-- Inspect stages zero through the inclusive bound, retaining the first halt or exact finite exhaustion evidence. -/
def inspect (initial : Configuration) (bound : Nat) : Result initial bound :=
  let result := scan initial 0 initial rfl (fun earlier impossible => (Nat.not_lt_zero earlier impossible).elim) bound
  Nat.zero_add bound ▸ result

/-- Read the retained first stage of one actual bounded inspection. -/
@[expose] def Result.firstStage {initial : Configuration} {bound : Nat} : Result initial bound → Option Nat
  | .found first => some first.stage
  | .pending _ _ _ => none

/-- Compute the first halting stage through the supplied inclusive bound, including initially halted configurations. -/
@[expose] def firstHalt (initial : Configuration) (bound : Nat) : Option Nat := (inspect initial bound).firstStage

/-- A reported first stage retains the exact same simulation's full first-halt certificate. -/
theorem firstHalt_some {initial : Configuration} {bound stage : Nat} (observed : firstHalt initial bound = some stage) :
    ∃ first : First initial bound, first.stage = stage := by
  unfold firstHalt at observed
  cases result : inspect initial bound with
  | found first =>
      rewrite [result] at observed
      have projected : some first.stage = some stage := observed
      exact ⟨first, Option.some.inj projected⟩
  | pending current currentEq absent =>
      rewrite [result] at observed
      cases observed

/-- Bounded absence excludes every successful output through that exact original inclusive bound. -/
theorem firstHalt_none {initial : Configuration} {bound : Nat} (observed : firstHalt initial bound = none) :
    NoHaltThrough initial bound := by
  unfold firstHalt at observed
  cases result : inspect initial bound with
  | found first =>
      rewrite [result] at observed
      cases observed
  | pending current currentEq absent => exact absent

/-- Every reported first stage is within its actual inclusive simulation bound. -/
theorem firstHalt_le {initial : Configuration} {bound stage : Nat}
    (observed : firstHalt initial bound = some stage) : stage ≤ bound := by
  rcases firstHalt_some observed with ⟨first, stageEq⟩
  exact stageEq ▸ first.within

/-- A first halt newly found after bounded absence occurs strictly after that earlier bound. -/
theorem firstHalt_after_none {initial : Configuration} {earlier later stage : Nat}
    (absent : firstHalt initial earlier = none) (observed : firstHalt initial later = some stage) :
    earlier < stage := by
  rcases firstHalt_some observed with ⟨first, stageEq⟩
  apply Nat.lt_of_not_ge
  intro order
  have actualOrder : first.stage ≤ earlier := stageEq.symm ▸ order
  have impossible := first.output.symm.trans (firstHalt_none absent first.stage actualOrder)
  nomatch impossible

/-- Initially halted configurations are detected at stage zero under every finite bound. -/
theorem firstHalt_initial (value : Value) (bound : Nat) : firstHalt (.halted value) bound = some 0 := by
  let first : First (.halted value) 0 :=
    ⟨0, value, Nat.le_refl 0, rfl, fun earlier impossible => (Nat.not_lt_zero earlier impossible).elim⟩
  unfold firstHalt
  cases result : inspect (.halted value) bound with
  | found next =>
      exact congrArg Option.some (next.stage_unique first)
  | pending current currentEq absent =>
      have impossible : some value = none := absent 0 (Nat.zero_le bound)
      nomatch impossible

/-- A retained first halt cannot disappear or change stage under a larger finite bound. -/
theorem firstHalt_persists {initial : Configuration} {earlier later stage : Nat} (order : earlier ≤ later)
    (observed : firstHalt initial earlier = some stage) : firstHalt initial later = some stage := by
  rcases firstHalt_some observed with ⟨first, stageEq⟩
  cases result : inspect initial later with
  | found next =>
      unfold firstHalt
      rewrite [result]
      change some next.stage = some stage
      exact congrArg Option.some ((next.stage_unique first).trans stageEq)
  | pending current currentEq absent =>
      have impossible := first.output.symm.trans (absent first.stage (Nat.le_trans first.within order))
      nomatch impossible

/-- Halting means that one finite bounded execution reaches an actual outermost returned value. -/
@[expose] def Halts (initial : Configuration) : Prop :=
  ∃ stage value, Simulation.run initial stage = .halted value

/-- A found first stage supplies the same original configuration's finite halting witness. -/
theorem halts_of_firstHalt {initial : Configuration} {bound stage : Nat}
    (observed : firstHalt initial bound = some stage) : Halts initial := by
  rcases firstHalt_some observed with ⟨first, _⟩
  exact ⟨first.stage, first.value, first.reaches⟩

/-- Every actual finite halt is detected by the inclusive scan at that same bound. -/
theorem firstHalt_of_halted {initial : Configuration} {bound : Nat} {value : Value}
    (observed : Simulation.run initial bound = .halted value) : ∃ stage, firstHalt initial bound = some stage := by
  cases result : inspect initial bound with
  | found first =>
      refine ⟨first.stage, ?_⟩
      unfold firstHalt
      rewrite [result]
      rfl
  | pending current currentEq absent =>
      have impossible := (congrArg Configuration.output observed).symm.trans (absent bound (Nat.le_refl bound))
      nomatch impossible

/-- Halting is exactly detection of a first stage at some supplied finite bound. -/
theorem halts_iff_firstHalt (initial : Configuration) :
    Halts initial ↔ ∃ bound stage, firstHalt initial bound = some stage := by
  constructor
  · intro halted
    rcases halted with ⟨bound, value, reached⟩
    rcases firstHalt_of_halted reached with ⟨stage, observed⟩
    exact ⟨bound, stage, observed⟩
  · intro observed
    rcases observed with ⟨bound, stage, observed⟩
    exact halts_of_firstHalt observed

/-- A delayed finite program has no successful output through its original tick count. -/
theorem delay_absent (ticks : Nat) (input : Value) {bound : Nat} (within : bound ≤ ticks) :
    firstHalt (Configuration.initial (Program.delay ticks) input) bound = none := by
  cases observed : firstHalt (Configuration.initial (Program.delay ticks) input) bound with
  | none => rfl
  | some stage =>
      rcases firstHalt_some observed with ⟨first, _⟩
      have running := Simulation.delay_running ticks input (Nat.le_trans first.within within)
      have impossible := running.symm.trans first.reaches
      nomatch impossible

/-- The first halt of a delayed finite program is exactly its original tick count plus one. -/
theorem delay_first (ticks : Nat) (input : Value) {bound : Nat} (within : ticks + 1 ≤ bound) :
    firstHalt (Configuration.initial (Program.delay ticks) input) bound = some (ticks + 1) := by
  let initial := Configuration.initial (Program.delay ticks) input
  let first : First initial (ticks + 1) :=
    ⟨ticks + 1, input, Nat.le_refl _, Simulation.delay_halted ticks input, by
      intro earlier before
      exact congrArg Configuration.output (Simulation.delay_running ticks input (Nat.le_of_lt_succ before))⟩
  unfold firstHalt
  cases result : inspect initial bound with
  | found next => exact congrArg Option.some (next.stage_unique first)
  | pending current currentEq absent =>
      have impossible := first.output.symm.trans (absent first.stage within)
      nomatch impossible

/-- No finite bound of the explicit loop can supply a first halting stage. -/
theorem loop_absent (input : Value) (bound : Nat) :
    firstHalt (Configuration.initial Program.loop input) bound = none := by
  cases observed : firstHalt (Configuration.initial Program.loop input) bound with
  | none => rfl
  | some stage =>
      rcases firstHalt_some observed with ⟨first, _⟩
      have same := Simulation.loop_run input first.stage
      have impossible := same.symm.trans first.reaches
      nomatch impossible

end Purelib.Computation.Machine.Halting

end
