module

public import Purelib.Approximation.Gaussian.Pi.Integral
public import Purelib.Approximation.Rational.Pi.Source.Presentation
public import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data

namespace Purelib.Approximation.Gaussian.Pi.Integral

open Purelib.Approximation
open Purelib.Approximation.Rational.Pi
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Enclosure.Ball.Data
open Source.Presentation

/-- The named integral's ball retains the lower endpoint and squared width of its history's bound.

The witness and sampled answer instead use the midpoint of that same bound.
The ball is the original rational-bound adapter's ball, not a reconstructed
interval or an assertion that its center equals the midpoint. -/
public theorem named_observations (state : Source.boundProcess.State) :
    (named.name.process.ball state).center =
        RationalEmbedding.realPoint (Source.boundProcess.bound state).lower ∧
      (named.name.process.witness state).val =
        RationalEmbedding.realPoint (Source.boundProcess.bound state).midpoint ∧
      (named.name.process.ball state).radiusSq = (Source.boundProcess.bound state).width ^ 2 := by
  have ball := Process.RationalBound.ball_eq Source.boundProcess state
  exact ⟨congrArg (·.center) ball, witness_eq state, congrArg (·.radiusSq) ball⟩

/-- The proposed finite readings agree with the observations of this exact history state. -/
@[expose] public def ObservationValid (state : Source.boundProcess.State)
    (ball : BallData) (midpoint : Basic.Canonical) : Prop :=
  ball.center = (named.name.process.ball state).center ∧
    ball.radiusSq = (named.name.process.ball state).radiusSq ∧
    midpoint = (named.name.process.witness state).val

set_option genInjectivity false in
/-- The result of comparing proposed observations with a retained pi history. -/
public inductive ObservationCheck (state : Source.boundProcess.State)
    (ball : BallData) (midpoint : Basic.Canonical) where
  /-- All three proposed fields match the actual observations. -/
  | valid (proof : ObservationValid state ball midpoint)
  /-- The proposed center differs from the retained ball center. -/
  | wrongCenter (proof : ball.center ≠ (named.name.process.ball state).center)
  /-- The proposed squared radius differs from the retained ball radius. -/
  | wrongRadius (proof : ball.radiusSq ≠ (named.name.process.ball state).radiusSq)
  /-- The proposed midpoint differs from the retained process witness. -/
  | wrongMidpoint (proof : midpoint ≠ (named.name.process.witness state).val)

/-- Compare finite observation data directly with the original history's process observations.

The supplied state already carries its original history and cached frontier. This
check neither reconstructs that history nor verifies an arbitrary proof term. -/
@[expose] public def checkObservation (state : Source.boundProcess.State)
    (ball : BallData) (midpoint : Basic.Canonical) : ObservationCheck state ball midpoint :=
  if center : ball.center = (named.name.process.ball state).center then
    if radius : ball.radiusSq = (named.name.process.ball state).radiusSq then
      if witness : midpoint = (named.name.process.witness state).val then
        .valid ⟨center, radius, witness⟩
      else .wrongMidpoint witness
    else .wrongRadius radius
  else .wrongCenter center

/-- Decide exact observation agreement using the same typed mismatch check. -/
@[expose] public def recognizeObservation (state : Source.boundProcess.State)
    (ball : BallData) (midpoint : Basic.Canonical) : Decidable (ObservationValid state ball midpoint) :=
  match checkObservation state ball midpoint with
  | .valid proof => .isTrue proof
  | .wrongCenter proof => .isFalse (fun valid => proof valid.1)
  | .wrongRadius proof => .isFalse (fun valid => proof valid.2.1)
  | .wrongMidpoint proof => .isFalse (fun valid => proof valid.2.2)

/-- The original process observations always satisfy the exact history-bound contract. -/
public theorem actualObservation_valid (state : Source.boundProcess.State) :
    ObservationValid state (BallData.ofBall (named.name.process.ball state))
      (named.name.process.witness state).val := ⟨rfl, rfl, rfl⟩

/-- An accepted ball and midpoint are the lower endpoint, squared width and midpoint of the same history. -/
public theorem observation_eq_bound (state : Source.boundProcess.State)
    (ball : BallData) (midpoint : Basic.Canonical) (valid : ObservationValid state ball midpoint) :
    ball.center = RationalEmbedding.realPoint (Source.boundProcess.bound state).lower ∧
      ball.radiusSq = (Source.boundProcess.bound state).width ^ 2 ∧
      midpoint = RationalEmbedding.realPoint (Source.boundProcess.bound state).midpoint := by
  have observed := named_observations state
  exact ⟨valid.1.trans observed.1, valid.2.1.trans observed.2.2, valid.2.2.trans observed.2.1⟩

/-- Quoting and checking an actual named-process refinement recovers its retained history.

The refinement is the original source process request, including its saved
frontier, continuation and cached readings. This round trip checks a quotation
of an already certified history; it does not decide arbitrary supplied proofs. -/
public theorem check_refinement (state : Source.boundProcess.State) (target : Fraction.Rational)
    (positive : 0 < target) :
    History.check
        (History.quote (named.name.process.refine state target positive)) =
      .ok (Source.boundProcess.request state (Rational.Request.Square.gapTarget target)
        (Rational.Request.Square.gapTarget_pos positive)) := by
  rw [← refine_eq]
  exact History.check_quote _

set_option genInjectivity false in
/-- The checked refinement of the original integral name from a raw history.

Success retains the exact predecessor and returned histories, the original
ball and witness equations, and squared-radius accuracy at that same returned
state. Failures retain the nonpositive target or the original history failure. -/
public inductive RawRefinement (code : History.RawCode)
    (target : Fraction.Rational) where
  /-- The squared tolerance is not positive. -/
  | nonpositive (reason : target ≤ 0)
  /-- The original finite history scan failed. -/
  | invalidHistory (failure : History.RawFailure)
      (checked : History.checkRaw code = .error failure)
  /-- The original named process refined the checked predecessor. -/
  | accepted (previous : History.State)
      (checked : History.checkRaw code = .ok previous)
      (positive : 0 < target) (returned : History.State)
      (refined : returned = named.name.process.refine previous target positive)
      (center : (named.name.process.ball returned).center =
        RationalEmbedding.realPoint (Source.boundProcess.bound returned).lower)
      (witness : (named.name.process.witness returned).val =
        RationalEmbedding.realPoint (Source.boundProcess.bound returned).midpoint)
      (radius : (named.name.process.ball returned).radiusSq =
        (Source.boundProcess.bound returned).width ^ 2)
      (accurate : (named.name.process.ball returned).radiusSq < target)

/-- Check a raw history and refine the public integral name to a positive squared tolerance.

The positive target is converted by the original `gapTarget`; the accepted
history returned by `History.requestRaw` is used directly for all observations. -/
@[expose] public def refineRaw (code : History.RawCode)
    (target : Fraction.Rational) : RawRefinement code target :=
  match AccuracyRequest.Presentation.check target with
  | .nonpositive reason => .nonpositive reason
  | .valid positive =>
    match History.requestRaw code (Rational.Request.Square.gapTarget target) with
    | .invalidHistory failure checked => .invalidHistory failure checked
    | .nonpositive _ _ reason => False.elim ((not_lt_of_ge reason) (Rational.Request.Square.gapTarget_pos positive))
    | .accepted previous checked _ returned requested _ _ => by
      have refined : returned = named.name.process.refine previous target positive := by
        change returned = process.refine previous target positive
        rw [refine_eq]
        exact requested
      have observations := named_observations returned
      have accurate : (named.name.process.ball returned).radiusSq < target := by
        rw [refined]
        exact named.name.process.accurate previous target positive
      exact .accepted previous checked positive returned refined
        observations.1 observations.2.1 observations.2.2 accurate

set_option genInjectivity false in
/-- Refinement of the original integral name from a history with unchecked cuts.

Success retains the checked predecessor and the actual returned state, together
with the original observation equations and squared-radius accuracy. -/
public inductive CutsRefinement (code : History.CutsCode) (target : Fraction.Rational) where
  /-- The squared tolerance is not positive. -/
  | nonpositive (reason : target ≤ 0)
  /-- The finite history scan identified its first invalid entry. -/
  | invalidHistory (failure : History.CutsFailure)
      (checked : History.checkCuts code = .error failure)
  /-- The original named process refined the checked predecessor. -/
  | accepted (previous : History.State)
      (checked : History.checkCuts code = .ok previous)
      (positive : 0 < target) (returned : History.State)
      (refined : returned = named.name.process.refine previous target positive)
      (center : (named.name.process.ball returned).center =
        RationalEmbedding.realPoint (Source.boundProcess.bound returned).lower)
      (witness : (named.name.process.witness returned).val =
        RationalEmbedding.realPoint (Source.boundProcess.bound returned).midpoint)
      (radius : (named.name.process.ball returned).radiusSq =
        (Source.boundProcess.bound returned).width ^ 2)
      (accurate : (named.name.process.ball returned).radiusSq < target)

/-- Check unchecked cuts once and refine the resulting original pi history.

Target positivity is checked first. An accepted history is passed directly to
the original named process; failures retain the first located history failure. -/
@[expose] public def refineCuts (code : History.CutsCode)
    (target : Fraction.Rational) : CutsRefinement code target :=
  match AccuracyRequest.Presentation.check target with
  | .nonpositive reason => .nonpositive reason
  | .valid positive =>
    match checked : History.checkCuts code with
    | .error failure => .invalidHistory failure checked
    | .ok previous =>
      let returned := named.name.process.refine previous target positive
      let observations := named_observations returned
      .accepted previous checked positive returned rfl
        observations.1 observations.2.1 observations.2.2
        (named.name.process.accurate previous target positive)

namespace PairedPresentation

/-- The original one-sided observation type of the pi rational-bound adapter. -/
public abbrev Observation := PairedObservation
  (Source.boundProcess.lowerRequestProcess 1 (by decide))
  (Source.boundProcess.upperRequestProcess 1 (by decide))

/-- Two independently certified finite histories, retaining their original order. -/
public abbrev Code := History.Display × History.Display

/-- The lower endpoint of the first state is below the upper endpoint of the second. -/
@[expose] public def Valid (code : Code) : Prop :=
  (Source.boundProcess.bound (History.read code.1)).lower ≤
    (Source.boundProcess.bound (History.read code.2)).upper

/-- Decide the actual cross-state ordering condition. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) := inferInstanceAs
  (Decidable ((Source.boundProcess.bound (History.read code.1)).lower ≤
    (Source.boundProcess.bound (History.read code.2)).upper))

/-- A pair of original history displays with a certified endpoint ordering. -/
public abbrev Display := {code : Code // Valid code}

/-- Construct the original paired observation from the two accepted states. -/
@[expose] public def read (display : Display) : Observation :=
  ⟨History.read display.val.1, History.read display.val.2, display.property⟩

/-- Quote both original states directly, retaining the original ordering evidence. -/
@[expose] public def quote (observation : Observation) : Display := by
  refine ⟨(History.display observation.lowerState, History.display observation.upperState), ?_⟩
  change (Source.boundProcess.bound (History.read (History.display observation.lowerState))).lower ≤
    (Source.boundProcess.bound (History.read (History.display observation.upperState))).upper
  rw [History.read_display, History.read_display]
  exact observation.ordered

/-- Reading a quotation recovers the original states and proof-irrelevant observation. -/
public theorem read_quote (observation : Observation) : read (quote observation) = observation := by
  have extensional (left right : Observation) (lower : left.lowerState = right.lowerState)
      (upper : left.upperState = right.upperState) : left = right := by
    cases left
    cases right
    cases lower
    cases upper
    rfl
  apply extensional
  · exact History.read_display observation.lowerState
  · exact History.read_display observation.upperState

/-- Quoting a readback recovers both original finite history displays. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  cases display with
  | mk code valid =>
    cases code with
    | mk lower upper =>
      change (History.display (History.read lower), History.display (History.read upper)) = (lower, upper)
      rw [History.display_read, History.display_read]

/-- Paired presentations agree when both retained finite histories agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare both finite history codes using their original comparisons. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) := by
  letI (a b : History.Display) : Decidable (a = b) :=
    match History.compare a b with
    | .isTrue same => .isTrue (Subtype.ext same)
    | .isFalse different => .isFalse (fun equal => different (congrArg Subtype.val equal))
  exact inferInstanceAs (Decidable (left.val = right.val))

/-- Code equality agrees exactly with equality of the original paired observations. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    cases Subtype.ext same
    rfl
  · intro same
    have equal := congrArg quote same
    rw [quote_read, quote_read] at equal
    exact congrArg Subtype.val equal

/-- The explicit finite presentation for compatible pairs of pi histories. -/
@[expose] public def presentation : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun equal => equal.symm, fun first second => first.trans second⟩

/-- A finite history input succeeds when its original indexed scan returns a state. -/
@[expose] public def RawHistoryValid (code : History.RawCode) : Prop :=
  ∃ state, History.checkRaw code = .ok state

/-- Quote the two original observation states as finite history inputs. -/
@[expose] public def quoteRaw (observation : Observation) : History.RawCode × History.RawCode :=
  (History.quoteRaw observation.lowerState, History.quoteRaw observation.upperState)

set_option genInjectivity false in
/-- A paired raw-history check retains its original observation or a located failure. -/
public inductive RawCheck (lower upper : History.RawCode) where
  /-- Both histories and their endpoint ordering are accepted. -/
  | accepted (observation : Observation) (lower_eq : History.quoteRaw observation.lowerState = lower)
      (upper_eq : History.quoteRaw observation.upperState = upper)
  /-- The lower history failed its original finite scan. -/
  | invalidLower (failure : History.RawFailure) (invalid : ¬ RawHistoryValid lower)
  /-- The upper history failed its original finite scan. -/
  | invalidUpper (failure : History.RawFailure) (invalid : ¬ RawHistoryValid upper)
  /-- Both histories were valid but the original endpoint ordering failed. -/
  | unordered (lowerState upperState : History.State) (lower_eq : History.quoteRaw lowerState = lower)
      (upper_eq : History.quoteRaw upperState = upper)
      (proof : ¬ (Source.boundProcess.bound lowerState).lower ≤ (Source.boundProcess.bound upperState).upper)

/-- Scan both finite histories once and retain the original states in their paired observation. -/
@[expose] public def checkRaw (lower upper : History.RawCode) : RawCheck lower upper :=
  match lowerResult : History.checkRaw lower with
  | .error failure => .invalidLower failure (fun ⟨_, success⟩ => by rw [lowerResult] at success; cases success)
  | .ok lowerState =>
    match upperResult : History.checkRaw upper with
    | .error failure => .invalidUpper failure (fun ⟨_, success⟩ => by rw [upperResult] at success; cases success)
    | .ok upperState =>
      let lowerEq := (History.checkRaw_agrees lower lowerState lowerResult).2
      let upperEq := (History.checkRaw_agrees upper upperState upperResult).2
      if ordered : (Source.boundProcess.bound lowerState).lower ≤ (Source.boundProcess.bound upperState).upper then
        .accepted ⟨lowerState, upperState, ordered⟩ lowerEq upperEq
      else .unordered lowerState upperState lowerEq upperEq ordered

/-- An accepted observation quotes to the exact two proposed history inputs. -/
public theorem quoteRaw_accepted {lower upper : History.RawCode} (observation : Observation)
    (lowerEq : History.quoteRaw observation.lowerState = lower)
    (upperEq : History.quoteRaw observation.upperState = upper) : quoteRaw observation = (lower, upper) :=
  Prod.ext lowerEq upperEq

/-- Every original paired observation is accepted with its exact original states. -/
public theorem checkRaw_quoteRaw (observation : Observation) :
    ∃ (result : Observation) (lowerEq : History.quoteRaw result.lowerState = (quoteRaw observation).1)
      (upperEq : History.quoteRaw result.upperState = (quoteRaw observation).2),
      checkRaw (quoteRaw observation).1 (quoteRaw observation).2 = .accepted result lowerEq upperEq ∧
        result = observation := by
  refine ⟨observation, rfl, rfl, ?_, rfl⟩
  unfold checkRaw quoteRaw
  dsimp only
  split
  · next failure failed =>
      have accepted := History.checkRaw_quoteRaw observation.lowerState
      rw [failed] at accepted
      cases accepted
  · next lowerState lowerResult =>
    have lowerEq := Except.ok.inj (lowerResult.symm.trans (History.checkRaw_quoteRaw observation.lowerState))
    cases lowerEq
    split
    · next failure failed =>
        have accepted := History.checkRaw_quoteRaw observation.upperState
        rw [failed] at accepted
        cases accepted
    · next upperState upperResult =>
      have upperEq := Except.ok.inj (upperResult.symm.trans (History.checkRaw_quoteRaw observation.upperState))
      cases upperEq
      split
      · next ordered =>
          cases observation
          rfl
      · next unordered => exact False.elim (unordered observation.ordered)

end PairedPresentation

end Purelib.Approximation.Gaussian.Pi.Integral
