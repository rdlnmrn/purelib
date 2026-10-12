module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Computation

import Purelib.Integration.CertifiedProgram

import Purelib.CCL.Progressive.IntegrationPrograms
public import Purelib.Data.Gaussian.Norm.Comparison
public import Purelib.Approximation.Gaussian.Sequence.Process

public section

/-!
# Finite integration model queries and checked readings

This is the source boundary shared by numerical chart replay and the public
integration observation runner.  The control data contain no source
function.  A reply retains its finite path model, cached sample and allowance
with their specification equalities.

The numerical checks enforce the declared bounds.  Acceptance of invented
replies does not prove their global coherence; generated accuracy uses the
certified program's existing finite estimates.
-/

namespace Purelib.CCL.Progressive.IntegrationReplay

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.Data.Rat in
/-- The canonical rational scalar type. -/
abbrev Coordinate := Fraction.Rational
open Purelib in
/-- The canonical Gaussian rational type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Enclosure in
/-- A Gaussian rational ball with a nonnegative squared radius. -/
abbrev Ball := Approximation.Gaussian.Enclosure.Ball
section
open Purelib.Integration.Program.Gaussian
/-- A finite path model retaining its sample, allowance and specification equalities. -/
abbrev CachedModel := Cached.Basic.CachedModel
/-- A stage-indexed integration program retaining exact numerical caches. -/
abbrev CachedProgram := Cached.Basic.CachedProgram
end

section
open Purelib.Computation
/-- An ordered finite trace of stage-index queries and cached-model replies. -/
abbrev Trace := Query.Basic.Trace Nat CachedModel
/-- A finite query computation whose replies are retained integration models. -/
abbrev QueryComputation (Value : Type) := Computation.Query.Protocol Nat CachedModel Value

end

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Numerical bounds sufficient to check cached-model replies.

The record retains nonnegative error and center bounds. It contains no stage function and cannot itself query an
integration program. -/
structure Control where
  /-- The nonnegative scale of the geometric error allowance. -/ errorScale : Fraction.Rational
  /-- The error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- The nonnegative upper bound for sample squared norms. -/ centerBound : Fraction.Rational
  /-- The center bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound

constructive_injectivity Control

/-- Project a cached program's retained numerical control bounds. -/
@[expose] def control (program : CachedProgram) : Control :=
  ⟨program.errorScale, program.errorScale_nonneg, program.centerBound, program.centerBound_nonneg⟩

open Purelib.Approximation.Rational in
/-- Find the first stage at or after the current index whose quarter-radius is below the target.

The original error scale, current stage and rational target are supplied
to the same finite geometric search. Its selected stage is retained unchanged. -/
@[expose] def selectedIndex (control : Control) (request : Request) : Nat :=
  Geometric.Search.firstQuarterBelow control.errorScale request.current request.target

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A finite integration observation with its sampled value, allowance and ball.

The complete cached-model reply is retained separately in the query trace; this record is the numerical reading of that
reply. -/
structure Reading where
  /-- The queried stage index. -/ index : Nat
  /-- The retained Gaussian sample. -/ sample : Gaussian
  /-- The reply's retained integration allowance. -/ allowance : Fraction.Rational
  /-- The Gaussian ball built from the sample and control radius. -/ ball : Ball

constructive_injectivity Reading

open Purelib.Approximation.Rational in
/-- Project a cached reply into a numerical reading at the supplied index.

The ball uses the control's nonnegative quarter-radius. This projection does not itself validate the reply's allowance
or center bound. -/
@[expose] def reading (control : Control) (index : Nat) (reply : CachedModel) : Reading :=
  { index := index
    sample := reply.sample
    allowance := reply.allowance
    ball := ⟨reply.sample, Geometric.Basic.quarterRadius control.errorScale index,
      Geometric.Basic.quarterRadius_nonneg control.errorScale_nonneg index⟩ }

@[expose] public section

open Purelib.Data.Rat in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A concrete violated numerical bound in a cached-model reply.

The certificate retains the stage, actual comparison operands and proof that either the allowance or sample-norm bound
fails. -/
inductive InvalidReply where
  /-- The reply's allowance exceeds its permitted geometric radius. -/ | allowance (index : Nat) (observed permitted :
    Fraction.Rational)
      (violated : ¬ observed ≤ permitted)
  /-- The sample's squared norm exceeds the retained center bound. -/ | center (index : Nat) (sample : Gaussian)
    (permitted : Fraction.Rational)
      (violated : ¬ Norm.Basic.normSq sample ≤ permitted)
deriving DecidableEq

constructive_injectivity InvalidReply

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Check the allowance and sample-norm bounds of a cached reply.

Success returns its numerical reading. Failure identifies a violated bound using the actual comparison operands; the
norm test uses the executable unreduced comparison. -/
@[expose] def validate (control : Control) (index : Nat) (reply : CachedModel) : Except InvalidReply Reading :=
  letI := Data.Gaussian.Basic.Canonical.Norm.Comparison.decidableNormSqLE reply.sample control.centerBound
  let permitted := Geometric.Basic.quarterRadius control.errorScale index
  if allowance : reply.allowance ≤ permitted then
    if center : Norm.Basic.normSq reply.sample ≤ control.centerBound then .ok (reading control index reply)
    else .error (.center index reply.sample control.centerBound center)
  else .error (.allowance index reply.allowance permitted allowance)

open Purelib.Approximation.Rational in
/-- An invalidity certificate retains the actual operands of this reply and control.

Each constructor must name the supplied index and its corresponding observed value and permitted bound. The sample
itself is retained for a center failure. -/
@[expose] def InvalidReply.Matches (control : Control) (index : Nat) (reply : CachedModel) : InvalidReply → Prop
  | .allowance atIndex observed permitted _ =>
      atIndex = index ∧ observed = reply.allowance ∧ permitted = Geometric.Basic.quarterRadius control.errorScale index
  | .center atIndex sample permitted _ =>
      atIndex = index ∧ sample = reply.sample ∧ permitted = control.centerBound

/-- Every validation error retains the actual reply and control operands. -/
theorem validate_error {control : Control} {index : Nat} {reply : CachedModel} {error : InvalidReply}
    (failure : validate control index reply = .error error) : error.Matches control index reply := by
  unfold validate at failure
  dsimp only at failure
  split at failure
  · split at failure
    · cases failure
    · cases failure
      exact ⟨rfl, rfl, rfl⟩
  · cases failure
    exact ⟨rfl, rfl, rfl⟩

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
/-- Validation returns the projected reading exactly when both numerical bounds hold. -/
theorem validate_ok_iff (control : Control) (index : Nat) (reply : CachedModel) :
    validate control index reply = .ok (reading control index reply) ↔
      reply.allowance ≤ Geometric.Basic.quarterRadius control.errorScale index ∧ Norm.Basic.normSq reply.sample
        ≤ control.centerBound := by
  unfold validate
  dsimp only
  split
  · rename_i allowance
    split
    · rename_i center
      exact ⟨fun _ => ⟨allowance, center⟩, fun _ => rfl⟩
    · rename_i center
      constructor
      · intro impossible
        cases impossible
      · intro bounds
        exact (center bounds.2).elim
  · rename_i allowance
    constructor
    · intro impossible
      cases impossible
    · intro bounds
      exact (allowance bounds.1).elim

/-- A validation error proves that the two required numerical bounds do not both hold. -/
theorem validate_error_violated {control : Control} {index : Nat} {reply : CachedModel}
    {error : InvalidReply} (failure : validate control index reply = .error error) :
    ¬ (reply.allowance ≤ Geometric.Basic.quarterRadius control.errorScale index ∧ Norm.Basic.normSq
      reply.sample ≤ control.centerBound) := by
  intro bounds
  have successful := (validate_ok_iff control index reply).mpr bounds
  rw [successful] at failure
  cases failure

end

open Purelib.Computation in
/-- Query one stage and validate its retained cached-model reply. -/
@[expose] def read (control : Control) (index : Nat) : QueryComputation (Except InvalidReply Reading) :=
  (Computation.Query.Protocol.query index).map (validate control index)

open Purelib.Data.Gaussian in
/-- A cached program's own stage satisfies its retained numerical control bounds. -/
theorem validate_stage (program : CachedProgram) (index : Nat) :
    validate (control program) index (program.stage index) =
      .ok (reading (control program) index (program.stage index)) := by
  unfold validate control
  rw [dif_pos (program.modelAllowance_le index), dif_pos (by
    simpa only [Norm.Basic.normSq_eq_canonical] using program.sample_bounded index)]

/-- Reading a program's stage returns its successful numerical reading. -/
theorem read_stage_value (program : CachedProgram) (index : Nat) :
    ((read (control program) index).run program.stage).value =
      .ok (reading (control program) index (program.stage index)) :=
  validate_stage program index

open Purelib.Computation in
/-- One stage read records exactly the supplied index and oracle reply. -/
theorem read_trace (control : Control) (index : Nat) (oracle : Nat → CachedModel) :
    ((read control index).run oracle).trace = [⟨index, oracle index⟩] :=
  Computation.Query.Protocol.map_run_trace _ _ _

/-- Read the first stage selected by the accuracy request and control. -/
@[expose] def requestReading (control : Control) (request : Request) : QueryComputation (Except InvalidReply Reading) :=
  read control (selectedIndex control request)

open Purelib.Approximation.Gaussian in
/-- Refine the program's Gaussian name from the request's current stage.

The operation uses the existing positive-target refinement and retains the program's approximation process. -/
@[expose] def refinedName (program : CachedProgram) (request : Request) : Name.Basic.Named :=
  Name.Refinement.refined
    { process := program.approximation.toProcess, state := request.current }
    request.target request.positive

/-- Project the prepared cache selected by an accuracy request.

Preparation retains the chosen index and cache; the reading consumes those retained values with the program's numerical
control. -/
@[expose] def requestedReading (program : CachedProgram) (request : Request) : Reading :=
  let prepared := program.prepare request
  reading (control program) prepared.index prepared.cache

/-- The requested reading's ball is the ball of the refined name at its retained state. -/
theorem requestedReading_ball (program : CachedProgram) (request : Request) :
    (requestedReading program request).ball =
      (refinedName program request).process.ball (refinedName program request).state := rfl

/-- The requested ball's squared radius is strictly below the target. -/
theorem requestedReading_accurate (program : CachedProgram) (request : Request) :
    (requestedReading program request).ball.radiusSq < request.target :=
  (program.prepare request).radiusSq_accurate

/-- The requested integration allowance is strictly below the target. -/
theorem requestedReading_allowance (program : CachedProgram) (request : Request) :
    (requestedReading program request).allowance < request.target :=
  (program.prepare request).allowance_accurate

/-- The requested sample equals the integral sample of its selected stage model. -/
theorem requestedReading_sample_model (program : CachedProgram) (request : Request) :
    (requestedReading program request).sample =
      (program.stage (selectedIndex (control program) request)).model.integralSample :=
  (program.prepare request).sample_model

/-- The requested ball contains every sample from a stage at or after the selected index. -/
theorem requestedReading_contains_later (program : CachedProgram) (request : Request)
    {later : Nat} (order : selectedIndex (control program) request ≤ later) :
    (requestedReading program request).ball.Contains (program.stage later).sample :=
  (program.prepare request).contains_later order

end Purelib.CCL.Progressive.IntegrationReplay
