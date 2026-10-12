module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Periods.PeriodPolicies
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

import Purelib.Computation.Query.Boundary
public import Purelib.Riemann.Periods.PolynomialPeriodInput
public import Purelib.Riemann.Periods.PeriodObservation

@[expose] public section

/-!
# Coefficient-only canonical standard-period observations

The public constructors accept a polynomial, raw standard-entry indices,
finite policies and a finite observation request.  They compute square-factor
reduction, genus, index validity and canonical preparation.  Successful
results retain the actual receipts and their numerical/ownership contracts;
failures have finite input or index evidence, never a numerical fuel budget.

These are standard periods of the reduced curve `z^2 = q`.  They do not
silently interpret its `x^k dx/z` as the original equation's `x^k dx/y`:
that different request needs the square-factor differential transport layer.
Different policies share one prepared entry.  No equality between different
cycles, sheets or independent preparations is asserted.
-/

namespace Purelib.Riemann.Periods.PolynomialPeriodObservation

universe u

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Riemann.Periods.PolynomialPeriodInput (Selection PreparedEntry Failure)
open Purelib.Riemann.Periods.PeriodPolicies (Policy Request program record)

set_option genInjectivity false in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Polynomial in
/-- Retain one computed standard-period entry, finite observation and its exact contract.

The receipt and contract share the polynomial, raw selection, policy, request and finite prefix length, retaining the
same prepared entry. -/
structure Observation (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection)
    (policy : Policy) (request : Request) (count : Nat) where
  /-- The original computed reduced-curve standard-period entry. -/ prepared : PreparedEntry polynomial selection
  /-- The actual finite observation receipt for the retained entry and policy. -/ recorded :
    Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program prepared.entry policy) request count
  /-- The numerical and ownership contract for this exact recorded receipt. -/ contract :
    Periods.PeriodObservation.Contract prepared.entry policy request count recorded

constructive_injectivity Observation

section
open Purelib.Riemann
open Purelib.Polynomial
/-- Record a finite observation using the supplied prepared standard-period entry.

The receipt is computed once and its contract is attached to that same entry, policy, request and prefix length. -/
def observePrepared {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    (prepared : PreparedEntry polynomial selection) (policy : Policy) (request : Request) (count : Nat) :
    Observation polynomial selection policy request count :=
  let recorded := record prepared.entry policy request count
  { prepared := prepared
    recorded := recorded
    contract := Periods.PeriodObservation.observation_contract prepared.entry policy request count recorded }

/-- Compute a certified finite standard-period observation directly from polynomial coefficients.

The finite input and raw-index checks run before the canonical entry is forced. Success retains the actual prepared
entry and receipt; failure retains the computed input or selection evidence. -/
def observe (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (selection :
  Selection)
    (policy : Policy) (request : Request) (count : Nat) :
    Except (Failure polynomial selection) (Observation polynomial selection policy request count) :=
  match Periods.PolynomialPeriodInput.prepare polynomial selection with
  | .error failure => .error failure
  | .ok prepared => .ok (observePrepared prepared policy request count)

end

namespace Observation

open Purelib.Integration

/-- Read the prepared numerical request from this observation's retained transcript.

The selected cache, model, sample, allowance and radius belong to the original
prepared period entry and policy. This operation performs no stage query. -/
def preparedRequest {polynomial : GaussianPolynomial} {selection : Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) :
    CertifiedProgram.Program.Prepared (program observed.prepared.entry policy) request :=
  observed.recorded.preparedRequest

open Purelib.Integration in
open Purelib.Polynomial in
/-- Replaying the retained query trace reconstructs the exact observed receipt. -/
theorem replay {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {selection :
  Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) :
    Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay
        (Purelib.CCL.Progressive.IntegrationReplay.control (program observed.prepared.entry policy))
        request count observed.recorded.trace = .ok observed.recorded.observation :=
  observed.contract.numerical.replay

section
open Purelib.Polynomial
/-- The retained selected enclosure has squared radius strictly below the requested target. -/
theorem accurate {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {selection
  : Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) :
    observed.recorded.observation.selected.ball.radiusSq < request.target :=
  observed.contract.numerical.accurate

/-- The retained observation word has exactly the requested finite length. -/
theorem length {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {selection :
  Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) :
    observed.recorded.observation.word.length = count := observed.contract.numerical.length

end

open Purelib.Riemann in
open Purelib.Polynomial in
/-- Continue the retained observation machine by the supplied number of entries.

The existing preparation, selected enclosure and policy are reused, and only the newly consumed query log is appended.
-/
def resume {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {selection :
  Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) (extra : Nat) :
    Observation polynomial selection policy request (count + extra) :=
  let recorded := (observed.recorded.resume extra).recorded
  { prepared := observed.prepared
    recorded := recorded
    contract := Periods.PeriodObservation.observation_contract
      observed.prepared.entry policy request (count + extra) recorded }

section
open Purelib.Polynomial
/-- Resuming preserves the exact selected enclosure. -/
theorem resume_selected {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) (extra : Nat) :
    (observed.resume extra).recorded.observation.selected = observed.recorded.observation.selected :=
  (observed.recorded.resume extra).selected_eq

/-- The original observation word is a prefix of the resumed word. -/
theorem resume_prefix {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count) (extra : Nat) :
    observed.recorded.observation.word.IsPrefix (observed.resume extra).recorded.observation.word := by
  rw [(observed.resume extra).recorded.eq_record]
  exact observed.contract.numerical.prefix_extends extra

end

open Purelib.Integration in
open Purelib.Polynomial in
/-- Arbitrary replies outside the consumed finite trace preserve the exact receipt and trace.

Overlaying the retained observations onto any payload-dependent source suffices to reproduce the recorded computation.
-/
theorem payload_erasure {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    {policy : Policy} {request : Request} {count : Nat}
    (observed : Observation polynomial selection policy request count)
    {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) :
    (Program.Gaussian.CCL.Replay.Observation.Basic.computation
        (Purelib.CCL.Progressive.IntegrationReplay.control (program observed.prepared.entry policy)) request count).run
      (Purelib.Computation.Query.Boundary.Trace.overlay observed.recorded.trace (outside payload)) =
        ⟨.ok observed.recorded.observation, observed.recorded.trace⟩ := by
  rw [observed.recorded.eq_record]
  exact Program.Gaussian.CCL.Replay.Observation.Noninterference.payload_erasure _ request count payload outside

end Observation

set_option genInjectivity false in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Polynomial in
/-- Retain two policy observations and their comparison on one prepared standard-period entry.

Both actual receipts have source-aware contracts, and the output names have an all-later-pairs operational equivalence.
-/
structure Comparison (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection)
    (left right : Policy) (request : Request) (count : Nat) where
  /-- The single prepared standard-period entry shared by both policies. -/ prepared : PreparedEntry polynomial
    selection
  /-- The actual finite receipt computed with the left policy. -/ leftRecorded :
    Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program prepared.entry left) request count
  /-- The actual finite receipt computed with the right policy. -/ rightRecorded :
    Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program prepared.entry right) request count
  /-- The operational equivalence of both policy output names on the shared entry. -/ outputs :
    Gaussian.Equivalence.NamedEquivalent
    (program prepared.entry left).output.name (program prepared.entry right).output.name
  /-- The exact observation contract for the left receipt. -/ left_observation : Periods.PeriodObservation.Contract
    prepared.entry left request count leftRecorded
  /-- The exact observation contract for the right receipt. -/ right_observation : Periods.PeriodObservation.Contract
    prepared.entry right request count rightRecorded

constructive_injectivity Comparison

namespace Comparison

variable {polynomial : GaussianPolynomial} {selection : Selection}
    {left right : Policy} {request : Request} {count : Nat}

/-- View the comparison's retained left receipt as an observation of the same prepared period entry.

The existing receipt and source contract are reused. Request projections and
resumption consume this view without running another observation. -/
def leftObservation (compared : Comparison polynomial selection left right request count) :
    Observation polynomial selection left request count :=
  { prepared := compared.prepared
    recorded := compared.leftRecorded
    contract := compared.left_observation }

/-- View the comparison's retained right receipt as an observation of the same prepared period entry.

The right policy, existing receipt and source contract remain attached to the
original shared entry; constructing the view performs no stage query. -/
def rightObservation (compared : Comparison polynomial selection left right request count) :
    Observation polynomial selection right request count :=
  { prepared := compared.prepared
    recorded := compared.rightRecorded
    contract := compared.right_observation }

end Comparison

open Purelib.Riemann
open Purelib.Polynomial
/-- Compute both policy receipts and their contracts from one retained prepared entry.

The output-name comparison uses the same entry as both actual observations, preserving their source ownership. -/
def comparePrepared {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {selection : Selection}
    (prepared : PreparedEntry polynomial selection)
    (left right : Policy) (request : Request) (count : Nat) :
    Comparison polynomial selection left right request count :=
  let leftRecorded := record prepared.entry left request count
  let rightRecorded := record prepared.entry right request count
  { prepared := prepared
    leftRecorded := leftRecorded
    rightRecorded := rightRecorded
    outputs := Periods.PeriodPolicies.outputs_equivalent prepared.entry left right
    left_observation :=
      Periods.PeriodObservation.observation_contract prepared.entry left request count leftRecorded
    right_observation :=
      Periods.PeriodObservation.observation_contract prepared.entry right request count rightRecorded }

/-- Compute two certified policy observations and their comparison from raw polynomial input.

Curve reduction and selection checks produce the retained entry internally; each failure retains the corresponding
finite input or index evidence. -/
def canonical_period_contract (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (selection :
  Selection)
    (left right : Policy) (request : Request) (count : Nat) :
    Except (Failure polynomial selection) (Comparison polynomial selection left right request count) :=
  match Periods.PolynomialPeriodInput.prepare polynomial selection with
  | .error failure => .error failure
  | .ok prepared => .ok (comparePrepared prepared left right request count)

/-- A finite observation succeeds exactly when the raw polynomial and selection are admissible.

Every admissible input produces its receipt for the supplied policy, positive-target request and finite prefix length.
-/
theorem observe_success_iff (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection :
  Selection)
    (policy : Policy) (request : Request) (count : Nat) :
    (∃ observed, observe polynomial selection policy request count = .ok observed) ↔
      Periods.PolynomialPeriodInput.Admissible polynomial selection := by
  constructor
  · rintro ⟨observed, success⟩
    apply (Periods.PolynomialPeriodInput.prepare_success_iff polynomial selection).mp
    cases input : Periods.PolynomialPeriodInput.prepare polynomial selection with
    | error failure =>
        rw [observe, input] at success
        nomatch success
    | ok entry => exact ⟨entry, rfl⟩
  · intro admissible
    rcases (Periods.PolynomialPeriodInput.prepare_success_iff polynomial selection).mpr admissible with
      ⟨entry, success⟩
    exact ⟨observePrepared entry policy request count, by rw [observe, success]⟩

/-- The two-policy contract succeeds exactly on the same admissible raw inputs.

The success boundary is independent of the chosen policies, positive-target request and finite prefix length. -/
theorem canonical_period_contract_success_iff (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection)
    (left right : Policy) (request : Request) (count : Nat) :
    (∃ comparison, canonical_period_contract polynomial selection left right request count = .ok comparison) ↔
      Periods.PolynomialPeriodInput.Admissible polynomial selection := by
  constructor
  · rintro ⟨compared, success⟩
    apply (Periods.PolynomialPeriodInput.prepare_success_iff polynomial selection).mp
    cases input : Periods.PolynomialPeriodInput.prepare polynomial selection with
    | error failure =>
        rw [canonical_period_contract, input] at success
        nomatch success
    | ok entry => exact ⟨entry, rfl⟩
  · intro admissible
    rcases (Periods.PolynomialPeriodInput.prepare_success_iff polynomial selection).mpr admissible with
      ⟨entry, success⟩
    exact ⟨comparePrepared entry left right request count, by rw [canonical_period_contract, success]⟩

end Purelib.Riemann.Periods.PolynomialPeriodObservation
