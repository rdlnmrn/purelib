module
import Purelib.Integration.CertifiedProgram

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Boundary
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.PathObservation
public import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram

public section

/-!
# Certified finite observations from a polynomial and an oriented segment

The executable constructors return the actual observation receipts, their
source-linked replay/accuracy contracts and (for two policies) the generated
all-later output comparison.  The input checker creates the required path
evidence.  No caller genus, squarefreeness, numerical coherence, successful
run or sufficient fuel is required.  Original-coordinate and cancelled
extension requests remain different types throughout resume and comparison.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation

universe u

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
set_option genInjectivity false in
/-- The exact prepared polynomial-path entry with a retained policy observation and its source contract.

The indices preserve the original polynomial, differential, segment, sheet, domain, numerical request and bit count. -/
structure Observation (polynomial : SquareFactor.GaussianPolynomial) (differential : SquareFactor.Request)
    (segment : PathInput.Segment) (sheet : Fin 2) (domain : ObservationInput.Domain)
    (policy : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) where
  /-- The exact retained prepared entry for the original polynomial-path request and domain. -/ entry :
    ObservationInput.PreparedEntry polynomial differential segment sheet domain
  /-- The exact retained policy-controlled source observation record. -/ recorded : Observation.Record.Recorded
    (PathObservation.program entry.source policy) query count
  /-- The original source and numerical contract for the exact retained record. -/ contract : PathObservation.Contract
    entry.source policy query count recorded

constructive_injectivity Observation

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Integration.Algebraic.SquareFactor
/-- Observe the exact retained prepared entry once and retain its original record and source contract. -/
@[expose] def observePrepared {polynomial : SquareFactor.GaussianPolynomial} {differential : SquareFactor.Request}
    {segment : PathInput.Segment} {sheet : Fin 2} {domain : ObservationInput.Domain}
    (entry : ObservationInput.PreparedEntry polynomial differential segment sheet domain)
    (policy : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) :
    PolynomialObservation.Observation polynomial differential segment sheet domain policy query count :=
  let recorded := PathObservation.record entry.source policy query count
  ⟨entry, recorded, PathObservation.observation_contract entry.source policy query count recorded⟩

/-- Prepare the original polynomial-path request and return either its retained typed failure or certified observation.
-/
@[expose] def observe (polynomial : SquareFactor.GaussianPolynomial) (differential : SquareFactor.Request)
    (segment : PathInput.Segment) (sheet : Fin 2) (domain : ObservationInput.Domain)
    (policy : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) :
    Except (ObservationInput.Failure polynomial differential segment)
      (PolynomialObservation.Observation polynomial differential segment sheet domain policy query count) :=
  match ObservationInput.prepare polynomial differential segment sheet domain with
  | .error failure => .error failure
  | .ok entry => .ok (PolynomialObservation.observePrepared entry policy query count)

end

namespace Observation

open Purelib.Integration
open Purelib.Integration.Algebraic.SquareFactor

/-- Read the prepared numerical request from the retained square-factor observation.

The original entry, sheet, domain and policy remain attached to the exact
recorded cache and its accuracy certificates. This operation makes no query. -/
@[expose] def preparedRequest {polynomial : GaussianPolynomial} {differential : Request}
    {segment : PathInput.Segment} {sheet : Fin 2} {domain : ObservationInput.Domain}
    {policy : PathObservation.Policy} {query : PathObservation.ObservationRequest} {count : Nat}
    (observed : Observation polynomial differential segment sheet domain policy query count) :
    CertifiedProgram.Program.Prepared (PathObservation.program observed.entry.source policy) query :=
  observed.recorded.preparedRequest

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request} {segment :
  Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {sheet : Fin 2} {domain : Purelib.Integration.Algebraic.SquareFactor.ObservationInput.Domain} {policy :
    Purelib.Integration.Algebraic.SquareFactor.PathObservation.Policy} {query :
    Purelib.Integration.Algebraic.SquareFactor.PathObservation.ObservationRequest} {count : Nat}

open Purelib.CCL.Progressive in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The retained polynomial observation's transcript replays to its exact recorded observation. -/
theorem replay (observed : PolynomialObservation.Observation polynomial differential segment sheet domain policy query
  count) :
    Program.Gaussian.CCL.Replay.Observation.Transcript.replay (IntegrationReplay.control (PathObservation.program
      observed.entry.source policy))
      query count observed.recorded.trace = .ok observed.recorded.observation :=
  observed.contract.numerical.replay

section
open Purelib.Integration.Algebraic.SquareFactor
/-- The retained polynomial observation's selected ball radius is below the original request target. -/
theorem accurate (observed : PolynomialObservation.Observation polynomial differential segment sheet domain policy query
  count) :
    observed.recorded.observation.selected.ball.radiusSq < query.target :=
  observed.contract.numerical.accurate

/-- The retained polynomial observation emits exactly the originally requested bit count. -/
theorem length (observed : PolynomialObservation.Observation polynomial differential segment sheet domain policy query
  count) :
    observed.recorded.observation.word.length = count := observed.contract.numerical.length

/-- Resume the exact saved record while retaining the original prepared entry and extending its certified count. -/
@[expose] def resume (observed : PolynomialObservation.Observation polynomial differential segment sheet domain policy
  query count) (extra : Nat) :
    PolynomialObservation.Observation polynomial differential segment sheet domain policy query (count + extra) :=
  let resumed := observed.recorded.resume extra
  ⟨observed.entry, resumed.recorded,
    PathObservation.resumed_contract observed.entry.source policy query count extra resumed⟩

/-- Resuming the polynomial observation preserves its exact original selected reading. -/
theorem resume_selected (observed : PolynomialObservation.Observation polynomial differential segment sheet domain
  policy query count)
    (extra : Nat) : (observed.resume extra).recorded.observation.selected = observed.recorded.observation.selected :=
  (observed.recorded.resume extra).selected_eq

/-- The original emitted word is a prefix of the exact resumed observation's word. -/
theorem resume_prefix (observed : PolynomialObservation.Observation polynomial differential segment sheet domain policy
  query count)
    (extra : Nat) : observed.recorded.observation.word.IsPrefix (observed.resume extra).recorded.observation.word := by
  rw [(observed.resume extra).recorded.eq_record]
  exact observed.contract.numerical.prefix_extends extra

end

open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Changing arbitrary outside-trace oracle payload preserves the exact retained polynomial observation execution. -/
theorem payload_erasure (observed : PolynomialObservation.Observation polynomial differential segment sheet domain
  policy query count)
    {Payload : Type u} (payload : Payload) (outside : Payload → Nat → Basic.CachedModel) :
    (Observation.Basic.computation
      (IntegrationReplay.control (PathObservation.program observed.entry.source policy)) query count).run
        (Boundary.Trace.overlay observed.recorded.trace (outside payload)) =
          ⟨.ok observed.recorded.observation, observed.recorded.trace⟩ := by
  rw [observed.recorded.eq_record]
  exact Observation.Noninterference.payload_erasure _ query count payload outside

end Observation

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- One retained prepared polynomial-path entry with separate policy records and their exact source comparison. -/
structure Comparison (polynomial : SquareFactor.GaussianPolynomial) (differential : SquareFactor.Request)
    (segment : PathInput.Segment) (sheet : Fin 2) (domain : ObservationInput.Domain)
    (left right : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) where
  /-- The exact retained prepared entry for the original polynomial-path request and domain. -/ entry :
    ObservationInput.PreparedEntry polynomial differential segment sheet domain
  /-- The separate retained policy observations and output equivalence for this exact prepared source. -/ comparison :
    PathObservation.Comparison entry.source left right query count

constructive_injectivity Comparison

namespace Comparison

open Purelib.Integration.Algebraic.SquareFactor

variable {polynomial : GaussianPolynomial} {differential : Request}
    {segment : PathInput.Segment} {sheet : Fin 2} {domain : ObservationInput.Domain}
    {left right : PathObservation.Policy} {query : PathObservation.ObservationRequest} {count : Nat}

/-- View the actual left comparison receipt as an observation of the original polynomial-path entry.

The sheet, domain, retained source and left policy contract are preserved.
The view makes the request and resume operations available without a new run. -/
@[expose] def leftObservation
    (compared : Comparison polynomial differential segment sheet domain left right query count) :
    Observation polynomial differential segment sheet domain left query count :=
  { entry := compared.entry
    recorded := compared.comparison.leftRecorded
    contract := compared.comparison.left_contract }

/-- View the actual right comparison receipt as an observation of the same original polynomial-path entry.

The right policy's existing receipt and source contract are reused, retaining
the original differential, segment, sheet and coordinate-domain evidence. -/
@[expose] def rightObservation
    (compared : Comparison polynomial differential segment sheet domain left right query count) :
    Observation polynomial differential segment sheet domain right query count :=
  { entry := compared.entry
    recorded := compared.comparison.rightRecorded
    contract := compared.comparison.right_contract }

end Comparison

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Integration.Algebraic.SquareFactor
/-- Compare both original policies on the same retained prepared entry and exact observation request. -/
@[expose] def comparePrepared {polynomial : SquareFactor.GaussianPolynomial} {differential : SquareFactor.Request}
    {segment : PathInput.Segment} {sheet : Fin 2} {domain : ObservationInput.Domain}
    (entry : ObservationInput.PreparedEntry polynomial differential segment sheet domain)
    (left right : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) :
    PolynomialObservation.Comparison polynomial differential segment sheet domain left right query count :=
  ⟨entry, PathObservation.compare entry.source left right query count⟩

/-- Prepare the original polynomial-path domain and return its typed failure or retained two-policy comparison. -/
@[expose] def polynomial_path_contract (polynomial : SquareFactor.GaussianPolynomial) (differential :
  SquareFactor.Request)
    (segment : PathInput.Segment) (sheet : Fin 2) (domain : ObservationInput.Domain)
    (left right : PathObservation.Policy) (query : PathObservation.ObservationRequest) (count : Nat) :
    Except (ObservationInput.Failure polynomial differential segment)
      (PolynomialObservation.Comparison polynomial differential segment sheet domain left right query count) :=
  match ObservationInput.prepare polynomial differential segment sheet domain with
  | .error failure => .error failure
  | .ok entry => .ok (PolynomialObservation.comparePrepared entry left right query count)

end Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
