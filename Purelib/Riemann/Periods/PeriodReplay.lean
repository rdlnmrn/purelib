module
public import Purelib.Data.List.GetD
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Computation.Query.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

public section

/-!
# Complete finite period-observation replay

A period entry retains its algebraic differential, lifted cycle and uniform
local certificates.  Replay now covers every requested finite prefix and its
enclosure, with no additional success or simulation premise.  Every logged
model remains tied to the original differential and sheet data.

Canonical entries derive preparation from finite curve validity.  Explicit
prepared entries retain their own realization; they are not identified with
an independently isolated cycle.  Cache/schedule comparisons are a separate
layer over the fixed prepared source.
-/

namespace Purelib.Riemann.Periods.PeriodReplay

open Purelib.Riemann.Curves.AlgebraicDifferentials

open Purelib.Integration in
/-- The certified integration request retaining its current state, target and positivity. -/
abbrev Request := CertifiedProgram.Request

open Purelib.Curves in
open Purelib.Geometry in
set_option genInjectivity false in
/-- A period observation retaining its differential, shared cycle thunk and certified program.

The program is indexed by that exact cached lifted cycle and differential, so every requested model remains tied to the
original geometric data. -/
structure Entry {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The retained algebraic differential integrated by this period entry. -/ differential :
    Hyperelliptic.Differentials.Basic.Differential genus
  /-- The shared thunk retaining the exact lifted cycle refinement. -/ cycleCache : Thunk
    (Path.Gaussian.Lifted.Refinement.LiftedCycleRefinement 2)
  /-- The certified period program indexed by the retained differential and cached cycle. -/ program :
    Hyperelliptic.Integration.Algebraic.Period.Basis.CertifiedPeriodProgram curve differential cycleCache.get

constructive_injectivity Entry

namespace Entry

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Geometry in
/-- Read the retained lifted cycle from its shared thunk. -/
@[expose] def cycle (entry : Entry curve) : Path.Gaussian.Lifted.Refinement.LiftedCycleRefinement 2 :=
  entry.cycleCache.get

section
open Purelib.Integration
/-- Read the numerical cached program from the retained certified integral view. -/
@[expose] def cached (entry : Entry curve) : Program.Gaussian.Cached.Basic.CachedProgram :=
  entry.program.integral.certifiedView.program

/-- Record the requested finite observation prefix and its consumed model trace. -/
@[expose] def record (entry : Entry curve) (request : Request) (count : Nat) :
    Program.Gaussian.CCL.Replay.Observation.Record.Recorded entry.cached request count :=
  Program.Gaussian.CCL.Replay.Observation.Record.record entry.cached request count

end

/-- Compute the requested observation's selected refinement index. -/
@[expose] def selectedIndex (entry : Entry curve) (request : Request) : Nat :=
  Purelib.CCL.Progressive.IntegrationReplay.selectedIndex (Purelib.CCL.Progressive.IntegrationReplay.control
    entry.cached) request

open Purelib.Curves in
/-- Read the exact local certificates of the selected retained cycle model. -/
@[expose] def selectedCertificates (entry : Entry curve) (request : Request) :
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      (entry.program.integral.model (entry.selectedIndex request)).cells
      (entry.cycle.liftedPath (entry.selectedIndex request)).path :=
  entry.program.certificates (entry.selectedIndex request)

open Purelib.Curves in
open Purelib.Integration in
/-- Recover local certificates for every actual model exchange in the recorded trace.

Trace membership identifies the retained reply with the original program model at the same queried cycle stage,
including adaptive later requests. -/
@[expose] def traceCertificates (entry : Entry curve) (request : Request) (count : Nat)
    (exchange : Purelib.Computation.Query.Basic.Exchange Nat Program.Gaussian.Cached.Basic.CachedModel)
    (member : exchange ∈ (entry.record request count).trace) :
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      exchange.reply.model.cells
      (entry.cycle.liftedPath exchange.query).path := by
  rw [Program.Gaussian.CCL.Replay.Observation.Record.recorded_reply entry.cached request count exchange member]
  exact entry.program.certificates exchange.query

open Purelib.Integration in
open Purelib.CCL.Progressive in
/-- The recorded observation sample equals the integral sample of the selected retained model. -/
theorem recorded_sample (entry : Entry curve) (request : Request) (count : Nat) :
    (entry.record request count).observation.selected.sample =
      (entry.program.integral.model (entry.selectedIndex request)).integralSample := by
  rw [record, Program.Gaussian.CCL.Replay.Observation.Record.recorded_selected]
  exact IntegrationReplay.requestedReading_sample_model entry.cached request

open Purelib.Integration in
/-- The first recorded model is the retained model at the selected request index. -/
theorem recorded_model (entry : Entry curve) (request : Request) (count : Nat) :
    (Purelib.Data.List.getElem? (entry.record request count).trace 0).map (fun exchange => exchange.reply.model) =
      some (entry.program.integral.model (entry.selectedIndex request)) :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_model entry.cached request count

open Purelib.Approximation in
/-- Refine the retained integral name from the request's current state to its positive target. -/
@[expose] def refinedName (entry : Entry curve) (request : Request) : Gaussian.Name.Basic.Named :=
  Gaussian.Name.Refinement.refined
    { process := entry.program.output.name.process, state := request.current }
    request.target request.positive

open Purelib.Integration in
open Purelib.Data in
/-- The recorded word is exactly the requested machine prefix of the refined integral name. -/
theorem recorded_prefix (entry : Entry curve) (request : Request) (count : Nat) :
    (entry.record request count).observation.word =
      (CCL.Transducer.Machine.Advance.advance (entry.refinedName request).machine count).emitted :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_prefix entry.cached request count

section
open Purelib.Integration
/-- The recorded selected enclosure has squared radius strictly below the requested target. -/
theorem recorded_accurate (entry : Entry curve) (request : Request) (count : Nat) :
    (entry.record request count).observation.selected.ball.radiusSq < request.target :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_accurate entry.cached request count

/-- The recorded output word has exactly the requested finite length. -/
theorem recorded_length (entry : Entry curve) (request : Request) (count : Nat) :
    (entry.record request count).observation.word.length = count :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_length entry.cached request count

/-- A longer record extends the earlier output word as a prefix. -/
theorem recorded_extends (entry : Entry curve) (request : Request) (count extra : Nat) :
    (entry.record request count).observation.word.IsPrefix
      (entry.record request (count + extra)).observation.word :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_extends entry.cached request count extra

end

open Purelib.Integration in
open Purelib.Data in
/-- The recorded word belongs to an actual exact cursor of the refined integral process. -/
theorem recorded_exactCursor (entry : Entry curve) (request : Request) (count : Nat) :
    ∃ actual : Data.CCL.Transducer.Machine,
      actual.emitted = (entry.record request count).observation.word ∧
      CCL.Transducer.Machine.Semantics.Basic.ExactCursor
        (entry.refinedName request).process (entry.refinedName request).state actual :=
  Program.Gaussian.CCL.Replay.Observation.Record.recorded_exactCursor entry.cached request count

open Purelib.Integration in
/-- Replaying the retained observation trace returns the exact recorded finite observation. -/
theorem replay (entry : Entry curve) (request : Request) (count : Nat) :
    Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay
      (Purelib.CCL.Progressive.IntegrationReplay.control
      entry.cached) request count
        (entry.record request count).trace = .ok (entry.record request count).observation :=
  Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.observation_replay entry.cached request count

end Entry

set_option genInjectivity false in
/-- An A- or B-period entry indexed by differential and cycle in the finite genus. -/
inductive StandardEntry (genus : Nat) where
  /-- Select an A-cycle period for the supplied differential and cycle indices. -/ | a (differential cycle : Fin genus)
  /-- Select a B-cycle period for the supplied differential and cycle indices. -/ | b (differential cycle : Fin genus)

constructive_injectivity StandardEntry

open Purelib.Riemann in
open Purelib.Curves in
/-- Select a replay entry from retained period data while sharing its exact cycle through a thunk. -/
@[expose] def ofPeriodData {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Periods.PeriodMatrix.PeriodData curve) : StandardEntry genus → Entry curve
  | .a differential cycle =>
      ⟨Periods.PeriodMatrix.standardDifferential differential,
        ⟨fun _ => data.cycles.aCycle cycle⟩, data.aProgram differential cycle⟩
  | .b differential cycle =>
      ⟨Periods.PeriodMatrix.standardDifferential differential,
        ⟨fun _ => data.cycles.bCycle cycle⟩, data.bProgram differential cycle⟩

open Purelib.Curves in
/-- Build the replay entry for the geometrically ordered corrected A/B cycle bank.

The certified curve determines the paired period bank; the selected differential and cycle retain that bank's exact
realization. -/
@[expose] def canonical {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (entry : StandardEntry
  genus) : Entry curve :=
  ofPeriodData (Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve).periodData entry

end Purelib.Riemann.Periods.PeriodReplay

end
