module
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Examples.Curves.Legendre.Prepared.LoopBase
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.PeriodReplay
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Examples.Curves.Legendre.LoopBaseBranches
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Riemann.Integration.PreparedRefinementProgramCore

public section

/-!
# Cached Legendre instantiations of complete observation replay

The retained context owns the measured geometry and coefficient banks.  The
A entry uses its generated direct-state cache; the B preparation remains
independently delayed in the same context.  Both entries replay arbitrary
finite prefixes of the cached numerical fixture. The connector-only B data
is not identified with the standard B tour.

This does not identify the fixture with independently isolated branch tracks
or claim a timing bound for a concrete request.
-/

namespace Purelib.Examples.Curves.Legendre.Replay

open Purelib.CCL
open Purelib
open Purelib.Examples
open Purelib.Integration
open Purelib.Riemann

open Purelib.Examples.Curves.Legendre.Prepared

open Purelib.Examples.Curves.Legendre.LoopBaseBranches (baseCurve)

open Purelib.Examples.Curves.Legendre.Prepared.LoopBase

/-- A certified integration request used for the retained Legendre replay entries. -/
abbrev Request := CertifiedProgram.Request

/-- The period data retaining a shared Legendre context and the chosen finite A-entry cache. -/
@[expose] def periodData (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat) :
    Periods.PeriodMatrix.PeriodData baseCurve :=
  LoopBase.fixturePeriodDataOfContextWithACache context
    (LoopBase.aPeriodCacheOfContext context cacheCount)

/-- The A-period replay entry with its exact standard differential, retained cycle and finite cached program. -/
@[expose] def aEntry (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat) :
    Periods.PeriodReplay.Entry baseCurve :=
  ⟨Periods.PeriodMatrix.standardDifferential 0,
    ⟨fun _ => (LoopBase.aPeriodScheduleOfContext context).cycle⟩,
    LoopBase.aPeriodProgramOfCache context
      (LoopBase.aPeriodCacheOfContext context cacheCount)⟩

/-- The B-period replay entry whose construction leaves the A-entry cache unforced. -/
@[expose] def bEntry (context : LoopBase.PreparedLegendreContext) :
    Periods.PeriodReplay.Entry baseCurve :=
  ⟨Periods.PeriodMatrix.standardDifferential 0,
    ⟨fun _ => (LoopBase.bPeriodScheduleOfContext context).cycle⟩,
      LoopBase.bPeriodProgramOfContext context⟩

/-- The A replay entry retains the A cycle of the original period data. -/
theorem a_entry_cycle (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat) :
    (aEntry context cacheCount).cycle = (periodData context
      cacheCount).cycles.aCycle 0 := rfl

/-- The B replay entry retains the B cycle of the original period data, independently of the A cache size. -/
theorem b_entry_cycle (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat) :
    (bEntry context).cycle = (periodData context cacheCount).cycles.bCycle
      0 := rfl

/-- Replaying a recorded finite A-entry trace succeeds with its original observation. -/
theorem a_observation_replay (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat)
  (request : Request) (count : Nat) :
    Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay
        (Progressive.IntegrationReplay.control (aEntry context cacheCount).cached) request count
        ((aEntry context cacheCount).record request count).trace =
      .ok ((aEntry context cacheCount).record request count).observation :=
  (aEntry context cacheCount).replay request count

/-- Replaying a recorded finite B-entry trace succeeds with its original observation. -/
theorem b_observation_replay (context : LoopBase.PreparedLegendreContext) (request :
  Request) (count : Nat) :
    Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay
        (Progressive.IntegrationReplay.control (bEntry context).cached) request count
        ((bEntry context).record request count).trace =
      .ok ((bEntry context).record request count).observation :=
  (bEntry context).replay request count

/-- The recorded A-entry word is the prefix actually emitted by the retained refined machine. -/
theorem a_actual_word (context : LoopBase.PreparedLegendreContext) (cacheCount : Nat) (request
  : Request) (count : Nat) :
    ((aEntry context cacheCount).record request count).observation.word =
      (Data.CCL.Transducer.Machine.Advance.advance
        ((aEntry context cacheCount).refinedName request).machine count).emitted :=
  (aEntry context cacheCount).recorded_prefix request count

/-- The recorded B-entry word is the prefix actually emitted by the retained refined machine. -/
theorem b_actual_word (context : LoopBase.PreparedLegendreContext) (request :
  Request) (count : Nat) :
    ((bEntry context).record request count).observation.word =
      (Data.CCL.Transducer.Machine.Advance.advance
        ((bEntry context).refinedName request).machine count).emitted :=
  (bEntry context).recorded_prefix request count

end Purelib.Examples.Curves.Legendre.Replay
