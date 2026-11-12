module
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# Trace-reading handoffs for actual prepared continuation

Turn the existing operational source-preparation and endpoint-retention
equivalences into synchronized finite root readings.  Source construction
consumes the retained prepared-owner cache.  The joins include no root
agreement assumption beyond the guarantees of the actual preparation code.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace

open Purelib.Riemann.Branches.PreparedSheetContinuation

/-- Finite trace handoff from the inherited owner to the exact prepared owner
already cached on an accepted edge. -/
def CachedSource.traceJoin {polynomial : GaussianPolynomial} {ambient :
  Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment
      polynomial ambient start finish}
    {current : Endpoint} {owner :
      Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} (cached :
      CachedSource segment current owner request) :
    Riemann.Paths.OwnerTraceReadings.OwnerJoin owner cached.preparedOwner := by
  by_cases ready : AlreadyPrepared segment current owner request ∧
      Riemann.Branches.ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter < owner.track.initial.clearance.bound
  · rw [cached.preparedOwner_eq, prepared_eq_self_of_ready segment current
      owner request ready.1 ready.2]
    exact OwnerJoin.reflexive owner
  · exact OwnerJoin.acquire owner cached.preparedOwner (by
      rw [cached.preparedOwner_eq]
      exact sourceRootEquivalent segment current owner request)

/-- The reserve-triggered endpoint reset supplies its own same-root trace
handoff.  Its two supplied owners are precisely the transported and retained
presentations used by `advance`. -/
def retainedTraceJoin {parameter : Gaussian} (owner :
  Riemann.Branches.PreparedSheetContinuation.Owner parameter) (reserve :
  Coordinate) :
    Riemann.Paths.OwnerTraceReadings.OwnerJoin owner (retainedAtReserve owner
      reserve) := by
  by_cases enough : reserve ≤ owner.track.initial.clearance.bound
  · rw [retainedAtReserve_eq_self owner reserve enough]
    exact OwnerJoin.reflexive owner
  · exact OwnerJoin.acquire owner
      (retainedAtReserve owner reserve)
      (retainedAtReserveRootEquivalent owner reserve)

open Purelib.RootIsolation in
/-- Handoff at the end of an actual accepted prepared step, before starting
the following step's source preparation. -/
def advanceTraceJoin {polynomial : GaussianPolynomial} {ambient :
  Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment
      polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt current.parameter)))
      (request : StepRequest)
    (small : Riemann.Branches.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        (prepared segment current owner
          request).track.initial.clearance.bound) :
    Riemann.Paths.OwnerTraceReadings.OwnerJoin (transported segment within
      current owner request small)
      (advance segment within current owner request small) :=
  retainedTraceJoin (transported segment
    within current owner request small)
    (preparedClearanceLower segment current request)

end Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace
