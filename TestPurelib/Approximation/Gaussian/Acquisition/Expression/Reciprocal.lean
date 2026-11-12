module

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
import Purelib.Approximation.Gaussian.Division.Acquisition.State
import Purelib.Approximation.Gaussian.Division.Acquisition.Report
import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.System.IO

/-! # Original-channel one-plus-root reciprocal acquisition and cached retry -/

namespace TestPurelib.Approximation.Gaussian.Acquisition.Expression.Reciprocal

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division.Acquisition.State (Route)
open Purelib.Approximation.Gaussian.Division.Acquisition.Report (Status)
open Purelib.Approximation.Gaussian.Division.Acquisition
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Emit one production stage before any further denominator work is forced. -/
private def progress (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Acquire one over the original one-plus-input expression and reuse its computed exact decision.

The supplied sidecar is the original annotation's actual algebraic evidence.
Both requests consume one retained finish decision and original refinement
state. The checked inverse computes its own exclusion floor; the caller
supplies no denominator gap, successful attempt or localization budget.
-/
public def check (annotation : Annotated)
    (sidecar : Algebraic.Sidecar annotation.channel) : IO Unit := do
  progress "production-reciprocal-start expression=1/(1+alpha)"
  let environment : Fin 1 → Annotated := fun _ => annotation
  let atom := Admitted.atom environment ⟨0, by decide⟩ sidecar
  let one := Admitted.rational environment 1
  match (one.add atom).run with
  | .completed denominator =>
      let finished := denominator.finish
      let state := Name.Coherent.Refinement.State.initial denominator.channel
      let first := finished.acquire state (CoherentNamed.Coherence.exact 1) (1 / 10) (by decide)
      let retry := Dispatch.Report.resume first (CoherentNamed.Coherence.exact 2) (1 / 20) (by decide)
      unless first.1.route = Route.cached ∧ first.2.status = Status.ready ∧
          retry.1.route = Route.cached ∧ retry.2.status = Status.ready ∧
          retry.1.next.state.nextIndex = first.1.next.state.nextIndex do
        throw (IO.userError
          "one-plus-input acquisition did not retain its cached ready decision and retry")
      progress "production-reciprocal-acquisition first=cached-ready retry=cached-ready"
      let materialized := finished.materialize
      match materialized.sidecar.inverse with
      | .obstructed _ => throw (IO.userError
          "the actual one-plus-input decision returned a typed zero obstruction")
      | .ready prepared cache result same =>
          let inverse := materialized.inverse prepared cache result same
          progress ("production-reciprocal-floor " ++ toString cache.comparison.leftIndex)
          let sample := inverse.sidecar.residual.source.sample 0
          unless 0 < normSq sample do
            throw (IO.userError "the actual checked reciprocal sample was zero")
          let repeated := inverse.sidecar.residual.source.sample 0
          unless repeated = sample do
            throw (IO.userError "the identical repeated reciprocal request changed its observation")
          progress "production-reciprocal-complete nonzero=true repeated=true"
  | .invalid _ => throw (IO.userError
      "the original one-plus-input expression returned a typed invalidity")
  | .pending _ => throw (IO.userError
      "the original one-plus-input expression retained a pending admission")

end TestPurelib.Approximation.Gaussian.Acquisition.Expression.Reciprocal
