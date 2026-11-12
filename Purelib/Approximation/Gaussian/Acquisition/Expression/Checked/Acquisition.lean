module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Admission
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
public import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked-expression completion in production denominator acquisition

Successful finite evaluation computes and stores one original-channel exact
decision. The existing acquisition dispatcher consumes that same stored
decision and the caller's actual retained refinement state on every retry.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Data.Rat.Fraction (Rational)

variable {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}

set_option genInjectivity false in
/-- One completed original checked expression and its same stored finite exact denominator decision. -/
structure Finished (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The actual original exact completion before its finite decision request. -/
  source : Construction.Result environment expression
  /-- The original exact completion retaining every cache paid by that actual decision route. -/
  completed : Construction.Result environment expression
  /-- The exact finite zero-or-preparation decision on this original output. -/
  decision : Prepared.Decision completed.channel
  /-- The complete retained completion/decision pair is the actual original exact decision procedure. -/
  decision_eq : (⟨completed, decision⟩ :
    (retained : Construction.Result environment expression) × Prepared.Decision retained.channel) = source.decide

  /-- The actual complete classification exists only when this same decision branch materialized its sidecar. -/
  resolved : Option (Construction.Result.Resolution completed decision)
  /-- The entire optional classification/result/decision bundle comes from the same single original branch. -/
  resolution_eq : (⟨⟨completed, decision⟩, resolved⟩ :
    Σ result : (retained : Construction.Result environment expression) × Prepared.Decision retained.channel,
      Option (Construction.Result.Resolution result.1 result.2)) = source.resolve

constructive_injectivity Finished

namespace Construction.Result

/-- Compute and store one exact original-channel decision and every cache paid by its actual route. -/
@[expose] def finish (completed : Construction.Result environment expression) :
    Finished environment expression :=
  let resolved := completed.resolve
  let result := resolved.1
  ⟨completed, result.1, result.2, rfl, resolved.2, rfl⟩

end Construction.Result

namespace Completed

/-- Finish a retained full materialization through the same original exact decision procedure. -/
@[expose] def finish (completed : Completed environment expression) : Finished environment expression :=
  completed.toResult.finish

end Completed

namespace Finished

/-- The exact decision route retains the original source channel, rather than replacing the numerical owner. -/
theorem source_channel (finished : Finished environment expression) :
    finished.completed.channel = finished.source.channel :=
  (congrArg (fun result :
      (retained : Construction.Result environment expression) × Prepared.Decision retained.channel =>
    result.1.channel) finished.decision_eq).trans finished.source.decide_channel

/-- Retain the caller's actual original refinement state and this same already computed exact decision. -/
@[expose] def input (finished : Finished environment expression) (state : State finished.source.channel) :
    Acquisition.State.Input finished.source.channel :=
  { state := state
    provenance := match finished.completed.cached with
      | some sidecar => some (.algebraic (finished.source_channel ▸ sidecar))
      | none => none
    cached := some (finished.source_channel ▸ finished.decision) }

/-- Acquire a quotient using the existing production dispatcher and this same cached original-channel decision. -/
@[expose] def acquire (finished : Finished environment expression) (state : State finished.source.channel)
    (numerator : CoherentNamed) (threshold : Rational) (positive : 0 < threshold) :
    Acquisition.Report numerator (finished.input state) threshold :=
  Acquisition.Dispatch.acquire numerator (finished.input state) threshold positive

/-- Production acquisition reuses the stored checked-expression decision and preserves the actual supplied state. -/
theorem acquire_cached (finished : Finished environment expression) (state : State finished.source.channel)
    (numerator : CoherentNamed) (threshold : Rational) (positive : 0 < threshold) :
    (finished.acquire state numerator threshold positive).1.route = .cached ∧
      (finished.acquire state numerator threshold positive).1.next.state = state :=
  Acquisition.Dispatch.acquire_cached numerator (finished.input state) threshold positive
    (finished.source_channel ▸ finished.decision) rfl

/-- Materialize and retain the actual full original output only at an explicit Sidecar boundary. -/
@[expose] def materialize (finished : Finished environment expression) : Completed environment expression :=
  finished.completed.materialize

/-- Compare independent original outputs after retaining both actual full materializations.

The returned original Completed inputs store their actual Sidecars and
construction equalities. The comparison consumes those same stored fields
and retains its requested original-root stage floors. Its separate difference
is materialized explicitly; exact completions expose no recomputing Sidecar
projection.
-/
@[expose] def compare {otherArity : Nat} {otherEnvironment : Fin otherArity → Annotated}
    {otherExpression : Expr otherArity}
    (first : Finished environment expression) (second : Finished otherEnvironment otherExpression)
    (firstStart secondStart : Nat := 0) :
    (left : Completed environment expression) × (right : Completed otherEnvironment otherExpression) ×
      Algebraic.Sidecar.Compared left.sidecar right.sidecar firstStart secondStart :=
  let left := first.materialize
  let right := second.materialize
  ⟨left, right, left.sidecar.compare right.sidecar firstStart secondStart⟩

end Finished

set_option genInjectivity false in
/-- A checked production frontend result preserving success, the first exact invalid reciprocal or all pending work. -/
inductive CheckedResult (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The original output decision and numerical caches are ready for production acquisition. -/
  | finished (result : Finished environment expression)
  /-- The original first invalid reciprocal has an exact typed zero obstruction. -/
  | invalid (first : Invalid environment expression)
  /-- The original cached finite work is retained with an exact typed admission request. -/
  | pending (request : Pending environment expression)

constructive_injectivity CheckedResult

/-- Finish an actual finite evaluation outcome while preserving its exact original failure and suspension data. -/
@[expose] def Outcome.finish : Outcome environment expression → CheckedResult environment expression
  | .completed value => .finished value.finish
  | .invalid first => .invalid first
  | .pending request => .pending request

/-- Recognize finite checked syntax through original compilation and return its fully typed production result. -/
@[expose] def Expr.check (environment : Fin arity → Annotated) (expression : Expr arity) :
    CheckedResult environment expression :=
  (expression.attempt environment).finish

/-- Supply the exact requested intrinsic original admission and continue through the same production frontend. -/
@[expose] def Pending.check (pending : Pending environment expression) (evidence : pending.Admission) :
    CheckedResult environment expression :=
  (pending.resume evidence).finish

/-- Complete an intrinsically admitted finite expression and cache its own computed production decision. -/
@[expose] def Admitted.check (admitted : Admitted environment expression) : CheckedResult environment expression :=
  admitted.run.finish

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
