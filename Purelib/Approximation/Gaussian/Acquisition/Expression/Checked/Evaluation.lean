module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Context
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Approximation.Gaussian.Provenance.Algebraic

/-!
# Finite checked evaluation and retained admission retries

Evaluation follows original syntax from left to right. Missing admission data
suspends at its exact original bounded binding; resumption supplies evidence
for that same channel and consumes the retained continuation frames.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Provenance

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- Inspect stored original admission slots without recompiling the total base or repeating its root producers. -/
@[expose] def Base.Cached.attempt {expression : Basic.Expr arity} (cached : Base.Cached environment expression) :
    Outcome environment (.base expression) :=
  match Base.Certificate.existing cached with
  | some certificate => .completed (Construction.Result.ofBaseCertificate cached certificate)
  | none => match Base.checkSlots cached.compiled.bindings cached.slots cached.required with
    | .ok ready => .completed (Construction.Result.ofBaseCertificate cached (cached.certificateReady ready.down))
    | .error missing =>
        .pending (.base cached missing (Base.Slots.missing cached.compiled.bindings cached.slots cached.required) rfl)

/-- Apply a total unary parent, retaining any original first obstruction or suspension frame. -/
@[expose] def Outcome.unary (operation : Unary) {expression : Expr arity} :
    Outcome environment expression → Outcome environment (operation.expression expression)
  | .completed child => .completed (operation.complete child)
  | .invalid first => .invalid (.through (.unary operation expression) first)
  | .pending request => .pending (.through (.unary operation expression) request)

/-- Compute a reciprocal using the same original child sidecar and its own computed localization bound. -/
@[expose] def Outcome.inverse {expression : Expr arity} :
    Outcome environment expression → Outcome environment (.inverse expression)
  | .completed child => match child.inverseAttempt with
    | .ok result => .completed result
    | .error obstruction => .invalid (.inverse obstruction.1 obstruction.2)
  | .invalid first => .invalid (.through (.inverse expression) first)
  | .pending request => .pending (.through (.inverse expression) request)

/-- Finish a right child using the same already completed and cached original left sibling. -/
@[expose] def Outcome.right (operation : Binary) {left right : Expr arity} (first :
    Construction.Result environment left) :
    Outcome environment right → Outcome environment (operation.expression left right)
  | .completed second => .completed (operation.complete first second)
  | .invalid firstInvalid => .invalid (.through (.right operation first right) firstInvalid)
  | .pending request => .pending (.through (.right operation first right) request)

/-- Visit the right syntax only after the original left child has completed productively. -/
@[expose] def Outcome.binary (operation : Binary) {left right : Expr arity}
    (first : Outcome environment left) (later : Unit → Outcome environment right) :
    Outcome environment (operation.expression left right) :=
  match first with
  | .completed firstDone => (later ()).right operation firstDone
  | .invalid firstInvalid => .invalid (.through (.left operation left right) firstInvalid)
  | .pending request => .pending (.through (.left operation left right) request)

/-- Evaluate finite original checked syntax, retaining every completed child and unresolved original admission. -/
@[expose] def Expr.attempt (environment : Fin arity → Annotated)
    (expression : Expr arity) : Outcome environment expression :=
  let Result : (mode : Basic.Mode) → Basic.Expr arity mode → Type 1 :=
    fun mode => match mode with
    | .total => fun _ => PUnit
    | .checked => fun expression => Outcome environment expression
  let rec visit {mode : Basic.Mode} (expression : Basic.Expr arity mode) : Result mode expression :=
    match expression with
    | .atom _ | .rational _ | .root _ _ => PUnit.unit
    | .base expression => (Base.Cached.ofExpression environment expression).attempt
    | .neg input =>
      match mode with
      | .total => PUnit.unit
      | .checked => (visit input).unary .neg
    | .add left right =>
      match mode with
      | .total => PUnit.unit
      | .checked => (visit left).binary .add (fun _ => visit right)
    | .sub left right =>
      match mode with
      | .total => PUnit.unit
      | .checked => (visit left).binary .sub (fun _ => visit right)
    | .mul left right =>
      match mode with
      | .total => PUnit.unit
      | .checked => (visit left).binary .mul (fun _ => visit right)
    | .pow input exponent => (visit input).unary (.pow exponent)
    | .conj input => (visit input).unary .conj
    | .inverse input => (visit input).inverse
  termination_by structural expression
  visit expression

/-- Evaluate original checked syntax and retain its actual complete Sidecar when full materialization is requested. -/
@[expose] def Expr.materialize (environment : Fin arity → Annotated) (expression : Expr arity) :
    MaterializedOutcome environment expression := (expression.attempt environment).materialize

namespace Pending

/-- The exact original base compilation at the unresolved occurrence, retaining all actual previous work. -/
@[expose] def original {expression : Expr arity} : Pending environment expression →
    (base : Basic.Expr arity) × Base.Cached environment base
  | .base cached _ _ _ => ⟨_, cached⟩
  | .through _ pending => pending.original

/-- Read every unresolved bounded original leaf position in the retained base table. -/
@[expose] def unresolved {expression : Expr arity} (pending : Pending environment expression) :
    List (Fin pending.original.2.compiled.bindings.length) :=
  match pending with
  | .base _ _ unresolved _ => unresolved
  | .through _ inner => inner.unresolved

/-- Read the first unresolved original bounded position from the retained request. -/
@[expose] def index {expression : Expr arity} : (pending : Pending environment expression) →
    Fin pending.original.2.compiled.bindings.length
  | .base _ missing _ _ => missing.index
  | .through _ pending => pending.index

/-- Read the actual original source binding whose intrinsic evidence is requested. -/
@[expose] def binding {expression : Expr arity} (pending : Pending environment expression) :
    Basic.Binding environment :=
  Basic.Binding.read pending.original.2.compiled.bindings pending.index

/-- Count retained parent frames from the exact unresolved base to the original output syntax. -/
@[expose] def depth {expression : Expr arity} : Pending environment expression → Nat
  | .base _ _ _ _ => 0
  | .through _ pending => pending.depth + 1

/-- Read every still unvisited original right sibling in its original evaluation order. -/
@[expose] def unvisited {expression : Expr arity} : Pending environment expression → List (Expr arity)
  | .base _ _ _ _ => []
  | .through (.left _ _ remaining) pending => pending.unvisited ++ [remaining]
  | .through (.unary _ _) pending | .through (.inverse _) pending | .through (.right _ _ _) pending =>
      pending.unvisited

/-- New intrinsic admission data for this exact first unresolved original channel.

The original source binding and its channel, rather than a matching syntax or
parameter, determine the requested evidence type.
-/
@[expose] def Admission {expression : Expr arity} : Pending environment expression → Type 1
  | .base cached missing _ _ =>
      Algebraic.Sidecar (Basic.Binding.read cached.compiled.bindings missing.index).annotation.channel
  | .through _ pending => pending.Admission

/-- The requested type is the intrinsic sidecar type of this same actual original source binding. -/
theorem admission_eq {expression : Expr arity} (pending : Pending environment expression) :
    pending.Admission = Algebraic.Sidecar pending.binding.annotation.channel := by
  induction pending with
  | base _ _ _ _ => rfl
  | through _ _ ih => exact ih

/-- Supply a same-channel sidecar to the exact retained request, without selecting a new source leaf. -/
@[expose] def admit {expression : Expr arity} (pending : Pending environment expression)
    (sidecar : Algebraic.Sidecar pending.binding.annotation.channel) : pending.Admission :=
  pending.admission_eq.symm ▸ sidecar

/-- Read newly supplied intrinsic original atom evidence through the actual original binding's full annotation law.

An explicit legacy root leaf stays unresolved on this route: a matching
parameter never supplies its missing intrinsic original root owner link.
-/
@[expose] def fromAtoms {expression : Expr arity} (pending : Pending environment expression)
    (supplied : (index : Fin arity) → Algebraic.Sidecar (environment index).channel) : Option pending.Admission :=
  let binding := pending.binding
  match selected : binding.leaf with
  | .root _ _ => none
  | .atom index =>
      have original : binding.annotation = environment index :=
        binding.annotation_eq.trans (congrArg (fun leaf => leaf.annotation environment) selected)
      some (pending.admit ((congrArg Annotated.channel original).symm ▸ supplied index))

end Pending

/-- Consume a retained evaluation frame without repeating its original completed siblings. -/
@[expose] def Frame.resume {input output : Expr arity} (frame : Frame environment input output)
    (outcome : Outcome environment input) : Outcome environment output :=
  match frame with
  | .unary operation _ => outcome.unary operation
  | .inverse _ => outcome.inverse
  | .left operation _ unvisited => outcome.binary operation (fun _ => unvisited.attempt environment)
  | .right operation first _ => outcome.right operation first

/-- Supply the exact missing original admission and resume only retained unfinished evaluation frames. -/
@[expose] def Pending.resume {expression : Expr arity} : (pending : Pending environment expression) →
    pending.Admission → Outcome environment expression
  | .base cached missing _ _, evidence => (cached.supply missing.index evidence).attempt
  | .through frame inner, evidence => frame.resume (inner.resume evidence)

/-- A resolved original child remains resolved under every total unary operation. -/
theorem Outcome.unary_resolved (operation : Unary) {expression : Expr arity}
    (outcome : Outcome environment expression) (resolved : outcome.Resolved) :
    (outcome.unary operation).Resolved := by
  cases outcome with
  | completed _ => exact True.intro
  | invalid _ => exact True.intro
  | pending _ => exact False.elim resolved

/-- A resolved original child yields either a productive checked reciprocal or its exact first zero obstruction. -/
theorem Outcome.inverse_resolved {expression : Expr arity} (outcome : Outcome environment expression)
    (resolved : outcome.Resolved) : outcome.inverse.Resolved := by
  cases outcome with
  | completed child =>
      dsimp only [Outcome.inverse]
      cases child.inverseAttempt with
      | ok _ => exact True.intro
      | error _ => exact True.intro
  | invalid _ => exact True.intro
  | pending _ => exact False.elim resolved

/-- A resolved right child remains resolved when joined to the same already completed original left sibling. -/
theorem Outcome.right_resolved (operation : Binary) {left right : Expr arity}
    (first : Construction.Result environment left) (outcome : Outcome environment right) (resolved : outcome.Resolved) :
    (outcome.right operation first).Resolved := by
  cases outcome with
  | completed _ => exact True.intro
  | invalid _ => exact True.intro
  | pending _ => exact False.elim resolved

/-- Two resolved original children yield a resolved binary operation in its original left-to-right order. -/
theorem Outcome.binary_resolved (operation : Binary) {left right : Expr arity}
    (first : Outcome environment left) (later : Unit → Outcome environment right)
    (firstResolved : first.Resolved) (laterResolved : (later ()).Resolved) :
    (first.binary operation later).Resolved := by
  cases first with
  | completed child => exact Outcome.right_resolved operation child (later ()) laterResolved
  | invalid _ => exact True.intro
  | pending _ => exact False.elim firstResolved

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
