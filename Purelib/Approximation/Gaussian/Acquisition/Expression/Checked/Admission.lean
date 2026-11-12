module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Executable completion from finite original algebraic admissions

A finite admission tree supplies intrinsic original leaf sidecars at each
retained total base compiler's actual bounded binding spine. No reciprocal
preparation, denominator floor or successful expression attempt is an input.
Evaluation computes every such decision from the stored quantitative residuals.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {arity : Nat} {environment : Fin arity → Annotated}

set_option genInjectivity false in
/-- Finite intrinsic original leaf admissions for all bases of one checked expression.

Root entries retain their original polynomial, isolation, multiplicity and
numerical channel comparison through their algebraic sidecars. The table
positions are those of the actual original compiler, including repeated leaves.
-/
inductive Admitted (environment : Fin arity → Annotated) : Expr arity → Type 1 where
  /-- Supply the finite actual original leaf admissions of this same retained total compilation. -/
  | base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
      (admissions : Base.Admissions cached.compiled.bindings) : Admitted environment (.base expression)
  /-- Retain intrinsic admissions of the original child under a total unary operation. -/
  | unary (operation : Unary) {input : Expr arity} (child : Admitted environment input) :
      Admitted environment (operation.expression input)
  /-- Retain intrinsic admissions of the original denominator without assuming its nonzero status. -/
  | inverse {input : Expr arity} (child : Admitted environment input) : Admitted environment (.inverse input)
  /-- Retain intrinsic admissions of both original ordered children under a binary operation. -/
  | binary (operation : Binary) {left right : Expr arity} (first : Admitted environment left)
      (second : Admitted environment right) : Admitted environment (operation.expression left right)

constructive_injectivity Admitted

namespace Admitted

/-- Admit one actual original input atom using its supplied intrinsic same-channel evidence.

The original annotation and its actual root owner are retained directly. No
root isolation, channel replacement or successful expression attempt is needed.
-/
@[expose] def atom (environment : Fin arity → Annotated) (index : Fin arity)
    (sidecar : Algebraic.Sidecar (environment index).channel) :
    Admitted environment (.atom index) :=
  let compiled : Basic.Compiled environment (.atom index) :=
    ⟨environment index, .atom index (environment index) rfl⟩
  let cached : Base.Cached environment (.atom index) := ⟨compiled, (some sidecar, PUnit.unit), none, PUnit.unit⟩
  .base cached (sidecar, PUnit.unit)

/-- Admit an exact Gaussian constant through its original total compiler constructor. -/
@[expose] def rational (environment : Fin arity → Annotated) (value : Canonical) :
    Admitted environment (.rational value) :=
  let annotation := Annotated.rational value
  let compiled : Basic.Compiled environment (.rational value) := ⟨annotation, .rational value annotation rfl⟩
  let cached : Base.Cached environment (.rational value) := ⟨compiled, PUnit.unit, none, PUnit.unit⟩
  .base cached PUnit.unit

/-- Retain the original admitted child under numerical negation. -/
@[expose] def neg {input : Expr arity} (child : Admitted environment input) : Admitted environment (.neg input) :=
  .unary .neg child

/-- Retain both original admitted children under numerical addition. -/
@[expose] def add {left right : Expr arity} (first : Admitted environment left) (second : Admitted environment right) :
    Admitted environment (.add left right) := .binary .add first second

/-- Retain both original admitted children under numerical subtraction. -/
@[expose] def sub {left right : Expr arity} (first : Admitted environment left) (second : Admitted environment right) :
    Admitted environment (.sub left right) := .binary .sub first second

/-- Retain both original admitted children under numerical multiplication. -/
@[expose] def mul {left right : Expr arity} (first : Admitted environment left) (second : Admitted environment right) :
    Admitted environment (.mul left right) := .binary .mul first second

/-- Retain the original admitted child under every finite natural power. -/
@[expose] def pow {input : Expr arity} (child : Admitted environment input) (exponent : Nat) :
    Admitted environment (.pow input exponent) := .unary (.pow exponent) child

/-- Retain the original admitted child under numerical conjugation. -/
@[expose] def conj {input : Expr arity} (child : Admitted environment input) : Admitted environment (.conj input) :=
  .unary .conj child

/-- Evaluate the admitted fragment using its same original inputs and internally computed finite decision bounds. -/
@[expose] def run : {expression : Expr arity} → Admitted environment expression → Outcome environment expression
  | _, .base cached admissions => .completed (Construction.Result.base cached admissions)
  | _, .unary operation child => child.run.unary operation
  | _, .inverse child => child.run.inverse
  | _, .binary operation first second => first.run.binary operation (fun _ => second.run)

/-- Complete all original inverse guards and retain the actual full Sidecar only at this named materialization
boundary. -/
@[expose] def materialize {expression : Expr arity} (admitted : Admitted environment expression) :
    MaterializedOutcome environment expression := admitted.run.materialize

/-- Every finite admitted checked expression resolves productively or at its first exact zero reciprocal.

This executable completeness claim includes arbitrary positive-degree admitted
atoms, constants, negation, addition, subtraction, multiplication, all natural
powers, conjugation and checked reciprocals. Its finite inputs are intrinsic
original leaf admissions; every exclusion floor and reciprocal cache is computed.
-/
theorem complete {expression : Expr arity} (admitted : Admitted environment expression) : admitted.run.Resolved := by
  induction admitted with
  | base _ _ => exact True.intro
  | unary operation child ih => exact Outcome.unary_resolved operation child.run ih
  | inverse child ih => exact Outcome.inverse_resolved child.run ih
  | binary operation first second firstIH secondIH =>
      exact Outcome.binary_resolved operation first.run (fun _ => second.run) firstIH secondIH

/-- Project the complete original total-compilation branch of an admitted base expression.

The syntax equality identifies this same branch; every non-base constructor is
excluded by its actual expression constructor. The retained compiler and
admissions are consumed directly, without another evaluation or compilation.
-/
@[expose] def baseCompleted {original : Expr arity} (admitted : Admitted environment original)
    (expression : Basic.Expr arity) (same : original = .base expression) :
    Completed environment (.base expression) :=
  match admitted with
  | .base cached admissions => same ▸ Completed.base cached admissions
  | .unary .neg _ => nomatch same
  | .unary (.pow _) _ => nomatch same
  | .unary .conj _ => nomatch same
  | .inverse _ => nomatch same
  | .binary .add _ _ => nomatch same
  | .binary .sub _ _ => nomatch same
  | .binary .mul _ _ => nomatch same

end Admitted

namespace Completed

/-- Complete an original atom by projecting its same intrinsic admission branch.

The retained compiler, bounded binding and root sidecar are exactly those of
`Admitted.atom`; this constructor performs no new root isolation or decision.
-/
@[expose] def atom (environment : Fin arity → Annotated) (index : Fin arity)
    (sidecar : Algebraic.Sidecar (environment index).channel) :
    Completed environment (.atom index) :=
  (Admitted.atom environment index sidecar).baseCompleted (.atom index) rfl

/-- Complete an exact constant by projecting its original intrinsic admission branch. -/
@[expose] def rational (environment : Fin arity → Annotated) (value : Canonical) :
    Completed environment (.rational value) :=
  (Admitted.rational environment value).baseCompleted (.rational value) rfl

/-- The completed atom retains the numerical channel of the original input annotation. -/
theorem atom_channel (environment : Fin arity → Annotated) (index : Fin arity)
    (sidecar : Algebraic.Sidecar (environment index).channel) :
    (atom environment index sidecar).channel = (environment index).channel := by
  dsimp only [atom, Admitted.atom, Admitted.baseCompleted, base]
  exact Construction.Result.materialize_channel _

/-- The completed constant retains the original exact numerical channel. -/
theorem rational_channel (environment : Fin arity → Annotated) (value : Canonical) :
    (rational environment value).channel =
      CoherentNamed.Coherence.exact value := rfl

/-- The materialized admitted atom retains the complete original atom completion. -/
theorem atom_run (environment : Fin arity → Annotated) (index : Fin arity)
    (sidecar : Algebraic.Sidecar (environment index).channel) :
    (Admitted.atom environment index sidecar).run.materialize = .ok (atom environment index sidecar) := rfl

/-- The materialized admitted constant retains the complete original exact completion. -/
theorem rational_run (environment : Fin arity → Annotated) (value : Canonical) :
    (Admitted.rational environment value).run.materialize = .ok (rational environment value) := rfl

end Completed

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
