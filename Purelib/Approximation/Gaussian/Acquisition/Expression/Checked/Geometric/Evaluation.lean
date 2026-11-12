module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Construction
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Context
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Approximation.Gaussian.Division (Prepared)

variable {arity : Nat} {environment : Fin arity → Annotated}

set_option genInjectivity false in
/-- An original checked context retaining its completed geometric prefix and unvisited original right input. -/
inductive Frame (environment : Fin arity → Annotated) : Expr arity → Expr arity → Type 2 where
  /-- A total unary parent retains its exact unfinished child syntax. -/
  | unary (operation : Unary) (input : Expr arity) : Frame environment input (operation.expression input)
  /-- An inverse parent retains its exact unfinished original denominator syntax. -/
  | inverse (input : Expr arity) : Frame environment input (.inverse input)
  /-- The original left child is unfinished and its actual right admission/geometry remains unvisited. -/
  | left (operation : Binary) (left right : Expr arity) (second : Admitted environment right)
      (geometry : Geometry second) : Frame environment left (operation.expression left right)
  /-- The original left child and all its geometric caches are complete while the right child is unfinished. -/
  | right (operation : Binary) (left : Expr arity) (first : Realization environment left) (right : Expr arity) :
      Frame environment right (operation.expression left right)

constructive_injectivity Frame

/-- Read the existing original checked frame, preserving its exact completed sibling. -/
@[expose] def Frame.original {input output : Expr arity} : Frame environment input output →
    Checked.Frame environment input output
  | .unary operation input => .unary operation input
  | .inverse input => .inverse input
  | .left operation firstExpression secondExpression _ _ => .left operation firstExpression secondExpression
  | .right operation _ first secondExpression => .right operation first.completed.toResult secondExpression

/-- Read the actual complete original geometric sibling retained by a right-child frame. -/
@[expose] def Frame.completed {input output : Expr arity} : Frame environment input output →
    Option ((original : Expr arity) × Realization environment original)
  | .right _ firstExpression first _ => some ⟨firstExpression, first⟩
  | .unary .. | .inverse .. | .left .. => none

set_option genInjectivity false in
/-- The first exact original inverse obstruction with its computed decision and geometric prefix. -/
inductive Invalid (environment : Fin arity → Annotated) : Expr arity → Type 2 where
  /-- The retained original completed denominator's actual cached decision proves operational zero. -/
  | inverse {input : Expr arity} (child : Realization environment input)
      (resolution : Resolution child.completed) (zero : ZeroIdentity child.completed.channel)
      (decided : resolution.decision = .excluded zero) : Invalid environment (.inverse input)
  /-- Retain the exact original context around the same first invalid occurrence. -/
  | through {input output : Expr arity} (frame : Frame environment input output)
      (first : Invalid environment input) : Invalid environment output

constructive_injectivity Invalid

/-- Project the existing exact-zero obstruction on the same original completed denominator and frames. -/
@[expose] def Invalid.original {expression : Expr arity} : Invalid environment expression →
    Checked.Invalid environment expression
  | .inverse child _ zero _ => .inverse child.completed.toResult zero
  | .through frame first => .through frame.original first.original

/-- Read the same original geometric denominator, cached resolution and exact operational zero identity. -/
@[expose] def Invalid.denominator {expression : Expr arity} : Invalid environment expression →
    (input : Expr arity) × (child : Realization environment input) ×
      Resolution child.completed × ZeroIdentity child.completed.channel
  | .inverse child resolution zero _ => ⟨_, child, resolution, zero⟩
  | .through _ first => first.denominator

/-- Read every actual original completed geometric sibling preceding the first invalid inverse. -/
@[expose] def Invalid.prefix {expression : Expr arity} : Invalid environment expression →
    List ((original : Expr arity) × Realization environment original)
  | .inverse .. => []
  | .through frame first => match frame.completed with
    | some sibling => sibling :: first.prefix
    | none => first.prefix

set_option genInjectivity false in
/-- An exact original base compilation whose genuine used-leaf geometric contract was not supplied. -/
structure BaseRequest (environment : Fin arity → Annotated) (expression : Basic.Expr arity) where
  /-- The complete actual original total compiler cache. -/
  cached : Base.Cached environment expression
  /-- The complete original intrinsic admission table. -/
  admissions : Base.Admissions cached.compiled.bindings
  /-- The complete actual original admission node is retained for retry. -/
  original : Admitted environment (.base expression)
  /-- The retained node is exactly this original compilation and admission table. -/
  original_eq : original = .base cached admissions
  /-- The actual offered geometric contract concerns exactly the same used original leaves. -/
  offered : Option cached.compiled.Geometry
  /-- This finite attempt has no supplied geometric tree for the same original compilation. -/
  unavailable : offered = none

constructive_injectivity BaseRequest

/-- Read the complete retained original compiler cache without invoking its original compiler. -/
abbrev BaseRequest.compiled {expression : Basic.Expr arity} (request : BaseRequest environment expression) :=
  request.cached.compiled

set_option genInjectivity false in
/-- A missing original geometric contract or insufficient spatial condition with all original caches retained.

The failed ball condition is only finite inconclusivity. Its cached algebraic
decision is nonzero at this original channel, but supplies no path-wide spatial
clearance by itself. Contexts retain all earlier caches and unvisited syntax.
-/
inductive Request (environment : Fin arity → Annotated) : Expr arity → Type 2 where
  /-- The exact original used-leaf geometry remains a typed fillable obligation. -/
  | base {expression : Basic.Expr arity} (request : BaseRequest environment expression) :
      Request environment (.base expression)
  /-- The actual spatial ball is insufficient while the same cached original-channel decision is nonzero. -/
  | clearance {input : Expr arity} (child : Realization environment input)
      (failed : ¬ Preparation.Separated child.enclosing.ball) (resolution : Resolution child.completed)
      (prepared : Prepared child.completed.channel) (decided : resolution.decision = .prepared prepared) :
      Request environment (.inverse input)
  /-- Retain the original context around the exact first outstanding obligation. -/
  | through {input output : Expr arity} (frame : Frame environment input output)
      (first : Request environment input) : Request environment output

constructive_injectivity Request

/-- Read the exact first missing used-leaf geometric contract through its retained original contexts. -/
@[expose] def Request.base? {expression : Expr arity} : Request environment expression →
    Option ((input : Basic.Expr arity) × BaseRequest environment input)
  | .base request => some ⟨_, request⟩
  | .clearance .. => none
  | .through _ first => first.base?

/-- Read every original completed geometric sibling preceding the first outstanding condition. -/
@[expose] def Request.prefix {expression : Expr arity} : Request environment expression →
    List ((original : Expr arity) × Realization environment original)
  | .base .. | .clearance .. => []
  | .through frame first => match frame.completed with
    | some sibling => sibling :: first.prefix
    | none => first.prefix

set_option genInjectivity false in
/-- A certified common enclosure refinement of the same original denominator sample program.

The new ball contains every reading of the unchanged program and carries genuine
apartness. Both the old enclosure and its completed cache remain in the request;
resumption stores this refinement beside them and reuses its cached decision.
-/
structure ClearanceFill {input : Expr arity} (child : Realization environment input) where
  /-- The actual common enclosure of the same original denominator channel. -/
  enclosing : Enclosure child.completed.channel
  /-- The geometric program is exactly the previously retained original program. -/
  source_eq : enclosing.source = child.enclosing.source
  /-- The retained refined ball has genuine positive denominator clearance. -/
  apart : Ball.Apart enclosing.ball

constructive_injectivity ClearanceFill

/-- Supply genuine apartness of the same retained ball without changing its original program or enclosure. -/
@[expose] def ClearanceFill.ofApart {input : Expr arity} (child : Realization environment input)
    (apart : Ball.Apart child.enclosing.ball) : ClearanceFill child := ⟨child.enclosing, rfl, apart⟩

/-- Genuine evidence fills exactly the original used-leaf or same-program clearance obligation. -/
@[expose] def Request.Fill {expression : Expr arity} : Request environment expression → Type
  | .base request => request.cached.compiled.Geometry
  | .clearance child .. => ClearanceFill child
  | .through _ first => first.Fill

set_option genInjectivity false in
/-- A completed original spatial construction, exact first zero obstruction or retained finite request. -/
inductive Outcome (environment : Fin arity → Annotated) (expression : Expr arity) : Type 2 where
  /-- Every supported original syntax node and required reciprocal condition was retained and realized. -/
  | completed (result : Realization environment expression)
  /-- The same original completed denominator proves an actual exact zero obstruction. -/
  | invalid (obstruction : Invalid environment expression)
  /-- All original work remains cached while genuine missing spatial evidence is requested. -/
  | requested (request : Request environment expression)

constructive_injectivity Outcome

namespace Outcome

/-- Apply a total unary operation only after its original child's required domain has succeeded. -/
@[expose] def unary (operation : Unary) {input : Expr arity} : Outcome environment input →
    Outcome environment (operation.expression input)
  | .completed child => .completed (child.unary operation)
  | .invalid first => .invalid (.through (.unary operation input) first)
  | .requested first => .requested (.through (.unary operation input) first)

/-- Check one same original denominator's spatial condition before constructing its reciprocal.

The positive branch computes its apartness and actual payment. Failure retains
the original algebraic resolution and decision once; only a genuine excluded
decision produces an obstruction. A nonzero decision leaves spatial clearance
as an explicit request rather than a global continuation claim.
-/
@[expose] def inverse {input : Expr arity} : Outcome environment input → Outcome environment (.inverse input)
  | .invalid first => .invalid (.through (.inverse input) first)
  | .requested first => .requested (.through (.inverse input) first)
  | .completed child =>
      if separated : Preparation.Separated child.enclosing.ball then
        let apart := Residual.apartOfCenter child.enclosing.ball separated
        .completed (child.inverse apart)
      else
        let resolution := resolve child.completed
        match decided : resolution.decision with
        | .excluded zero => .invalid (.inverse child resolution zero decided)
        | .prepared prepared => .requested (.clearance child separated resolution prepared decided)

/-- Complete the original right child after retaining the exact already completed geometric left child. -/
@[expose] def right (operation : Binary) {left right : Expr arity} (first : Realization environment left) :
    Outcome environment right → Outcome environment (operation.expression left right)
  | .completed second => .completed (first.binary operation second)
  | .invalid failed => .invalid (.through (.right operation left first right) failed)
  | .requested pending => .requested (.through (.right operation left first right) pending)

end Outcome

/-- Interpret the original finite admitted syntax in order without changing fixed-point completion.

Optional geometry concerns only actual used base leaves. Missing geometry,
failed spatial clearance and exact-zero obstructions preserve their original
contexts and caches. Every power, including zero, first checks its child.
-/
@[expose] def run : {expression : Expr arity} → (admitted : Admitted environment expression) →
    Geometry admitted → Outcome environment expression
  | _, .base cached admissions, offered =>
      match offered with
      | some geometry => .completed (Realization.base cached admissions geometry)
      | none => .requested (.base ⟨cached, admissions, .base cached admissions, rfl, none, rfl⟩)
  | _, .unary operation child, geometry => (run child geometry).unary operation
  | _, .inverse child, geometry => (run child geometry).inverse
  | _, .binary operation first second, geometry =>
      match run first geometry.1 with
      | .completed left => (run second geometry.2).right operation left
      | .invalid firstFailure =>
          .invalid (.through (.left operation _ _ second geometry.2) firstFailure)
      | .requested firstRequest =>
          .requested (.through (.left operation _ _ second geometry.2) firstRequest)

/-- Continue an original context using its exact cached completed sibling or unvisited right admission. -/
@[expose] def Frame.resume {input output : Expr arity} (frame : Frame environment input output)
    (outcome : Outcome environment input) : Outcome environment output :=
  match frame with
  | .unary operation _ => outcome.unary operation
  | .inverse _ => outcome.inverse
  | .right operation _ first _ => outcome.right operation first
  | .left operation firstExpression secondExpression second geometry =>
      match outcome with
      | .completed first => (run second geometry).right operation first
      | .invalid failed =>
          .invalid (.through (.left operation firstExpression secondExpression second geometry) failed)
      | .requested pending =>
          .requested (.through (.left operation firstExpression secondExpression second geometry) pending)

/-- Fill the exact original outstanding contract and continue without rebuilding completed prefixes. -/
@[expose] def Request.resume {expression : Expr arity} : (request : Request environment expression) →
    request.Fill → Outcome environment expression
  | .base request, geometry => .completed (Realization.base request.cached request.admissions geometry)
  | .clearance child _ resolution prepared decided, filled =>
      .completed ((child.refine filled.enclosing filled.source_eq).resumeInverse filled.apart
        resolution prepared decided)
  | .through frame first, filled => frame.resume (first.resume filled)

/-- A zero power preserves the actual child's exact first obstruction and original unary frame. -/
theorem Outcome.pow_zero_invalid {input : Expr arity} (obstruction : Invalid environment input) :
    (Outcome.invalid obstruction).unary (.pow 0) =
      .invalid (.through (.unary (.pow 0) input) obstruction) := rfl

/-- A zero power preserves the same first outstanding original geometry or domain contract. -/
theorem Outcome.pow_zero_requested {input : Expr arity} (request : Request environment input) :
    (Outcome.requested request).unary (.pow 0) =
      .requested (.through (.unary (.pow 0) input) request) := rfl

/-- The original missing base node retains the exact total compiler and intrinsic admissions. -/
theorem run_base_missing {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (admissions : Base.Admissions cached.compiled.bindings) :
    run (.base cached admissions) none =
      .requested (.base ⟨cached, admissions, .base cached admissions, rfl, none, rfl⟩) := rfl

/-- Completing a suspended right child consumes the exact cached original left realization. -/
theorem Frame.right_completed (operation : Binary) {left right : Expr arity}
    (first : Realization environment left) (second : Realization environment right) :
    (Frame.right operation left first right).resume (.completed second) =
      .completed (first.binary operation second) := rfl

/-- Reading a right-child frame preserves its complete original left geometric realization. -/
theorem Frame.right_prefix (operation : Binary) {left : Expr arity}
    (first : Realization environment left) (right : Expr arity) :
    (Frame.right operation left first right).completed = some ⟨left, first⟩ := rfl

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

end
