module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Admission
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Enclosure
public import Purelib.Approximation.Gaussian.Geometric.Enclosure.Inverse
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Context
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Enclosure.Residual
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Polynomial.Approximation.Gaussian

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- Optional genuine geometry for precisely the original base nodes of an admitted checked expression. -/
@[expose] def Geometry : {expression : Expr arity} → Admitted environment expression → Type
  | _, .base cached _ => Option cached.compiled.Geometry
  | _, .unary _ child => Geometry child
  | _, .inverse child => Geometry child
  | _, .binary _ first second => Geometry first × Geometry second

namespace Geometry

/-- Exact constants supply their original empty geometric obligation directly. -/
@[expose] def rational (environment : Fin arity → Annotated) (value : Purelib.Data.Gaussian.Basic.Canonical) :
    Geometry (Admitted.rational environment value) := some ()

/-- Supply genuine geometry at an admitted atom's same original bounded compiler occurrence. -/
@[expose] def atom (environment : Fin arity → Annotated) (index : Fin arity)
    (sidecar : Algebraic.Sidecar (environment index).channel) (enclosing : Enclosure (environment index).channel) :
    Geometry (Admitted.atom environment index sidecar) :=
  some ⟨⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩, rfl, enclosing⟩

end Geometry

set_option genInjectivity false in
/-- One actual original algebraic resolution and its once read division decision.

The decision is stored beside the complete original resolution. Resuming a
spatial request consumes that same preparation or zero identity rather than
re-running scalar reading, localization or the resolution's decision reader.
-/
structure Resolution {expression : Expr arity} (child : Checked.Completed environment expression) where
  /-- The actual original algebraic decision construction. -/
  original : Algebraic.Sidecar.Resolved child.sidecar
  /-- The retained construction is the original resolver on the unchanged child. -/
  original_eq : original = child.sidecar.resolve
  /-- The once read original-channel decision. -/
  decision : Prepared.Decision child.channel
  /-- The stored decision is exactly the retained resolution's decision. -/
  decision_eq : decision = original.decision

constructive_injectivity Resolution

/-- Resolve one original completed child and retain its exact actual decision once. -/
@[expose] def resolve {expression : Expr arity} (child : Checked.Completed environment expression) : Resolution child :=
  let original := child.sidecar.resolve
  let decision := original.decision
  ⟨original, rfl, decision, rfl⟩

/-- Pay an actual geometric observation using only the retained common ball's certified lower quadrance. -/
@[expose] def prepareInverse {expression : Expr arity} (child : Checked.Completed environment expression)
    (enclosing : Enclosure child.channel) (apart : Ball.Apart enclosing.ball) : Inverse child :=
  fromLower child enclosing.source enclosing.equivalent
    (Refinement.State.initial (Preparation.sampledChannel enclosing.source)) apart.lowerSq apart.positive
    (fun index => apart.lower (enclosing.contains index))

set_option genInjectivity false in
/-- Retained geometric child caches following the original completed checked construction.

All syntax children remain in the tree, including the child of exponent zero.
Base nodes retain their complete original compiler interpretation. Reciprocal
nodes preserve both the formal enclosure and the distinct actual residual cache.
-/
inductive Cache : {expression : Expr arity} → (completed : Checked.Completed environment expression) →
    Enclosure completed.channel → Type 2 where
  /-- Retain the actual original compilation, used geometry and complete spatial interpretation. -/
  | base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
      (admissions : Base.Admissions cached.compiled.bindings) (geometry : cached.compiled.Geometry)
      (basic : cached.compiled.Enclosed cached.compiled.bindings)
      (computed : basic = cached.compiled.encloseBindings geometry) :
      Cache (Checked.Completed.base cached admissions) basic.result
  /-- Retain the original child and its formal numerical negation. -/
  | neg {expression : Expr arity} (child : Checked.Completed environment expression)
      (enclosing : Enclosure child.channel) (cache : Cache child enclosing) :
      Cache child.neg enclosing.neg
  /-- Retain both actual ordered original children of addition. -/
  | add {left right : Expr arity} (first : Checked.Completed environment left)
      (second : Checked.Completed environment right)
      (firstGeometry : Enclosure first.channel) (secondGeometry : Enclosure second.channel)
      (firstCache : Cache first firstGeometry) (secondCache : Cache second secondGeometry) :
      Cache (first.add second) (firstGeometry.add secondGeometry)
  /-- Retain both actual ordered original children of subtraction. -/
  | sub {left right : Expr arity} (first : Checked.Completed environment left)
      (second : Checked.Completed environment right)
      (firstGeometry : Enclosure first.channel) (secondGeometry : Enclosure second.channel)
      (firstCache : Cache first firstGeometry) (secondCache : Cache second secondGeometry) :
      Cache (first.sub second) (firstGeometry.sub secondGeometry)
  /-- Retain both actual ordered original children of multiplication. -/
  | mul {left right : Expr arity} (first : Checked.Completed environment left)
      (second : Checked.Completed environment right)
      (firstGeometry : Enclosure first.channel) (secondGeometry : Enclosure second.channel)
      (firstCache : Cache first firstGeometry) (secondCache : Cache second secondGeometry) :
      Cache (first.mul second) (firstGeometry.mul secondGeometry)
  /-- Every finite power retains its original child and all that child's domain obligations. -/
  | pow {expression : Expr arity} (child : Checked.Completed environment expression)
      (enclosing : Enclosure child.channel) (cache : Cache child enclosing) (exponent : Nat) :
      Cache (child.pow exponent) (enclosing.pow exponent)
  /-- Conjugation retains the same original child and its actual formal sample program. -/
  | conj {expression : Expr arity} (child : Checked.Completed environment expression)
      (enclosing : Enclosure child.channel) (cache : Cache child enclosing) :
      Cache child.conj enclosing.conj
  /-- Retain the original cached interpretation while narrowing its same actual geometric sample program. -/
  | refined {expression : Expr arity} (child : Checked.Completed environment expression)
      (original : Enclosure child.channel) (cache : Cache child original) (enclosing : Enclosure child.channel)
      (source_eq : enclosing.source = original.source) : Cache child enclosing
  /-- A sufficient spatial condition pays an actual original observation and retains its original inverse cache. -/
  | inverse {expression : Expr arity} (child : Checked.Completed environment expression)
      (enclosing : Enclosure child.channel) (cache : Cache child enclosing) (apart : Ball.Apart enclosing.ball)
      (inverse : Inverse child) (computed : inverse = prepareInverse child enclosing apart) :
      Cache inverse.completed ((enclosing.inverse inverse.paid.prepared apart).cast inverse.channel.symm)
  /-- Resumption consumes the original cached nonzero decision after genuine missing spatial evidence is supplied. -/
  | resumedInverse {expression : Expr arity} (child : Checked.Completed environment expression)
      (enclosing : Enclosure child.channel) (cache : Cache child enclosing) (apart : Ball.Apart enclosing.ball)
      (resolution : Resolution child) (prepared : Prepared child.channel)
      (decided : resolution.decision = .prepared prepared)
      (reciprocal : Residual.Reciprocal child.sidecar.residual prepared)
      (reciprocal_eq : reciprocal = Residual.Reciprocal.ofPrepared child.sidecar.residual prepared)
      (result : Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
      (result_eq : result = child.sidecar.reciprocalFromCache reciprocal) :
      Cache (child.inverse prepared reciprocal result result_eq) (enclosing.inverse prepared apart)

constructive_injectivity Cache

set_option genInjectivity false in
/-- A completed original checked node and its retained formal geometric realization.

The complete cache tree retains original children, bounded base receipts,
computed observations and residual caches. Its enclosure refers to its actual
formal program through an operational comparison, not residual sample identity.
-/
structure Realization (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The complete actual original checked construction and algebraic sidecar. -/
  completed : Checked.Completed environment expression
  /-- The original channel's retained formal program and common sample enclosure. -/
  enclosing : Enclosure completed.channel
  /-- The exact original child tree and computed spatial caches producing this node. -/
  cache : Cache completed enclosing

constructive_injectivity Realization

namespace Realization

/-- Narrow the common ball of the same original sample program while retaining all its prior caches. -/
@[expose] def refine {expression : Expr arity} (original : Realization environment expression)
    (enclosing : Enclosure original.completed.channel) (source_eq : enclosing.source = original.enclosing.source) :
    Realization environment expression :=
  ⟨original.completed, enclosing, .refined original.completed original.enclosing original.cache enclosing source_eq⟩

/-- Enclose one original admitted base using the actual supplied used-leaf geometry. -/
@[expose] def base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (admissions : Base.Admissions cached.compiled.bindings) (geometry : cached.compiled.Geometry) :
    Realization environment (.base expression) :=
  let basic := cached.compiled.encloseBindings geometry
  let completed := Checked.Completed.base cached admissions
  ⟨completed, basic.result, .base cached admissions geometry basic rfl⟩

/-- Apply a total unary operation after retaining every original child and domain obligation. -/
@[expose] def unary (operation : Unary) {input : Expr arity} (child : Realization environment input) :
    Realization environment (operation.expression input) :=
  match operation with
  | .neg => ⟨child.completed.neg, child.enclosing.neg, .neg child.completed child.enclosing child.cache⟩
  | .pow exponent =>
      ⟨child.completed.pow exponent, child.enclosing.pow exponent,
        .pow child.completed child.enclosing child.cache exponent⟩
  | .conj => ⟨child.completed.conj, child.enclosing.conj, .conj child.completed child.enclosing child.cache⟩

/-- Apply an ordered binary operation to the two same retained original children. -/
@[expose] def binary (operation : Binary) {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) : Realization environment (operation.expression left right) :=
  match operation with
  | .add =>
      ⟨first.completed.add second.completed, first.enclosing.add second.enclosing,
        .add first.completed second.completed first.enclosing second.enclosing first.cache second.cache⟩
  | .sub =>
      ⟨first.completed.sub second.completed, first.enclosing.sub second.enclosing,
        .sub first.completed second.completed first.enclosing second.enclosing first.cache second.cache⟩
  | .mul =>
      ⟨first.completed.mul second.completed, first.enclosing.mul second.enclosing,
        .mul first.completed second.completed first.enclosing second.enclosing first.cache second.cache⟩

/-- Prepare the original reciprocal from the computed sufficient spatial certificate and retain all original caches. -/
@[expose] def inverse {input : Expr arity} (child : Realization environment input)
    (apart : Ball.Apart child.enclosing.ball) : Realization environment (.inverse input) :=
  let inverse := prepareInverse child.completed child.enclosing apart
  let enclosing := (child.enclosing.inverse inverse.paid.prepared apart).cast inverse.channel.symm
  ⟨inverse.completed, enclosing, .inverse child.completed child.enclosing child.cache apart inverse rfl⟩

/-- Resume a missing spatial condition with genuine evidence while reusing its original cached nonzero decision. -/
@[expose] def resumeInverse {input : Expr arity} (child : Realization environment input)
    (apart : Ball.Apart child.enclosing.ball) (resolution : Resolution child.completed)
    (prepared : Prepared child.completed.channel) (decided : resolution.decision = .prepared prepared) :
    Realization environment (.inverse input) :=
  let reciprocal := Residual.Reciprocal.ofPrepared child.completed.sidecar.residual prepared
  let result := child.completed.sidecar.reciprocalFromCache reciprocal
  let completed := child.completed.inverse prepared reciprocal result rfl
  let enclosing := child.enclosing.inverse prepared apart
  ⟨completed, enclosing,
    .resumedInverse child.completed child.enclosing child.cache apart resolution prepared decided
      reciprocal rfl result rfl⟩

/-- Apply original negation with its retained exact common ball and the same original child cache. -/
@[expose] def negFromBall {input : Expr arity} (child : Realization environment input)
    (ball : Ball) (same : ball = child.enclosing.ball.neg) : Realization environment (.neg input) :=
  let enclosing := child.enclosing.negFromBall ball same
  let cache : Cache child.completed.neg enclosing :=
    Eq.ndrec (motive := fun result => Cache child.completed.neg result)
      (Cache.neg child.completed child.enclosing child.cache) (child.enclosing.negFromBall_eq ball same).symm
  ⟨child.completed.neg, enclosing, cache⟩

/-- The original negation realization consumes exactly its retained supplied common ball. -/
theorem negFromBall_ball {input : Expr arity} (child : Realization environment input)
    (ball : Ball) (same : ball = child.enclosing.ball.neg) :
    (child.negFromBall ball same).enclosing.ball = ball := child.enclosing.negFromBall_ball ball same

/-- Apply original conjugation with its retained exact common ball and the same original child cache. -/
@[expose] def conjFromBall {input : Expr arity} (child : Realization environment input)
    (ball : Ball) (same : ball = child.enclosing.ball.conj) : Realization environment (.conj input) :=
  let enclosing := child.enclosing.conjFromBall ball same
  let cache : Cache child.completed.conj enclosing :=
    Eq.ndrec (motive := fun result => Cache child.completed.conj result)
      (Cache.conj child.completed child.enclosing child.cache) (child.enclosing.conjFromBall_eq ball same).symm
  ⟨child.completed.conj, enclosing, cache⟩

/-- The original conjugation realization consumes exactly its retained supplied common ball. -/
theorem conjFromBall_ball {input : Expr arity} (child : Realization environment input)
    (ball : Ball) (same : ball = child.enclosing.ball.conj) :
    (child.conjFromBall ball same).enclosing.ball = ball := child.enclosing.conjFromBall_ball ball same

/-- Apply original ordered add arithmetic using its retained common ball and both original child caches. -/
@[expose] def addFromBall {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.add second.enclosing.ball) :
    Realization environment (.add left right) :=
  let enclosing := first.enclosing.addFromBall second.enclosing ball same
  let cache : Cache (first.completed.add second.completed) enclosing :=
    Eq.ndrec (motive := fun result => Cache (first.completed.add second.completed) result)
      (Cache.add first.completed second.completed first.enclosing second.enclosing first.cache second.cache)
      (first.enclosing.addFromBall_eq second.enclosing ball same).symm
  ⟨first.completed.add second.completed, enclosing, cache⟩

/-- Original ordered add consumes exactly the supplied common ball. -/
theorem addFromBall_ball {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.add second.enclosing.ball) :
    (first.addFromBall second ball same).enclosing.ball = ball :=
  first.enclosing.addFromBall_ball second.enclosing ball same

/-- Apply original ordered sub arithmetic using its retained common ball and both original child caches. -/
@[expose] def subFromBall {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.sub second.enclosing.ball) :
    Realization environment (.sub left right) :=
  let enclosing := first.enclosing.subFromBall second.enclosing ball same
  let cache : Cache (first.completed.sub second.completed) enclosing :=
    Eq.ndrec (motive := fun result => Cache (first.completed.sub second.completed) result)
      (Cache.sub first.completed second.completed first.enclosing second.enclosing first.cache second.cache)
      (first.enclosing.subFromBall_eq second.enclosing ball same).symm
  ⟨first.completed.sub second.completed, enclosing, cache⟩

/-- Original ordered sub consumes exactly the supplied common ball. -/
theorem subFromBall_ball {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.sub second.enclosing.ball) :
    (first.subFromBall second ball same).enclosing.ball = ball :=
  first.enclosing.subFromBall_ball second.enclosing ball same

/-- Apply original ordered mul arithmetic using its retained common ball and both original child caches. -/
@[expose] def mulFromBall {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.mul second.enclosing.ball) :
    Realization environment (.mul left right) :=
  let enclosing := first.enclosing.mulFromBall second.enclosing ball same
  let cache : Cache (first.completed.mul second.completed) enclosing :=
    Eq.ndrec (motive := fun result => Cache (first.completed.mul second.completed) result)
      (Cache.mul first.completed second.completed first.enclosing second.enclosing first.cache second.cache)
      (first.enclosing.mulFromBall_eq second.enclosing ball same).symm
  ⟨first.completed.mul second.completed, enclosing, cache⟩

/-- Original ordered mul consumes exactly the supplied common ball. -/
theorem mulFromBall_ball {left right : Expr arity} (first : Realization environment left)
    (second : Realization environment right) (ball : Ball)
    (same : ball = first.enclosing.ball.mul second.enclosing.ball) :
    (first.mulFromBall second ball same).enclosing.ball = ball :=
  first.enclosing.mulFromBall_ball second.enclosing ball same

/-- Apply the original natural power using the retained common ball and every original child obligation. -/
@[expose] def powFromBall {input : Expr arity} (child : Realization environment input) (exponent : Nat)
    (ball : Ball) (same : ball = child.enclosing.ball.pow exponent) : Realization environment (.pow input exponent) :=
  let enclosing := child.enclosing.powFromBall exponent ball same
  let cache : Cache (child.completed.pow exponent) enclosing :=
    Eq.ndrec (motive := fun result => Cache (child.completed.pow exponent) result)
      (Cache.pow child.completed child.enclosing child.cache exponent)
      (child.enclosing.powFromBall_eq exponent ball same).symm
  ⟨child.completed.pow exponent, enclosing, cache⟩

/-- Original natural power consumes its actual supplied common bound. -/
theorem powFromBall_ball {input : Expr arity} (child : Realization environment input) (exponent : Nat)
    (ball : Ball) (same : ball = child.enclosing.ball.pow exponent) :
    (child.powFromBall exponent ball same).enclosing.ball = ball :=
  child.enclosing.powFromBall_ball exponent ball same

/-- Pay the original reciprocal once while consuming its retained exact common division bound. -/
@[expose] def inverseFromBall {input : Expr arity} (child : Realization environment input)
    (apart : Ball.Apart child.enclosing.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div child.enclosing.ball apart) : Realization environment (.inverse input) :=
  let inverse := prepareInverse child.completed child.enclosing apart
  let enclosing := (child.enclosing.inverseFromBall inverse.paid.prepared apart ball same).cast inverse.channel.symm
  have enclosureEq : enclosing = (child.enclosing.inverse inverse.paid.prepared apart).cast inverse.channel.symm :=
    congrArg (fun original => original.cast inverse.channel.symm)
      (child.enclosing.inverseFromBall_eq inverse.paid.prepared apart ball same)
  let cache : Cache inverse.completed enclosing := enclosureEq.symm ▸
    Cache.inverse child.completed child.enclosing child.cache apart inverse rfl
  ⟨inverse.completed, enclosing, cache⟩

/-- The original paid reciprocal realization retains exactly the supplied common division ball. -/
theorem inverseFromBall_ball {input : Expr arity} (child : Realization environment input)
    (apart : Ball.Apart child.enclosing.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div child.enclosing.ball apart) :
    (child.inverseFromBall apart ball same).enclosing.ball = ball := by
  unfold inverseFromBall
  rewrite [Enclosure.cast_ball, Enclosure.inverseFromBall_ball]
  rfl

end Realization

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric

end
