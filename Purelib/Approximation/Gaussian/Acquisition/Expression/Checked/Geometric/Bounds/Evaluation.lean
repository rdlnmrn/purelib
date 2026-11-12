module
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds.Realization
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)

variable {arity : Nat} {environment : Fin arity → Annotated} {leafBalls : Basic.Leaf arity → Ball}

/-- An unresolved original geometric outcome retaining its existing exact-zero or finite-request owner. -/
private abbrev Unresolved (environment : Fin arity → Annotated) (expression : Expr arity) :=
  Geometric.Invalid environment expression ⊕ Geometric.Request environment expression

/-- Retain an original numerical context around the same exact unresolved geometric owner. -/
private def Unresolved.through {input output : Expr arity} (frame : Geometric.Frame environment input output) :
    Unresolved environment input → Unresolved environment output
  | .inl invalid => .inl (.through frame invalid)
  | .inr request => .inr (.through frame request)

/-- Read the original exact-zero or nonzero decision at one actual insufficient common denominator bound. -/
private def Failure.specialize (failure : Failure leafBalls)
    (admitted : Admitted environment failure.input) (inputs : Inputs leafBalls admitted) :
    Unresolved environment (.inverse failure.input) :=
  let actual := failure.child.realize (leafBalls := leafBalls) admitted inputs
  let resolution := Geometric.resolve actual.value.completed
  have insufficient : ¬ Purelib.Approximation.Gaussian.Geometric.Preparation.Separated
      actual.value.enclosing.ball := fun separated => failure.failed (actual.common_ball ▸ separated)
  match decided : resolution.decision with
  | .prepared prepared => .inr (.clearance actual.value insufficient resolution prepared decided)
  | .excluded zero => .inl (.inverse actual.value resolution zero decided)

set_option genInjectivity false in
/-- A genuine used-geometry receipt retaining the complete original admission object. -/
structure Input {expression : Expr arity} (leafBalls : Basic.Leaf arity → Ball)
    (admitted : Admitted environment expression) where
  /-- The same actual original admission tree remains physically retained. -/
  original : Admitted environment expression
  /-- The retained admission is the complete original parent. -/
  original_eq : original = admitted
  /-- Its genuine used-leaf geometry has the same original common bounds. -/
  geometry : Inputs leafBalls admitted

constructive_injectivity Input

/-- Retain an actual original admission and its genuine used-leaf geometry without rebuilding either. -/
@[expose] def Input.retain {expression : Expr arity} (admitted : Admitted environment expression)
    (geometry : Inputs leafBalls admitted) : Input leafBalls admitted := ⟨admitted, rfl, geometry⟩

/-- Preserve the original unvisited right admission and geometry around the same left-side condition. -/
private def Unresolved.left (operation : Binary) {left right : Expr arity}
    (second : Admitted environment right) (inputs : Inputs leafBalls second)
    (pending : Unresolved environment left) : Unresolved environment (operation.expression left right) :=
  let geometry := Inputs.geometry (leafBalls := leafBalls) (admitted := second) inputs
  Unresolved.through (Geometric.Frame.left operation left right second geometry) pending

/-- Consume the retained original left common programme and preserve its numerical cache around a right condition. -/
private def Unresolved.right (operation : Binary) {left right : Expr arity}
    (common : Common leafBalls left) (first : Admitted environment left) (inputs : Inputs leafBalls first)
    (pending : Unresolved environment right) : Unresolved environment (operation.expression left right) :=
  let actual := common.realize (leafBalls := leafBalls) first inputs
  Unresolved.through (Geometric.Frame.right operation left actual.value right) pending

/-- Specialize the first computed insufficient common bound at genuine original numerical inputs.

The positive prefix consumes its retained common programmes once. The actual
original algebraic decision then distinguishes operational zero from finite
spatial inconclusivity. No failed ball test is promoted to a geometric pole.
-/
private def specializeRequest : {expression : Expr arity} → (admitted : Admitted environment expression) →
    (request : Request leafBalls expression) → Input leafBalls admitted → Unresolved environment expression
  | _, .base _ _, request, _ => nomatch request
  | _, .inverse (input := expression) admitted, request, inputs =>
      match request with
      | .inverse common failed =>
          Failure.specialize (leafBalls := leafBalls) ⟨_, common, failed⟩ admitted inputs.geometry
      | .outerInverse first =>
          let pending := specializeRequest admitted first
            (Input.retain (leafBalls := leafBalls) admitted inputs.geometry)
          Unresolved.through (Geometric.Frame.inverse expression) pending
  | _, .unary .neg (input := expression) admitted, request, inputs =>
      match request with
      | .neg first =>
          let pending := specializeRequest admitted first
            (Input.retain (leafBalls := leafBalls) admitted inputs.geometry)
          Unresolved.through (Geometric.Frame.unary .neg expression) pending
  | _, .unary (.pow exponent) (input := expression) admitted, request, inputs =>
      match request with
      | .pow _ first =>
          let pending := specializeRequest admitted first
            (Input.retain (leafBalls := leafBalls) admitted inputs.geometry)
          Unresolved.through (Geometric.Frame.unary (.pow exponent) expression) pending
  | _, .unary .conj (input := expression) admitted, request, inputs =>
      match request with
      | .conj first =>
          let pending := specializeRequest admitted first
            (Input.retain (leafBalls := leafBalls) admitted inputs.geometry)
          Unresolved.through (Geometric.Frame.unary .conj expression) pending
  | _, .binary .add admittedFirst admittedSecond, request, inputs =>
      match request with
      | .addLeft _ first =>
          let pending := specializeRequest admittedFirst first
            (Input.retain (leafBalls := leafBalls) admittedFirst inputs.geometry.1)
          Unresolved.left (leafBalls := leafBalls) .add admittedSecond inputs.geometry.2 pending
      | .addRight common remaining =>
          let pending := specializeRequest admittedSecond remaining
            (Input.retain (leafBalls := leafBalls) admittedSecond inputs.geometry.2)
          Unresolved.right (leafBalls := leafBalls) .add common admittedFirst inputs.geometry.1 pending
  | _, .binary .sub admittedFirst admittedSecond, request, inputs =>
      match request with
      | .subLeft _ first =>
          let pending := specializeRequest admittedFirst first
            (Input.retain (leafBalls := leafBalls) admittedFirst inputs.geometry.1)
          Unresolved.left (leafBalls := leafBalls) .sub admittedSecond inputs.geometry.2 pending
      | .subRight common remaining =>
          let pending := specializeRequest admittedSecond remaining
            (Input.retain (leafBalls := leafBalls) admittedSecond inputs.geometry.2)
          Unresolved.right (leafBalls := leafBalls) .sub common admittedFirst inputs.geometry.1 pending
  | _, .binary .mul admittedFirst admittedSecond, request, inputs =>
      match request with
      | .mulLeft _ first =>
          let pending := specializeRequest admittedFirst first
            (Input.retain (leafBalls := leafBalls) admittedFirst inputs.geometry.1)
          Unresolved.left (leafBalls := leafBalls) .mul admittedSecond inputs.geometry.2 pending
      | .mulRight common remaining =>
          let pending := specializeRequest admittedSecond remaining
            (Input.retain (leafBalls := leafBalls) admittedSecond inputs.geometry.2)
          Unresolved.right (leafBalls := leafBalls) .mul common admittedFirst inputs.geometry.1 pending

/-- Project actual original numerical certificates while retaining their parent in the enclosing specialization. -/
private def Outcome.project {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (inputs : Input leafBalls admitted) :
    Geometric.Outcome environment expression :=
  match outcome with
  | .prepared common => .completed (common.realize (leafBalls := leafBalls) admitted inputs.geometry).value
  | .requested remaining =>
      match specializeRequest (leafBalls := leafBalls) admitted remaining inputs with
      | .inl invalid => .invalid invalid
      | .inr request => .requested request

/-- The result is exactly the original numerical procedure on the same retained programme and used geometry.

This owned equality certificate keeps the executable implementation private.
It refers to the actual original source inputs and complete result, rather
than an arbitrary successful flag or scalar channel agreement.
-/
def Computed {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted)
    (result : Geometric.Outcome environment expression) : Prop :=
  result = outcome.project admitted (Input.retain (leafBalls := leafBalls) admitted geometry)

/-- Two certificates for the same original computation identify the same complete original numerical outcome. -/
theorem Computed.deterministic {expression : Expr arity} {outcome : Outcome leafBalls expression}
    {admitted : Admitted environment expression} {geometry : Inputs leafBalls admitted}
    {first second : Geometric.Outcome environment expression}
    (firstComputed : Computed outcome admitted geometry first)
    (secondComputed : Computed outcome admitted geometry second) : first = second :=
  firstComputed.trans secondComputed.symm

set_option genInjectivity false in
/-- An actual numerical specialization retaining its complete original bound result and admission receipt.

The existing geometric outcome holds its original arithmetic, exact-zero or
finite-request certificates. The whole bound programme and its original parent
identity remain beside it, including successful prefixes and unvisited syntax.
-/
structure Specialization {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) where
  /-- The actual complete original common programme or finite spatial request is retained. -/
  bounds : Outcome leafBalls expression
  /-- The retained result is exactly this same original bound parent. -/
  bounds_eq : bounds = outcome
  /-- The complete original admission and genuine used geometry remain physically retained. -/
  input : Input leafBalls admitted
  /-- The actual original numerical success, exact-zero obstruction or finite geometric request. -/
  result : Geometric.Outcome environment expression
  /-- The retained result is the actual once computed original procedure on those same parents. -/
  computed : Computed bounds admitted input.geometry result

constructive_injectivity Specialization

/-- A completed retained specialization has the exact ball of its positive original common programme.

The computation certificate identifies the actual stored output with the
realization on its retained geometry. This readback applies to that output
without executing another realization or replacing its original inputs.
-/
theorem Specialization.completed_ball {expression : Expr arity}
    {outcome : Outcome leafBalls expression} {admitted : Admitted environment expression}
    (actual : Specialization outcome admitted) {common : Common leafBalls expression}
    (positive : outcome = .prepared common) {value : Geometric.Realization environment expression}
    (completed : actual.result = .completed value) : value.enclosing.ball = common.ball := by
  cases positive
  have computed : Computed (.prepared common) admitted actual.input.geometry actual.result :=
    Eq.ndrec (motive := fun outcome => Computed outcome admitted actual.input.geometry actual.result)
      actual.computed actual.bounds_eq
  have result : actual.result = .completed (common.realize admitted actual.input.geometry).value := computed
  have values := Geometric.Outcome.completed.inj (completed.symm.trans result)
  exact (congrArg (fun value => value.enclosing.ball) values).trans
    (common.realize admitted actual.input.geometry).common_ball

/-- Consume the actual retained structural result on genuine original inputs and keep both complete parents. -/
def Outcome.specialize {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    Specialization outcome admitted :=
  let input := Input.retain (leafBalls := leafBalls) admitted geometry
  let result := outcome.project admitted input
  ⟨outcome, rfl, input, result, rfl⟩

/-- Specialization retains the complete same original common programme or request. -/
theorem Outcome.specialize_bounds {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    (outcome.specialize admitted geometry).bounds = outcome :=
  (outcome.specialize admitted geometry).bounds_eq

/-- Specialization physically retains the same complete original admission tree. -/
theorem Outcome.specialize_original {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    (outcome.specialize admitted geometry).input.original = admitted :=
  (outcome.specialize admitted geometry).input.original_eq

/-- The specialization's cached result is certified by the original exact computation owner. -/
theorem Outcome.specialize_computed {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    Computed outcome admitted geometry (outcome.specialize admitted geometry).result := by
  exact (outcome.specialize admitted geometry).computed

/-- The actual specialization retains its complete supplied used-geometry object unchanged. -/
private theorem specialize_geometry_readback {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    (outcome.specialize admitted geometry).input.geometry = geometry := rfl

/-- The actual specialization retains its same supplied used-geometry object. -/
theorem Outcome.specialize_geometry {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    (outcome.specialize admitted geometry).input.geometry = geometry :=
  specialize_geometry_readback outcome admitted geometry

/-- The retained positive factory result is the same complete cached original realization. -/
private theorem specialize_prepared_readback {expression : Expr arity} (common : Common leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    ((Outcome.prepared common).specialize admitted geometry).result =
      .completed (common.realize admitted geometry).value := rfl

/-- A positive retained programme specializes to its actual cached original realization. -/
theorem Outcome.specialize_prepared {expression : Expr arity} (common : Common leafBalls expression)
    (admitted : Admitted environment expression) (geometry : Inputs leafBalls admitted) :
    ((Outcome.prepared common).specialize admitted geometry).result =
      .completed (common.realize admitted geometry).value :=
  specialize_prepared_readback common admitted geometry

set_option genInjectivity false in
/-- The original bound programme and admission whose genuine used-leaf geometry has not been supplied. -/
structure Missing {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) where
  /-- The same complete computed programme and every unresolved bound occurrence remain retained. -/
  bounds : Outcome leafBalls expression
  /-- The retained programme is the original supplied parent. -/
  bounds_eq : bounds = outcome
  /-- The same original complete admission is retained for filling its actual geometric contract. -/
  original : Admitted environment expression
  /-- The retained admission is exactly the original parent. -/
  original_eq : original = admitted
  /-- The exact offered used-geometry contract of this finite attempt. -/
  offered : Option (Inputs leafBalls original)
  /-- This attempt had no supplied used-geometry contract. -/
  unavailable : offered = none

constructive_injectivity Missing

/-- Fill genuine used geometry while consuming the exact original bound programme and admission already retained. -/
def Missing.resume {expression : Expr arity} {outcome : Outcome leafBalls expression}
    {admitted : Admitted environment expression} (missing : Missing outcome admitted)
    (geometry : Inputs leafBalls missing.original) : Specialization missing.bounds missing.original :=
  missing.bounds.specialize missing.original geometry

set_option genInjectivity false in
/-- An actual retained numerical specialization or the same original fillable used-geometry obligation. -/
inductive Attempt {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) where
  /-- Genuine used geometry produced actual original numerical certificates. -/
  | specialized (actual : Specialization outcome admitted)
  /-- The original admission and computed programme await their genuine used-geometry contract. -/
  | missing (request : Missing outcome admitted)

constructive_injectivity Attempt

/-- Consume an actual computed bound result with optional genuine geometry, retaining every original parent. -/
def Outcome.prepare {expression : Expr arity} (outcome : Outcome leafBalls expression)
    (admitted : Admitted environment expression) (offered : Option (Inputs leafBalls admitted)) :
    Attempt outcome admitted :=
  match offered with
  | none => .missing ⟨outcome, rfl, admitted, rfl, none, rfl⟩
  | some geometry => .specialized (outcome.specialize admitted geometry)

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds
end
