module

import Purelib.System.IO

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Evaluation
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Field

namespace TestPurelib.Approximation.Gaussian.CheckedGeometric

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic (Canonical)

section

variable {arity : Nat} {environment : Fin arity → Annotated} {input : Checked.Expr arity}

/-- Conjugation and zero power preserve the complete first obstructed denominator and its actual decision. -/
example (obstruction : Checked.Geometric.Invalid environment input) :
    (Checked.Geometric.Invalid.through (.unary (.pow 0) (.conj input))
      (.through (.unary .conj input) obstruction)).denominator = obstruction.denominator := rfl

/-- Nested unary contexts preserve the complete first missing original compiler and used geometry obligation. -/
example (request : Checked.Geometric.Request environment input) :
    (Checked.Geometric.Request.through (.unary (.pow 0) (.conj input))
      (.through (.unary .conj input) request)).base? = request.base? := rfl

/-- A suspended ordered product retains the full original geometric left sibling and its checked parent. -/
example {left right : Checked.Expr arity} (first : Checked.Geometric.Realization environment left) :
    (Checked.Geometric.Frame.right .mul left first right).completed = some ⟨left, first⟩ ∧
      (Checked.Geometric.Frame.right .mul left first right).original =
        Checked.Frame.right .mul first.completed.toResult right := ⟨rfl, rfl⟩

end

/-- The actual bounded original atom position used by these finite clients. -/
private def index : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩

/-- Read the actual original compiler sizes and bounded occurrence receipts retained at spatial base nodes. -/
private def basePositions {arity : Nat} {environment : Fin arity → Annotated} {expression : Checked.Expr arity}
    {completed : Checked.Completed environment expression} {enclosing : Enclosure completed.channel} :
    Checked.Geometric.Cache completed enclosing → List (Nat × List Nat)
  | .base cached _ _ basic _ => [(cached.compiled.bindings.length, basic.enclosed.cache.positions)]
  | .neg _ _ child | .pow _ _ child _ | .conj _ _ child | .refined _ _ child _ _ => basePositions child
  | .add _ _ _ _ first second | .sub _ _ _ _ first second | .mul _ _ _ _ first second =>
      basePositions first ++ basePositions second
  | .inverse _ _ child _ _ _ | .resumedInverse _ _ child _ _ _ _ _ _ _ _ => basePositions child

/-- Read original denominator samples from the actual retained inverse children, without rebuilding their programs. -/
private def inverseChildren {arity : Nat} {environment : Fin arity → Annotated} {expression : Checked.Expr arity}
    {completed : Checked.Completed environment expression} {enclosing : Enclosure completed.channel} :
    Checked.Geometric.Cache completed enclosing → List Canonical
  | .base .. => []
  | .neg _ _ child | .pow _ _ child _ | .conj _ _ child | .refined _ _ child _ _ => inverseChildren child
  | .add _ _ _ _ first second | .sub _ _ _ _ first second | .mul _ _ _ _ first second =>
      inverseChildren first ++ inverseChildren second
  | .inverse child _ cache _ _ _ | .resumedInverse child _ cache _ _ _ _ _ _ _ _ =>
      child.sidecar.residual.source.sample 0 :: inverseChildren cache

/-- Read each retained original power child beside its formal source and exponent. -/
private def powerChildren {arity : Nat} {environment : Fin arity → Annotated} {expression : Checked.Expr arity}
    {completed : Checked.Completed environment expression} {enclosing : Enclosure completed.channel} :
    Checked.Geometric.Cache completed enclosing → List (Nat × Canonical × Canonical)
  | .base .. => []
  | .neg _ _ child | .conj _ _ child | .refined _ _ child _ _ => powerChildren child
  | .pow child original cache exponent =>
      (exponent, child.sidecar.residual.source.sample 0, original.source.sample 0) :: powerChildren cache
  | .add _ _ _ _ first second | .sub _ _ _ _ first second | .mul _ _ _ _ first second =>
      powerChildren first ++ powerChildren second
  | .inverse _ _ child _ _ _ | .resumedInverse _ _ child _ _ _ _ _ _ _ _ => powerChildren child

/-- Check first-domain order and nonreal reciprocal arithmetic through the original spatial interpreter. -/
public def check : IO Unit := do
  let value : Canonical := ⟨3, 4⟩
  let environment : Fin 1 → Annotated := fun _ => Annotated.rational value
  let zero := Checked.Admitted.rational environment 0
  let first := Checked.Admitted.rational environment value
  let geometry := Checked.Geometric.Geometry.rational environment value
  let original := Checked.Geometric.run (first.add (zero.inverse.pow 0))
    ⟨geometry, Checked.Geometric.Geometry.rational environment 0⟩
  match original with
  | .invalid obstruction =>
      let ⟨_, child, resolution, _⟩ := obstruction.denominator
      unless child.enclosing.source.sample 0 == 0 && obstruction.prefix.length == 1 do
        throw (IO.userError "Zero power changed the first original inverse occurrence or completed prefix")
      match obstruction.prefix with
      | ⟨_, left⟩ :: [] =>
          unless left.enclosing.source.sample 0 == value do
            throw (IO.userError "The first zero inverse lost its original completed nonreal left sibling")
      | _ => throw (IO.userError "The first zero inverse changed its original ordered prefix")
      match resolution.decision with
      | .excluded _ => pure ()
      | .prepared _ => throw (IO.userError "The original zero inverse lost its actual exclusion decision")
  | _ => throw (IO.userError "Zero power erased an actual original inverse domain obstruction")
  let admitted := Checked.Admitted.atom environment index (Algebraic.Sidecar.ofRational (RationalSidecar.exact value))
  let offered := Checked.Geometric.Geometry.atom environment index
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact value)) (Enclosure.exact value)
  match Checked.Geometric.run (admitted.inverse.conj.pow 2) offered with
  | .completed result =>
      unless result.enclosing.source.sample 0 == (⟨-7 / 625, 24 / 625⟩ : Canonical) do
        throw (IO.userError "The original nonreal reciprocal, conjugation and power changed their formal reading")
      unless inverseChildren result.cache == [value] &&
          (powerChildren result.cache).map Prod.fst == [2] do
        throw (IO.userError "The nonreal inverse arithmetic lost its actual original child/domain caches")
  | _ => throw (IO.userError "The computed original nonreal inverse domain did not complete")
  Purelib.System.IO.println
    "Checked geometric domains: original right zero occurrence and nonreal inverse caches retained"

/-- Check an actual original cubic admission, its formal power and a suspended same-owner geometry retry.

The supplied sidecar and enclosure authenticate the same original annotation.
The client reads only its initial primitive sample; no root producer or deep
numerical request is invoked. Missing geometry retains this exact original
compilation, and retry consumes its already completed original left sibling.
-/
public def checkCubic (annotation : Annotated) (sidecar : Algebraic.Sidecar annotation.channel)
    (enclosing : Enclosure annotation.channel) : IO Unit := do
  let environment : Fin 1 → Annotated := fun _ => annotation
  let compiled : Basic.Compiled environment (.atom index) := ⟨annotation, .atom index annotation rfl⟩
  let cached : Checked.Base.Cached environment (.atom index) := ⟨compiled, (some sidecar, PUnit.unit), none, PUnit.unit⟩
  let admissions : Checked.Base.Admissions cached.compiled.bindings := ⟨sidecar, PUnit.unit⟩
  let admitted := Checked.Admitted.base cached admissions
  have admitted_eq : admitted = Checked.Admitted.atom environment index sidecar := rfl
  let leafGeometry : cached.compiled.Geometry :=
    ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl, enclosing⟩
  let geometry : Checked.Geometric.Geometry admitted := some leafGeometry
  let sample := enclosing.source.sample 0
  match Checked.Geometric.run (admitted.pow 3) geometry with
  | .completed result =>
      let exact := result.completed.sidecar.scalar?
      if available : exact.isSome then
        let reading := exact.get available
        unless reading.value == 2 && result.enclosing.source.sample 0 == sample ^ 3 && sample ^ 3 != reading.value do
          throw (IO.userError "The original cubic formal sample was replaced by its optimized exact power reading")
      else throw (IO.userError "The original cubic retained power equation was not consumed")
      unless basePositions result.cache == [(1, [0])] &&
          powerChildren result.cache == [(3, sidecar.residual.source.sample 0, sample)] do
        throw (IO.userError "The original cubic power lost its bounded leaf, compiler or actual child caches")
  | _ => throw (IO.userError "The actual admitted cubic power failed to complete")
  let first := Checked.Geometric.Realization.base cached admissions leafGeometry
  let base : Checked.Geometric.BaseRequest environment (.atom index) :=
    ⟨cached, admissions, admitted, rfl, none, rfl⟩
  let pending := Checked.Geometric.Request.through
    (.right .add (Checked.Expr.atom index) first (.pow (.conj (Checked.Expr.atom index)) 0))
    (.through (.unary (.pow 0) (.conj (Checked.Expr.atom index)))
      (.through (.unary .conj (Checked.Expr.atom index)) (.base base)))
  let actual := Checked.Geometric.run (admitted.add (admitted.conj.pow 0)) ⟨geometry, none⟩
  have actual_eq : actual = .requested pending := rfl
  match observed : actual with
  | .requested request =>
      unless request.prefix.length == 1 do
        throw (IO.userError "Missing cubic right geometry discarded its original completed left prefix")
      match request.base? with
      | some ⟨_, original⟩ =>
          unless original.compiled.bindings.length == 1 && original.offered.isNone do
            throw (IO.userError "Missing cubic geometry changed its actual compiler or offered contract")
      | none => throw (IO.userError "Missing cubic geometry lost its exact original used-leaf obligation")
      match request.prefix with
      | ⟨_, left⟩ :: [] =>
          unless left.enclosing.source.sample 0 == sample do
            throw (IO.userError "Missing cubic geometry changed its original completed left observation")
      | _ => throw (IO.userError "Missing cubic geometry changed its original prefix order")
      have request_eq : request = pending :=
        Checked.Geometric.Outcome.requested.inj (observed.symm.trans actual_eq)
      let supplied : request.Fill := request_eq.symm ▸ leafGeometry
      match request.resume supplied with
      | .completed result =>
          unless result.enclosing.source.sample 0 == sample + 1 &&
              basePositions result.cache == [(1, [0]), (1, [0])] &&
              powerChildren result.cache ==
                [(0, (sidecar.residual.source.sample 0).conj, sample.conj)] do
            throw (IO.userError "The same cubic retry lost its actual compiler, child or domain cache")
      | _ => throw (IO.userError "The exact original cubic geometry request failed to resume")
  | _ => throw (IO.userError "Missing cubic geometry was silently completed or excluded")
  let _ := admitted_eq
  Purelib.System.IO.println
    "Checked cubic geometry: original compiler, formal cube and same-request cached retry retained"

end TestPurelib.Approximation.Gaussian.CheckedGeometric
