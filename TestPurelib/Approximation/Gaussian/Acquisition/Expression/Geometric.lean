module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Evaluation
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.System.IO

namespace TestPurelib.Approximation.Gaussian.Acquisition.Expression.Geometric

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Enclosure (Ball)

section

variable {arity : Nat} {environment : Fin arity → Annotated} {input : Checked.Expr arity}

/-- Zero exponent cannot erase an actual original inverse obstruction. -/
example (obstruction : Checked.Geometric.Invalid environment input) :
    (Checked.Geometric.Outcome.invalid obstruction).unary (.pow 0) =
      .invalid (.through (.unary (.pow 0) input) obstruction) :=
  Checked.Geometric.Outcome.pow_zero_invalid obstruction

/-- A missing original geometry request survives zero exponent with the same actual unvisited input. -/
example (request : Checked.Geometric.Request environment input) :
    (Checked.Geometric.Outcome.requested request).unary (.pow 0) =
      .requested (.through (.unary (.pow 0) input) request) :=
  Checked.Geometric.Outcome.pow_zero_requested request

/-- A suspended right child retains and consumes the exact original completed geometric left sibling. -/
example (operation : Checked.Binary) {left right : Checked.Expr arity}
    (first : Checked.Geometric.Realization environment left)
    (second : Checked.Geometric.Realization environment right) :
    (Checked.Geometric.Frame.right operation left first right).resume (.completed second) =
      .completed (first.binary operation second) :=
  Checked.Geometric.Frame.right_completed operation first second

end

/-- The same bounded numerical environment supplies the original exact atom in the native regression. -/
private def environment : Fin 1 → Annotated := fun _ => Annotated.rational 3

/-- The original atom's actual bounded index. -/
private def index : Fin 1 := ⟨0, by decide +kernel⟩

/-- The original same-channel admission remains separate from its formal spatial sample program. -/
private def sidecar := Algebraic.Sidecar.ofRational (RationalSidecar.exact 3)

/-- One actual retained total compilation of the original numerical atom. -/
private def atomCache := Checked.Base.Cached.ofExpression environment (.atom index)

/-- The original singleton compilation has its actual same-channel intrinsic admission. -/
private def atomAdmissions : Checked.Base.Admissions atomCache.compiled.bindings := ⟨sidecar, PUnit.unit⟩

/-- The actual original bounded leaf geometry is supplied at its authenticated occurrence. -/
private def atomGeometry : atomCache.compiled.Geometry :=
  ⟨⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩, rfl, Enclosure.exact 3⟩

/-- The same original constant program has a valid coarse ball that contains zero. -/
private def coarse : Enclosure (environment index).channel where
  source := (Enclosure.exact 3).source
  equivalent := (Enclosure.exact 3).equivalent
  ball := ⟨0, 9, by decide +kernel⟩
  contains := fun stage => by
    rewrite [Enclosure.exact_sample]
    change Purelib.Data.Gaussian.Norm.Basic.normSq ((3 : Canonical) - 0) ≤ 9
    decide +kernel

/-- The coarse ball concerns the exact same original bounded atom occurrence. -/
private def coarseGeometry : atomCache.compiled.Geometry :=
  ⟨⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩, rfl, coarse⟩

/-- One actual original total compilation of exact two. -/
private def constantCache := Checked.Base.Cached.ofExpression environment (.rational 2)

/-- Check exact-zero order, positive inverse arithmetic, and fillable original cache retention. -/
public def check : IO Unit := do
  let zero := Checked.Admitted.rational environment 0
  let invalid := Checked.Geometric.run (zero.inverse.pow 0) (Checked.Geometric.Geometry.rational environment 0)
  match invalid with
  | .invalid obstruction =>
      let ⟨_, child, resolution, _⟩ := obstruction.denominator
      unless child.enclosing.source.sample 0 == 0 do
        throw (IO.userError "The zero-power obstruction lost its actual original denominator")
      match resolution.decision with
      | .excluded _ => pure ()
      | .prepared _ => throw (IO.userError "The exact-zero obstruction lost its actual cached decision")
  | _ => throw (IO.userError "Exponent zero erased the original inverse-zero domain obstruction")
  let atom := Checked.Admitted.atom environment index sidecar
  let geometry := Checked.Geometric.Geometry.atom environment index sidecar (Enclosure.exact 3)
  match Checked.Geometric.run (atom.inverse.conj.pow 2) geometry with
  | .completed result =>
      unless result.enclosing.source.sample 0 == (1 : Canonical) / 9 do
        throw (IO.userError "The formal inverse/conjugate/power arithmetic changed its original value")
  | _ => throw (IO.userError "The positive original inverse arithmetic failed to complete")
  let first := Checked.Geometric.Realization.base constantCache PUnit.unit ()
  let base : Checked.Geometric.BaseRequest environment (.atom index) :=
    ⟨atomCache, atomAdmissions, .base atomCache atomAdmissions, rfl, none, rfl⟩
  let pending := Checked.Geometric.Request.through
    (.right .add (.rational 2) first (.atom index)) (.base base)
  let actual := Checked.Geometric.run
    ((Checked.Admitted.base constantCache PUnit.unit).add (.base atomCache atomAdmissions)) ⟨some (), none⟩
  have actual_eq : actual = .requested pending := rfl
  match actual with
  | .requested request =>
      unless request.prefix.length == 1 do
        throw (IO.userError "The missing original right geometry discarded its completed left prefix")
      match request.base? with
      | some ⟨_, original⟩ =>
          unless original.compiled.bindings.length == 1 && original.offered.isNone do
            throw (IO.userError "The missing original used-leaf geometry changed its retained obligation")
      | none => throw (IO.userError "The missing original base contract disappeared")
  | _ => throw (IO.userError "The absent original right geometry did not produce a typed request")
  match pending.resume atomGeometry with
  | .completed result =>
      unless result.enclosing.source.sample 0 == 5 do
        throw (IO.userError "Filling original right geometry failed to reuse the completed left sibling")
  | _ => throw (IO.userError "The same original geometry request failed to resume")
  let coarseChild := Checked.Geometric.Realization.base atomCache atomAdmissions coarseGeometry
  let preciseChild := Checked.Geometric.Realization.base atomCache atomAdmissions atomGeometry
  have coarse_ball : coarseChild.enclosing.ball = coarse.ball := Enclosure.cast_ball coarse _
  have precise_ball : preciseChild.enclosing.ball = Ball.point 3 :=
    (Enclosure.cast_ball (Enclosure.exact 3) _).trans (Enclosure.exact_ball 3)
  have same_source : preciseChild.enclosing.source = coarseChild.enclosing.source :=
    (Enclosure.cast_source (Enclosure.exact 3) _).trans (Enclosure.cast_source coarse _).symm
  match Checked.Geometric.Outcome.inverse (.completed coarseChild) with
  | .requested _ => pure ()
  | _ => throw (IO.userError "A coarse nonzero enclosure was mistaken for path clearance or a pole")
  let resolution := Checked.Geometric.resolve coarseChild.completed
  match decided : resolution.decision with
  | .excluded _ => throw (IO.userError "The retained original exact three was incorrectly excluded")
  | .prepared prepared =>
      let request := Checked.Geometric.Request.clearance coarseChild
        (by rewrite [coarse_ball]; decide +kernel)
        resolution prepared decided
      let filled : Checked.Geometric.ClearanceFill coarseChild :=
        ⟨preciseChild.enclosing, same_source,
          Purelib.Approximation.Gaussian.Enclosure.Residual.apartOfCenter preciseChild.enclosing.ball
            (by rewrite [precise_ball]; decide +kernel)⟩
      match request.resume filled with
      | .completed result =>
          unless result.enclosing.source.sample 0 == (1 : Canonical) / 3 do
            throw (IO.userError "The same-program spatial refinement lost the original reciprocal value")
      | _ => throw (IO.userError "The refined original clearance failed to reuse its cached decision")
  Purelib.System.IO.println
    "Checked spatial expressions: original inverse-zero order, arithmetic and cached geometry retry passed"

end TestPurelib.Approximation.Gaussian.Acquisition.Expression.Geometric
