module

import Purelib.System.IO

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Evaluation
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Geometric.Enclosure
import Purelib.Approximation.Gaussian.Geometric.Enclosure.Inverse
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Field

namespace TestPurelib.Approximation.Gaussian.CheckedGeometric.Compound

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Data.Gaussian.Basic (Canonical)

section

variable {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (leftBall : left.ball = ball) (rightBall : right.ball = ball)

/-- Two original programs with one supplied common ball retain a common compound bound at arbitrary indices.

The programs and indices remain independent. Only their genuine original ball
readbacks are shared; the power equation of an algebraic residual is not used.
-/
example (firstIndex secondIndex exponent : Nat) :
    (((ball.pow exponent).conj.mul (Ball.point 2)).add (Ball.point 1)).Contains
      (((left.source.sample firstIndex ^ exponent).conj * 2) + 1) ∧
    (((ball.pow exponent).conj.mul (Ball.point 2)).add (Ball.point 1)).Contains
      (((right.source.sample secondIndex ^ exponent).conj * 2) + 1) := by
  constructor
  · have bound := (((left.pow exponent).conj.mul (Enclosure.exact 2)).add (Enclosure.exact 1)).contains firstIndex
    rewrite [Enclosure.add_ball, Enclosure.mul_ball, Enclosure.conj_ball, Enclosure.pow_ball,
      Enclosure.exact_ball, Enclosure.exact_ball, leftBall, Enclosure.add_sample,
      Enclosure.mul_sample, Enclosure.conj_sample, Enclosure.pow_sample,
      Enclosure.exact_sample, Enclosure.exact_sample] at bound
    exact bound
  · have bound := (((right.pow exponent).conj.mul (Enclosure.exact 2)).add (Enclosure.exact 1)).contains secondIndex
    rewrite [Enclosure.add_ball, Enclosure.mul_ball, Enclosure.conj_ball, Enclosure.pow_ball,
      Enclosure.exact_ball, Enclosure.exact_ball, rightBall, Enclosure.add_sample,
      Enclosure.mul_sample, Enclosure.conj_sample, Enclosure.pow_sample,
      Enclosure.exact_sample, Enclosure.exact_sample] at bound
    exact bound

/-- Actual prepared quotient programs at two original channels obey one common inverse ball at arbitrary indices.

The same genuine common-ball apartness is transported to each original input.
Both preparations and both numerical programs remain independent; no equality
between parameters or between a residual equation and a sample is assumed.
-/
example (firstPrepared : Prepared first) (secondPrepared : Prepared second) (apart : Ball.Apart ball)
    (firstIndex secondIndex : Nat) :
    ((Ball.point 1).div ball apart).Contains
      ((left.inverse firstPrepared (leftBall.symm ▸ apart)).source.sample firstIndex) ∧
    ((Ball.point 1).div ball apart).Contains
      ((right.inverse secondPrepared (rightBall.symm ▸ apart)).source.sample secondIndex) := by
  constructor
  · have inside := (left.inverse firstPrepared (leftBall.symm ▸ apart)).contains firstIndex
    rewrite [Enclosure.inverse_ball] at inside
    have same : (Ball.point 1).div left.ball (leftBall.symm ▸ apart) = (Ball.point 1).div ball apart := by
      cases leftBall
      rfl
    exact (congrArg (fun common : Ball =>
      common.Contains ((left.inverse firstPrepared (leftBall.symm ▸ apart)).source.sample firstIndex))
        same).mp inside
  · have inside := (right.inverse secondPrepared (rightBall.symm ▸ apart)).contains secondIndex
    rewrite [Enclosure.inverse_ball] at inside
    have same : (Ball.point 1).div right.ball (rightBall.symm ▸ apart) = (Ball.point 1).div ball apart := by
      cases rightBall
      rfl
    exact (congrArg (fun common : Ball =>
      common.Contains ((right.inverse secondPrepared (rightBall.symm ▸ apart)).source.sample secondIndex))
        same).mp inside

end

/-- The actual singleton occurrence of the retained original cubic annotation. -/
private def index : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩

/-- Exercise compound formal programs and colliding zero equations on one genuine original cubic owner.

The caller supplies the actual intrinsic sidecar and all-index enclosure of the
same annotation. Only its primitive initial sample is read. The algebraic cube
equation remains distinct from that formal sample throughout the interpreter.
-/
public def checkCubic (annotation : Annotated) (sidecar : Algebraic.Sidecar annotation.channel)
    (enclosing : Enclosure annotation.channel) : IO Unit := do
  let environment : Fin 1 → Annotated := fun _ => annotation
  let atom := Checked.Admitted.atom environment index sidecar
  let geometry := Checked.Geometric.Geometry.atom environment index sidecar enclosing
  let one := Checked.Admitted.rational environment 1
  let two := Checked.Admitted.rational environment 2
  let zero := Checked.Admitted.rational environment 0
  let oneGeometry := Checked.Geometric.Geometry.rational environment 1
  let twoGeometry := Checked.Geometric.Geometry.rational environment 2
  let zeroGeometry := Checked.Geometric.Geometry.rational environment 0
  let originalSample := enclosing.source.sample 0
  let compound := (atom.pow 3).conj.mul two |>.add one
  match Checked.Geometric.run compound ⟨⟨geometry, twoGeometry⟩, oneGeometry⟩ with
  | .completed result =>
      let expectedSample := (originalSample ^ 3).conj * 2 + 1
      let expectedBall := ((enclosing.ball.pow 3).conj.mul (Ball.point 2)).add (Ball.point 1)
      unless result.enclosing.source.sample 0 = expectedSample ∧ result.enclosing.ball = expectedBall ∧
          result.enclosing.ball.Contains expectedSample do
        throw (IO.userError "The original cubic compound changed its formal sample or computed common ball")
      let scalar := result.completed.sidecar.scalar?
      if available : scalar.isSome then
        unless (scalar.get available).value == 5 && expectedSample != (scalar.get available).value do
          throw (IO.userError "A retained cubic equation was substituted for the actual compound sample")
      else throw (IO.userError "The compound lost its independently retained cubic scalar equation")
  | _ => throw (IO.userError "The actual cubic compound failed its supplied original geometry")
  let inverseCompound := (atom.inverse.conj.pow 2).mul one |>.add zero
  match Checked.Geometric.run inverseCompound ⟨⟨geometry, oneGeometry⟩, zeroGeometry⟩ with
  | .completed result =>
      let expectedSample := (((1 : Canonical) / originalSample).conj ^ 2) * 1 + 0
      unless result.enclosing.source.sample 0 = expectedSample ∧ result.enclosing.ball.Contains expectedSample do
        throw (IO.userError "Checked inversion changed the original cubic formal inverse program")
  | _ => throw (IO.userError "The genuine original cubic ball did not pay the compound inverse domain")
  let collision := (atom.pow 3).sub two
  let collisionGeometry := (geometry, twoGeometry)
  match Checked.Geometric.run (collision.inverse.pow 0) collisionGeometry with
  | .invalid obstruction =>
      let ⟨_, child, resolution, _⟩ := obstruction.denominator
      unless child.enclosing.source.sample 0 == originalSample ^ 3 - 2 &&
          child.enclosing.source.sample 0 != 0 do
        throw (IO.userError "The zero cube equation replaced its original nonzero finite denominator sample")
      match resolution.decision with
      | .excluded _ => pure ()
      | .prepared _ => throw (IO.userError "The original cubic zero collision lost its exact exclusion")
  | _ => throw (IO.userError "Power zero erased the colliding original cubic denominator domain")
  match Checked.Geometric.run ((zero.mul atom).inverse.pow 0) ⟨zeroGeometry, geometry⟩ with
  | .invalid obstruction =>
      let ⟨_, child, resolution, _⟩ := obstruction.denominator
      unless child.enclosing.source.sample 0 == 0 do
        throw (IO.userError "The second zero collision changed its same original multiplication samples")
      match resolution.decision with
      | .excluded _ => pure ()
      | .prepared _ => throw (IO.userError "The second original zero collision lost its cached exclusion")
  | _ => throw (IO.userError "A derived zero product incorrectly required a squarefree output polynomial")
  Purelib.System.IO.println "Checked cubic compounds: common balls, formal inverse samples, \
    distinct zero collisions and zero-power domains retained"

end TestPurelib.Approximation.Gaussian.CheckedGeometric.Compound
