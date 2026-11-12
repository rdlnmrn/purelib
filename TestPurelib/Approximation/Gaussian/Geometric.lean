module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import Init.System.IOError

/-! # Finite geometric powers and original input enclosures -/

namespace TestPurelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation
open Purelib.Data.Gaussian.Basic (Canonical)

example (source : GeometricApproximation) : source.pow 0 = .exact 1 := source.pow_zero

example (source : GeometricApproximation) (exponent : Nat) :
    source.pow (exponent + 1) = (source.pow exponent).mul source := source.pow_succ exponent

example (source : GeometricApproximation) (exponent index : Nat) :
    (source.pow exponent).sample index = source.sample index ^ exponent := source.pow_sample exponent index

example (source : GeometricApproximation) (exponent : Nat) :
    (source.pow exponent).centerBound = source.centerBound ^ exponent := source.pow_centerBound exponent

example (ball : Ball) : ball.pow 0 = .point 1 := ball.pow_zero

example (ball : Ball) (exponent : Nat) :
    ball.pow (exponent + 1) = (ball.pow exponent).mul ball := ball.pow_succ exponent

example (ball : Ball) (exponent : Nat) : (ball.pow exponent).center = ball.center ^ exponent :=
  ball.pow_center exponent

example {ball : Ball} {value : Canonical} (inside : ball.Contains value) (exponent : Nat) :
    (ball.pow exponent).Contains (value ^ exponent) := Ball.contains_pow inside exponent

example (input : CoherentNamed) (source : GeometricApproximation)
    (same : NamedEquivalent input.name source.toApproximation.toNamed) (exponent : Nat) :
    NamedEquivalent (Power.namedPower input exponent).name (source.pow exponent).toApproximation.toNamed :=
  CoherentEvaluation.pow_agrees input source same exponent

example (input : CoherentNamed) (source : GeometricApproximation)
    (same : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Power.namedPower input 0).name (source.pow 0).toApproximation.toNamed :=
  CoherentEvaluation.pow_agrees input source same 0

/-- Check powers of an actual retained input and distinguish its formal samples from optimized algebraic samples.

The original input enclosure certifies every finite sample. Only its initial
observation is read for positive powers; zero power is also read at a large
index without running that original input's numerical refinement program.
-/
public def check (source : GeometricApproximation) (ball : Ball)
    (inside : ∀ index, ball.Contains (source.sample index)) (optimized : GeometricApproximation) : IO Unit := do
  let first := source.sample 0
  let zero := source.pow 0
  unless zero.sample 100000 = 1 ∧ zero.errorScale = 0 ∧ (ball.pow 0).radiusSq = 0 do
    throw (IO.userError "zero geometric power changed its exact unit program or enclosure")
  for exponent in [1, 3, 4, 7] do
    let powered := source.pow exponent
    let enclosure := ball.pow exponent
    let reading := powered.sample 0
    have member := Ball.contains_pow (inside 0) exponent
    have sampleMember : enclosure.Contains reading := by
      change (ball.pow exponent).Contains ((source.pow exponent).sample 0)
      rewrite [source.pow_sample exponent 0]
      exact member
    let retained : { value : Canonical // enclosure.Contains value } :=
      ⟨reading, sampleMember⟩
    unless retained.val = first ^ exponent ∧ enclosure.Contains retained.val do
      throw (IO.userError "finite power changed its actual original sample or lost its computed enclosure")
  let formal := (source.pow 3).sample 0
  let exactReading := optimized.sample 0
  unless formal ≠ exactReading do
    throw (IO.userError "formal root power was incorrectly replaced by its optimized algebraic sample")
  Purelib.System.IO.println
    "geometric power: original root samples, full input enclosure and distinct optimized reading checked"

end TestPurelib.Approximation.Gaussian.Geometric
