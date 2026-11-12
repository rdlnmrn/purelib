module
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Conjugation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Common enclosures of original geometric sample programs -/

public section

namespace Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Approximation

set_option genInjectivity false in
/-- One common rational ball containing every sample of a retained original geometric program.

The original coherent channel is the index. Its comparison identifies the
retained geometric program, and the common ball bounds that same program at
every finite index. Arithmetic computes new programs and balls from the
retained operands without substituting an algebraically optimized program.
-/
structure Enclosure (channel : CoherentNamed) where
  /-- The actual retained geometric sample program. -/
  source : GeometricApproximation
  /-- The original channel compares to this same retained sample program. -/
  equivalent : NamedEquivalent channel.name source.toApproximation.toNamed
  /-- The retained common rational enclosure of all original samples. -/
  ball : Ball
  /-- Every finite sample of that actual retained program belongs to the common ball. -/
  contains : ∀ index, ball.Contains (source.sample index)

constructive_injectivity Enclosure

namespace Enclosure

/-- Realize an exact channel with its retained point ball and exact formula readback. -/
def exactFromBall (value : Canonical) (ball : Ball) (same : ball = Ball.point value) :
    Enclosure (CoherentNamed.Coherence.exact value) :=
  let result := GeometricApproximation.exact value
  { source := result
    equivalent := Coherent.Comparison.exact_agreesWith value result (fun _ => rfl)
    ball := ball
    contains := fun _ => same.symm ▸ Ball.contains_point value }

/-- Enclose the actual exact channel by its original constant program and exact point ball. -/
def exact (value : Canonical) : Enclosure (CoherentNamed.Coherence.exact value) :=
  exactFromBall value (Ball.point value) rfl

/-- Negate the original program while consuming the retained exact negation ball. -/
def negFromBall {channel : CoherentNamed} (original : Enclosure channel) (ball : Ball)
    (same : ball = original.ball.neg) : Enclosure (CoherentNamed.neg channel) :=
  let result := original.source.neg
  { source := result
    equivalent := Coherent.Comparison.neg_agreesWith channel original.source result original.equivalent
      (fun _ => rfl)
    ball := ball
    contains := fun index => same.symm ▸ Ball.contains_neg (original.contains index) }

/-- Negate the original channel, program and common ball using their original unary operations. -/
def neg {channel : CoherentNamed} (original : Enclosure channel) : Enclosure (CoherentNamed.neg channel) :=
  original.negFromBall original.ball.neg rfl

/-- Add both original programs using the retained exact common addition ball. -/
def addFromBall {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (ball : Ball)
    (same : ball = left.ball.add right.ball) : Enclosure (CoherentNamed.add first second) :=
  let result := left.source.add right.source
  { source := result
    equivalent := Coherent.Comparison.add_agreesWith first second left.source right.source result
      left.equivalent right.equivalent (fun _ => rfl)
    ball := ball
    contains := fun index => same.symm ▸ Ball.contains_add (left.contains index) (right.contains index) }

/-- Add original channels while retaining equal-index sample addition and the computed common sum ball. -/
def add {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    Enclosure (CoherentNamed.add first second) := left.addFromBall right (left.ball.add right.ball) rfl

/-- Subtract original programs using the retained exact common subtraction ball. -/
def subFromBall {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (ball : Ball)
    (same : ball = left.ball.sub right.ball) : Enclosure (CoherentNamed.add first (CoherentNamed.neg second)) :=
  let negative := right.source.neg
  let result := left.source.add negative
  { source := result
    equivalent := Coherent.Comparison.sub_agreesWith first second left.source right.source negative result
      left.equivalent right.equivalent (fun _ => rfl) (fun _ => rfl)
    ball := ball
    contains := fun index => by
      have inside : (left.ball.sub right.ball).Contains (result.sample index) := by
        change (left.ball.sub right.ball).Contains ((left.source.sub right.source).sample index)
        rewrite [GeometricApproximation.sub_sample]
        exact Ball.contains_sub (left.contains index) (right.contains index)
      exact same.symm ▸ inside }

/-- Subtract original channels through ordered addition and negation of the original second operand.

The source uses equal-index geometric subtraction. The ball retains the
same original two operand bounds and the existing subtraction allowance.
-/
def sub {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    Enclosure (CoherentNamed.add first (CoherentNamed.neg second)) :=
  left.subFromBall right (left.ball.sub right.ball) rfl

/-- Multiply both original programs using the retained exact common product ball. -/
def mulFromBall {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (ball : Ball)
    (same : ball = left.ball.mul right.ball) : Enclosure (CoherentNamed.mul first second) :=
  let result := left.source.mul right.source
  { source := result
    equivalent := Coherent.Comparison.mul_agreesWith first second left.source right.source result
      left.equivalent right.equivalent (fun _ => rfl)
    ball := ball
    contains := fun index => same.symm ▸ Ball.contains_mul (left.contains index) (right.contains index) }

/-- Multiply original channels, retaining both original programs and the computed common product ball. -/
def mul {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    Enclosure (CoherentNamed.mul first second) := left.mulFromBall right (left.ball.mul right.ball) rfl

/-- Realize the original natural power using its retained exact ball and paired cached program.

The original named channel and geometric prefix remain paired in the existing
power realization. The supplied ball is consumed directly; its equality is
used only by the all-index containment proof.
-/
def powFromBall {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) (ball : Ball)
    (same : ball = original.ball.pow exponent) : Enclosure (Power.namedPower channel exponent) :=
  let cache := Coherent.Comparison.PowerRealization.build channel original.source original.equivalent exponent
  { source := cache.source
    equivalent := cache.original_agrees
    ball := ball
    contains := fun index => by
      have inside : (original.ball.pow exponent).Contains (cache.source.sample index) := by
        rewrite [cache.source_eq, GeometricApproximation.pow_sample]
        exact Ball.contains_pow (original.contains index) exponent
      exact same.symm ▸ inside }

/-- Enclose the original named natural power using its same ordered geometric and ball power folds.

Zero gives the exact unit channel and point ball. Positive powers use the
original input at every factor; obligations belonging to syntax children
remain with the caller's retained construction.
-/
def pow {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) :
    Enclosure (Power.namedPower channel exponent) :=
  original.powFromBall exponent (original.ball.pow exponent) rfl

/-- Conjugate the original program using the retained exact conjugation ball. -/
def conjFromBall {channel : CoherentNamed} (original : Enclosure channel) (ball : Ball)
    (same : ball = original.ball.conj) : Enclosure (CoherentNamed.conj channel) :=
  let result := original.source.conj
  { source := result
    equivalent := CoherentNamed.conj_geometricWith original.source result original.equivalent (fun _ => rfl)
    ball := ball
    contains := fun index => same.symm ▸ Ball.contains_conj (original.contains index) }

/-- Conjugate the original channel and every same-index sample while retaining the ball's squared radius. -/
def conj {channel : CoherentNamed} (original : Enclosure channel) : Enclosure (CoherentNamed.conj channel) :=
  original.conjFromBall original.ball.conj rfl

/-- Reuse the same original sample program and ball at an operationally equivalent original channel. -/
def transport {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) : Enclosure second where
  source := original.source
  equivalent := equivalent.symm.trans original.equivalent
  ball := original.ball
  contains := original.contains

/-- Transport the complete retained enclosure through an exact equality of its original channel index. -/
def cast {first second : CoherentNamed} (original : Enclosure first) (same : first = second) : Enclosure second :=
  same ▸ original

/-- The supplied-ball exact retains the complete original enclosure construction. -/
theorem exactFromBall_eq (value : Canonical)
    (ball : Ball) (same : ball = Ball.point value) :
    exactFromBall value ball same = exact value := by
  cases same
  rfl

/-- The retained exact ball and its all-index containment have their defining values. -/
private theorem exactFromBall_readback (value : Canonical)
    (ball : Ball) (same : ball = Ball.point value) :
    (exactFromBall value ball same).ball = ball ∧
      ∀ index, ball.Contains ((exactFromBall value ball same).source.sample index) :=
  ⟨rfl, fun index => (exactFromBall value ball same).contains index⟩

/-- The supplied-ball exact consumes exactly the retained ball data. -/
theorem exactFromBall_ball (value : Canonical)
    (ball : Ball) (same : ball = Ball.point value) : (exactFromBall value ball same).ball = ball :=
  (exactFromBall_readback value ball same).1

/-- Every original exact reading belongs to the same retained supplied ball. -/
theorem exactFromBall_contains (value : Canonical)
    (ball : Ball) (same : ball = Ball.point value) (index : Nat) :
    ball.Contains ((exactFromBall value ball same).source.sample index) :=
  (exactFromBall_readback value ball same).2 index

/-- The supplied-ball neg retains the complete original enclosure construction. -/
theorem negFromBall_eq {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.neg) :
    original.negFromBall ball same = original.neg := by
  cases same
  rfl

/-- The retained neg ball and its all-index containment have their defining values. -/
private theorem negFromBall_readback {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.neg) :
    (original.negFromBall ball same).ball = ball ∧
      ∀ index, ball.Contains ((original.negFromBall ball same).source.sample index) :=
  ⟨rfl, fun index => (original.negFromBall ball same).contains index⟩

/-- The supplied-ball neg consumes exactly the retained ball data. -/
theorem negFromBall_ball {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.neg) : (original.negFromBall ball same).ball = ball :=
  (negFromBall_readback original ball same).1

/-- Every original neg reading belongs to the same retained supplied ball. -/
theorem negFromBall_contains {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.neg) (index : Nat) :
    ball.Contains ((original.negFromBall ball same).source.sample index) :=
  (negFromBall_readback original ball same).2 index

/-- The supplied-ball add retains the complete original enclosure construction. -/
theorem addFromBall_eq {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.add right.ball) :
    left.addFromBall right ball same = left.add right := by
  cases same
  rfl

/-- The retained add ball and its all-index containment have their defining values. -/
private theorem addFromBall_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.add right.ball) :
    (left.addFromBall right ball same).ball = ball ∧
      ∀ index, ball.Contains ((left.addFromBall right ball same).source.sample index) :=
  ⟨rfl, fun index => (left.addFromBall right ball same).contains index⟩

/-- The supplied-ball add consumes exactly the retained ball data. -/
theorem addFromBall_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.add right.ball) : (left.addFromBall right ball same).ball = ball :=
  (addFromBall_readback left right ball same).1

/-- Every original add reading belongs to the same retained supplied ball. -/
theorem addFromBall_contains {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.add right.ball) (index : Nat) :
    ball.Contains ((left.addFromBall right ball same).source.sample index) :=
  (addFromBall_readback left right ball same).2 index

/-- The supplied-ball sub retains the complete original enclosure construction. -/
theorem subFromBall_eq {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.sub right.ball) :
    left.subFromBall right ball same = left.sub right := by
  cases same
  rfl

/-- The retained sub ball and its all-index containment have their defining values. -/
private theorem subFromBall_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.sub right.ball) :
    (left.subFromBall right ball same).ball = ball ∧
      ∀ index, ball.Contains ((left.subFromBall right ball same).source.sample index) :=
  ⟨rfl, fun index => (left.subFromBall right ball same).contains index⟩

/-- The supplied-ball sub consumes exactly the retained ball data. -/
theorem subFromBall_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.sub right.ball) : (left.subFromBall right ball same).ball = ball :=
  (subFromBall_readback left right ball same).1

/-- Every original sub reading belongs to the same retained supplied ball. -/
theorem subFromBall_contains {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.sub right.ball) (index : Nat) :
    ball.Contains ((left.subFromBall right ball same).source.sample index) :=
  (subFromBall_readback left right ball same).2 index

/-- The supplied-ball mul retains the complete original enclosure construction. -/
theorem mulFromBall_eq {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) :
    left.mulFromBall right ball same = left.mul right := by
  cases same
  rfl

/-- The retained mul ball and its all-index containment have their defining values. -/
private theorem mulFromBall_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) :
    (left.mulFromBall right ball same).ball = ball ∧
      ∀ index, ball.Contains ((left.mulFromBall right ball same).source.sample index) :=
  ⟨rfl, fun index => (left.mulFromBall right ball same).contains index⟩

/-- The supplied-ball mul consumes exactly the retained ball data. -/
theorem mulFromBall_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) : (left.mulFromBall right ball same).ball = ball :=
  (mulFromBall_readback left right ball same).1

/-- Every original mul reading belongs to the same retained supplied ball. -/
theorem mulFromBall_contains {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) (index : Nat) :
    ball.Contains ((left.mulFromBall right ball same).source.sample index) :=
  (mulFromBall_readback left right ball same).2 index

/-- The supplied-ball pow retains the complete original enclosure construction. -/
theorem powFromBall_eq {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat)
    (ball : Ball) (same : ball = original.ball.pow exponent) :
    original.powFromBall exponent ball same = original.pow exponent := by
  cases same
  rfl

/-- The retained pow ball and its all-index containment have their defining values. -/
private theorem powFromBall_readback {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat)
    (ball : Ball) (same : ball = original.ball.pow exponent) :
    (original.powFromBall exponent ball same).ball = ball ∧
      ∀ index, ball.Contains ((original.powFromBall exponent ball same).source.sample index) :=
  ⟨rfl, fun index => (original.powFromBall exponent ball same).contains index⟩

/-- The supplied-ball pow consumes exactly the retained ball data. -/
theorem powFromBall_ball {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat)
    (ball : Ball) (same : ball = original.ball.pow exponent) : (original.powFromBall exponent ball same).ball = ball :=
  (powFromBall_readback original exponent ball same).1

/-- Every original pow reading belongs to the same retained supplied ball. -/
theorem powFromBall_contains {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat)
    (ball : Ball) (same : ball = original.ball.pow exponent) (index : Nat) :
    ball.Contains ((original.powFromBall exponent ball same).source.sample index) :=
  (powFromBall_readback original exponent ball same).2 index

/-- The supplied-ball conj retains the complete original enclosure construction. -/
theorem conjFromBall_eq {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.conj) :
    original.conjFromBall ball same = original.conj := by
  cases same
  rfl

/-- The retained conj ball and its all-index containment have their defining values. -/
private theorem conjFromBall_readback {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.conj) :
    (original.conjFromBall ball same).ball = ball ∧
      ∀ index, ball.Contains ((original.conjFromBall ball same).source.sample index) :=
  ⟨rfl, fun index => (original.conjFromBall ball same).contains index⟩

/-- The supplied-ball conj consumes exactly the retained ball data. -/
theorem conjFromBall_ball {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.conj) : (original.conjFromBall ball same).ball = ball :=
  (conjFromBall_readback original ball same).1

/-- Every original conj reading belongs to the same retained supplied ball. -/
theorem conjFromBall_contains {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.conj) (index : Nat) :
    ball.Contains ((original.conjFromBall ball same).source.sample index) :=
  (conjFromBall_readback original ball same).2 index

/-- The exact constructor's retained source and ball have their defining values. -/
private theorem exact_readback (value : Canonical) :
    (exact value).source = GeometricApproximation.exact value ∧ (exact value).ball = Ball.point value :=
  ⟨rfl, rfl⟩

/-- The exact constructor retains the complete original geometric construction. -/
theorem exact_source (value : Canonical) :
    (exact value).source = GeometricApproximation.exact value := (exact_readback value).1

/-- The exact constructor retains the complete computed common ball. -/
theorem exact_ball (value : Canonical) :
    (exact value).ball = Ball.point value := (exact_readback value).2

/-- The exact constructor reads its original operands at the same unchanged sample index. -/
theorem exact_sample (value : Canonical) (index : Nat) :
    (exact value).source.sample index = value := by
  rewrite [exact_source]
  exact GeometricApproximation.exact_sample value index

/-- The neg constructor's retained source and ball have their defining values. -/
private theorem neg_readback {channel : CoherentNamed} (original : Enclosure channel) :
    (original.neg).source = original.source.neg ∧ (original.neg).ball = original.ball.neg :=
  ⟨rfl, rfl⟩

/-- The neg constructor retains the complete original geometric construction. -/
theorem neg_source {channel : CoherentNamed} (original : Enclosure channel) :
    (original.neg).source = original.source.neg := (neg_readback original).1

/-- The neg constructor retains the complete computed common ball. -/
theorem neg_ball {channel : CoherentNamed} (original : Enclosure channel) :
    (original.neg).ball = original.ball.neg := (neg_readback original).2

/-- The neg constructor reads its original operands at the same unchanged sample index. -/
theorem neg_sample {channel : CoherentNamed} (original : Enclosure channel) (index : Nat) :
    (original.neg).source.sample index = -original.source.sample index := by
  rewrite [neg_source]
  exact GeometricApproximation.neg_sample original.source index

/-- The add constructor's retained source and ball have their defining values. -/
private theorem add_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.add right).source = left.source.add right.source ∧ (left.add right).ball = left.ball.add right.ball :=
  ⟨rfl, rfl⟩

/-- The add constructor retains the complete original geometric construction. -/
theorem add_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.add right).source = left.source.add right.source := (add_readback left right).1

/-- The add constructor retains the complete computed common ball. -/
theorem add_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.add right).ball = left.ball.add right.ball := (add_readback left right).2

/-- The add constructor reads its original operands at the same unchanged sample index. -/
theorem add_sample {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.add right).source.sample index = left.source.sample index + right.source.sample index := by
  rewrite [add_source]
  exact GeometricApproximation.add_sample left.source right.source index

/-- The sub constructor's retained source and ball have their defining values. -/
private theorem sub_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.sub right).source = left.source.sub right.source ∧ (left.sub right).ball = left.ball.sub right.ball :=
  ⟨rfl, rfl⟩

/-- The sub constructor retains the complete original geometric construction. -/
theorem sub_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.sub right).source = left.source.sub right.source := (sub_readback left right).1

/-- The sub constructor retains the complete computed common ball. -/
theorem sub_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.sub right).ball = left.ball.sub right.ball := (sub_readback left right).2

/-- The sub constructor reads its original operands at the same unchanged sample index. -/
theorem sub_sample {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.sub right).source.sample index = left.source.sample index - right.source.sample index := by
  rewrite [sub_source]
  exact GeometricApproximation.sub_sample left.source right.source index

/-- The mul constructor's retained source and ball have their defining values. -/
private theorem mul_readback {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.mul right).source = left.source.mul right.source ∧ (left.mul right).ball = left.ball.mul right.ball :=
  ⟨rfl, rfl⟩

/-- The mul constructor retains the complete original geometric construction. -/
theorem mul_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.mul right).source = left.source.mul right.source := (mul_readback left right).1

/-- The mul constructor retains the complete computed common ball. -/
theorem mul_ball {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) :
    (left.mul right).ball = left.ball.mul right.ball := (mul_readback left right).2

/-- The mul constructor reads its original operands at the same unchanged sample index. -/
theorem mul_sample {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.mul right).source.sample index = left.source.sample index * right.source.sample index := by
  rewrite [mul_source]
  exact GeometricApproximation.mul_sample left.source right.source index

/-- The pow constructor's retained source and ball have their defining values. -/
private theorem pow_readback {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) :
    (original.pow exponent).source = original.source.pow exponent ∧
      (original.pow exponent).ball = original.ball.pow exponent := by
  constructor
  · exact (Coherent.Comparison.PowerRealization.build channel original.source original.equivalent exponent).source_eq
  · rfl

/-- The pow constructor retains the complete original geometric construction. -/
theorem pow_source {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) :
    (original.pow exponent).source = original.source.pow exponent := (pow_readback original exponent).1

/-- The pow constructor retains the complete computed common ball. -/
theorem pow_ball {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) :
    (original.pow exponent).ball = original.ball.pow exponent := (pow_readback original exponent).2

/-- The pow constructor reads its original operands at the same unchanged sample index. -/
theorem pow_sample {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat) (index : Nat) :
    (original.pow exponent).source.sample index = original.source.sample index ^ exponent := by
  rewrite [pow_source]
  exact GeometricApproximation.pow_sample original.source exponent index

/-- The conj constructor's retained source and ball have their defining values. -/
private theorem conj_readback {channel : CoherentNamed} (original : Enclosure channel) :
    (original.conj).source = original.source.conj ∧ (original.conj).ball = original.ball.conj :=
  ⟨rfl, rfl⟩

/-- The conj constructor retains the complete original geometric construction. -/
theorem conj_source {channel : CoherentNamed} (original : Enclosure channel) :
    (original.conj).source = original.source.conj := (conj_readback original).1

/-- The conj constructor retains the complete computed common ball. -/
theorem conj_ball {channel : CoherentNamed} (original : Enclosure channel) :
    (original.conj).ball = original.ball.conj := (conj_readback original).2

/-- The conj constructor reads its original operands at the same unchanged sample index. -/
theorem conj_sample {channel : CoherentNamed} (original : Enclosure channel) (index : Nat) :
    (original.conj).source.sample index = (original.source.sample index).conj := by
  rewrite [conj_source]
  exact GeometricApproximation.conj_sample original.source index

/-- The transport constructor's retained source and ball have their defining values. -/
private theorem transport_readback {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) :
    (original.transport equivalent).source = original.source ∧ (original.transport equivalent).ball = original.ball :=
  ⟨rfl, rfl⟩

/-- The transport constructor retains the complete original geometric construction. -/
theorem transport_source {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) :
    (original.transport equivalent).source = original.source := (transport_readback original equivalent).1

/-- The transport constructor retains the complete computed common ball. -/
theorem transport_ball {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) :
    (original.transport equivalent).ball = original.ball := (transport_readback original equivalent).2

/-- The transport constructor reads its original operands at the same unchanged sample index. -/
theorem transport_sample {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) (index : Nat) :
    (original.transport equivalent).source.sample index = original.source.sample index := by
  rewrite [transport_source]
  rfl

/-- The cast constructor's retained source and ball have their defining values. -/
private theorem cast_readback {first second : CoherentNamed} (original : Enclosure first) (same : first = second) :
    (original.cast same).source = original.source ∧ (original.cast same).ball = original.ball :=
  by cases same; exact ⟨rfl, rfl⟩

/-- The cast constructor retains the complete original geometric construction. -/
theorem cast_source {first second : CoherentNamed} (original : Enclosure first) (same : first = second) :
    (original.cast same).source = original.source := (cast_readback original same).1

/-- The cast constructor retains the complete computed common ball. -/
theorem cast_ball {first second : CoherentNamed} (original : Enclosure first) (same : first = second) :
    (original.cast same).ball = original.ball := (cast_readback original same).2

/-- The cast constructor reads its original operands at the same unchanged sample index. -/
theorem cast_sample {first second : CoherentNamed} (original : Enclosure first) (same : first = second) (index : Nat) :
    (original.cast same).source.sample index = original.source.sample index := by
  rewrite [cast_source]
  rfl

/-- The supplied-ball exact retains exactly the original geometric sample program. -/
theorem exactFromBall_source (value : Canonical)
    (ball : Ball) (same : ball = Ball.point value) :
    (exactFromBall value ball same).source = GeometricApproximation.exact value := by
  rewrite [exactFromBall_eq]
  exact exact_source value

/-- The supplied-ball neg retains exactly the original geometric sample program. -/
theorem negFromBall_source {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.neg) :
    (original.negFromBall ball same).source = original.source.neg := by
  rewrite [negFromBall_eq]
  exact neg_source original

/-- The supplied-ball add retains exactly the original geometric sample program. -/
theorem addFromBall_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.add right.ball) :
    (left.addFromBall right ball same).source = left.source.add right.source := by
  rewrite [addFromBall_eq]
  exact add_source left right

/-- The supplied-ball sub retains exactly the original geometric sample program. -/
theorem subFromBall_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.sub right.ball) :
    (left.subFromBall right ball same).source = left.source.sub right.source := by
  rewrite [subFromBall_eq]
  exact sub_source left right

/-- The supplied-ball mul retains exactly the original geometric sample program. -/
theorem mulFromBall_source {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) :
    (left.mulFromBall right ball same).source = left.source.mul right.source := by
  rewrite [mulFromBall_eq]
  exact mul_source left right

/-- The supplied-ball pow retains exactly the original geometric sample program. -/
theorem powFromBall_source {channel : CoherentNamed} (original : Enclosure channel) (exponent : Nat)
    (ball : Ball) (same : ball = original.ball.pow exponent) :
    (original.powFromBall exponent ball same).source = original.source.pow exponent := by
  rewrite [powFromBall_eq]
  exact pow_source original exponent

/-- The supplied-ball conj retains exactly the original geometric sample program. -/
theorem conjFromBall_source {channel : CoherentNamed} (original : Enclosure channel)
    (ball : Ball) (same : ball = original.ball.conj) :
    (original.conjFromBall ball same).source = original.source.conj := by
  rewrite [conjFromBall_eq]
  exact conj_source original

end Enclosure

end Purelib.Approximation.Gaussian.Geometric

end
