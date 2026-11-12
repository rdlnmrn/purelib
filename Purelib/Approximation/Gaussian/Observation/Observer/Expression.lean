module

public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Data.List.GetD
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

/-!
# Finite numerical observer expressions

Expressions retain literal data and register coordinates. Their ordered
arithmetic evaluation and failures are shared by numerical observer control.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Observer

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat

set_option genInjectivity false in
/-- The numerical values visible to a first-order observer. -/
inductive Value where
  /-- An exact canonical rational. -/ | rational (value : Fraction.Rational)
  /-- A finite natural count or coordinate. -/ | natural (value : Nat)
  /-- One finite numerical decision. -/ | bit (value : Bool)
  /-- An exact finite raw word. -/ | word (value : List Bool)
  /-- A Gaussian rational coordinate pair. -/ | point (value : Gaussian.Basic.Canonical)
  /-- One observed rational ball, with no source identity. -/ | ball (value : Enclosure.Ball)

set_option genInjectivity false in
/-- The explicit unary numerical operations of the observer language. -/
inductive Unary where
  /-- Read a ball's squared radius. -/ | radiusSq
  /-- Read a ball's rational centre. -/ | center
  /-- Read the real rational coordinate. -/ | real
  /-- Read the imaginary rational coordinate. -/ | imaginary
  /-- Compute a Gaussian point's squared norm. -/ | normSq
  /-- Read the exact length of a finite word. -/ | length
  /-- Convert a natural count to its canonical rational reading. -/ | toRational
  /-- Negate a rational reading. -/ | negate
  /-- Negate a Boolean numerical decision. -/ | notBit

set_option genInjectivity false in
/-- The explicit binary numerical operations of the observer language. -/
inductive Binary where
  /-- Add rational readings. -/ | add
  /-- Subtract rational readings. -/ | subtract
  /-- Multiply rational readings. -/ | multiply
  /-- Use the owned total rational division operation. -/ | divide
  /-- Compare rational readings strictly. -/ | less
  /-- Compare rational readings weakly. -/ | lessEqual
  /-- Test exact rational equality. -/ | equal
  /-- Add finite natural counts. -/ | addCount
  /-- Compare finite natural counts strictly. -/ | lessCount
  /-- Append the two original finite words in order. -/ | appendWord
  /-- Prepend one supplied bit to the original word. -/ | consBit
  /-- Take a supplied finite count of bits from the original word. -/ | takeWord

set_option genInjectivity false in
/-- A concrete finite observer failure retaining its offending numerical data. -/
inductive Error where
  /-- No register exists at this original finite coordinate. -/ | missingVariable (index : Nat)
  /-- A unary operation received a value of the wrong numerical kind. -/ | unaryType (operation : Unary) (value : Value)
  /-- A binary operation received incompatible numerical kinds. -/ | binaryType
      (operation : Binary) (left right : Value)
  /-- A branch received a non-Boolean numerical value. -/ | branchType (value : Value)
  /-- A refinement target was not a rational value. -/ | targetType (value : Value)
  /-- The actual rational refinement target violates strict positivity. -/ | nonpositiveTarget
      (target : Fraction.Rational) (notPositive : ¬ 0 < target)
  /-- A finite loop count was not a natural value. -/ | countType (value : Value)
  /-- A recalled occurrence coordinate was not a natural value. -/ | recallType (value : Value)
  /-- No saved occurrence exists at this original finite coordinate. -/ | missingRecall (index : Nat)
  /-- The finite instruction list ended without an explicit return. -/ | missingReturn
  /-- A counter jump has no retained original program frame before the caller boundary. -/ | missingCounter
  /-- A numerical return has no retained original caller. -/ | missingCaller

namespace Unary

/-- Apply the selected unary operation to its actual numerical operand.

Each operation accepts its declared numerical kind. A mismatched kind returns
the same operation tag and original operand as a concrete type failure.
-/
@[expose] def apply (operation : Unary) (value : Value) : Except Error Value :=
  match operation, value with
  | .radiusSq, .ball ball => .ok (.rational ball.radiusSq)
  | .center, .ball ball => .ok (.point ball.center)
  | .real, .point point => .ok (.rational point.re)
  | .imaginary, .point point => .ok (.rational point.im)
  | .normSq, .point point => .ok (.rational (Gaussian.Norm.Basic.normSq point))
  | .length, .word word => .ok (.natural word.length)
  | .toRational, .natural count => .ok (.rational (Fraction.Cast.fromInt (count : Int)))
  | .negate, .rational scalar => .ok (.rational (-scalar))
  | .notBit, .bit bit => .ok (.bit (!bit))
  | operation, value => .error (.unaryType operation value)

end Unary

namespace Binary

/-- Apply the selected binary operation to the two actual numerical operands.

Compatible kinds use the owned rational, natural and finite-word operations.
Otherwise the failure retains the selected operation and both original
operands, without replacing either numerical value.
-/
@[expose] def apply (operation : Binary) (left right : Value) : Except Error Value :=
  match operation, left, right with
  | .add, .rational left, .rational right => .ok (.rational (left + right))
  | .subtract, .rational left, .rational right => .ok (.rational (left - right))
  | .multiply, .rational left, .rational right => .ok (.rational (left * right))
  | .divide, .rational left, .rational right => .ok (.rational (left / right))
  | .less, .rational left, .rational right => .ok (.bit (decide (left < right)))
  | .lessEqual, .rational left, .rational right => .ok (.bit (decide (left ≤ right)))
  | .equal, .rational left, .rational right => .ok (.bit (decide (left = right)))
  | .addCount, .natural left, .natural right => .ok (.natural (left + right))
  | .lessCount, .natural left, .natural right => .ok (.bit (decide (left < right)))
  | .appendWord, .word left, .word right => .ok (.word (left ++ right))
  | .consBit, .bit bit, .word word => .ok (.word (bit :: word))
  | .takeWord, .natural count, .word word => .ok (.word (word.take count))
  | operation, left, right => .error (.binaryType operation left right)

end Binary

set_option genInjectivity false in
/-- Finite numerical expressions with literal data and original register coordinates. -/
inductive Expr where
  /-- Retain fixed finite numerical control data. -/ | literal (value : Value)
  /-- Read the register at its original natural coordinate. -/ | variable (index : Nat)
  /-- Apply one explicit unary operation. -/ | unary (operation : Unary) (operand : Expr)
  /-- Apply one explicit binary operation in left-to-right evaluation order. -/ | binary
      (operation : Binary) (left right : Expr)

namespace Expr

/-- Evaluate finite expression data without a source or external callback.

Register lookup uses the original natural coordinate. Binary expressions
evaluate the left operand before the right and stop at the first failure;
only two successful operands reach their selected numerical operation.
-/
@[expose] def evaluate (registers : List Value) : Expr → Except Error Value
  | .literal value => .ok value
  | .variable index =>
      match Data.List.getElem? registers index with
      | some value => .ok value
      | none => .error (.missingVariable index)
  | .unary operation operand =>
      match evaluate registers operand with
      | .error error => .error error
      | .ok value => operation.apply value
  | .binary operation left right =>
      match evaluate registers left with
      | .error error => .error error
      | .ok leftValue =>
          match evaluate registers right with
          | .error error => .error error
          | .ok rightValue => operation.apply leftValue rightValue

end Expr

set_option genInjectivity false in
/-- The finite outcome of an observer, distinct from any decision about its source. -/
inductive Outcome where
  /-- The observer returned this explicit numerical value. -/ | returned (value : Value)
  /-- The observer encountered this concrete finite failure. -/ | failed (error : Error)
  /-- Explicit execution fuel was exhausted. -/ | exhausted

end Purelib.Approximation.Gaussian.Observation.Observer

end
