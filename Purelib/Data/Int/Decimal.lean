module

-- The public ToString contract also retains the original Nat.repr owner publicly.
import Init.Data.ToString.Basic
public import Purelib.Data.Nat.Decimal
import Init.Data.Repr
-- The exposed signed renderer retains the original native append and UTF8 certificate.
public import Purelib.Data.String.Basic

/-!
# Signed decimal representations

Signed rendering retains the original integer constructors and decimal bytes.
Natural magnitudes retain the original cached and machine-word runtime paths;
larger values use the same digit procedure with proved binary-width fuel.
-/

namespace Purelib.Data.Int.Decimal

open Purelib.Data.String (append)

/-- Render an integer with its original natural magnitude and sign bytes.

Both branches use the original magnitude's complete decimal record. Negative
successors retain the same successor magnitude and original minus prefix. -/
@[expose] public def repr : Int → _root_.String
  | Int.ofNat value => Nat.Decimal.repr value
  | Int.negSucc value => append "-" (Nat.Decimal.repr (Nat.succ value))

/-- Rendering a nonnegative integer retains the original natural renderer's bytes.

The natural renderer's all-input readback retains the complete original bytes,
including the same small-value cache and machine-word backend. -/
public theorem toByteArray_ofNat (value : Nat) :
    (repr (Int.ofNat value)).toByteArray = (Nat.repr value).toByteArray := by
  exact congrArg _root_.String.toByteArray (Nat.Decimal.repr_eq value)

/-- Rendering a negative successor retains the original minus and magnitude bytes.

The successor magnitude is rendered once with its original-byte readback.
String concatenation retains that output and the original minus prefix in order. -/
public theorem toByteArray_negSucc (value : Nat) :
    (repr (Int.negSucc value)).toByteArray =
      "-".toByteArray ++ (Nat.repr (Nat.succ value)).toByteArray := by
  unfold repr
  dsimp only
  rewrite [Nat.Decimal.repr_eq]
  rfl

/-- Use the retained original signed decimal representation for integer scalars.

Opening the scope selects the exact original decimal bytes and native append;
the natural magnitude uses proved shortened fuel when it exceeds one word. -/
public scoped instance (priority := 1001) : ToString Int where
  toString := repr

/-- Format an integer with its original signed decimal and application parentheses.

The original negative test and precedence rule retain Core's exact Repr grammar.
Only signed string concatenation follows the direct retained UTF8 certificate. -/
public scoped instance (priority := 1001) : Repr Int where
  reprPrec value precedence :=
    if value < 0 then Repr.addAppParen (repr value) precedence else repr value

end Purelib.Data.Int.Decimal
