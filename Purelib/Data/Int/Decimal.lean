module

-- The public ToString contract also retains the original Nat.repr owner publicly.
public import Init.Data.ToString.Basic
import Init.Data.Repr
-- The exposed signed renderer retains the original native append and UTF8 certificate.
public import Purelib.Data.String.Basic

/-!
# Signed decimal representations

Signed rendering retains the original integer constructors and the original
natural-number renderer, including its cached and machine-word runtime paths.
Only the negative prefix uses the direct original-byte append certificate.
-/

namespace Purelib.Data.Int.Decimal

open Purelib.Data.String (append)

/-- Render an integer with its original natural magnitude and sign bytes.

Nonnegative values call the original Nat.repr directly. Negative successors retain
the same successor magnitude and original minus prefix with direct UTF8 validity. -/
@[expose] public def repr : Int → _root_.String
  | Int.ofNat value => Nat.repr value
  | Int.negSucc value => append "-" (Nat.repr (Nat.succ value))

/-- Rendering a nonnegative integer retains the original natural renderer's bytes.

The original Nat.repr output is used directly, including its existing runtime
cache and backend. No copied digits, reconstructed string or new printer is used. -/
public theorem toByteArray_ofNat (value : Nat) :
    (repr (Int.ofNat value)).toByteArray = (Nat.repr value).toByteArray := rfl

/-- Rendering a negative successor retains the original minus and magnitude bytes.

The original Nat.repr renders the successor magnitude once. String concatenation
keeps that exact output and the original one-byte minus prefix in order. -/
public theorem toByteArray_negSucc (value : Nat) :
    (repr (Int.negSucc value)).toByteArray =
      "-".toByteArray ++ (Nat.repr (Nat.succ value)).toByteArray := rfl

/-- Use the retained original signed decimal representation for integer scalars.

Opening the scope selects the original natural renderer and native string append;
only the append validity certificate follows the owned direct proof route. -/
public scoped instance (priority := 1001) : ToString Int where
  toString := repr

/-- Format an integer with its original signed decimal and application parentheses.

The original negative test and precedence rule retain Core's exact Repr grammar.
Only signed string concatenation follows the direct retained UTF8 certificate. -/
public scoped instance (priority := 1001) : Repr Int where
  reprPrec value precedence :=
    if value < 0 then Repr.addAppParen (repr value) precedence else repr value

end Purelib.Data.Int.Decimal
