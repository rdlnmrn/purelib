module

public import Purelib.Data.Nat.Remainder
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Multiplication

/-!
# Scalar transports for original natural remainders

The retained quotient and remainder reconstruct each supplied dividend.
A displayed divisor multiple drops out of the same remainder computation,
so addition and multiplication may retain a reduced argument before the final remainder.
-/

open Purelib.Data.Nat

namespace Purelib.Data.Nat.Remainder.Arithmetic

/-- Reducing the first addend preserves the final natural remainder.

The original quotient reconstructs the removed divisor multiple. Its same
multiple is discarded by the original remainder procedure, including when
the divisor is zero. -/
public theorem add_mod_left (left right divisor : Nat) :
    (left % divisor + right) % divisor = (left + right) % divisor := by
  have reconstructed : left = divisor * (left / divisor) + left % divisor :=
    (Division.mod_add_div left divisor).symm.trans (Nat.add_comm _ _)
  calc
    (left % divisor + right) % divisor =
        (divisor * (left / divisor) + (left % divisor + right)) % divisor :=
      (Remainder.mul_add_mod divisor (left / divisor) _).symm
    _ = ((divisor * (left / divisor) + left % divisor) + right) % divisor :=
      congrArg (fun value : Nat => value % divisor) (Nat.add_assoc _ _ _).symm
    _ = (left + right) % divisor :=
      congrArg (fun value : Nat => (value + right) % divisor) reconstructed.symm

/-- Reducing the second addend preserves the final natural remainder.

Commutativity places the same retained reduced addend first. The original
quotient/remainder reconstruction then transports that displayed scalar sum
without changing either argument or the final remainder algorithm. -/
public theorem add_mod_right (left right divisor : Nat) :
    (left + right % divisor) % divisor = (left + right) % divisor := by
  calc
    (left + right % divisor) % divisor = (right % divisor + left) % divisor :=
      congrArg (fun value : Nat => value % divisor) (Nat.add_comm _ _)
    _ = (right + left) % divisor := add_mod_left right left divisor
    _ = (left + right) % divisor :=
      congrArg (fun value : Nat => value % divisor) (Nat.add_comm _ _)

/-- Reducing the first factor preserves the final natural remainder.

The original quotient contributes a displayed divisor multiple after
multiplication by the unchanged second factor. Direct distributivity
separates that same multiple from the retained remainder product. -/
public theorem mul_mod_left (left right divisor : Nat) :
    (left % divisor * right) % divisor = (left * right) % divisor := by
  have reconstructed : left = divisor * (left / divisor) + left % divisor :=
    (Division.mod_add_div left divisor).symm.trans (Nat.add_comm _ _)
  calc
    (left % divisor * right) % divisor =
        (divisor * (left / divisor * right) + left % divisor * right) % divisor :=
      (Remainder.mul_add_mod divisor (left / divisor * right) _).symm
    _ = (divisor * (left / divisor) * right + left % divisor * right) % divisor :=
      congrArg (fun value : Nat => (value + left % divisor * right) % divisor)
        (Multiplication.mul_assoc _ _ _).symm
    _ = ((divisor * (left / divisor) + left % divisor) * right) % divisor :=
      congrArg (fun value : Nat => value % divisor)
        (Multiplication.right_distrib _ _ _).symm
    _ = (left * right) % divisor :=
      congrArg (fun value : Nat => (value * right) % divisor) reconstructed.symm

/-- Reducing the second factor preserves the final natural remainder.

Commutativity puts that same reduced factor first. The retained original
quotient and the direct multiplication transport preserve the scalar product
and its final remainder, including the total zero-divisor case. -/
public theorem mul_mod_right (left right divisor : Nat) :
    (left * (right % divisor)) % divisor = (left * right) % divisor := by
  calc
    (left * (right % divisor)) % divisor = (right % divisor * left) % divisor :=
      congrArg (fun value : Nat => value % divisor) (Nat.mul_comm _ _)
    _ = (right * left) % divisor := mul_mod_left right left divisor
    _ = (left * right) % divisor :=
      congrArg (fun value : Nat => value % divisor) (Nat.mul_comm _ _)

end Purelib.Data.Nat.Remainder.Arithmetic
