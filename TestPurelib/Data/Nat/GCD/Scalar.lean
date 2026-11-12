module

import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.Coprime.Presentation
meta import Purelib.Data.Nat.Coprime.Presentation
import Purelib.Data.Nat.GCD.Extended.Presentation
meta import Purelib.Data.Nat.GCD.Extended.Presentation
import Purelib.System.IO
import Init.Data.List.Control
import Init.System.IO
import Init.System.IOError

namespace TestPurelib.Data.Nat.GCD.Scalar

open Purelib.Data.Nat
open Purelib.Data.Nat.GCD
open Purelib.Data.Nat.GCD.Scalar (gcd reduceAux gcdAux gcd_eq_gcdAux gcd_eq_reduceAux)

example (left right : Nat) :
    Extended.Presentation.Claim left right (Extended.compute left right) :=
  Extended.Presentation.computed_claim left right

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval ((match Extended.Presentation.check 6 9 (Extended.compute 6 9) with
    | .valid _ => true | _ => false),
  (match Extended.Presentation.check 6 9 ⟨1, 0, 0⟩ with
    | .wrongIdentity _ => true | _ => false),
  (match Extended.Presentation.check 4 7 ⟨3, -1, 1⟩ with
    | .notLeftDivisor _ => true | _ => false),
  (match Extended.Presentation.check 4 3 ⟨2, -1, 2⟩ with
    | .notRightDivisor _ => true | _ => false),
  (match Extended.Presentation.recognize ⟨1, 0, 0⟩ with
    | .isTrue _ => true | .isFalse _ => false),
  (match Extended.Presentation.compare ⟨⟨1, 0, 0⟩, True.intro⟩
      ⟨⟨1, 1, 0⟩, True.intro⟩ with
    | .isFalse _ => true | .isTrue _ => false))

private def twoFive : Coprime.Presentation.Display 2 5 :=
  ⟨(-2, 1), by
    change (-2 : Int) * 2 + 1 * 5 = 1
    decide +kernel⟩

private def otherTwoFive : Coprime.Presentation.Display 2 5 :=
  ⟨(3, -1), by
    change (3 : Int) * 2 + (-1) * 5 = 1
    decide +kernel⟩

example : 2 ∣ 6 := by
  apply (Coprime.Presentation.read twoFive).dvd_of_dvd_mul_right
  exact ⟨15, by decide +kernel⟩

example (first second : Coprime.Presentation.Valid 2 5 (-2, 1)) :
    Coprime.Presentation.read ⟨(-2, 1), first⟩ =
      Coprime.Presentation.read ⟨(-2, 1), second⟩ := rfl

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval ((match Coprime.Presentation.check 2 5 (-2, 1) with
    | .valid _ => true | .invalid _ => false),
  (match Coprime.Presentation.check 2 5 (0, 0) with
    | .invalid _ => true | .valid _ => false),
  (match Coprime.Presentation.compare twoFive (Coprime.Presentation.quote (Coprime.Presentation.read twoFive)) with
    | .isTrue _ => true | .isFalse _ => false),
  (match Coprime.Presentation.compare twoFive otherTwoFive with
    | .isFalse _ => true | .isTrue _ => false),
  (match Coprime.Presentation.check 2 7 (-2, 1) with
    | .invalid _ => true | .valid _ => false))

example (left right : Nat) :
    gcd left right = reduceAux (2 * BitWidth.natWidth right + 1) left right :=
  gcd_eq_reduceAux left right

example (left right : Nat) : gcd left right = gcdAux (right + 1) left right :=
  gcd_eq_gcdAux left right

/-- Evaluate the original retained-right Euclidean loop independently of the native gcd entry. -/
@[noinline] private def original (left right : Nat) : Nat :=
  reduceAux (2 * BitWidth.natWidth right + 1) left right

/-- Read one native gcd through an opaque IO boundary while retaining both input values. -/
@[noinline] private def observe (left right : Nat) : IO Nat := pure (gcd left right)

/-- Compare native and original results in both orders, then reuse the original arguments again. -/
private def checkPair (left right : Nat) : IO Unit := do
  let expected := original left right
  let actual ← observe left right
  unless actual == expected do
    throw (IO.userError "native gcd changed the original Euclidean result")
  let reversed ← observe right left
  unless reversed == original right left do
    throw (IO.userError "native gcd changed the reversed original result")
  let repeated ← observe left right
  unless repeated == expected do
    throw (IO.userError "native gcd failed while reusing its retained inputs")

/-- Check zero, unit, common factors, word boundaries and aliased inputs against the original finite evaluator.

The displayed larger pairs have at most 4096 bits. Repeated and equal-input
calls retain their original natural values across each native borrowed call.
-/
public def check : IO Unit := do
  let small : List (Nat × Nat) :=
    [(0, 0), (0, 1), (1, 0), (1, 1), (0, 37), (37, 0), (1, 1071), (1071, 1),
      (1071, 462), (462, 1071), (54, 24), (37 * 462, 37 * 1071)]
  for pair in small do checkPair pair.1 pair.2
  for width in [62, 63, 64, 127, 256, 1024, 2048, 4093] do
    let power := 2 ^ width
    for pair in [(0, power + 1), (power + 1, 0), (power, power + 1),
        (power - 1, power + 1), (3 * (power + 1), 5 * (power + 1))] do
      checkPair pair.1 pair.2
    checkPair power power
    let aliased := power + 19
    checkPair aliased aliased
  checkPair (2 ^ 2048 + 2 ^ 1024 + 37) (3 ^ 1280 + 17)
  Purelib.System.IO.println
    "Scalar gcd: zero, unit, common-factor, word-boundary, large and reused/aliased inputs matched original Euclid."

end TestPurelib.Data.Nat.GCD.Scalar
