module

import Purelib.Data.Nat.GCD.Scalar
import Init.Data.Nat.Gcd
import Init.Prelude

/-!
# Native scalar Euclidean regression

The compiled checks compare the actual scalar gcd entry point with its original
sufficient-fuel recurrence and independent expected values. Large operands are
retained across aliasing, zero, coprime and common-factor calls; the last pair
contains consecutive Fibonacci numbers with a long Euclidean remainder chain.
-/

namespace TestPurelib.Data.Nat.GCD

open Purelib.Data.Nat.GCD

/-- Compare native gcd with the original recurrence and the independently stated result.

The selected Core implementation is also retained directly, so its logical model
belongs to the checked dependency closure alongside the independent recurrence.
-/
@[noinline] private def check (left right expected : Nat) : Bool :=
  let actual := Scalar.gcd left right
  let original := Scalar.gcdAux (right + 1) left right
  let implementation := _root_.Nat.gcd left right
  actual == original && implementation == original && actual == expected

/-- Exercise zero, retained shared big integers, large coprimes and a long remainder chain.

The same 4097-bit operand is passed in both positions, aliased to itself and
reused afterwards. Its final difference from the independent base also checks
that later arithmetic can still consume the original retained value.
-/
public def compiledRegressionPassed : Bool :=
  let base : Nat := 2 ^ 4096
  let shared := base + 37
  let common := base + 1
  let fibonacciLeft : Nat :=
    44893845313309942978077298160660626646181883623886239791269694466661322268805744081870933775586567858979269
  let fibonacciRight : Nat :=
    72639767602615659833415769076743441675530755653534070653184546540063470576806357692953027861477736726533858
  check 0 0 0 &&
    check 0 37 37 &&
    check 37 0 37 &&
    check 1071 462 21 &&
    check shared 0 shared &&
    check 0 shared shared &&
    check shared shared shared &&
    check shared 1 1 &&
    check 1 shared 1 &&
    check shared (shared + 1) 1 &&
    check (shared + 1) shared 1 &&
    check (3 * common) (5 * common) common &&
    check (5 * common) (3 * common) common &&
    check fibonacciLeft fibonacciRight 1 &&
    check fibonacciRight fibonacciLeft 1 &&
    check (shared - base) 37 37

end TestPurelib.Data.Nat.GCD
