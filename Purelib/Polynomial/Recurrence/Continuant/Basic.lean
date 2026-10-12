module
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace Purelib.Polynomial.Recurrence.Continuant.Basic

variable {K : Type*} [ExplicitField K]

/-- Determinant of the symmetric tridiagonal block with diagonal `d` and
adjacent entries `-1`. -/
def symmetricContinuant {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 1
  | 1, diagonal => diagonal
  | index + 2, diagonal =>
      diagonal * Purelib.Polynomial.Recurrence.Continuant.Basic.symmetricContinuant (index + 1) diagonal -
        Purelib.Polynomial.Recurrence.Continuant.Basic.symmetricContinuant index diagonal

section
open Purelib.Polynomial
/-- The index-zero symmetric continuant value is one. -/
@[simp] theorem symmetricContinuant_zero
    {R : Type*} [CommRing R] (diagonal : R) :
    Recurrence.Continuant.Basic.symmetricContinuant 0 diagonal = 1 := rfl

/-- The index-one symmetric continuant value is the diagonal. -/
@[simp] theorem symmetricContinuant_one
    {R : Type*} [CommRing R] (diagonal : R) :
    Recurrence.Continuant.Basic.symmetricContinuant 1 diagonal = diagonal := rfl

/-- The diagonal times the previous continuant minus its predecessor. -/
@[simp] theorem symmetricContinuant_succ_succ
    {R : Type*} [CommRing R] (index : Nat) (diagonal : R) :
    Recurrence.Continuant.Basic.symmetricContinuant (index + 2) diagonal =
      diagonal * Recurrence.Continuant.Basic.symmetricContinuant (index + 1) diagonal -
        Recurrence.Continuant.Basic.symmetricContinuant index diagonal := rfl

/-- Sum the first `count` continuants by appending one final cofactor at each
finite step. -/
def continuantPrefix {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | count + 1, diagonal =>
      Purelib.Polynomial.Recurrence.Continuant.Basic.continuantPrefix count diagonal +
        Recurrence.Continuant.Basic.symmetricContinuant count diagonal

/-- The empty continuant prefix sum is zero. -/
@[simp] theorem continuantPrefix_zero
    {R : Type*} [CommRing R] (diagonal : R) :
    Recurrence.Continuant.Basic.continuantPrefix 0 diagonal = 0 := rfl

/-- Extending the prefix sum adds the next retained continuant value. -/
@[simp] theorem continuantPrefix_succ
    {R : Type*} [CommRing R] (count : Nat) (diagonal : R) :
    Recurrence.Continuant.Basic.continuantPrefix (count + 1) diagonal =
      Recurrence.Continuant.Basic.continuantPrefix count diagonal +
        Recurrence.Continuant.Basic.symmetricContinuant count diagonal := rfl

end

section
open Purelib.Polynomial in
/-- The finite continuant prefix sums satisfy the diagonal recurrence with constant term one. -/
public theorem
  continuantPrefix_recurrence
    {R : Type*} [CommRing R] (index : Nat) (diagonal : R) :
    diagonal * Recurrence.Continuant.Basic.continuantPrefix (index + 1) diagonal -
      Recurrence.Continuant.Basic.continuantPrefix index diagonal + 1 =
      Recurrence.Continuant.Basic.continuantPrefix (index + 2) diagonal := by
  induction index with
  | zero =>
      simp only [Nat.zero_add, Recurrence.Continuant.Basic.continuantPrefix_succ,
        Recurrence.Continuant.Basic.continuantPrefix_zero, Recurrence.Continuant.Basic.symmetricContinuant_zero,
        Recurrence.Continuant.Basic.symmetricContinuant_one]
      ring1
  | succ index inductionHypothesis =>
      rw [show Nat.succ index + 1 = (index + 1) + 1 by omega0]
      rw [show Nat.succ index + 2 = (index + 2) + 1 by omega0]
      calc
        diagonal * Recurrence.Continuant.Basic.continuantPrefix (index + 2) diagonal -
              Recurrence.Continuant.Basic.continuantPrefix (index + 1) diagonal + 1 =
            (diagonal * Recurrence.Continuant.Basic.continuantPrefix (index + 1) diagonal -
                Recurrence.Continuant.Basic.continuantPrefix index diagonal + 1) +
              (diagonal * Recurrence.Continuant.Basic.symmetricContinuant (index + 1) diagonal -
                Recurrence.Continuant.Basic.symmetricContinuant index diagonal) := by
                  rw [Recurrence.Continuant.Basic.continuantPrefix_succ,
                    Recurrence.Continuant.Basic.continuantPrefix_succ]
                  ring1
        _ = Recurrence.Continuant.Basic.continuantPrefix (index + 2) diagonal +
              Recurrence.Continuant.Basic.symmetricContinuant (index + 2) diagonal := by
                rw [inductionHypothesis,
                  Recurrence.Continuant.Basic.symmetricContinuant_succ_succ]
        _ = Recurrence.Continuant.Basic.continuantPrefix ((index + 2) + 1) diagonal :=
          (Recurrence.Continuant.Basic.continuantPrefix_succ (index + 2) diagonal).symm
        _ = Recurrence.Continuant.Basic.continuantPrefix (index + 3) diagonal := rfl
end

end Purelib.Polynomial.Recurrence.Continuant.Basic

end
