module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Omega.LinearCombination.Presentation
import Purelib.Tactic.Omega.Constraint.Presentation
import Purelib.Tactic.Omega.Coefficients
meta import Purelib.Tactic.Omega.LinearCombination.Presentation
meta import Purelib.Tactic.Omega.Constraint.Presentation

/-!
# Omega reconstruction regressions

These proofs exercise natural and integer comparisons, constant scaling and
original affine equality hypotheses. Kernel checking and the authoritative
axiom audit verify the reconstructed certificates, including quantified inputs.
-/

namespace TestPurelib.Tactic.Omega

open Lean.Omega
open Purelib.Tactic.Omega.LinearCombination

private def emptyDisplay : Presentation.Display := ⟨(3, []), True.intro⟩

private def zeroDisplay : Presentation.Display := ⟨(3, [0]), True.intro⟩

example (combination : LinearCombo) : Presentation.read (Presentation.quote combination) = combination :=
  Presentation.read_quote combination

example (code : Presentation.Code) : Presentation.quote (Presentation.read code) = code :=
  Presentation.quote_read code

example : ¬ Presentation.Same emptyDisplay zeroDisplay := by
  intro equal
  have fields := (Presentation.same_iff_fields emptyDisplay zeroDisplay).mp equal
  cases fields.2

example (values : Coeffs) :
    (Presentation.read emptyDisplay.val).eval values = (Presentation.read zeroDisplay.val).eval values := by
  have zeroEntries : Coeffs.isZero [0] := by
    intro value member
    cases member with
    | head => rfl
    | tail _ member => cases member
  have zeroDot := Purelib.Tactic.Omega.Coefficients.intList_dot_of_left_zero [0] values zeroEntries
  change (3 : Int) + IntList.dot [] values = 3 + IntList.dot [0] values
  rw [zeroDot]
  rfl

/-- info: (true, true) -/
#guard_msgs in
#eval ((match Presentation.compare emptyDisplay emptyDisplay with
    | .isTrue _ => true | .isFalse _ => false),
  (match Presentation.compare emptyDisplay zeroDisplay with
    | .isTrue _ => false | .isFalse _ => true))

namespace ConstraintCases

open Purelib.Tactic.Omega.Constraint.Presentation

private def unbounded : Display := ⟨(none, none), True.intro⟩

private def exactTwo : Display := ⟨(some 2, some 2), True.intro⟩

private def inconsistent : Display := ⟨(some 2, some 1), True.intro⟩

example (constraint : Lean.Omega.Constraint) : read (quote constraint) = constraint := read_quote constraint

example (code : Code) : quote (read code) = code := quote_read code

example : Valid (some 2, some 1) := True.intro

example : ¬ Same unbounded exactTwo := by
  intro equal
  have bounds := (same_iff_fields unbounded exactTwo).mp equal
  cases bounds.1

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (((read unbounded.val).sat 2), ((read exactTwo.val).sat 2),
  !(read exactTwo.val).sat 3, !(read inconsistent.val).sat 0,
  (match compare unbounded unbounded with | .isTrue _ => true | .isFalse _ => false),
  (match compare unbounded exactTwo with | .isTrue _ => false | .isFalse _ => true))

end ConstraintCases

/-- A separated natural bound implies a strict comparison.

The supplied gap exercises natural-to-integer preprocessing and constant
normalization while retaining both original natural operands. -/
public theorem omega_nat_regression (left right : Nat)
    (separated : left + 2 ≤ right) : left < right := by
  omega0

/-- The two incompatible integer inequalities are rejected constructively.

Both hypotheses constrain the same affine evaluation of the original integer
operands, exercising coefficient scaling and linear combination. -/
public theorem omega_int_regression (left right : Int)
    (first : 2 * left + right ≤ 3)
    (second : 4 ≤ 2 * left + right) : False := by
  omega0

/-- An exact integer affine value excludes a strictly larger lower bound.

The universally quantified operands and retained equality exercise equality
constraint reconstruction alongside the original inequality certificate. -/
private theorem integer_affine_equality : ∀ left right : Int,
    left + right = 3 → 4 ≤ left + right → False := by
  intro left right exactValue lowerBound
  omega0

/-- An exact natural affine value excludes a strictly smaller upper bound.

The retained equality and comparison share the original quantified operands.
The natural preprocessing and affine equality certificates must agree. -/
private theorem natural_affine_equality : ∀ left right : Nat,
    left + 2 = right → right < left + 2 → False := by
  intro left right exactValue upperBound
  omega0

/-- Opposite integer bounds exclude a retained disequality.

Weak bounds on the same quantified operands force equality. Reconstruction
must preserve the disequality split and both original comparison witnesses. -/
private theorem integer_disequality : ∀ left right : Int,
    left ≤ right → right ≤ left → left ≠ right → False := by
  intro left right forward backward distinct
  omega0

/-- Every original integer lies below its positive quotient multiple plus 64.

The quantified input has no sign restriction and its original quotient operation
is retained. The frontend must reconstruct the positive divisor certificate. -/
private theorem upper : ∀ numerator : Int, numerator < 64 * (numerator / 64) + 64 := by
  intro numerator
  omega0

/-- The positive quotient multiple bounds every quantified original integer below.

Negative and nonnegative inputs retain the same original Euclidean quotient.
The frontend must reconstruct its original lower-bound proposition. -/
private theorem lower : ∀ numerator : Int, 64 * (numerator / 64) ≤ numerator := by
  intro numerator
  omega0

/-- Every quantified original remainder retains its positive-divisor reconstruction.

The complete equality uses the denominator on the left of the quotient product,
matching the original certificate type and the frontend's exact comparison. -/
private theorem remainder : ∀ numerator : Int,
    numerator % 64 = numerator - 64 * (numerator / 64) := by
  intro numerator
  omega0

/-- A quantified truncated natural difference has the same bounded quotient interval.

The original natural subtraction forces its constructive dichotomy into the
proof. Division then retains the same original cast dividend in each branch. -/
private theorem subtraction : ∀ left right : Nat,
    (((left - right : Nat) : Int)) <
      64 * ((((left - right : Nat) : Int)) / 64) + 64 := by
  intro left right
  omega0

/-- Eleven retained variables preserve the final coordinate of their finite valuation.

The original scalar equations reconstruct its final quotient bound without
changing variable order or introducing a generic extensional lookup law. -/
private theorem large_valuation : ∀ value lowQuotient lowRemainder middleQuotient
    middleRemainder highQuotient highRemainder highMiddleQuotient highMiddleRemainder
    topQuotient topRemainder : Nat,
    value < 0x110000 → lowRemainder + 64 * lowQuotient = value →
    middleRemainder + 64 * middleQuotient = lowQuotient →
    highRemainder + 4096 * highQuotient = value →
    highMiddleRemainder + 64 * highMiddleQuotient = highQuotient →
    topRemainder + 262144 * topQuotient = value →
    lowRemainder < 64 → middleRemainder < 64 → highRemainder < 4096 →
    highMiddleRemainder < 64 → topRemainder < 262144 → topQuotient < 8 := by
  intro value lowQuotient lowRemainder middleQuotient middleRemainder highQuotient
    highRemainder highMiddleQuotient highMiddleRemainder topQuotient topRemainder
    bound low middle high highMiddle top lowBound middleBound highBound highMiddleBound topBound
  omega0

end TestPurelib.Tactic.Omega
