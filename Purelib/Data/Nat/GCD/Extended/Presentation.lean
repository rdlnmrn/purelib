module

public import Purelib.Data.Presentation
public import Purelib.Data.Nat.GCD.Extended

namespace Purelib.Data.Nat.GCD.Extended.Presentation

/-- Every original finite result is an admissible triple of a natural and two integers. -/
@[expose] public def Valid (_ : Result) : Prop := True

/-- Recognize the original typed result without imposing an input-dependent claim. -/
@[expose] public def recognize (result : Result) : Decidable (Valid result) := .isTrue True.intro

/-- Two admissible triples are the same exactly when the original results are equal. -/
@[expose] public def Same (left right : {result : Result // Valid result}) : Prop :=
  left.val = right.val

/-- Compare the three retained fields using the original result equality decision. -/
@[expose] public def compare (left right : {result : Result // Valid result}) :
    Decidable (Same left right) := inferInstanceAs (Decidable (left.val = right.val))

/-- The unrestricted presentation of the original finite Euclidean result. -/
@[expose] public def result : Purelib.Data.Presentation Result where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- The Bézout equation and common divisibility for the specified input pair. -/
@[expose] public def Claim (leftInput rightInput : Nat) (value : Result) : Prop :=
  (value.gcd : Int) = value.left * (leftInput : Int) + value.right * (rightInput : Int) ∧
    value.gcd ∣ leftInput ∧ value.gcd ∣ rightInput

set_option genInjectivity false in
/-- The result of checking a proposed input-bound Euclidean claim. -/
public inductive Check (leftInput rightInput : Nat) (value : Result) where
  /-- The three finite conditions hold. -/
  | valid (proof : Claim leftInput rightInput value)
  /-- The displayed coefficients fail the Bézout equation. -/
  | wrongIdentity (proof : (value.gcd : Int) ≠
      value.left * (leftInput : Int) + value.right * (rightInput : Int))
  /-- The displayed divisor does not divide the left input. -/
  | notLeftDivisor (proof : ¬ value.gcd ∣ leftInput)
  /-- The displayed divisor does not divide the right input. -/
  | notRightDivisor (proof : ¬ value.gcd ∣ rightInput)

/-- Check the equation and both divisibility conditions in order. -/
@[expose] public def check (leftInput rightInput : Nat) (value : Result) :
    Check leftInput rightInput value :=
  if identity : (value.gcd : Int) =
      value.left * (leftInput : Int) + value.right * (rightInput : Int) then
    if left : value.gcd ∣ leftInput then
      if right : value.gcd ∣ rightInput then .valid ⟨identity, left, right⟩
      else .notRightDivisor right
    else .notLeftDivisor left
  else .wrongIdentity identity

/-- Decide the input-bound claim using the same typed checker. -/
@[expose] public def recognizeClaim (leftInput rightInput : Nat) (value : Result) :
    Decidable (Claim leftInput rightInput value) :=
  match check leftInput rightInput value with
  | .valid proof => .isTrue proof
  | .wrongIdentity proof => .isFalse (fun claim => proof claim.1)
  | .notLeftDivisor proof => .isFalse (fun claim => proof claim.2.1)
  | .notRightDivisor proof => .isFalse (fun claim => proof claim.2.2)

/-- The original extended Euclidean computation satisfies its input-bound claim. -/
public theorem computed_claim (leftInput rightInput : Nat) :
    Claim leftInput rightInput (compute leftInput rightInput) :=
  compute_spec leftInput rightInput

/-!
`Result` itself is the finite triple, and every such triple is admissible.
Its original `DecidableEq` compares the natural gcd field and both integer
coefficients; this does not assert an input-dependent mathematical property.
`check` separately decides the Bézout equation and divisibility of each input,
retaining a proof for success or for the particular failed condition. The
existing `compute_spec` proves `computed_claim` for every input pair. The
claimed equation and divisibility imply the usual greatest-common-divisor
property, but equality of two results retains the coefficients as well as the
gcd field. The finite recursive arithmetic decisions use existing owners;
proof-system, construction-admission and native-runtime accounts are separate.
-/

end Purelib.Data.Nat.GCD.Extended.Presentation
