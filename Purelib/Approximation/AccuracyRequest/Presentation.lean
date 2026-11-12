module

public import Purelib.Data.Presentation
public import Purelib.Approximation.AccuracyRequest

namespace Purelib.Approximation.AccuracyRequest.Presentation

open Purelib.Data.Rat

/-- An admissible accuracy tolerance is strictly positive. -/
@[expose] public def Valid (tolerance : Fraction.Rational) : Prop := 0 < tolerance

set_option genInjectivity false in
/-- The result of checking a rational accuracy tolerance. -/
public inductive Check (tolerance : Fraction.Rational) where
  /-- The tolerance is strictly positive. -/ | valid (positive : Valid tolerance)
  /-- The tolerance is zero or negative. -/ | nonpositive (nonpositive : tolerance ≤ 0)

/-- Check a tolerance using the original rational order decision. -/
@[expose] public def check (tolerance : Fraction.Rational) : Check tolerance :=
  if positive : 0 < tolerance then .valid positive else .nonpositive (le_of_not_gt positive)

/-- Decide admissibility using the same typed checker. -/
@[expose] public def recognize (tolerance : Fraction.Rational) : Decidable (Valid tolerance) :=
  match check tolerance with
  | .valid positive => .isTrue positive
  | .nonpositive nonpositive => .isFalse (not_lt_of_ge nonpositive)

/-- Decide whether a rational tolerance is admissible. -/
public instance (tolerance : Fraction.Rational) : Decidable (Valid tolerance) := recognize tolerance

/-- A rational tolerance with its positive accuracy certificate. -/
public abbrev Display := {tolerance : Fraction.Rational // Valid tolerance}

/-- Construct the original accuracy request from its accepted tolerance. -/
@[expose] public def read (display : Display) : AccuracyRequest :=
  ⟨display.val, display.property⟩

/-- Quote the retained tolerance and certificate of an original request. -/
@[expose] public def quote (request : AccuracyRequest) : Display :=
  ⟨request.tolerance, request.positive⟩

/-- Accepted tolerances represent the same request when their retained values agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare requests using the original request equality decision. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  match (inferInstance : Decidable (read left = read right)) with
  | .isTrue equal => .isTrue (congrArg AccuracyRequest.tolerance equal)
  | .isFalse unequal => .isFalse (fun equal => unequal
      (AccuracyRequest.eq_of_tolerance_eq (first := read left) (last := read right) equal))

/-- Reading a quoted request recovers the original request. -/
public theorem read_quote (request : AccuracyRequest) : read (quote request) = request :=
  AccuracyRequest.eq_of_tolerance_eq rfl

/-- Quoting a read tolerance recovers its original display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Display equality is exactly equality of the original accuracy requests. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    exact AccuracyRequest.eq_of_tolerance_eq (first := read left) (last := read right) equal
  · exact congrArg AccuracyRequest.tolerance

/-!
## Positive rational accuracy requests

The input is a canonical rational tolerance. `check` returns its strict
positivity proof or a proof that it is nonpositive. `read` and `quote` use the
original `AccuracyRequest`, with two round trips; `compare` uses the owner's
existing equality decision and `same_iff_read_eq` identifies its relation.
Rational order and equality are finite decisions inherited from their original
owners. The proof-system and native-runtime accounts remain separate.
-/
/-- The explicit presentation of original positive accuracy requests. -/
@[expose] public def accuracyRequest : Purelib.Data.Presentation Fraction.Rational where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Approximation.AccuracyRequest.Presentation
