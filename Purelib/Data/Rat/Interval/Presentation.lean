module

public import Purelib.Data.Presentation
public import Purelib.Data.Rat.Interval.Basic

namespace Purelib.Data.Rat.Interval.Presentation

open Purelib.Data.Rat.Fraction.Order

/-- A pair of endpoints presents an interval when they are ordered. -/
@[expose] public def Valid (endpoints : Fraction.Rational × Fraction.Rational) : Prop :=
  endpoints.1 ≤ endpoints.2

set_option genInjectivity false in
/-- The result of checking the endpoint order of a proposed interval. -/
public inductive Check (endpoints : Fraction.Rational × Fraction.Rational) where
  /-- The endpoints are ordered. -/ | valid (ordered : Valid endpoints)
  /-- The proposed upper endpoint is strictly below the lower endpoint. -/
  | reversed (reversed : endpoints.2 < endpoints.1)

/-- Check endpoint order using rational comparison. -/
@[expose] public def check (endpoints : Fraction.Rational × Fraction.Rational) : Check endpoints :=
  if ordered : endpoints.1 ≤ endpoints.2 then .valid ordered else .reversed (lt_of_not_ge ordered)

/-- Decide admissibility using the typed checker. -/
@[expose] public def recognize (endpoints : Fraction.Rational × Fraction.Rational) :
    Decidable (Valid endpoints) :=
  match check endpoints with
  | .valid ordered => .isTrue ordered
  | .reversed reversed => .isFalse (not_le_of_gt reversed)

/-- Decide whether an endpoint pair is admissible. -/
public instance (endpoints : Fraction.Rational × Fraction.Rational) : Decidable (Valid endpoints) :=
  recognize endpoints

/-- An ordered pair of rational endpoints. -/
public abbrev Display := {endpoints : Fraction.Rational × Fraction.Rational // Valid endpoints}

/-- Construct the original rational interval with the supplied endpoint certificate. -/
@[expose] public def read (display : Display) : Interval :=
  ⟨display.val.1, display.val.2, display.property⟩

/-- Quote an interval's retained endpoints and order certificate. -/
@[expose] public def quote (bound : Interval) : Display :=
  ⟨(bound.lower, bound.upper), bound.valid⟩

/-- Two displays are the same when both retained endpoints agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the retained rational endpoint pairs. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Reading a quoted interval recovers the original interval. -/
public theorem read_quote (bound : Interval) : read (quote bound) = bound :=
  Interval.ext rfl rfl

/-- Quoting an interval constructed from a display recovers that display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  cases display with
  | mk endpoints ordered =>
    cases endpoints
    rfl

/-- Display equality is exactly equality of the original intervals. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    exact Interval.ext (congrArg Prod.fst equal) (congrArg Prod.snd equal)
  · intro equal
    exact Prod.ext (congrArg Interval.lower equal) (congrArg Interval.upper equal)

/-!
## Rational interval displays

The input is an ordered pair of canonical rational endpoints. `check` returns
an order proof or a proof of reversed order, including the singleton case.
`read` constructs the original interval and `quote` projects its retained
endpoints; `read_quote` and `quote_read` prove both round trips. `compare`
decides endpoint equality, which `same_iff_read_eq` identifies with original
interval equality using proof irrelevance. The rational comparisons terminate
through their original finite decisions. Proof-system and native-runtime
certification are separate obligations.
-/
/-- The explicit presentation of original rational intervals. -/
@[expose] public def interval : Purelib.Data.Presentation (Fraction.Rational × Fraction.Rational) where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

namespace Bounds

/-!
`Interval.Bounds` is the distinct nominal owner consumed by rational
bisection, including the pi integral midpoint. Its finite presentation uses
the same endpoint `check`, `recognize`, `Same` and `compare` above: no second
order scan is needed. The readback and quotation below preserve this owner,
and proof irrelevance makes endpoint identity independent of the order proof.
The midpoint computation and its dependencies remain in `Interval.Bisection`;
these laws do not certify its native execution or the supplied proof system.
-/

/-- Construct the original midpoint-bounds owner from checked endpoints. -/
@[expose] public def read (display : Display) : Interval.Bounds :=
  ⟨display.val.1, display.val.2, display.property⟩

/-- Quote the retained endpoints and order evidence of midpoint bounds. -/
@[expose] public def quote (bounds : Interval.Bounds) : Display :=
  ⟨(bounds.lower, bounds.upper), bounds.valid⟩

/-- Reading quoted bounds recovers the original owner, independently of proof text. -/
public theorem read_quote (bounds : Interval.Bounds) : read (quote bounds) = bounds := by
  cases bounds
  rfl

/-- Quoting bounds constructed from a display recovers that display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  cases display with
  | mk endpoints ordered =>
    cases endpoints
    rfl

/-- Endpoint comparison decides equality of the original bounds. -/
public theorem same_iff_read_eq (left right : Display) :
    Same left right ↔ read left = read right := by
  constructor
  · intro equal
    cases left with
    | mk left orderedLeft =>
      cases right with
      | mk right orderedRight =>
        cases equal
        rfl
  · intro equal
    exact Prod.ext (congrArg Interval.Bounds.lower equal) (congrArg Interval.Bounds.upper equal)

end Bounds

end Purelib.Data.Rat.Interval.Presentation
