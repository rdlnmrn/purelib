module

public import Purelib.Data.Presentation
public import Purelib.Integration.Partition.Ownership

/-! Finite proposed-data presentations of original point and interval owners. -/

namespace Purelib.Integration.Partition.Ownership.PointOwner.Presentation

open Purelib.Data.Rat

/-- A proposed original occurrence index and its exact parent interval. -/
public abbrev Code := Nat × Interval

/-- A proposal is valid when lookup and both half-open bounds hold. -/
@[expose] public def Valid (intervals : List Interval) (point : Fraction.Rational) (code : Code) : Prop :=
  Purelib.Data.List.getElem? intervals code.1 = some code.2 ∧
    code.2.start ≤ point ∧ point < code.2.finish

set_option genInjectivity false in
/-- The first invalid condition or a proof that the proposal is an owner. -/
public inductive Check (intervals : List Interval) (point : Fraction.Rational) (code : Code) where
  /-- The original list has no occurrence at the proposed index. -/
  | outOfRange (lookup : Purelib.Data.List.getElem? intervals code.1 = none)
  /-- The occurrence exists but its parent differs from the proposal. -/
  | wrongParent (actual : Interval) (lookup : Purelib.Data.List.getElem? intervals code.1 = some actual)
      (different : actual ≠ code.2)
  /-- The point is below the proposed parent's start. -/
  | beforeStart (invalid : ¬ code.2.start ≤ point)
  /-- The point is not strictly below the proposed parent's finish. -/
  | atOrBeyondFinish (invalid : ¬ point < code.2.finish)
  /-- Lookup and half-open containment all hold. -/
  | accepted (valid : Valid intervals point code)

/-- Check the original finite lookup, parent identity and half-open bounds in order. -/
@[expose] public def check (intervals : List Interval) (point : Fraction.Rational) (code : Code) :
    Check intervals point code :=
  match lookup : Purelib.Data.List.getElem? intervals code.1 with
  | none => .outOfRange lookup
  | some actual =>
    if equal : actual = code.2 then
      if lower : code.2.start ≤ point then
        if upper : point < code.2.finish then
          .accepted ⟨lookup.trans (congrArg some equal), lower, upper⟩
        else .atOrBeyondFinish upper
      else .beforeStart lower
    else .wrongParent actual lookup equal

/-- Decide validity from the same typed checker. -/
@[expose] public def recognize (intervals : List Interval) (point : Fraction.Rational) (code : Code) :
    Decidable (Valid intervals point code) :=
  match check intervals point code with
  | .outOfRange lookup => .isFalse (fun valid => by cases lookup.symm.trans valid.1)
  | .wrongParent _ lookup different => .isFalse (fun valid =>
      different (Option.some.inj (lookup.symm.trans valid.1)))
  | .beforeStart invalid => .isFalse (fun valid => invalid valid.2.1)
  | .atOrBeyondFinish invalid => .isFalse (fun valid => invalid valid.2.2)
  | .accepted valid => .isTrue valid

/-- A checked finite proposal for an owner of the supplied point. -/
public abbrev Display (intervals : List Interval) (point : Fraction.Rational) :=
  {code : Code // Valid intervals point code}

/-- Read a valid proposal into the original indexed owner. -/
@[expose] public def read {intervals : List Interval} {point : Fraction.Rational}
    (display : Display intervals point) : PointOwner intervals point :=
  ⟨display.val.1, display.val.2, display.property.1, display.property.2.1, display.property.2.2⟩

/-- Quote the original index, parent and certificates without scanning the list. -/
@[expose] public def quote {intervals : List Interval} {point : Fraction.Rational}
    (owner : PointOwner intervals point) : Display intervals point :=
  ⟨(owner.index, owner.parent), owner.at_index, owner.start_le, owner.point_lt_finish⟩

/-- Reading an original owner's quotation recovers that owner. -/
public theorem read_quote {intervals : List Interval} {point : Fraction.Rational}
    (owner : PointOwner intervals point) : read (quote owner) = owner := by
  apply PointOwner.eq_of_index_eq
  rfl

/-- Quoting an accepted proposal recovers its exact proposed index and parent. -/
public theorem quote_read {intervals : List Interval} {point : Fraction.Rational}
    (display : Display intervals point) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Accepted proposals represent the same original owner when their occurrence indices agree. -/
@[expose] public def Same {intervals : List Interval} {point : Fraction.Rational}
    (first second : Display intervals point) : Prop := first.val.1 = second.val.1

/-- Compare the retained occurrence indices. -/
@[expose] public def compare {intervals : List Interval} {point : Fraction.Rational}
    (first second : Display intervals point) : Decidable (Same first second) := inferInstanceAs
  (Decidable (first.val.1 = second.val.1))

/-- Presentation equality agrees exactly with equality of original owners. -/
public theorem same_iff_read_eq {intervals : List Interval} {point : Fraction.Rational}
    (first second : Display intervals point) : Same first second ↔ read first = read second := by
  constructor
  · intro same
    apply PointOwner.eq_of_index_eq
    exact same
  · intro equal
    exact congrArg PointOwner.index equal

/-- The explicit finite presentation for owners of a point in an original interval list. -/
@[expose] public def presentation (intervals : List Interval) (point : Fraction.Rational) :
    Purelib.Data.Presentation Code where
  Valid := Valid intervals point
  recognize := recognize intervals point
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

end Purelib.Integration.Partition.Ownership.PointOwner.Presentation

namespace Purelib.Integration.Partition.Ownership.IntervalOwner.Presentation

open Purelib.Data.Rat

/-- A proposed original occurrence index and its exact parent interval. -/
public abbrev Code := Nat × Interval

/-- A proposal is valid when lookup and both closed bounds hold. -/
@[expose] public def Valid (intervals : List Interval) (child : Interval) (code : Code) : Prop :=
  Purelib.Data.List.getElem? intervals code.1 = some code.2 ∧
    code.2.start ≤ child.start ∧ child.finish ≤ code.2.finish

set_option genInjectivity false in
/-- The first invalid condition or a proof that the proposal is an owner. -/
public inductive Check (intervals : List Interval) (child : Interval) (code : Code) where
  /-- The original list has no occurrence at the proposed index. -/
  | outOfRange (lookup : Purelib.Data.List.getElem? intervals code.1 = none)
  /-- The occurrence exists but its parent differs from the proposal. -/
  | wrongParent (actual : Interval) (lookup : Purelib.Data.List.getElem? intervals code.1 = some actual)
      (different : actual ≠ code.2)
  /-- The child's start is below the proposed parent's start. -/
  | beforeStart (invalid : ¬ code.2.start ≤ child.start)
  /-- The child's finish is not at most the proposed parent's finish. -/
  | afterFinish (invalid : ¬ child.finish ≤ code.2.finish)
  /-- Lookup and closed containment all hold. -/
  | accepted (valid : Valid intervals child code)

/-- Check the original finite lookup, parent identity and closed bounds in order. -/
@[expose] public def check (intervals : List Interval) (child : Interval) (code : Code) :
    Check intervals child code :=
  match lookup : Purelib.Data.List.getElem? intervals code.1 with
  | none => .outOfRange lookup
  | some actual =>
    if equal : actual = code.2 then
      if lower : code.2.start ≤ child.start then
        if upper : child.finish ≤ code.2.finish then
          .accepted ⟨lookup.trans (congrArg some equal), lower, upper⟩
        else .afterFinish upper
      else .beforeStart lower
    else .wrongParent actual lookup equal

/-- Decide validity from the same typed checker. -/
@[expose] public def recognize (intervals : List Interval) (child : Interval) (code : Code) :
    Decidable (Valid intervals child code) :=
  match check intervals child code with
  | .outOfRange lookup => .isFalse (fun valid => by cases lookup.symm.trans valid.1)
  | .wrongParent _ lookup different => .isFalse (fun valid =>
      different (Option.some.inj (lookup.symm.trans valid.1)))
  | .beforeStart invalid => .isFalse (fun valid => invalid valid.2.1)
  | .afterFinish invalid => .isFalse (fun valid => invalid valid.2.2)
  | .accepted valid => .isTrue valid

/-- A checked finite proposal for an owner of the supplied child interval. -/
public abbrev Display (intervals : List Interval) (child : Interval) :=
  {code : Code // Valid intervals child code}

/-- Read a valid proposal into the original indexed owner. -/
@[expose] public def read {intervals : List Interval} {child : Interval}
    (display : Display intervals child) : IntervalOwner intervals child :=
  ⟨display.val.1, display.val.2, display.property.1, display.property.2.1, display.property.2.2⟩

/-- Quote the original index, parent and certificates without scanning the list. -/
@[expose] public def quote {intervals : List Interval} {child : Interval}
    (owner : IntervalOwner intervals child) : Display intervals child :=
  ⟨(owner.index, owner.parent), owner.at_index, owner.start_le, owner.finish_le⟩

/-- Reading an original owner's quotation recovers that owner. -/
public theorem read_quote {intervals : List Interval} {child : Interval}
    (owner : IntervalOwner intervals child) : read (quote owner) = owner := by
  apply IntervalOwner.eq_of_index_eq
  rfl

/-- Quoting an accepted proposal recovers its exact proposed index and parent. -/
public theorem quote_read {intervals : List Interval} {child : Interval}
    (display : Display intervals child) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Accepted proposals represent the same original owner when their occurrence indices agree. -/
@[expose] public def Same {intervals : List Interval} {child : Interval}
    (first second : Display intervals child) : Prop := first.val.1 = second.val.1

/-- Compare the retained occurrence indices. -/
@[expose] public def compare {intervals : List Interval} {child : Interval}
    (first second : Display intervals child) : Decidable (Same first second) := inferInstanceAs
  (Decidable (first.val.1 = second.val.1))

/-- Presentation equality agrees exactly with equality of original owners. -/
public theorem same_iff_read_eq {intervals : List Interval} {child : Interval}
    (first second : Display intervals child) : Same first second ↔ read first = read second := by
  constructor
  · intro same
    apply IntervalOwner.eq_of_index_eq
    exact same
  · intro equal
    exact congrArg IntervalOwner.index equal

/-- The explicit finite presentation for owners of a child interval in an original interval list. -/
@[expose] public def presentation (intervals : List Interval) (child : Interval) :
    Purelib.Data.Presentation Code where
  Valid := Valid intervals child
  recognize := recognize intervals child
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

end Purelib.Integration.Partition.Ownership.IntervalOwner.Presentation
