module

public import Purelib.Integration.Partition.Unit.Common
public import Purelib.Integration.Partition.Ownership.Presentation

namespace Purelib.Integration.Partition.Unit.Common.CommonEntry.Presentation

open Purelib.Integration.Partition
open Purelib.Integration.Partition.Ownership

/-- A child interval and proposed indexed parents in the left and right partitions. -/
public abbrev Code := Interval × IntervalOwner.Presentation.Code × IntervalOwner.Presentation.Code

/-- Both proposed parent occurrences contain the same child in their original partitions. -/
@[expose] public def Valid (left right : Normalized) (code : Code) : Prop :=
  IntervalOwner.Presentation.Valid left.intervals code.1 code.2.1 ∧
    IntervalOwner.Presentation.Valid right.intervals code.1 code.2.2

/-- Decide a previously computed owner check without repeating its lookup or comparisons. -/
private def decideChecked {intervals : List Interval} {child : Interval}
    {code : IntervalOwner.Presentation.Code}
    (result : IntervalOwner.Presentation.Check intervals child code) :
    Decidable (IntervalOwner.Presentation.Valid intervals child code) :=
  match result with
  | .outOfRange lookup => .isFalse (fun valid => by cases lookup.symm.trans valid.1)
  | .wrongParent _ lookup different => .isFalse (fun valid =>
      different (Option.some.inj (lookup.symm.trans valid.1)))
  | .beforeStart invalid => .isFalse (fun valid => invalid valid.2.1)
  | .afterFinish invalid => .isFalse (fun valid => invalid valid.2.2)
  | .accepted valid => .isTrue valid

set_option genInjectivity false in
/-- A common-entry proposal succeeds or retains the first invalid parent check. -/
public inductive Check (left right : Normalized) (code : Code) where
  /-- The proposed left parent is invalid for this child. -/
  | invalidLeft (reason : IntervalOwner.Presentation.Check left.intervals code.1 code.2.1)
      (invalid : ¬ IntervalOwner.Presentation.Valid left.intervals code.1 code.2.1)
  /-- The left parent is valid but the proposed right parent is invalid. -/
  | invalidRight (leftValid : IntervalOwner.Presentation.Valid left.intervals code.1 code.2.1)
      (reason : IntervalOwner.Presentation.Check right.intervals code.1 code.2.2)
      (invalid : ¬ IntervalOwner.Presentation.Valid right.intervals code.1 code.2.2)
  /-- Both original parent occurrences contain the proposed child. -/
  | accepted (valid : Valid left right code)

/-- Check both proposed owners in order, retaining their original typed rejection.

The original finite lookup and rational comparisons are executed once per
visited side. No positivity or nonempty-child assumption is imposed. -/
public def check (left right : Normalized) (code : Code) : Check left right code :=
  let leftResult := IntervalOwner.Presentation.check left.intervals code.1 code.2.1
  match decideChecked leftResult with
  | .isFalse invalid => .invalidLeft leftResult invalid
  | .isTrue leftValid =>
      let rightResult := IntervalOwner.Presentation.check right.intervals code.1 code.2.2
      match decideChecked rightResult with
      | .isFalse invalid => .invalidRight leftValid rightResult invalid
      | .isTrue rightValid => .accepted ⟨leftValid, rightValid⟩

/-- Decide validity using the same typed two-owner check. -/
public def recognize (left right : Normalized) (code : Code) : Decidable (Valid left right code) :=
  match check left right code with
  | .invalidLeft _ invalid => .isFalse (fun valid => invalid valid.1)
  | .invalidRight _ _ invalid => .isFalse (fun valid => invalid valid.2)
  | .accepted valid => .isTrue valid

/-- A checked finite display bound to the two original partitions. -/
public abbrev Display (left right : Normalized) := {code : Code // Valid left right code}

/-- Read a checked display into the original common-entry owner. -/
@[expose] public def read {left right : Normalized} (display : Display left right) : CommonEntry left right :=
  ⟨display.val.1, IntervalOwner.Presentation.read ⟨display.val.2.1, display.property.1⟩,
    IntervalOwner.Presentation.read ⟨display.val.2.2, display.property.2⟩⟩

/-- Quote an original entry by projecting its child and both retained parents. -/
@[expose] public def quote {left right : Normalized} (entry : CommonEntry left right) : Display left right :=
  ⟨(entry.child, (IntervalOwner.Presentation.quote entry.leftOwner).val,
      (IntervalOwner.Presentation.quote entry.rightOwner).val),
    (IntervalOwner.Presentation.quote entry.leftOwner).property,
    (IntervalOwner.Presentation.quote entry.rightOwner).property⟩

/-- Reading an original quotation recovers the same common entry. -/
public theorem read_quote {left right : Normalized} (entry : CommonEntry left right) :
    read (quote entry) = entry := by
  apply CommonEntry.eq_of_fields
  · rfl
  · rfl
  · rfl

/-- Quoting a read display recovers all its proposed finite data. -/
public theorem quote_read {left right : Normalized} (display : Display left right) :
    quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Two displays agree when their original common entries are equal. -/
@[expose] public def Same {left right : Normalized} (first second : Display left right) : Prop :=
  read first = read second

/-- Compare displays through the original common-entry equality decision. -/
public def compare {left right : Normalized} (first second : Display left right) : Decidable (Same first second) :=
  CommonEntry.compare (read first) (read second)

/-- Display equality is exactly equality of the original entries. -/
public theorem same_iff_read_eq {left right : Normalized} (first second : Display left right) :
    Same first second ↔ read first = read second := Iff.rfl

/-- The finite presentation of common entries for two fixed original partitions. -/
public def presentation (left right : Normalized) : Purelib.Data.Presentation Code where
  Valid := Valid left right
  recognize := recognize left right
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun equal => equal.symm, fun first second => first.trans second⟩

end Purelib.Integration.Partition.Unit.Common.CommonEntry.Presentation
