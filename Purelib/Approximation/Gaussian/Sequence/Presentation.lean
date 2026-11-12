module

public import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Presentation

namespace Purelib.Approximation.Gaussian.Sequence.ApproximationData

open Purelib.Data.Gaussian

/-- A displayed later index witnesses this particular possible sample. -/
@[expose] public def WitnessValid (approximation : ApproximationData) (start later : Nat)
    (value : Basic.Canonical) : Prop :=
  start ≤ later ∧ value = approximation.sample later

set_option genInjectivity false in
/-- The finite check of one proposed later index and its proposed reading. -/
public inductive WitnessCheck (approximation : ApproximationData) (start later : Nat)
    (value : Basic.Canonical) where
  /-- The index and reading witness the original possibility relation. -/
  | valid (proof : WitnessValid approximation start later value)
  /-- The proposed witness is earlier than the requested stage. -/
  | beforeStart (proof : ¬ start ≤ later)
  /-- The proposed reading differs from the original sample at that index. -/
  | wrongSample (proof : value ≠ approximation.sample later)

/-- Check a supplied index and reading against the original approximation.

The procedure evaluates the sample only at the supplied finite index. Rejection
of this witness does not decide whether some other later index witnesses `Possible`. -/
@[expose] public def checkWitness (approximation : ApproximationData) (start later : Nat)
    (value : Basic.Canonical) : WitnessCheck approximation start later value :=
  if order : start ≤ later then
    if same : value = approximation.sample later then .valid ⟨order, same⟩
    else .wrongSample same
  else .beforeStart order

/-- Decide validity of the supplied witness using the same proof-bearing check. -/
@[expose] public def recognizeWitness (approximation : ApproximationData) (start later : Nat)
    (value : Basic.Canonical) : Decidable (WitnessValid approximation start later value) :=
  match checkWitness approximation start later value with
  | .valid proof => .isTrue proof
  | .beforeStart proof => .isFalse (fun valid => proof valid.1)
  | .wrongSample proof => .isFalse (fun valid => proof valid.2)

/-- Check a cached original sample entry without recomputing its sample.

The entry retains its original approximation and index. Its existing readback
proof supplies the sample equality, so only the stage-floor decision is needed. -/
@[expose] public def checkEntry {approximation : ApproximationData} (start : Nat)
    (entry : SamplePrefix.Entry approximation) :
    WitnessCheck approximation start entry.index entry.value :=
  if order : start ≤ entry.index then .valid ⟨order, entry.value_eq⟩
  else .beforeStart order

/-- An accepted displayed index supplies the original possibility relation. -/
public theorem possible_of_witness {approximation : ApproximationData} {start later : Nat}
    {value : Basic.Canonical} (valid : WitnessValid approximation start later value) :
    approximation.Possible start value := ⟨later, valid.1, valid.2⟩

/-- Every original sample is a valid witness at its own stage. -/
public theorem sample_witness (approximation : ApproximationData) (index : Nat) :
    WitnessValid approximation index index (approximation.sample index) := ⟨Nat.le_refl _, rfl⟩

end Purelib.Approximation.Gaussian.Sequence.ApproximationData

namespace Purelib.Approximation.Gaussian.Sequence.SamplePrefix.Entry.Presentation

open Purelib.Data.Gaussian

/-- The finite input is an original sample index and its proposed Gaussian reading. -/
public abbrev Code := Nat × Basic.Canonical

/-- A proposed entry is valid when the retained reading is the original sample at its index. -/
@[expose] public def Valid (original : ApproximationData) (code : Code) : Prop :=
  ApproximationData.WitnessValid original 0 code.1 code.2

/-- Check an entry using the original finite witness checker at stage zero. -/
@[expose] public def check (original : ApproximationData) (code : Code) :
    ApproximationData.WitnessCheck original 0 code.1 code.2 :=
  ApproximationData.checkWitness original 0 code.1 code.2

/-- Decide entry validity through the same typed witness checker. -/
@[expose] public def recognize (original : ApproximationData) (code : Code) : Decidable (Valid original code) :=
  ApproximationData.recognizeWitness original 0 code.1 code.2

/-- An accepted original-index and reading pair. -/
public abbrev Display (original : ApproximationData) := {code : Code // Valid original code}

/-- Construct the original cached-entry owner from an accepted finite pair. -/
@[expose] public def read {original : ApproximationData} (display : Display original) : Entry original :=
  ⟨display.val.1, display.val.2, display.property.2⟩

/-- Quote an existing entry by projecting its retained index, reading and certificate.

This does not invoke the original sample function or rebuild a cache. -/
@[expose] public def quote {original : ApproximationData} (entry : Entry original) : Display original :=
  ⟨(entry.index, entry.value), Nat.zero_le _, entry.value_eq⟩

/-- Entries have the same presentation when their retained index and reading agree. -/
@[expose] public def Same {original : ApproximationData} (left right : Display original) : Prop :=
  left.val = right.val

/-- Decide equality of retained entry data without evaluating the sample function. -/
@[expose] public def compare {original : ApproximationData} (left right : Display original) :
    Decidable (Same left right) := inferInstanceAs (Decidable (left.val = right.val))

/-- Reading a quoted entry recovers the original entry, independently of its proof text. -/
public theorem read_quote {original : ApproximationData} (entry : Entry original) : read (quote entry) = entry := by
  cases entry
  rfl

/-- Quoting an accepted entry preserves the proposed index and reading. -/
public theorem quote_read {original : ApproximationData} (display : Display original) :
    quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Equality of accepted data agrees with equality of the original cached entries. -/
public theorem same_iff_read_eq {original : ApproximationData} (left right : Display original) :
    Same left right ↔ read left = read right := by
  constructor
  · intro equal
    cases Subtype.ext equal
    rfl
  · intro equal
    have quoted := congrArg quote equal
    rw [quote_read, quote_read] at quoted
    exact congrArg Subtype.val quoted

/-- The explicit presentation of original sample-prefix entries for a fixed approximation. -/
@[expose] public def presentation (original : ApproximationData) : Purelib.Data.Presentation Code where
  Valid := Valid original
  recognize := recognize original
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Approximation.Gaussian.Sequence.SamplePrefix.Entry.Presentation
