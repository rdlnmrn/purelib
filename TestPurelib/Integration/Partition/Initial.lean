module
import Purelib.Examples.Integration.Partition.Unit.Presentation
import Purelib.Integration.Partition.Unit.Initial
import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Integration.Partition.Interval.Presentation
import Purelib.Integration.Partition.Interval.Chain.Presentation
import Purelib.Integration.Partition.Ownership
import Purelib.Integration.Partition.Ownership.Presentation
import Purelib.Integration.Partition.Unit.Ownership
import Purelib.Integration.Partition.Unit.Occurrence
import Purelib.Integration.Partition.Unit.Check
import Purelib.Integration.Partition.Unit.Common.Presentation
meta import Purelib.Integration.Partition.Unit.Occurrence
meta import Purelib.Integration.Partition.Unit.Check
meta import Purelib.Integration.Partition.Unit.Common.Presentation
meta import Purelib.Integration.Partition.Interval.Chain.Presentation
meta import Purelib.Integration.Partition.Unit.Presentation
meta import Purelib.Examples.Integration.Partition.Unit.Presentation

/-! Initial-region coverage and endpoint accounting on a finite grid. -/

namespace TestPurelib.Integration.Partition.Initial

open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Integration.Partition.Ownership
open Purelib.Integration.Partition.Interval
open Unit.Common
open Purelib.Examples.Integration.Partition.Unit.Presentation

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let cuts : Unit.Presentation.Code := [1 / 2, 0, 0]
  (match Unit.Occurrence.check cuts 1 with
    | .accepted selected _ => selected.index.val == 1 && selected.entry == 0
    | _ => false,
   match Unit.Occurrence.check cuts 2 with
    | .wrongPosition selected _ => selected.index.val == 1 && selected.entry == 0
    | _ => false,
   match Unit.Occurrence.check cuts 3 with | .outOfRange _ => true | _ => false,
   match Unit.Occurrence.check [1 / 2] 0 with | .noOccurrence _ => true | _ => false,
   match Unit.Presentation.check cuts with
    | .outOfRange index _ => index.val == 1
    | _ => false))

example {cuts : Unit.Presentation.Code} (left right : Unit.Occurrence.Selected cuts) :
    left = right := Unit.Occurrence.subsingleton left right

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let cuts : Unit.Presentation.Code := [1 / 2, 0, 0]
  (match Unit.Occurrence.checkEntry cuts 1 0 with
    | .accepted selected _ _ => selected.index.val == 1 && selected.entry == 0
    | _ => false,
   match Unit.Occurrence.checkEntry cuts 1 1 with
    | .wrongEntry selected _ _ => selected.index.val == 1 && selected.entry == 0
    | _ => false,
   match Unit.Occurrence.checkEntry cuts 2 0 with
    | .invalidPosition (.wrongPosition selected _) _ => selected.index.val == 1
    | _ => false,
   match Unit.Occurrence.checkEntry cuts 3 0 with
    | .invalidPosition (.outOfRange _) _ => true | _ => false,
   match Unit.Occurrence.checkEntry [1 / 2] 0 (1 / 2) with
    | .invalidPosition (.noOccurrence _) _ => true | _ => false))

example {cuts : Unit.Presentation.Code} (left right : Unit.Occurrence.Selected cuts) :
    left = right ↔ left.index = right.index ∧ left.entry = right.entry :=
  Unit.Occurrence.eq_iff_index_entry_eq left right

example {cuts : Unit.Presentation.Code} (selected : Unit.Occurrence.Selected cuts)
    (earlier : Fin cuts.length) (before : earlier.val < selected.index.val) :
    Unit.Presentation.Interior (cuts[earlier.val]'earlier.isLt) := by
  have notInvalid := selected.earlier earlier before
  by_cases interior : Unit.Presentation.Interior (cuts[earlier.val]'earlier.isLt)
  · exact interior
  · exact False.elim (notInvalid interior)

example {cuts : Unit.Presentation.Code} {position : Nat} {entry : Fraction.Rational}
    (selected : Unit.Occurrence.Selected cuts) (first second : selected.index.val = position)
    (entryFirst entrySecond : selected.entry = entry) :
    Unit.Occurrence.EntryCheck.accepted selected first entryFirst =
      Unit.Occurrence.EntryCheck.accepted selected second entrySecond := rfl

private def firstAdjacent : Unit.Presentation.Check [twoThirds, third, third] :=
  .badAdjacent [] twoThirds third [third] rfl (by decide) (by decide)

private def secondAdjacent : Unit.Presentation.Check [twoThirds, third, third] :=
  .badAdjacent [twoThirds] third third [] rfl (by decide) (by decide)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Unit.Presentation.Check.compare firstAdjacent firstAdjacent with
    | .isTrue _ => true | .isFalse _ => false,
  match Unit.Presentation.Check.compare firstAdjacent secondAdjacent with
    | .isTrue _ => false | .isFalse _ => true,
  match Unit.Presentation.Check.compare
      (Unit.Presentation.check [twoThirds, third, third]) firstAdjacent with
    | .isTrue _ => true | .isFalse _ => false)

example {cuts before after : Unit.Presentation.Code} {left right : Fraction.Rational}
    (position position' : cuts = before ++ left :: right :: after)
    (failed failed' : ¬ left < right) (notSorted notSorted' : ¬ cuts.Pairwise (· < ·)) :
    Unit.Presentation.Check.badAdjacent before left right after position failed notSorted =
      Unit.Presentation.Check.badAdjacent before left right after position' failed' notSorted' := rfl

private def duplicateIntervals : List Interval := [⟨0, 1⟩, ⟨0, 1⟩]

private def firstOwner : Ownership.PointOwner duplicateIntervals 0 :=
  ⟨0, ⟨0, 1⟩, rfl, by decide, by decide⟩

private def secondOwner : Ownership.PointOwner duplicateIntervals 0 :=
  ⟨1, ⟨0, 1⟩, rfl, by decide, by decide⟩

example : (match Ownership.PointOwner.compare firstOwner firstOwner with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Ownership.PointOwner.compare firstOwner secondOwner with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (first second : Ownership.PointOwner duplicateIntervals 0)
    (indices : first.index = second.index) : first = second :=
  Ownership.PointOwner.eq_of_index_eq first second indices

example : (Ownership.pointOwnerBetween 0 1 (1 / 2) [1 / 2] (by decide) (by decide)).index = 1 := by decide

private def normalizedOwner : Ownership.PointOwner partition.intervals (1 / 2) :=
  partition.pointOwner (1 / 2) (by decide) (by decide)

example : PointOwner.Presentation.read
    (PointOwner.Presentation.quote normalizedOwner) = normalizedOwner :=
  PointOwner.Presentation.read_quote normalizedOwner

example : (match PointOwner.Presentation.check partition.intervals (1 / 2)
    (PointOwner.Presentation.quote normalizedOwner).val with
    | .accepted _ => true | _ => false) = true := by decide

example : (match PointOwner.Presentation.check duplicateIntervals 0 (2, ⟨0, 1⟩) with
    | .outOfRange _ => true | _ => false) = true := by decide

example : (match PointOwner.Presentation.check duplicateIntervals 0 (0, ⟨0, 2⟩) with
    | .wrongParent _ _ _ => true | _ => false) = true := by decide

example : (match PointOwner.Presentation.check duplicateIntervals (-1) (0, ⟨0, 1⟩) with
    | .beforeStart _ => true | _ => false) = true := by decide

example : (match PointOwner.Presentation.check duplicateIntervals 1 (0, ⟨0, 1⟩) with
    | .atOrBeyondFinish _ => true | _ => false) = true := by decide

example : (match PointOwner.Presentation.compare
    (PointOwner.Presentation.quote firstOwner)
    (PointOwner.Presentation.quote secondOwner) with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (first second : PointOwner.Presentation.Display duplicateIntervals 0) :
    PointOwner.Presentation.Same first second ↔
      PointOwner.Presentation.read first = PointOwner.Presentation.read second :=
  PointOwner.Presentation.same_iff_read_eq first second

private def boundaryChild : Interval := ⟨1 / 3, 1 / 3⟩

private def leftBoundaryOwner : Ownership.IntervalOwner partition.intervals boundaryChild :=
  ⟨0, ⟨0, 1 / 3⟩, by decide, by decide, by decide⟩

private def rightBoundaryOwner : Ownership.IntervalOwner partition.intervals boundaryChild :=
  ⟨1, ⟨1 / 3, 2 / 3⟩, by decide, by decide, by decide⟩

private def firstEntry : Unit.Common.CommonEntry partition partition :=
  ⟨boundaryChild, leftBoundaryOwner, leftBoundaryOwner⟩

private def secondEntry : Unit.Common.CommonEntry partition partition :=
  ⟨boundaryChild, rightBoundaryOwner, leftBoundaryOwner⟩

private def thirdEntry : Unit.Common.CommonEntry partition partition :=
  ⟨boundaryChild, leftBoundaryOwner, rightBoundaryOwner⟩

example (entry : CommonEntry partition partition) :
    CommonEntry.Presentation.read (CommonEntry.Presentation.quote entry) = entry :=
  CommonEntry.Presentation.read_quote entry

example (display : CommonEntry.Presentation.Display partition partition) :
    CommonEntry.Presentation.quote (CommonEntry.Presentation.read display) = display :=
  CommonEntry.Presentation.quote_read display

example (first second : CommonEntry.Presentation.Display partition partition) :
    CommonEntry.Presentation.Same first second ↔
      CommonEntry.Presentation.read first = CommonEntry.Presentation.read second :=
  CommonEntry.Presentation.same_iff_read_eq first second

/-- info: (true, true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (let good := (CommonEntry.Presentation.quote firstEntry).val
  let leftParent := good.2.1
  let rightParent := good.2.2
  (match CommonEntry.Presentation.check partition partition good with
    | .accepted _ => true | _ => false,
   match CommonEntry.Presentation.compare (CommonEntry.Presentation.quote firstEntry)
      (CommonEntry.Presentation.quote secondEntry) with
    | .isTrue _ => false | .isFalse _ => true,
   match CommonEntry.Presentation.check partition partition (good.1, (99, leftParent.2), rightParent) with
    | .invalidLeft (.outOfRange _) _ => true | _ => false,
   match CommonEntry.Presentation.check partition partition (good.1, leftParent, (99, rightParent.2)) with
    | .invalidRight _ (.outOfRange _) _ => true | _ => false,
   match CommonEntry.Presentation.check partition partition (good.1, (0, ⟨0, 1⟩), rightParent) with
    | .invalidLeft (.wrongParent ..) _ => true | _ => false,
   match CommonEntry.Presentation.check partition partition (good.1, leftParent, (0, ⟨0, 1⟩)) with
    | .invalidRight _ (.wrongParent ..) _ => true | _ => false,
   match CommonEntry.Presentation.check partition partition (⟨0, 1 / 3⟩, (1, ⟨1 / 3, 2 / 3⟩), rightParent) with
    | .invalidLeft (.beforeStart _) _ => true | _ => false,
   match CommonEntry.Presentation.check partition partition (⟨0, 1 / 3⟩, leftParent, (1, ⟨1 / 3, 2 / 3⟩)) with
    | .invalidRight _ (.beforeStart _) _ => true | _ => false))

private def firstIntervalOwner : Ownership.IntervalOwner partition.intervals ⟨0, 1 / 3⟩ :=
  ⟨0, ⟨0, 1 / 3⟩, by decide, by decide, by decide⟩

private def normalizedIntervalOwner : Ownership.IntervalOwner partition.intervals ⟨0, 1 / 3⟩ :=
  partition.intervalOwner partition (fun _ member => member) ⟨0, 1 / 3⟩
    (Purelib.Data.List.mem_of_getElem? _ _ _ firstIntervalOwner.at_index)

example : IntervalOwner.Presentation.read (IntervalOwner.Presentation.quote normalizedIntervalOwner) =
    normalizedIntervalOwner := IntervalOwner.Presentation.read_quote normalizedIntervalOwner

example : (match IntervalOwner.Presentation.check partition.intervals ⟨0, 1 / 3⟩
    (IntervalOwner.Presentation.quote normalizedIntervalOwner).val with
    | .accepted _ => true | _ => false) = true := by decide

example : (match IntervalOwner.Presentation.check partition.intervals boundaryChild
    (IntervalOwner.Presentation.quote leftBoundaryOwner).val,
    IntervalOwner.Presentation.check partition.intervals boundaryChild
      (IntervalOwner.Presentation.quote rightBoundaryOwner).val with
    | .accepted _, .accepted _ => true | _, _ => false) = true := by decide

example : (match IntervalOwner.Presentation.compare
    (IntervalOwner.Presentation.quote leftBoundaryOwner)
    (IntervalOwner.Presentation.quote rightBoundaryOwner) with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : (match IntervalOwner.Presentation.check duplicateIntervals ⟨0, 1⟩ (2, ⟨0, 1⟩) with
    | .outOfRange _ => true | _ => false) = true := by decide

example : (match IntervalOwner.Presentation.check duplicateIntervals ⟨0, 1⟩ (0, ⟨0, 2⟩) with
    | .wrongParent _ _ _ => true | _ => false) = true := by decide

example : (match IntervalOwner.Presentation.check duplicateIntervals ⟨-1, 0⟩ (0, ⟨0, 1⟩) with
    | .beforeStart _ => true | _ => false) = true := by decide

example : (match IntervalOwner.Presentation.check duplicateIntervals ⟨0, 2⟩ (0, ⟨0, 1⟩) with
    | .afterFinish _ => true | _ => false) = true := by decide

example (first second : IntervalOwner.Presentation.Display partition.intervals boundaryChild) :
    IntervalOwner.Presentation.Same first second ↔
      IntervalOwner.Presentation.read first = IntervalOwner.Presentation.read second :=
  IntervalOwner.Presentation.same_iff_read_eq first second

private def fourthEntry : Unit.Common.CommonEntry partition partition :=
  ⟨⟨0, 1 / 3⟩, firstIntervalOwner, firstIntervalOwner⟩

example : (match Unit.Common.CommonEntry.compare firstEntry firstEntry with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Unit.Common.CommonEntry.compare firstEntry secondEntry with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : (match Unit.Common.CommonEntry.compare firstEntry thirdEntry with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : (match Unit.Common.CommonEntry.compare firstEntry fourthEntry with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (first second : Unit.Common.CommonEntry partition partition)
    (child : first.child = second.child) (left : first.leftOwner.index = second.leftOwner.index)
    (right : first.rightOwner.index = second.rightOwner.index) : first = second :=
  Unit.Common.CommonEntry.eq_of_fields first second child left right

private def emptyPartition : Unit.Normalized := Unit.Presentation.read empty

/-- info: true -/
#guard_msgs in
#eval (let entries := (Unit.Common.commonRefinement partition emptyPartition).entries
  !entries.isEmpty && entries.all fun entry =>
    match CommonEntry.Presentation.check partition emptyPartition (CommonEntry.Presentation.quote entry).val with
    | .accepted _ => true | _ => false)

private theorem emptyCutsIncluded (target : Unit.Normalized) :
    ∀ cut ∈ emptyPartition.cuts, cut ∈ target.cuts := by
  intro cut member
  change cut ∈ (Unit.Presentation.read empty).cuts at member
  rw [Unit.Presentation.read_cuts] at member
  cases member

private def emptyRefinement : Unit.Common.CommonRefinement emptyPartition emptyPartition :=
  Unit.Common.CommonRefinement.ofPartition emptyPartition emptyPartition emptyPartition
    (emptyCutsIncluded emptyPartition) (emptyCutsIncluded emptyPartition)

private def orderedRefinement : Unit.Common.CommonRefinement emptyPartition emptyPartition :=
  Unit.Common.CommonRefinement.ofPartition emptyPartition emptyPartition partition
    (emptyCutsIncluded partition) (emptyCutsIncluded partition)

example : (match Unit.Common.CommonRefinement.compare emptyRefinement emptyRefinement with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Unit.Common.CommonRefinement.compare emptyRefinement orderedRefinement with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example : (match Interval.Presentation.check ⟨0, 1⟩ with
    | .valid _ => true | _ => false) = true := by decide

example : (match Interval.Presentation.check ⟨-1, 1⟩ with
    | .negativeStart _ => true | _ => false) = true := by decide

example : (match Interval.Presentation.check ⟨0, 0⟩ with
    | .nonpositiveLength _ => true | _ => false) = true := by decide

example : (match Interval.Presentation.check ⟨1, 0⟩ with
    | .nonpositiveLength _ => true | _ => false) = true := by decide

example : (match Interval.Presentation.check ⟨0, 2⟩ with
    | .aboveOne _ => true | _ => false) = true := by decide

example : Interval.Presentation.read (1, 0) = ⟨1, 0⟩ := rfl

example : (match Interval.Presentation.compare (1, 0) (1, 0) with
    | .isTrue _ => true | .isFalse _ => false) = true := by decide

example : (match Interval.Presentation.compare (1, 0) (0, 1) with
    | .isTrue _ => false | .isFalse _ => true) = true := by decide

example (interval : Interval) : Interval.Presentation.read (Interval.Presentation.quote interval) = interval :=
  Interval.Presentation.read_quote interval

example (code : Interval.Presentation.Code) : Interval.Presentation.quote (Interval.Presentation.read code) = code :=
  Interval.Presentation.quote_read code

example (original : Unit.Normalized) (interval : Interval) (member : interval ∈ original.intervals) :
    interval.Valid ∧ Interval.Presentation.read (Interval.Presentation.quote interval) = interval :=
  ⟨original.valid interval member, Interval.Presentation.read_quote interval⟩

example (original : Unit.Normalized) (interval : Interval) (member : interval ∈ original.intervals) :
    (match Interval.Presentation.recognize interval with | .isTrue _ => True | .isFalse _ => False) := by
  cases Interval.Presentation.recognize interval with
  | isTrue _ => trivial
  | isFalse rejected => exact False.elim (rejected (original.valid interval member))

/-- Distinguish successful recognition, range rejection and adjacent-order rejection. -/
private def recognitionKind (cuts : Unit.Presentation.Code) : Nat :=
  match Unit.Presentation.check cuts with
  | .accepted _ => 0
  | .outOfRange _ _ => 1
  | .badAdjacent _ _ _ _ _ _ _ => 2

/-- Read the answer of a proof-bearing comparison. -/
private def comparisonResult {proposition : Prop} : Decidable proposition → Bool
  | .isTrue _ => true
  | .isFalse _ => false

/-- Execute acceptance and rejection through the original occurrence scan. -/
private def checkRecognition : IO Unit := do
  if recognitionKind [] = 0 ∧ recognitionKind [third, twoThirds] = 0 ∧
      recognitionKind [twoThirds, third] = 2 ∧ recognitionKind [third, third] = 2 ∧
      recognitionKind [0] = 1 ∧ recognitionKind [1] = 1 ∧
      comparisonResult (Unit.Presentation.recognize [third, twoThirds]) = true ∧
      comparisonResult (Unit.Presentation.partition.recognize []) = true ∧
      comparisonResult (Unit.Presentation.partition.recognize [twoThirds, third]) = false ∧
      comparisonResult (Unit.Presentation.partition.recognize [0]) = false then pure ()
  else throw (IO.userError "incorrect normalized-cut recognition")

#eval checkRecognition

/-- Execute both rejection paths and inspect their original positions and entries. -/
private def checkLocatedFailures : IO Unit := do
  match Unit.Presentation.check [third, 0] with
  | .outOfRange index _ =>
      if index.val = 1 then pure ()
      else throw (IO.userError "wrong original out-of-range position")
  | _ => throw (IO.userError "missing out-of-range rejection")
  match Unit.Presentation.check [third, twoThirds, third] with
  | .badAdjacent before left right after _ _ _ =>
      if before = [third] ∧ left = twoThirds ∧ right = third ∧ after = [] then pure ()
      else throw (IO.userError "wrong original adjacent pair")
  | _ => throw (IO.userError "missing adjacent-order rejection")

#eval checkLocatedFailures

/-- Execute display comparison, original-owner readback and request normalization. -/
private def checkReadback : IO Unit := do
  if comparisonResult (Unit.Presentation.compare empty empty) = true ∧
      comparisonResult (Unit.Presentation.partition.compare empty ordered) = false ∧
      comparisonResult (Unit.Presentation.compare (Unit.Presentation.quote partition) ordered) = true ∧
      (Unit.Presentation.read empty).cuts = [] ∧
      (Unit.Presentation.read empty).intervals.length = 1 ∧
      (Unit.Presentation.read (Unit.Presentation.quote partition)).cuts = [third, twoThirds] ∧
      (Unit.Presentation.read (Unit.Presentation.quote partition)).intervals = partition.intervals ∧
      (Unit.Normalized.ofRequest [twoThirds, third]).cuts = [third, twoThirds] ∧
      (Unit.Normalized.ofRequest [third, third]).cuts = [third] then pure ()
  else throw (IO.userError "incorrect normalized-partition readback or comparison")

#eval checkReadback

/-- Distinct valid cut lists remain distinct despite covering the same unit interval. -/
example : ¬ Unit.Presentation.Same empty ordered := by decide

/-- The named presentation compares the original distinct cut lists. -/
example : comparisonResult (Unit.Presentation.partition.compare empty ordered) = false := by decide

/-- Both original cached partitions chain across the entire unit interval. -/
example : Interval.Chain 0 1 (Unit.Presentation.read empty).intervals ∧
    Interval.Chain 0 1 partition.intervals :=
  ⟨(Unit.Presentation.read empty).chain, partition.chain⟩

/-- info: (true, true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (match Chain.Presentation.check 0 0 [] with
    | .accepted _ => true | _ => false,
  match Chain.Presentation.check 0 1 [] with
    | .rejected (.endpoint _) => true | _ => false,
  match Chain.Presentation.check 0 1 [⟨1 / 2, 1⟩] with
    | .rejected (.head ..) => true | _ => false,
  match Chain.Presentation.check 0 1 [⟨0, 1 / 2⟩, ⟨1 / 3, 1⟩] with
    | .rejected (.tail _ _ (.head ..)) => true | _ => false,
  match Chain.Presentation.check 0 1 [⟨0, 1 / 2⟩] with
    | .rejected (.tail _ _ (.endpoint _)) => true | _ => false,
  match Chain.Presentation.check 1 0 [⟨1, 0⟩] with
    | .accepted _ => true | _ => false,
  match Chain.Presentation.check 0 0 [⟨0, 0⟩] with
    | .accepted _ => true | _ => false,
  match Chain.Presentation.check 0 1 partition.intervals with
    | .accepted _ => true | _ => false)

example (original : Unit.Normalized) :
    (match Chain.Presentation.recognize 0 1 original.intervals with
    | .isTrue _ => True | .isFalse _ => False) := by
  cases Chain.Presentation.recognize 0 1 original.intervals with
  | isTrue _ => trivial
  | isFalse rejected => exact False.elim (rejected original.chain)

/-- Existing request normalization still sorts and consolidates unrestricted inputs. -/
example : (Unit.Normalized.ofRequest [twoThirds, third]).cuts = [third, twoThirds] ∧
    (Unit.Normalized.ofRequest [third, third]).cuts = [third] := by decide

/-- Reading a quotation equals the original owner and its certified interval list. -/
example : Unit.Presentation.read (Unit.Presentation.quote partition) = partition :=
  Unit.Presentation.read_quote partition

/-- The actual four-cell grid computed for a third-unit mesh request. -/
private def quarters : Unit.Normalized := Uniform.Grid.forWidth (1 / 3)

/-- A zero endpoint includes its adjacent cell; a shared cut includes both adjacent cells. -/
example : quarters.initialLength 0 = (1 / 4 : Fraction.Rational) ∧
    quarters.initialLength (1 / 2) = (3 / 4 : Fraction.Rational) := by decide +kernel

/-- A point inside the first cell and the full unit region retain their exact cell lengths. -/
example : quarters.initialLength (1 / 8) = (1 / 4 : Fraction.Rational) ∧
    quarters.initialLength 1 = 1 := by decide +kernel

/-- The general budget is derived from this grid's actual mesh construction. -/
example : quarters.initialLength (1 / 2) ≤ (1 / 2 : Fraction.Rational) + 1 / 3 :=
  quarters.initialLength_le (1 / 2) (1 / 3) (by decide) (by decide)
    (fun interval member => Uniform.Grid.forWidth_interval_lt (by decide) interval member)

end TestPurelib.Integration.Partition.Initial
