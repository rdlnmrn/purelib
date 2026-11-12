module

public import Purelib.Data.Presentation
import Purelib.Data.List.Search
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Integration.Partition.Unit.Basic

namespace Purelib.Integration.Partition.Unit.Presentation

open Purelib.Data
open Purelib.Data.Rat

/-- An already normalized unit-partition display is a finite list of rational cuts. -/
public abbrev Code := List Fraction.Rational

/-- A cut is strictly inside the unit interval. -/
@[expose] public def Interior (cut : Fraction.Rational) : Prop := 0 < cut ∧ cut < 1

/-- Decide whether a rational cut is strictly inside the unit interval. -/
public instance (cut : Fraction.Rational) : Decidable (Interior cut) :=
  inferInstanceAs (Decidable (0 < cut ∧ cut < 1))

/-- A display has strictly increasing interior cuts. -/
@[expose] public def Valid (cuts : Code) : Prop :=
  cuts.Pairwise (· < ·) ∧ ∀ cut ∈ cuts, Interior cut

set_option genInjectivity false in
/-- A finite adjacent-order check retains either sortedness or a concrete bad pair.

The preceding and following lists locate the consecutive entries in the input;
`notSorted` proves that this particular failure violates strict order. -/
private inductive OrderCheck (cuts : Code) where
  /-- Every earlier cut is strictly smaller than every later cut. -/
  | ordered (sorted : cuts.Pairwise (· < ·))
  /-- The original list contains an adjacent pair in the wrong order. -/
  | badAdjacent (before : Code) (left right : Fraction.Rational) (suffix : Code)
      (position : cuts = before ++ left :: right :: suffix)
      (failed : ¬ left < right) (notSorted : ¬ cuts.Pairwise (· < ·))

/-- Check neighboring cuts in one finite traversal.

Transitivity of rational strict order promotes successful adjacent comparisons
to the original owner's pairwise ordering. A rejected result retains the exact
two original adjacent values and a proof that they are not strictly ordered. -/
private def checkOrder : (cuts : Code) → OrderCheck cuts
  | [] => .ordered List.Pairwise.nil
  | [_] => .ordered (List.Pairwise.cons (fun _ impossible => by nomatch impossible) List.Pairwise.nil)
  | first :: second :: rest =>
      if ordered : first < second then
        match checkOrder (second :: rest) with
        | .ordered tailSorted => .ordered (List.Pairwise.cons (by
            intro value member
            cases member with
            | head => exact ordered
            | tail _ later =>
              exact lt_trans ordered ((List.pairwise_cons.mp tailSorted).1 value later)) tailSorted)
        | .badAdjacent before left right suffix position failed notSorted =>
            .badAdjacent (first :: before) left right suffix
              (congrArg (List.cons first) position) failed
              (fun sorted => notSorted (List.pairwise_cons.mp sorted).2)
      else
        .badAdjacent [] first second rest rfl ordered
          (fun sorted => ordered ((List.pairwise_cons.mp sorted).1 second List.mem_cons_self))

set_option genInjectivity false in
/-- A normalized-cut check returns a certificate or a proved, located invalidity. -/
public inductive Check (cuts : Code) where
  /-- The original cut list is strictly ordered and interior. -/
  | accepted (valid : Valid cuts)
  /-- The original bounded position contains an out-of-range cut. -/
  | outOfRange (index : Fin cuts.length) (failed : ¬ Interior (cuts.get index))
  /-- An adjacent pair in the original list is not strictly ordered. -/
  | badAdjacent (before : Code) (left right : Fraction.Rational) (suffix : Code)
      (position : cuts = before ++ left :: right :: suffix)
      (failed : ¬ left < right) (notSorted : ¬ cuts.Pairwise (· < ·))

/-- Recognize already normalized cuts, retaining the original cause of rejection.

The existing finite occurrence search returns a bounded invalid position or
proves that every cut is interior. The separate adjacent scan checks order
without normalizing the request. -/
public def check (cuts : Code) : Check cuts :=
  match result : List.Search.firstOccurrence (fun cut => ¬ Interior cut)
      (fun cut => inferInstance) cuts with
  | some occurrence =>
      .outOfRange occurrence.index (by
        rw [List.get_eq_getElem, ← occurrence.entry_eq]
        exact occurrence.accepted)
  | none =>
      have interior : ∀ cut ∈ cuts, Interior cut := by
        intro cut member
        by_cases inside : Interior cut
        · exact inside
        · have selected := List.Search.firstAccepted (fun cut => ¬ Interior cut)
            (fun cut => inferInstance) cuts ⟨cut, member, inside⟩
          have impossible : none = some selected.val := result.symm.trans selected.property
          cases impossible
      match checkOrder cuts with
      | .ordered sorted => .accepted ⟨sorted, interior⟩
      | .badAdjacent before left right suffix position failed notSorted =>
          .badAdjacent before left right suffix position failed notSorted

/-- Decide validity using the same typed finite checker. -/
public def recognize (cuts : Code) : Decidable (Valid cuts) :=
  match check cuts with
  | .accepted valid => .isTrue valid
  | .outOfRange index failed => .isFalse (fun valid =>
      failed (valid.2 (cuts.get index) (List.getElem_mem index.isLt)))
  | .badAdjacent _ _ _ _ _ _ notSorted => .isFalse (fun valid => notSorted valid.1)

/-- An admissible display retains its original cut list and validity evidence. -/
public abbrev Display := {cuts : Code // Valid cuts}

/-- Two admissible displays denote the same partition exactly when their cuts agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the original ordered rational cut lists directly. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Decide partition-display equality by the original ordered cuts. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Construct the original normalized partition and its adjacent interval cache. -/
@[expose] public def read (display : Display) : Normalized :=
  Normalized.ofRequest display.val

/-- Quote an existing partition by projecting its retained cut list. -/
@[expose] public def quote (partition : Normalized) : Display :=
  ⟨partition.cuts, partition.sorted, partition.inside⟩

/-- Reading an admissible display retains its exact original cuts. -/
public theorem read_cuts (display : Display) : (read display).cuts = display.val :=
  Normalize.normalize_eq_of_sorted display.property.1 display.property.2

/-- Display equality is exactly equality of the original normalized owners. -/
public theorem same_iff_read_eq (left right : Display) :
    Same left right ↔ read left = read right := by
  constructor
  · intro equal
    apply Normalized.ext_cuts
    exact (read_cuts left).trans (equal.trans (read_cuts right).symm)
  · intro equal
    exact (read_cuts left).symm.trans
      ((congrArg Normalized.cuts equal).trans (read_cuts right))

/-- Reading a quotation equals the complete original partition, including its interval list. -/
public theorem read_quote (partition : Normalized) : read (quote partition) = partition :=
  Normalized.ext_cuts (read_cuts (quote partition))

/-!
## Normalized unit-partition displays

* **Object and expressions:** `Code` is a typed finite list of canonical
  rationals, displayed as the ordered interior cuts of a unit partition.
* **Recognition:** `check` accepts `Valid`; it reports a bounded out-of-range
  occurrence or an adjacent pair with a proved strict-order failure.
* **Equality:** `compare` decides equality of the retained cut lists;
  `same_iff_read_eq` proves that this is equality of the original partitions,
  not merely equality of their covered interval.
* **Constructions and operations:** `read` builds the original cached owner;
  `quote` directly projects existing cuts. `read_cuts` and `read_quote`
  establish exact retention and the complete owner round trip. `ofRequest`
  separately filters, sorts and consolidates unrestricted requests.
* **Termination and dependencies:** the list check, occurrence search and
  adjacent comparison recurse on finite list tails, using the original
  rational order and normalization. The repository's proof-system and runtime
  assumptions remain inherited; this record does not certify them itself.
* **Examples and non-examples:**
  `Purelib.Examples.Integration.Partition.Unit.Presentation` defines `empty`
  and `ordered`, the latter with cuts at 1/3 and 2/3.
  `TestPurelib.Integration.Partition.Initial` compares these distinct partitions
  and exhibits each interval chain from zero to one. Repeated, reversed, zero
  and one cuts are rejected; `ofRequest` instead normalizes general requests.
-/
/-- The explicit presentation of normalized unit partitions by their cuts. -/
@[expose] public def partition : Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun proof => proof.symm, fun first second => first.trans second⟩

end Purelib.Integration.Partition.Unit.Presentation
