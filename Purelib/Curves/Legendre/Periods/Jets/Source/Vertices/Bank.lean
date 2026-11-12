module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices
public import Purelib.Data.List.Search
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite banks of actual original vertex readings

Lookup retains the first matching original vertex and its three cached
requests. A failed finite lookup reports the actual absence from this bank;
it does not identify another root owner or make a pole claim.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

set_option genInjectivity false in
/-- One original lifted vertex together with its actual owner and three paid bank-channel readings. -/
structure Vertex.Entry (parameter : Canonical) (allocation : Rational) where
  /-- The exact original lifted coordinate and selected sheet. -/
  point : LiftedPoint 2
  /-- The actual original continued point and primitive denotations. -/
  original : Vertex parameter point
  /-- The actual original requests and retained possible readings of those same channels. -/
  readings : Vertex.Readings original allocation

namespace Vertex.Entry

/-- Request all three bank readings from an original vertex, keeping that exact owner. -/
@[expose] def request {parameter : Canonical} {point : LiftedPoint 2} (original : Vertex parameter point)
    (allocation : Rational) (positive : 0 < allocation) : Vertex.Entry parameter allocation :=
  ⟨point, original, original.request allocation positive⟩

end Vertex.Entry

/-- A finite structural bank of original lifted vertices and their cached actual readings. -/
abbrev Vertex.Bank (parameter : Canonical) (allocation : Rational) := List (Vertex.Entry parameter allocation)

namespace Vertex.Bank

variable {parameter : Canonical} {allocation : Rational}

/-- Decide equality of original lifted coordinates and labels through their two retained fields. -/
private def pointEq (first second : LiftedPoint 2) : Decidable (first = second) := by
  cases first with
  | mk firstCoordinate firstSheet =>
    cases second with
    | mk secondCoordinate secondSheet =>
      by_cases coordinate : firstCoordinate = secondCoordinate
      · by_cases sheet : firstSheet = secondSheet
        · exact isTrue (by cases coordinate; cases sheet; rfl)
        · exact isFalse (fun same => sheet (congrArg LiftedPoint.sheet same))
      · exact isFalse (fun same => coordinate (congrArg LiftedPoint.coordinate same))

/-- Scan the original bank once and retain the exact first accepted occurrence and complete stored entry.

The private original point decision is passed unchanged to the shared finite
worker. No bank entry, primitive request, observation or root owner is built
by this lookup. Repeated keys retain their first actual position.
-/
def findOccurrence (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) :
    Option (Data.List.Search.Occurrence (fun entry : Vertex.Entry parameter allocation => entry.point = point) bank) :=
  Data.List.Search.firstOccurrence (fun entry => entry.point = point) (fun entry => pointEq entry.point point) bank

/-- Locate the first actual bank entry by the value view of the same original occurrence scan. -/
def find (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) :
    Option (Vertex.Entry parameter allocation) :=
  Data.List.Search.firstValue (fun entry => entry.point = point) (fun entry => pointEq entry.point point) bank

/-- Forgetting only the same scan's positional evidence preserves its complete selected original entry. -/
theorem find_eq_occurrence (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) :
    find bank point = (findOccurrence bank point).map Data.List.Search.Occurrence.entry := by
  unfold find findOccurrence
  exact Data.List.Search.firstValue_eq_occurrence
    (fun entry : Vertex.Entry parameter allocation => entry.point = point)
    (fun entry => pointEq entry.point point) bank

/-- The empty original bank has no selected entry or owner. -/
theorem find_nil (point : LiftedPoint 2) : find ([] : Vertex.Bank parameter allocation) point = none := by
  unfold find
  exact Data.List.Search.firstValue_nil
    (fun entry : Vertex.Entry parameter allocation => entry.point = point)
    (fun entry => pointEq entry.point point)

/-- A matching first point selects its original bank entry without visiting the tail. -/
theorem find_cons_eq (entry : Vertex.Entry parameter allocation) (remaining : Vertex.Bank parameter allocation)
    (point : LiftedPoint 2) (same : entry.point = point) : find (entry :: remaining) point = some entry := by
  unfold find
  exact Data.List.Search.firstValue_cons_pos (fun value => value.point = point)
    (fun value => pointEq value.point point) entry remaining same

/-- A distinct first point preserves the original remaining finite bank lookup. -/
theorem find_cons_ne (entry : Vertex.Entry parameter allocation) (remaining : Vertex.Bank parameter allocation)
    (point : LiftedPoint 2) (different : entry.point ≠ point) :
    find (entry :: remaining) point = find remaining point := by
  unfold find
  exact Data.List.Search.firstValue_cons_neg (fun value => value.point = point)
    (fun value => pointEq value.point point) entry remaining different

/-- Equal ordered original vertices preserve the original projection of the actual finite lookup.

Readings may have independent allocations. The same ordered signed
occurrences give matching absence or the same selected original vertex;
no lookup or request is executed by this proof.
-/
theorem find_origins_eq (firstBank : Vertex.Bank parameter allocation)
    {replacement : Rational} (lastBank : Vertex.Bank parameter replacement)
    (same : firstBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
      lastBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
    (atPoint : LiftedPoint 2) :
    (firstBank.find atPoint).map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
      (lastBank.find atPoint).map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) := by
  induction firstBank generalizing lastBank with
  | nil =>
    cases lastBank with
    | nil =>
      rewrite [find_nil (parameter := parameter) (allocation := allocation) atPoint,
        find_nil (parameter := parameter) (allocation := replacement) atPoint]
      rfl
    | cons entry remaining => cases same
  | cons firstEntry remaining ih =>
    cases lastBank with
    | nil => cases same
    | cons lastEntry rest =>
      have headSame :
          (⟨firstEntry.point, firstEntry.original⟩ :
            Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) =
          ⟨lastEntry.point, lastEntry.original⟩ :=
        congrArg (fun entries : List (Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) =>
          entries.headD ⟨firstEntry.point, firstEntry.original⟩) same
      have tailSame :
          remaining.map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
          rest.map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) :=
        congrArg List.tail same
      have pointSame : firstEntry.point = lastEntry.point :=
        congrArg (fun original : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint =>
          original.1) headSame
      cases pointEq firstEntry.point atPoint with
      | isTrue atRequestedPoint =>
        have firstReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter allocation =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
          (find_cons_eq firstEntry remaining atPoint atRequestedPoint)
        have lastReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter replacement =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
          (find_cons_eq lastEntry rest atPoint (pointSame.symm.trans atRequestedPoint))
        exact firstReadback.trans ((congrArg some headSame).trans lastReadback.symm)
      | isFalse different =>
        have lastDifferent : lastEntry.point ≠ atPoint := fun equal => different (pointSame.trans equal)
        have firstReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter allocation =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
          (find_cons_ne firstEntry remaining atPoint different)
        have lastReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter replacement =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
          (find_cons_ne lastEntry rest atPoint lastDifferent)
        exact firstReadback.trans ((ih rest tailSame).trans lastReadback.symm)

/-- The actual finite bank lookup preserves the requested original lifted point. -/
theorem find_point (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2)
    (entry : Vertex.Entry parameter allocation) (present : bank.find point = some entry) : entry.point = point := by
  induction bank with
  | nil =>
      have impossible := (find_nil (parameter := parameter) (allocation := allocation) point).symm.trans present
      cases impossible
  | cons first remaining ih =>
      cases pointEq first.point point with
      | isTrue equal =>
          have entryEqual : first = entry :=
            Option.some.inj ((find_cons_eq first remaining point equal).symm.trans present)
          exact entryEqual ▸ equal
      | isFalse different =>
          exact ih ((find_cons_ne first remaining point different).symm.trans present)

/-- The actual successful lookup selects one of the retained original bank entries. -/
theorem find_member (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2)
    (entry : Vertex.Entry parameter allocation) (present : bank.find point = some entry) : entry ∈ bank := by
  induction bank with
  | nil =>
      have impossible := (find_nil (parameter := parameter) (allocation := allocation) point).symm.trans present
      cases impossible
  | cons first remaining ih =>
      cases pointEq first.point point with
      | isTrue equal =>
          have entryEqual : first = entry :=
            Option.some.inj ((find_cons_eq first remaining point equal).symm.trans present)
          exact entryEqual ▸ List.Mem.head remaining
      | isFalse different =>
          exact List.Mem.tail first (ih ((find_cons_ne first remaining point different).symm.trans present))

/-- An original retained entry prevents an absent result at its exact original lifted point. -/
private theorem find_ne_none (bank : Vertex.Bank parameter allocation) (entry : Vertex.Entry parameter allocation)
    (member : entry ∈ bank) : bank.find entry.point ≠ none := by
  induction member with
  | head remaining =>
      have selected : find (entry :: remaining) entry.point = some entry :=
        find_cons_eq entry remaining entry.point rfl
      intro absent
      have impossible := selected.symm.trans absent
      cases impossible
  | tail first member ih =>
      rename_i remaining
      cases pointEq first.point entry.point with
      | isTrue equal =>
          have selected : find (first :: remaining) entry.point = some first :=
            find_cons_eq first remaining entry.point equal
          intro absent
          have impossible := selected.symm.trans absent
          cases impossible
      | isFalse different =>
          have unchanged : find (first :: remaining) entry.point = find remaining entry.point :=
            find_cons_ne first remaining entry.point different
          exact fun absent => ih (unchanged.symm.trans absent)

set_option genInjectivity false in
/-- A retained successful finite lookup, including its actual selected original bank entry. -/
structure Found (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) where
  /-- The actual original selected entry, owner and three requests. -/
  entry : Vertex.Entry parameter allocation
  /-- The retained entry is the result of this exact original finite lookup. -/
  present : bank.find point = some entry
  /-- The retained entry belongs to the requested original lifted point. -/
  point_eq : entry.point = point

/-- Locate the actual first matching bank entry when an original entry certifies finite membership. -/
def ofMember (bank : Vertex.Bank parameter allocation) (entry : Vertex.Entry parameter allocation)
    (member : entry ∈ bank) : Found bank entry.point :=
  match present : bank.find entry.point with
  | some selected => ⟨selected, present, bank.find_point entry.point selected present⟩
  | none => False.elim (find_ne_none bank entry member present)

set_option genInjectivity false in
/-- The actual result of locating one original lifted point in a finite retained bank. -/
inductive Outcome (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) where
  /-- The original finite bank contains a retained matching vertex. -/
  | found (retained : Found bank point)
  /-- The actual finite scan found no entry at this original lifted point. -/
  | absent (missing : bank.find point = none)

/-- The exact selected occurrence and complete scan factory identity of an unchanged original lookup outcome.

A found case retains its original Found and a bounded position in the SAME
bank. A failed case keeps the original absent outcome, with no fabricated
position. Existing Sigma/subtype containers retain this additional cache.
-/
@[expose] def Position {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2} :
    Outcome bank point → Type 1
  | .found found =>
      { selected : Data.List.Search.Occurrence
          (fun entry : Vertex.Entry parameter allocation => entry.point = point) bank //
        selected.entry = found.entry ∧ findOccurrence bank point = some selected }
  | .absent _ => PUnit

/-- One original lookup outcome together with its actual first-occurrence cache. -/
@[expose] def Located (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) :=
  (outcome : Outcome bank point) × Position outcome

/-- Execute the shared bank scan once and retain its original outcome, selected entry, position and factory identity.

Both selected Owners and all three old requests are read from the actual
stored entry. No observer, root check, entry producer or second lookup runs.
-/
def checkWithOccurrence (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) : Located bank point :=
  match selected_eq : findOccurrence bank point with
  | none =>
      let missing : find bank point = none := by
        rewrite [find_eq_occurrence, selected_eq]
        rfl
      ⟨.absent missing, PUnit.unit⟩
  | some selected =>
      let found : Found bank point := ⟨selected.entry, by
        rewrite [find_eq_occurrence, selected_eq]
        rfl, selected.accepted⟩
      ⟨.found found, ⟨selected, rfl, selected_eq⟩⟩

/-- Read the unchanged original finite lookup outcome, forgetting only its newly retained position. -/
def check (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) : Outcome bank point :=
  (checkWithOccurrence bank point).1

/-- The occurrence-retaining lookup returns exactly the complete original check outcome. -/
theorem checkWithOccurrence_outcome (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) :
    (checkWithOccurrence bank point).1 = check bank point := by
  unfold check
  rfl

namespace Position

variable {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}
    {found : Found bank point} (position : Position (.found found))

/-- Read the original selected bank position without another scan or source query. -/
@[expose] def index : Fin bank.length := position.val.index

/-- The actual entry at that exact original position is the SAME full retained Found entry. -/
theorem entry_eq : bank[position.index.val]'position.index.isLt = found.entry :=
  position.val.entry_eq.symm.trans position.property.1

/-- The occurrence cache retains the complete original shared scan factory result. -/
theorem factory_eq : findOccurrence bank point = some position.val := position.property.2

/-- No earlier original bank position has the same lifted key as this actual first match. -/
theorem earlier (index : Fin bank.length) (before : index.val < position.index.val) :
    (bank[index.val]'index.isLt).point ≠ point := position.val.earlier index before

end Position

/-- The original check returns the same complete retained first matching lookup. -/
theorem check_found {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}
    (found : Found bank point) : bank.check point = Outcome.found found := by
  unfold check checkWithOccurrence
  split
  next missing =>
    have absent : find bank point = none := by
      rewrite [find_eq_occurrence, missing]
      rfl
    have impossible := absent.symm.trans found.present
    cases impossible
  next selected present =>
    have actual : find bank point = some selected.entry := by
      rewrite [find_eq_occurrence, present]
      rfl
    have equal := Option.some.inj (actual.symm.trans found.present)
    cases found with
    | mk entry _ _ =>
        change selected.entry = entry at equal
        cases equal
        rfl

/-- The original check retains the actual absent result of this same finite bank scan. -/
theorem check_absent (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2)
    (missing : bank.find point = none) : bank.check point = Outcome.absent missing := by
  unfold check checkWithOccurrence
  split
  next _ => rfl
  next selected present =>
    have actual : find bank point = some selected.entry := by
      rewrite [find_eq_occurrence, present]
      rfl
    have impossible := missing.symm.trans actual
    cases impossible

namespace Outcome

/-- Locate an actual first bank match from erased finite membership evidence without evaluating a new entry.

The original check supplies the returned entry and all three cached
readings. The membership witness only rules out its absent branch; no
entry-producing expression is passed as an executable argument.
-/
def locate {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}
    (outcome : Outcome bank point) (present : ∃ entry, entry ∈ bank ∧ entry.point = point) : Found bank point :=
  match outcome with
  | .found retained => retained
  | .absent missing => False.elim (by
      rcases present with ⟨entry, member, equal⟩
      exact find_ne_none bank entry member (equal.symm ▸ missing))

/-- The original finite outcome is the SAME found branch returned by its membership-paid locator.

The original cached Found and all its observations survive unchanged. Erased
membership only rules out the absent branch; no bank scan or entry/observer
factory is executed to recover an occurrence.
-/
theorem locate_eq {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}
    (outcome : Outcome bank point) (present : ∃ entry, entry ∈ bank ∧ entry.point = point) :
    outcome = .found (outcome.locate present) := by
  cases outcome with
  | found retained =>
      unfold locate
      rfl
  | absent missing =>
      rcases present with ⟨entry, member, equal⟩
      exact False.elim (find_ne_none bank entry member (equal.symm ▸ missing))

end Outcome

/-- Locate the actual first bank match with one original check and erased membership evidence. -/
def locate (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2)
    (present : ∃ entry, entry ∈ bank ∧ entry.point = point) : Found bank point :=
  (bank.check point).locate present

/-- The first primitive's total finite lookup reads its actual cached bank witness when present. -/
@[expose] def zero (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) : Canonical :=
  match bank.find point with
  | some entry => entry.readings.zero.reading.value
  | none => 0

/-- The second primitive's total finite lookup reads its actual cached bank witness when present. -/
@[expose] def one (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) : Canonical :=
  match bank.find point with
  | some entry => entry.readings.one.reading.value
  | none => 0

/-- The scalar primitive's total finite lookup reads its actual cached bank witness when present. -/
@[expose] def scalar (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2) : Canonical :=
  match bank.find point with
  | some entry => entry.readings.scalar.reading.value
  | none => 0

namespace Found

variable {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}

/-- Retain the actual first bank entry at its original point without reconstructing its owner or requests. -/
@[expose] def head (entry : Vertex.Entry parameter allocation) (remaining : Vertex.Bank parameter allocation) :
    Found (entry :: remaining) entry.point :=
  ⟨entry, find_cons_eq entry remaining entry.point rfl, rfl⟩

/-- Preserve an actual retained lookup when prepending a bank entry at a distinct original lifted point. -/
@[expose] def prepend (first : Vertex.Entry parameter allocation) (found : Found bank point)
    (different : first.point ≠ point) : Found (first :: bank) point :=
  ⟨found.entry, (find_cons_ne first bank point different).trans found.present, found.point_eq⟩

/-- The retained selected entry belongs to the exact original finite bank. -/
theorem member (found : Found bank point) : found.entry ∈ bank := bank.find_member point found.entry found.present

/-- View the exact retained original bank vertex at its certified original lifted point. -/
@[expose] def original (found : Found bank point) : Vertex parameter point := found.point_eq ▸ found.entry.original

/-- Two successful lookups at the same original bank point retain exactly the same original vertex. -/
theorem original_eq (first second : Found bank point) : first.original = second.original := by
  have selected := first.present.symm.trans second.present
  have entries := congrArg (fun value : Option (Vertex.Entry parameter allocation) => value.getD first.entry) selected
  change first.entry = second.entry at entries
  cases first with
  | mk firstEntry firstPresent firstPoint =>
    cases second with
    | mk secondEntry secondPresent secondPoint =>
      change firstEntry = secondEntry at entries
      cases entries
      rfl

/-- Equal ordered original vertices identify the owners of both actual retained first matches.

Both Found values and their independent reading caches remain unchanged.
The equality concerns the entire selected original vertex, including its
continued point, factors and primitive denotations; no distinctness of
physical coordinates or signed keys is required.
-/
theorem original_eq_of_origins (firstBank : Vertex.Bank parameter allocation)
    {replacement : Rational} (lastBank : Vertex.Bank parameter replacement)
    (same : firstBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
      lastBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
    (atPoint : LiftedPoint 2) (first : Found firstBank atPoint) (last : Found lastBank atPoint) :
    first.original = last.original := by
  have firstReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter allocation =>
      (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint))) first.present
  have lastReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter replacement =>
      (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint))) last.present
  have selected := Option.some.inj
    (firstReadback.symm.trans ((find_origins_eq firstBank lastBank same atPoint).trans lastReadback))
  have second_heq (left right : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)
      (equal : left = right) : HEq left.2 right.2 := by
    cases equal
    rfl
  cases first with
  | mk firstEntry firstPresent firstPoint =>
    cases last with
    | mk lastEntry lastPresent lastPoint =>
      cases firstEntry with
      | mk firstLocation firstOriginal firstReadings =>
        cases lastEntry with
        | mk lastLocation lastOriginal lastReadings =>
          cases firstPoint
          cases lastPoint
          exact eq_of_heq (second_heq _ _ selected)

/-- Transport only the point index of the same original cached bank requests. -/
@[expose] def readings (found : Found bank point) : Vertex.Readings found.original allocation :=
  match found with
  | ⟨entry, _, same⟩ => by
    cases same
    exact entry.readings

/-- The first original bank witness is the actual finite lookup at the retained point. -/
theorem zero_eq (found : Found bank point) : found.readings.zero.reading.value = bank.zero point := by
  cases found with
  | mk entry present same =>
      cases same
      change entry.readings.zero.reading.value = _
      rewrite [zero, present]
      rfl

/-- The second original bank witness is the actual finite lookup at the retained point. -/
theorem one_eq (found : Found bank point) : found.readings.one.reading.value = bank.one point := by
  cases found with
  | mk entry present same =>
      cases same
      change entry.readings.one.reading.value = _
      rewrite [one, present]
      rfl

/-- The scalar original bank witness is the actual finite lookup at the retained point. -/
theorem scalar_eq (found : Found bank point) : found.readings.scalar.reading.value = bank.scalar point := by
  cases found with
  | mk entry present same =>
      cases same
      change entry.readings.scalar.reading.value = _
      rewrite [scalar, present]
      rfl

end Found

/-- Different retained bank occurrences have different original lifted point keys. -/
abbrev Distinct (bank : Vertex.Bank parameter allocation) :=
  bank.Pairwise (fun first last => first.point ≠ last.point)

namespace Distinct

open Purelib.Data.List

/-- A distinct-key bank has only one retained entry at any one original lifted point. -/
theorem eq_of_point_eq {bank : Vertex.Bank parameter allocation} (distinct : Distinct bank)
    {first last : Vertex.Entry parameter allocation} (firstMember : first ∈ bank) (lastMember : last ∈ bank)
    (equal : first.point = last.point) : first = last := by
  induction bank with
  | nil => cases firstMember
  | cons head remaining induction =>
      rcases Membership.mem_cons.mp firstMember with same | firstMember
      · subst first
        rcases Membership.mem_cons.mp lastMember with same | lastMember
        · exact same.symm
        · exact False.elim ((List.pairwise_cons.mp distinct).1 last lastMember equal)
      · rcases Membership.mem_cons.mp lastMember with same | lastMember
        · subst last
          exact False.elim ((List.pairwise_cons.mp distinct).1 first firstMember equal.symm)
        · exact induction (List.pairwise_cons.mp distinct).2 firstMember lastMember

end Distinct

namespace Found

/-- In a checked distinct bank, the actual selected vertex is the supplied original member at that same point.

The supplied entry occurs only in this proof. Its executable vertex or
request factory is never used to choose or rebuild the actual Found data.
-/
theorem original_eq_entry {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2}
    (found : Found bank point) (distinct : Distinct bank) (entry : Vertex.Entry parameter allocation)
    (member : entry ∈ bank) (pointEq : entry.point = point) :
    found.original = (pointEq ▸ entry.original) := by
  have equal := distinct.eq_of_point_eq found.member member (found.point_eq.trans pointEq.symm)
  cases found with
  | mk actual present actualPoint =>
      change actual = entry at equal
      cases equal
      rfl

end Found

set_option genInjectivity false in
/-- Either all original bank keys are distinct or two actual original occurrences have the same lifted point.

The repeated case retains an exact prefix/tail decomposition and the
actual first matching lookup within that retained tail. It disproves
key-distinctness only, without comparing or rejecting their root branches.
-/
inductive DistinctOutcome (bank : Vertex.Bank parameter allocation) : Type 1 where
  /-- Every two different original occurrences have different lifted point keys. -/
  | distinct (paid : Distinct bank)
  /-- An original entry repeats the point of the actual selected entry in its original retained tail. -/
  | repeated (before : Vertex.Bank parameter allocation) (entry : Vertex.Entry parameter allocation)
      (remaining : Vertex.Bank parameter allocation) (bank_eq : bank = before ++ entry :: remaining)
      (found : Found remaining entry.point)

constructive_injectivity DistinctOutcome

namespace DistinctOutcome

/-- A retained repeated-tail lookup explicitly disproves distinctness of the original bank's lifted point keys. -/
theorem repeated_not_distinct {bank : Vertex.Bank parameter allocation}
    (before : Vertex.Bank parameter allocation) (entry : Vertex.Entry parameter allocation)
    (remaining : Vertex.Bank parameter allocation) (equal : bank = before ++ entry :: remaining)
    (found : Found remaining entry.point) : ¬ Distinct bank := by
  intro distinct
  have suffix : ∀ beforeEntries : Vertex.Bank parameter allocation,
      Distinct (beforeEntries ++ entry :: remaining) → Distinct (entry :: remaining) := by
    intro beforeEntries
    induction beforeEntries with
    | nil => intro paid; exact paid
    | cons head tail induction =>
        intro paid
        exact induction (List.pairwise_cons.mp paid).2
  have final := suffix before (equal ▸ distinct)
  exact (List.pairwise_cons.mp final).1 found.entry found.member found.point_eq.symm

end DistinctOutcome

/-- Check original bank-key distinctness using its existing finite lookups and retain a real repeated occurrence.

Each accepted head has an actual absent-tail lookup, while the recursion
checks the unchanged tail. A repeated point stops with the exact original
prefix, current entry and tail Found; it asserts no root mismatch.
-/
def checkDistinct : (bank : Vertex.Bank parameter allocation) → DistinctOutcome bank
  | [] => .distinct List.Pairwise.nil
  | entry :: remaining =>
      match check remaining entry.point with
      | .found found => .repeated [] entry remaining rfl found
      | .absent missing =>
          match checkDistinct remaining with
          | .distinct paid => .distinct (List.pairwise_cons.mpr ⟨fun other member same =>
              find_ne_none remaining other member (same ▸ missing), paid⟩)
          | .repeated before repeated rest equal found =>
              .repeated (entry :: before) repeated rest (congrArg (fun tail => entry :: tail) equal) found

end Vertex.Bank

end Purelib.Curves.Legendre.Periods.Jets.Source

end
