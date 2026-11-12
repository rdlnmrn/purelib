module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
public import Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement.Check

/-! # Actual bank lookups with checked original-owner refinements

The original finite lookup is retained once. If it finds an entry, the
specified finite common-refinement check uses that exact selected vertex
owner and the supplied original continued point. An absent lookup or unpaid
strict containment remains visible in the complete retained result.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Vertex.Bank

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter : Canonical} {count : Nat} {point : LiftedPoint 2}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {allocation : Rational}

/-- The actual first matching bank lookup and its original-owner common-refinement attempt when present.

The dependent second component exists only for a real found entry. It
retains the entire existing finite checking outcome rather than replacing
an absent or unpaid branch by a root or a desired numerical comparison.
The final field retains that same original lookup's actual first position;
no second lookup or source query is executed to recover its occurrence.
-/
abbrev RootCheck (sample : ContinuedNeighborhood.Point patch point.coordinate)
    (bank : Vertex.Bank parameter allocation) (stage : Nat) :=
  (lookup : Outcome bank point) ×
    (match lookup with
      | .found found => RootOwnerCommonRefinement.Outcome sample.owner found.original.sample.owner stage
      | .absent _ => PUnit) × Position lookup

namespace RootCheck

variable {sample : ContinuedNeighborhood.Point patch point.coordinate}
variable {bank : Vertex.Bank parameter allocation} {stage : Nat}

/-- A bank endpoint is ready exactly when its actual lookup exists and its retained common refinement passed. -/
@[expose] def Ready : RootCheck sample bank stage → Prop
  | ⟨.found _, .ready _ _, _⟩ => True
  | ⟨.found _, .inconclusive _ _ _ _, _⟩ => False
  | ⟨.absent _, _, _⟩ => False

/-- Decide readiness from the already retained lookup and containment outcome without running either again. -/
@[expose] def decideReady : (checked : RootCheck sample bank stage) → Decidable checked.Ready
  | ⟨.found _, .ready _ _, _⟩ => isTrue True.intro
  | ⟨.found _, .inconclusive _ _ _ _, _⟩ => isFalse (fun impossible => impossible)
  | ⟨.absent _, _, _⟩ => isFalse (fun impossible => impossible)

/-- Read the SAME actual first-occurrence cache kept beside the unchanged lookup and refinement outcome. -/
@[expose] def occurrence (checked : RootCheck sample bank stage) : Position checked.1 := checked.2.2

/-- Forget only positional evidence, retaining the complete original lookup and common-refinement outcome. -/
@[expose] def eraseOccurrence (checked : RootCheck sample bank stage) :
    (lookup : Outcome bank point) ×
      match lookup with
      | .found found => RootOwnerCommonRefinement.Outcome sample.owner found.original.sample.owner stage
      | .absent _ => PUnit :=
  ⟨checked.1, checked.2.1⟩

/-- Perform the original common-refinement check on the SAME retained lookup outcome.

Only a found case checks the supplied point against that exact original
selected bank Owner. An absent case returns its original empty check data.
This is the original checkRoot branch operation, shared before packing the
additional occurrence evidence.
-/
def checkLookup (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat)
    (lookup : Outcome bank point) :
    match lookup with
    | .found found => RootOwnerCommonRefinement.Outcome sample.owner found.original.sample.owner stage
    | .absent _ => PUnit :=
  match lookup with
  | .found found => RootOwnerCommonRefinement.checkAt sample.owner found.original.sample.owner stage
  | .absent _ => PUnit.unit

/-- A retained found lookup invokes the original common-refinement factory on its exact selected Owner. -/
theorem checkLookup_found (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat)
    (found : Found bank point) :
    checkLookup sample stage (.found found) =
      RootOwnerCommonRefinement.checkAt sample.owner found.original.sample.owner stage := by
  unfold checkLookup
  rfl

/-- An absent original lookup performs no common-refinement acquisition. -/
theorem checkLookup_absent (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat)
    (missing : find bank point = none) : checkLookup sample stage (.absent missing) = PUnit.unit := by
  unfold checkLookup
  rfl

end RootCheck

/-- Locate the actual original bank entry once and check one refinement of that exact selected owner.

The unchanged sample, actual first matching Found and requested finite
stage determine the check. The missing-entry branch stores the actual
absence; it neither requests a substitute owner nor changes the bank.
-/
def checkRoot (bank : Vertex.Bank parameter allocation)
    (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat) : RootCheck sample bank stage :=
  let lookup := bank.checkWithOccurrence point
  ⟨lookup.1, RootCheck.checkLookup sample stage lookup.1, lookup.2⟩

/-- Forgetting positional evidence keeps the complete original lookup and its exact original refinement factory.

The scalar lookup equality transports the full dependent pair, not only
its selected entry or readiness Boolean. No lookup or refinement executes
as data during this readback proof.
-/
theorem checkRoot_eraseOccurrence (bank : Vertex.Bank parameter allocation)
    (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat) :
    (checkRoot bank sample stage).eraseOccurrence =
      ⟨check bank point, RootCheck.checkLookup sample stage (check bank point)⟩ := by
  unfold checkRoot RootCheck.eraseOccurrence
  exact congrArg (fun lookup : Outcome bank point =>
    (⟨lookup, RootCheck.checkLookup sample stage lookup⟩ :
      (original : Outcome bank point) ×
        match original with
        | .found found => RootOwnerCommonRefinement.Outcome sample.owner found.original.sample.owner stage
        | .absent _ => PUnit))
    (checkWithOccurrence_outcome bank point)

/-- An actual Found fixes the whole retained original lookup/refinement projection.

The actual first-occurrence cache stays separately retained in RootCheck.
This equality reads its same original lookup and complete checking outcome;
it does not compare positions belonging to different banks.
-/
theorem checkRoot_found (bank : Vertex.Bank parameter allocation)
    (sample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat) (found : Found bank point) :
    (bank.checkRoot (point := point) sample stage).eraseOccurrence =
      ⟨.found found, RootOwnerCommonRefinement.checkAt sample.owner found.original.sample.owner stage⟩ := by
  have selected := check_found (parameter := parameter) (allocation := allocation) (point := point) found
  have same := congrArg (fun lookup : Outcome bank point =>
    (⟨lookup, RootCheck.checkLookup sample stage lookup⟩ :
      (original : Outcome bank point) ×
        match original with
        | .found retained => RootOwnerCommonRefinement.Outcome sample.owner retained.original.sample.owner stage
        | .absent _ => PUnit)) selected
  exact (checkRoot_eraseOccurrence bank sample stage).trans same

namespace RootCheck

/-- Exact original sample and selected-vertex identities preserve the whole retained finite owner-check Outcome.

Both input RootCheck caches and their original factory equations are
retained. Only the actual owner indices are transported; ready Commons,
inconclusive candidates, factory laws and stopping stage remain unchanged.
No scan, refinement, admission or readiness decision is executed.
-/
theorem outcome_heq {replacement : Rational}
    (firstBank : Vertex.Bank parameter allocation) (lastBank : Vertex.Bank parameter replacement)
    (firstSample lastSample : ContinuedNeighborhood.Point patch point.coordinate) (stage : Nat)
    (firstCheck : RootCheck (point := point) firstSample firstBank stage)
    (lastCheck : RootCheck (point := point) lastSample lastBank stage)
    (firstFactory : firstCheck = firstBank.checkRoot (point := point) firstSample stage)
    (lastFactory : lastCheck = lastBank.checkRoot (point := point) lastSample stage)
    (firstFound : Found firstBank point) (lastFound : Found lastBank point)
    (samples : firstSample = lastSample) (originals : firstFound.original = lastFound.original) :
    HEq firstCheck.eraseOccurrence.2 lastCheck.eraseOccurrence.2 := by
  have firstWhole := (congrArg
    (fun checked : RootCheck (point := point) firstSample firstBank stage => checked.eraseOccurrence)
    firstFactory).trans
    (checkRoot_found (parameter := parameter) (point := point) firstBank firstSample stage firstFound)
  have lastWhole := (congrArg
    (fun checked : RootCheck (point := point) lastSample lastBank stage => checked.eraseOccurrence)
    lastFactory).trans
    (checkRoot_found (parameter := parameter) (point := point) lastBank lastSample stage lastFound)
  have second_heq {readingAllocation : Rational} (bank : Vertex.Bank parameter readingAllocation)
      (sample : ContinuedNeighborhood.Point patch point.coordinate)
      (first last : (lookup : Outcome bank point) ×
        match lookup with
        | .found retained => RootOwnerCommonRefinement.Outcome sample.owner retained.original.sample.owner stage
        | .absent _ => PUnit) (equal : first = last) :
      HEq first.2 last.2 := by
    cases equal
    rfl
  have check_heq {radicand : Canonical}
      (firstLeft firstRight lastLeft lastRight : RootOwnerCommonRefinement.Owner radicand)
      (left : firstLeft = lastLeft) (right : firstRight = lastRight) :
      HEq (RootOwnerCommonRefinement.checkAt firstLeft firstRight stage)
        (RootOwnerCommonRefinement.checkAt lastLeft lastRight stage) := by
    cases left
    cases right
    rfl
  have firstOwners := congrArg
    (fun sample : ContinuedNeighborhood.Point patch point.coordinate => sample.owner) samples
  have lastOwners := congrArg (fun vertex : Vertex parameter point => vertex.sample.owner) originals
  have outcomes := check_heq _ _ _ _ firstOwners lastOwners
  exact (second_heq firstBank firstSample firstCheck.eraseOccurrence _ firstWhole).trans
    (outcomes.trans (second_heq lastBank lastSample lastCheck.eraseOccurrence _ lastWhole).symm)

end RootCheck

end Purelib.Curves.Legendre.Periods.Jets.Source.Vertex.Bank

end
