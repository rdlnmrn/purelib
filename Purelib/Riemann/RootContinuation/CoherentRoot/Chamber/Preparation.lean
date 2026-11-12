module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Prepared original chamber owners and missing overlap requests

The acquisition boundary consumes prepared geometric evidence. A missing
overlap returns the original root cache and both original endpoint frames,
with an equality identifying the absent supplied contract. It makes no claim
of collision, singularity or failure of any later geometric search.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

set_option genInjectivity false in
/-- A finite request retaining the original current root cache and exact missing prepared overlap.

The offered data are part of the request index. Their absence is certified;
the unresolved obligation is an overlap between the same original frames.
-/
structure OverlapRequest {start : ChamberFrame} (finish : ChamberFrame)
    {index : start.Index} (original : Root start index) (offered : Option (ChamberOverlap start finish)) where
  /-- The actual original current root cache, retained for a later retry. -/
  current : Root start index
  /-- The retained current root is the original input object. -/
  current_eq : current = original
  /-- This finite acquisition had no supplied prepared overlap for those same frames. -/
  unavailable : offered = none

constructive_injectivity OverlapRequest

set_option genInjectivity false in
/-- A checked prepared step or a precise request for its absent original overlap.

Success stores the actual supplied overlap and its numerical trace. The request
alternative keeps the actual current root cache and the missing-contract proof.
-/
inductive StepOutcome {start : ChamberFrame} (finish : ChamberFrame)
    {index : start.Index} (original : Root start index) (offered : Option (ChamberOverlap start finish)) : Type 2
  /-- Consume the actual offered overlap and retain its original numerical trace. -/
  | prepared (overlap : ChamberOverlap start finish) (offered_eq : offered = some overlap)
      (trace : Trace (ChamberPath.cons overlap (.nil finish)) index original)
  /-- Retain the exact absent contract and original cache for a later retry. -/
  | requested (request : OverlapRequest finish original offered)

constructive_injectivity StepOutcome

/-- Consume one supplied prepared overlap, or return its exact missing-contract request on the original cache. -/
@[expose] def acquireStep {start : ChamberFrame} (finish : ChamberFrame)
    {index : start.Index} (original : Root start index) :
    (offered : Option (ChamberOverlap start finish)) → StepOutcome finish original offered
  | some overlap => .prepared overlap rfl (Trace.build (.cons overlap (.nil finish)) index original)
  | none => .requested ⟨original, rfl, rfl⟩

/-- Retrying with an original prepared overlap consumes the same request's retained current cache. -/
@[expose] def OverlapRequest.resume {start finish : ChamberFrame} {index : start.Index}
    {original : Root start index} {offered : Option (ChamberOverlap start finish)}
    (request : OverlapRequest finish original offered) (overlap : ChamberOverlap start finish) :
    Trace (.cons overlap (.nil finish)) index request.current :=
  Trace.build (.cons overlap (.nil finish)) index request.current

namespace Trace

open Purelib.RootIsolation

set_option genInjectivity false in
/-- Exact cached local owners at every successive occurrence of an original path.

Each cons keeps the actual selected target index, its equality to the original
overlap's matching and the complete prepared owner there. Its tail follows the
same retained path and index; no segment or intermediate occurrence is
discarded. The starting root cache is supplied separately.
-/
inductive Owners : {start finish : ChamberFrame} →
    (path : ChamberPath start finish) → (index : start.Index) → Type 2
  /-- An empty original path needs no additional owner cache. -/
  | nil (frame : ChamberFrame) (index : frame.Index) : Owners (.nil frame) index
  /-- Retain the next complete original owner and all remaining original occurrences. -/
  | cons {start middle finish : ChamberFrame}
      {step : ChamberOverlap start middle} {remaining : ChamberPath middle finish}
      {index : start.Index}
      (targetIndex : middle.Index) (targetIndex_eq : targetIndex = step.matching.forward index)
      (target : Owner.Local.Preparation.Prepared (middle.owner targetIndex))
      (rest : Owners remaining targetIndex) :
      Owners (.cons step remaining) index

constructive_injectivity Owners

/-- Construct the original numerical trace by consuming its exact cached owners.

The supplied starting cache is retained unchanged. Every next cache is built
from the prepared box and clearance at that same original matched occurrence,
rather than invoking its canonical local-owner producer again.
-/
@[expose] def ofPreparedOwners {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} (source : Root start index) (owners : Owners path index) : Trace path index source :=
  Owners.casesOn (motive := fun {start _} path index _ => (source : Root start index) → Trace path index source)
    owners
    (fun _ _ source => .nil source)
    (fun {_ _ _ step remaining index} targetIndex same prepared rest _ =>
      let target := Root.ofPreparedOwner _ targetIndex prepared
      let cached := ofPreparedOwners target rest
      let transported : Sigma (fun target : Root _ (step.matching.forward index) =>
          Trace remaining (step.matching.forward index) target) := same ▸ ⟨target, cached⟩
      .cons transported.1 transported.2) source
termination_by structural owners

/-- Reindex exact already prepared owner caches along whole equality of their original path. -/
@[expose] def Owners.castPath {start finish : ChamberFrame} {before after : ChamberPath start finish}
    {index : start.Index} (same : before = after) (owners : Owners before index) : Owners after index := same ▸ owners

/-- Reindexing original owner caches in both directions retains their complete original records. -/
theorem Owners.castPath_inverse {start finish : ChamberFrame} {before after : ChamberPath start finish}
    {index : start.Index} (same : before = after) (owners : Owners before index) :
    Owners.castPath same.symm (Owners.castPath same owners) = owners := by
  cases same
  rfl

/-- Exact owner readbacks identify the complete prepared trace with the original builder.

The equality retains the supplied starting cache, every original path segment,
all intermediate matched indices and every numerical track and certified cache.
-/
theorem ofPreparedOwners_eq : {start finish : ChamberFrame} →
    {path : ChamberPath start finish} → {index : start.Index} →
    (source : Root start index) → (owners : Owners path index) →
    ofPreparedOwners source owners = build path index source
  | _, _, .nil _, _, _, .nil _ _ => rfl
  | _, _, .cons step remaining, index, source, .cons targetIndex same prepared rest => by
      cases same
      change Trace.cons (Root.ofPreparedOwner _ _ prepared)
          (ofPreparedOwners (Root.ofPreparedOwner _ _ prepared) rest) =
        Trace.cons (Root.ofOwner _ _) (build _ _ (Root.ofOwner _ _))
      have same := Root.ofPreparedOwner_eq _ (step.matching.forward index) prepared
      rewrite [same]
      exact congrArg (Trace.cons (Root.ofOwner _ (step.matching.forward index)))
        (ofPreparedOwners_eq (Root.ofOwner _ (step.matching.forward index)) rest)

end Trace

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

end
