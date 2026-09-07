import CCL.Progressive.LogRelation
import CCL.Progressive.PartialLogarithmExamples

/-!
# Finite local logarithm-relation examples

Two branches obtained from different retained target states share one explicit
owner but remain in an unresolved local cluster.  Selection of the second is
performed only after constructing a zero-discrepancy alignment to the first.
-/

namespace CCL.ProgressiveLogRelationExamples

open CCL.ProgressiveLogRelation

inductive Owner
  | principal
  deriving DecidableEq

def firstCandidate : Candidate Owner where
  owner := .principal
  input := CCL.ProgressivePartialLogarithm.preparedTarget
    CCL.ProgressivePartialLogarithmExamples.refined
  branch := CCL.ProgressivePartialLogarithmExamples.refinedOutput

def secondCandidate : Candidate Owner where
  owner := .principal
  input := CCL.ProgressivePartialLogarithm.preparedTarget
    CCL.ProgressivePartialLogarithmExamples.refinedAgain
  branch := CCL.ProgressivePartialLogarithmExamples.refinedAgainOutput

def candidates : Fin 2 → Candidate Owner :=
  Fin.cases firstCandidate (fun _ => secondCandidate)

def displayedFibre := localFibre candidates

def both_candidates_satisfy_the_local_relation (label : Fin 2) :
    RelationWitness (candidates label) :=
  displayedFibre.certified label

/-- Cross-schedule chart congruence supplies exactly the explicit local
alignment required to select the second candidate relative to the first. -/
def secondAlignedToFirst : Aligned secondCandidate firstCandidate :=
  CCL.LogBranchGeometry.difference_zero_of_equivalent
    firstCandidate.branch.output secondCandidate.branch.output
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      CCL.ProgressivePartialLogarithmExamples.different_schedules_equivalent)

def alignedSelection : AlignedSelection candidates where
  label := ⟨1, by decide⟩
  reference := firstCandidate
  aligned := secondAlignedToFirst

@[simp] theorem aligned_selection_is_second :
    (selectAligned alignedSelection).owner = Owner.principal := rfl

/-! ## Same-owner overlap transport -/

def sourceCandidate : Candidate Owner where
  owner := .principal
  input := CCL.ProgressivePartialLogarithmExamples.sourceInput
  branch := CCL.ProgressivePartialLogarithmExamples.sourceAnchor

def singletonSource (_label : Fin 1) : Candidate Owner := sourceCandidate

def singletonTransport : TransportFamily singletonSource where
  target _ := CCL.ProgressivePartialLogarithm.preparedTarget
    CCL.ProgressivePartialLogarithmExamples.refined
  extension _ := CCL.ProgressivePartialLogarithmExamples.refinedExtension

@[simp] theorem overlap_transport_retains_owner (label : Fin 1) :
    singletonTransport.refinement.continues label = [label] := rfl

end CCL.ProgressiveLogRelationExamples
