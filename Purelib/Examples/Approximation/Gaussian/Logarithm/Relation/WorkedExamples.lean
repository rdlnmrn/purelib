module
public import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Relation.Alignment
import Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Relation.Transport
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
public import Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.WorkedExamples
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Relation.Refinement
import Purelib.Approximation.Relation.Fibre
import Purelib.Approximation.Relation.Selection

@[expose] public section

/-!
# Finite local logarithm-relation examples

Two branches obtained from different retained target states share one explicit
owner but remain in an unresolved local cluster.  Selection of the second is
performed only after constructing a zero-discrepancy alignment to the first.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Relation.WorkedExamples

open Purelib.Examples.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Examples.Approximation.Gaussian
open Purelib.Data
open Purelib.Approximation.Gaussian.Name

/-- The single retained principal owner of the displayed logarithm candidates. -/
inductive Owner
  /-- The retained principal logarithm owner. -/ | principal
  deriving DecidableEq

/-- The principal candidate from the once-refined target and its transported chart. -/
def firstCandidate : Logarithm.Relation.Basic.Candidate Owner where
  owner := .principal
  input := LogarithmState.preparedTarget
    Partial.WorkedExamples.refined
  branch := Partial.WorkedExamples.refinedOutput

/-- The same principal owner with the twice-refined target and transported chart. -/
def secondCandidate : Logarithm.Relation.Basic.Candidate Owner where
  owner := .principal
  input := LogarithmState.preparedTarget
    Partial.WorkedExamples.refinedAgain
  branch := Partial.WorkedExamples.refinedAgainOutput

/-- The ordered two-candidate family from the original refinement schedules. -/
def candidates : Fin 2 → Logarithm.Relation.Basic.Candidate Owner :=
  Fin.casesByRecursion firstCandidate (fun _ =>
    secondCandidate)

/-- The certified local logarithm fibre over the two retained candidates. -/
def displayedFibre := Logarithm.Relation.Basic.localFibre candidates

/-- Each retained candidate has its original local logarithm relation witness. -/
def both_candidates_satisfy_the_local_relation (label : Fin 2) :
    Logarithm.Relation.Basic.RelationWitness (candidates label) :=
  displayedFibre.certified label

/-- Alignment of the second retained candidate to the first candidate's chart.

Uses the exact operational equivalence of the two original schedule outputs to certify their zero difference. -/
def secondAlignedToFirst : Logarithm.Relation.Alignment.Aligned secondCandidate
  firstCandidate :=
  Coherent.Difference.difference_zero_of_equivalent
    firstCandidate.branch.output
      secondCandidate.branch.output
    (Equivalence.NamedEquivalent.symm
      Partial.WorkedExamples.different_schedules_equivalent)

/-- Select the second original candidate with its retained first-candidate alignment. -/
def alignedSelection : Logarithm.Relation.Alignment.AlignedSelection candidates where
  label := ⟨1, by decide⟩
  reference := firstCandidate
  aligned := secondAlignedToFirst

/-- The aligned selection retains the principal owner. -/
@[simp] theorem aligned_selection_is_second :
    (Logarithm.Relation.Alignment.selectAligned alignedSelection).owner =
      Owner.principal := rfl

/-! ## Same-owner overlap transport -/

/-- The principal candidate retaining the original exact source anchor. -/
def sourceCandidate : Logarithm.Relation.Basic.Candidate Owner where
  owner := .principal
  input := Partial.WorkedExamples.sourceInput
  branch := Partial.WorkedExamples.sourceAnchor

/-- The singleton family of the original principal source candidate. -/
def singletonSource (_label : Fin 1) : Logarithm.Relation.Basic.Candidate Owner :=
  sourceCandidate

/-- Transport the singleton source through the retained safe overlap extension.

Keeps the original once-refined target and the same chart-extension certificate. -/
def singletonTransport : Logarithm.Relation.Transport.TransportFamily singletonSource
  where
  target _ := LogarithmState.preparedTarget
    Partial.WorkedExamples.refined
  extension _ := Partial.WorkedExamples.refinedExtension

/-- The overlap transport continues the original singleton label unchanged. -/
@[simp] theorem overlap_transport_retains_owner (label : Fin 1) :
    singletonTransport.refinement.continues label = [label] := rfl

end Purelib.Examples.Approximation.Gaussian.Logarithm.Relation.WorkedExamples

end
