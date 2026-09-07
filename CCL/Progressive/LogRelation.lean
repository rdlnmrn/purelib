import CCL.Progressive.FiniteRelation
import CCL.Transcendental.LogChartCongruence
import CCL.Transcendental.LogExpInverse

/-!
# Local logarithm branches as a finite multivalued relation

A candidate is one anchored chart on one explicit coherent input cell, tagged
by a caller-supplied persistent owner.  A displayed finite family is local; it
does not enumerate all logarithm values.  Until separation has genuinely been
certified, distinct candidates remain in one explicit unresolved cluster.
-/

namespace CCL.ProgressiveLogRelation

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Fibre := CCL.FiniteMultivaluedRelation.Fibre

universe u

/-- One local logarithm branch with a persistent caller-defined identity. -/
structure Candidate (Owner : Type u) : Type (max u 2) where
  owner : Owner
  input : CoherentNamed
  branch : AnchoredChart input

/-- The finite logarithm relation witness carried by every candidate. -/
def RelationWitness {Owner : Type u} (candidate : Candidate Owner) : Type :=
  NamedEquivalent
    (CCL.ProgressiveExpRange.named candidate.branch.output.name)
    candidate.input.name

/-- No generic separation test between independently acquired logarithm
branches is claimed.  Clients may later replace this empty family with a
genuine local cell-separation certificate. -/
inductive BranchSeparated {Owner : Type u}
    (left right : Candidate Owner) : Type

/-- Every pair is conservatively retained in one unresolved local cluster. -/
def localFibre {Owner : Type u} {count : Nat}
    (candidate : Fin count → Candidate Owner) :
    Fibre (Candidate Owner) BranchSeparated RelationWitness where
  count := count
  candidate := candidate
  certified := fun label => (candidate label).branch.exponential_inverse
  clusterCount := 1
  cluster _ := List.ofFn id
  pairResolution := by
    intro left right _different
    exact Sum.inr
      ⟨⟨0, by decide⟩,
        List.mem_ofFn.mpr ⟨left, rfl⟩,
        List.mem_ofFn.mpr ⟨right, rfl⟩⟩

/-- Refinement preserves branch identity only through the explicit owner tag. -/
def Continues {Owner : Type u}
    (old new : Candidate Owner) : Prop := old.owner = new.owner

theorem Continues.refl {Owner : Type u} (candidate : Candidate Owner) :
    Continues candidate candidate := rfl

theorem Continues.trans {Owner : Type u} {first second third : Candidate Owner}
    (firstSecond : Continues first second)
    (secondThird : Continues second third) : Continues first third :=
  Eq.trans firstSecond secondThird

/-- Transport one candidate through one actual safe overlap while retaining
its persistent owner. -/
def transportCandidate {Owner : Type u} (source : Candidate Owner)
    (target : CoherentNamed)
    (extension : CCL.LogBranchGeometry.SafeOverlapExtension
      source.input target source.branch) : Candidate Owner where
  owner := source.owner
  input := target
  branch := extension.transport source.branch

/-- Simultaneous local transport data for one displayed family. -/
structure TransportFamily {Owner : Type u} {count : Nat}
    (source : Fin count → Candidate Owner) where
  target : Fin count → CoherentNamed
  extension : ∀ label,
    CCL.LogBranchGeometry.SafeOverlapExtension
      (source label).input (target label) (source label).branch

namespace TransportFamily

def candidate {Owner : Type u} {count : Nat}
    {source : Fin count → Candidate Owner}
    (transport : TransportFamily source) (label : Fin count) :
    Candidate Owner :=
  transportCandidate (source label) (transport.target label)
    (transport.extension label)

/-- Each old owner continues to exactly its same-labelled transported branch.
Changing cardinality remains available in the generic core, but is not
invented by overlap transport itself. -/
def refinement {Owner : Type u} {count : Nat}
    {source : Fin count → Candidate Owner}
    (transport : TransportFamily source) :
    CCL.FiniteMultivaluedRelation.Refinement
      (localFibre source) (localFibre transport.candidate) Continues :=
  CCL.FiniteMultivaluedRelation.Refinement.ofLabelEquivalence
    (fun label => label) (fun label => label) (fun _ => rfl)
    (fun _ => rfl)

@[simp] theorem refinement_continues
    {Owner : Type u} {count : Nat}
    {source : Fin count → Candidate Owner}
    (transport : TransportFamily source) (label : Fin count) :
    transport.refinement.continues label = [label] := rfl

end TransportFamily

/-- Explicit zero discrepancy aligns one displayed branch to an independently
owned reference branch. -/
def Aligned {Owner : Type u}
    (candidate reference : Candidate Owner) : Type :=
  CCL.LogExpInverse.LocalAlignment
    reference.branch.output candidate.branch.output

abbrev AlignedSelection {Owner : Type u} {count : Nat}
    (candidate : Fin count → Candidate Owner) :=
  CCL.FiniteMultivaluedRelation.AlignedSelection Aligned
    (localFibre candidate)

/-- Selection exposes exactly the candidate named by explicit alignment; list
order and numerical nearest-neighbour rules play no role. -/
def selectAligned {Owner : Type u} {count : Nat}
    {candidate : Fin count → Candidate Owner}
    (selection : AlignedSelection candidate) : Candidate Owner :=
  (localFibre candidate).candidate selection.label

/-- Two target branches transported from the same source candidate are
operationally equivalent whenever their target inputs are operationally
equivalent. -/
def transported_outputs_equivalent {Owner : Type u}
    (source : Candidate Owner)
    (firstTarget secondTarget : CoherentNamed)
    (firstExtension : CCL.LogBranchGeometry.SafeOverlapExtension
      source.input firstTarget source.branch)
    (secondExtension : CCL.LogBranchGeometry.SafeOverlapExtension
      source.input secondTarget source.branch)
    (targetsEquivalent : NamedEquivalent
      firstTarget.name secondTarget.name) :
    NamedEquivalent
      (firstExtension.transport source.branch).output.name
      (secondExtension.transport source.branch).output.name :=
  CCL.LogChartCongruence.transportedOutput_respects source.branch
    firstExtension secondExtension targetsEquivalent

end CCL.ProgressiveLogRelation
