module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Relation.Fibre
import Init.Core
import Init.Data.List.OfFn
public import Purelib.Data.List.OfFn.Basic
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Relation

section
@[expose] public section

/-!
# Local logarithm branches as a finite multivalued relation

A candidate is one anchored chart on one explicit coherent input cell, tagged
by a caller-supplied persistent owner.  A displayed finite family is local; it
does not enumerate all logarithm values.  Until separation has genuinely been
certified, distinct candidates remain in one explicit unresolved cluster.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
universe u

set_option genInjectivity false in
/-- One local logarithm branch with a persistent caller-defined identity. -/
structure Candidate (Owner : Type u) : Type (max u 2)
  where
  /-- The persistent caller-supplied identity of this local branch. -/ owner : Owner
  /-- The original coherent input cell retained by the candidate. -/ input : Coherent.CoherentNamed
  /-- The anchored logarithm chart indexed by the retained input. -/ branch : Anchored.AnchoredChart input

constructive_injectivity Candidate

/-- The finite logarithm relation witness carried by every candidate. -/
def RelationWitness {Owner : Type u} (candidate :
  Candidate Owner) : Type :=
  Gaussian.Equivalence.NamedEquivalent
    (Exponential.Progressive.Range.Name.named candidate.branch.output.name)
    candidate.input.name

/-- No generic separation test between independently acquired logarithm branches is claimed. Clients may later replace
this empty family with a genuine local cell-separation certificate. -/
inductive BranchSeparated {Owner : Type u}
    (left right : Candidate Owner) : Type

/-- Every pair is conservatively retained in one unresolved local cluster. -/
def localFibre {Owner : Type u} {count : Nat}
    (candidate : Fin count → Candidate Owner) :
    Approximation.Relation.Fibre (Candidate Owner)
      BranchSeparated
      RelationWitness where
  count := count
  candidate := candidate
  certified := fun label => (candidate label).branch.exponential_inverse
  clusterCount := 1
  cluster _ := List.ofFn id
  pairResolution := by
    intro left right _different
    exact Sum.inr
      ⟨⟨0, by decide⟩,
        Data.List.OfFn.Basic.mem_ofFn.mpr ⟨left, rfl⟩,
        Data.List.OfFn.Basic.mem_ofFn.mpr ⟨right, rfl⟩⟩

/-- Refinement preserves branch identity only through the explicit owner tag. -/
def Continues {Owner : Type u}
    (old new : Candidate Owner) : Prop := old.owner = new.owner

/-- A branch candidate continues its own persistent owner. -/
theorem Continues.refl {Owner : Type u} (candidate :
  Candidate Owner) :
    Continues candidate candidate := rfl

/-- Equality of retained branch owners composes across two continuation steps. -/
theorem Continues.trans {Owner : Type u} {first second
  third : Candidate Owner}
    (firstSecond : Continues first second)
    (secondThird : Continues second third) :
      Continues first third :=
  Eq.trans firstSecond secondThird
end Purelib.Approximation.Gaussian.Logarithm.Relation.Basic

end

public section
namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Basic

end Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
end
