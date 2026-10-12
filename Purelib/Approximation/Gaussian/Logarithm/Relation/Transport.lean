module
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
public import Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Relation.Refinement
import Init.Prelude
import Purelib.Approximation.Relation.Fibre
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Logarithm.Relation.Basic (Candidate)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Relation

open Purelib.Approximation.Relation.Refinement

section
@[expose] public section

/-!
# Local logarithm branches as a finite multivalued relation

A candidate is one anchored chart on one explicit coherent input cell, tagged
by a caller-supplied persistent owner.  A displayed finite family is local; it
does not enumerate all logarithm values.  Until separation has genuinely been
certified, distinct candidates remain in one explicit unresolved cluster.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Transport
universe u

/-- Transport one candidate through one actual safe overlap while retaining its persistent owner. -/
def transportCandidate {Owner : Type u} (source :
  Candidate Owner)
    (target : Coherent.CoherentNamed)
    (extension : Transport.SafeOverlapExtension
      source.input target source.branch) : Candidate Owner where
  owner := source.owner
  input := target
  branch := extension.transport source.branch

set_option genInjectivity false in
/-- Simultaneous local transport data for one displayed family. -/
structure TransportFamily {Owner : Type u} {count :
  Nat}
    (source : Fin count → Candidate Owner) where
  /-- The coherent target input retained at each original finite label. -/ target : Fin count → Coherent.CoherentNamed
  /-- The safe overlap extension for each original branch and its same-labelled target. -/ extension : ∀ label,
    Transport.SafeOverlapExtension
      (source label).input (target label) (source label).branch

constructive_injectivity TransportFamily

namespace TransportFamily

/-- Transport the candidate at the supplied label using its retained target and safe overlap extension. -/
def candidate {Owner : Type u} {count
  : Nat}
    {source : Fin count → Candidate Owner}
    (transport : Approximation.Gaussian.Logarithm.Relation.Transport.TransportFamily source) (label : Fin count) :
    Candidate Owner :=
  Approximation.Gaussian.Logarithm.Relation.Transport.transportCandidate (source label) (transport.target label)
    (transport.extension label)

/-- Each old owner continues to exactly its same-labelled transported branch. Changing cardinality remains available in
the generic core, but is not invented by overlap transport itself. -/
def refinement {Owner : Type u}
  {count : Nat}
    {source : Fin count → Candidate Owner}
    (transport : Approximation.Gaussian.Logarithm.Relation.Transport.TransportFamily source) :
    Approximation.Relation.Refinement
      (Relation.Basic.localFibre source) (Relation.Basic.localFibre transport.candidate) Relation.Basic.Continues :=
  Approximation.Relation.Refinement.ofLabelEquivalence
    (fun label => label) (fun label => label) (fun _ => rfl)
    (fun _ => rfl)

/-- The transported family continues each original label at exactly the same singleton label. -/
@[simp] theorem refinement_continues
    {Owner : Type u} {count : Nat}
    {source : Fin count → Candidate Owner}
    (transport : Approximation.Gaussian.Logarithm.Relation.Transport.TransportFamily source) (label : Fin count) :
    transport.refinement.continues label = [label] := rfl

end TransportFamily
end Purelib.Approximation.Gaussian.Logarithm.Relation.Transport

end

public section
namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Transport

end Purelib.Approximation.Gaussian.Logarithm.Relation.Transport
end
