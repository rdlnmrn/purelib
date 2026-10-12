module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Congruence
public import Purelib.Approximation.Gaussian.Logarithm.Relation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

/-!
# Local logarithm branches as a finite multivalued relation

A candidate is one anchored chart on one explicit coherent input cell, tagged
by a caller-supplied persistent owner.  A displayed finite family is local; it
does not enumerate all logarithm values.  Until separation has genuinely been
certified, distinct candidates remain in one explicit unresolved cluster.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Relation.Congruence
universe u

/-- Two target branches transported from the same source candidate are operationally equivalent whenever their target
inputs are operationally equivalent. -/
def transported_outputs_equivalent {Owner : Type u}
    (source : Relation.Basic.Candidate Owner)
    (firstTarget secondTarget : Coherent.CoherentNamed)
    (firstExtension : Transport.SafeOverlapExtension
      source.input firstTarget source.branch)
    (secondExtension : Transport.SafeOverlapExtension
      source.input secondTarget source.branch)
    (targetsEquivalent : Gaussian.Equivalence.NamedEquivalent
      firstTarget.name secondTarget.name) :
    Gaussian.Equivalence.NamedEquivalent
      (firstExtension.transport source.branch).output.name
      (secondExtension.transport source.branch).output.name :=
  Congruence.transportedOutput_respects source.branch
    firstExtension secondExtension targetsEquivalent

end Purelib.Approximation.Gaussian.Logarithm.Relation.Congruence

end
