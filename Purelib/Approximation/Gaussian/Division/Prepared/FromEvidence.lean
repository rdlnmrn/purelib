module
public import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
@[expose] public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared

/-- Build an equivalent prepared denominator from apartness at the exact retained refinement state.

The result keeps the constructed denominator, its whole-ball apartness and its operational identity to the original
channel. -/
def ofEvidence {channel : Coherent.CoherentNamed}
  (state : Name.Coherent.Refinement.State channel)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based channel.name.process state.source)) : Prepared channel :=
  { denominator := Preparation.preparedDenominator state evidence
    apart := Preparation.preparedApart state evidence
    equivalent := Equivalence.preparedDenominatorEquivalent state evidence }
end Purelib.Approximation.Gaussian.Division.Prepared

end
