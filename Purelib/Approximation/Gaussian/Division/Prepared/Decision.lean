module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

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

set_option genInjectivity false in
/-- An exact division decision for the retained coherent channel.

The alternatives supply either an equivalent apart denominator presentation or an operational identity to zero. -/
inductive Decision (channel : Coherent.CoherentNamed) :
  Type 1
  /-- Retain an equivalent whole-ball-apart presentation of the original channel. -/ | prepared (result :
    Prepared channel)
  /-- Retain the original channel's finite operational identity to zero. -/ | excluded (identity : Zero.ZeroIdentity
    channel)

constructive_injectivity Decision

end Purelib.Approximation.Gaussian.Division.Prepared

end
