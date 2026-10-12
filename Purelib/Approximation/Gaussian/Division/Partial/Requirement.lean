module
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial

/-- The sole manually satisfiable obligation for division at a retained state. Its state index prevents a certificate
for another base state from being replayed here. -/
inductive Requirement {denominator :
  Coherent.CoherentNamed}
    (state : State denominator) : Type
  /-- Request a positive uniform squared-norm lower bound for all candidates of the exact retained denominator state. -/
    | candidateApartness

namespace Requirement

/-- Division preflight has no constructive automatic exclusion certificate. In particular, repeated failure of centre
separation cannot inhabit this family and therefore cannot be mistaken for proof that the denominator is zero. -/
inductive Exclusion {denominator :
  Coherent.CoherentNamed}
    (state : State denominator) : Type

/-- Evidence is indexed by the exact requirement and retained state. -/
def Evidence {denominator : Coherent.CoherentNamed}
  {state : State denominator} :
    Requirement state → Type
  | .candidateApartness =>
      Possible.PossibleApart
        (Gaussian.Process.Based.based denominator.name.process state.source)

end Requirement

end Purelib.Approximation.Gaussian.Division.Partial

end

section
@[expose] public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

section Purelib.CCL.Progressive.PartialLogQuotient

section Division
end Division
end Purelib.CCL.Progressive.PartialLogQuotient

end
