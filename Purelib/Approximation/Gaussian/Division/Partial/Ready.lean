module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

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

namespace Ready

/-- The ordinary total quotient returned after preflight succeeds. -/
def readyName (numerator denominator :
  Coherent.CoherentNamed)
    (state : Name.Coherent.Refinement.State denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source)) :
    Coherent.CoherentNamed :=
  CoherentNamed.div numerator
    (Preparation.preparedDenominator state evidence) (Preparation.preparedApart state evidence)

end Ready

set_option genInjectivity false in
/-- A ready result records the exact state-indexed evidence from which its ordinary coherent quotient was constructed.
-/
structure Ready (numerator denominator :
  Coherent.CoherentNamed)
    (state : Name.Coherent.Refinement.State denominator) (output : Coherent.CoherentNamed) where
  /-- The denominator apartness witness indexed by the exact retained refinement source. -/ evidence :
    Possible.PossibleApart
    (Gaussian.Process.Based.based denominator.name.process state.source)
  /-- The retained output is exactly the quotient constructed from this state and its apartness evidence. -/ output_eq :
    output = Ready.readyName numerator denominator state evidence

constructive_injectivity Ready

end Purelib.Approximation.Gaussian.Division.Partial

end
