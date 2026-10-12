module
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
@[expose] public section

/-! # Transporting exact rational provenance through finite arithmetic -/

namespace Purelib.Approximation.Gaussian.Division.Obstruction.Symbolic

/-- A denominator formed by a coherent name plus its stateful negation exhausts every finite division-preflight budget.

The obstruction retains the actual reachable denominator state and follows from the operational zero identity of the
original sum. -/
theorem addNeg_excludes_every_budget (input
  numerator : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State (CoherentNamed.add input
      (CoherentNamed.neg input))) (fuel : Nat) :
    ∃ final reachable, Run.attempt numerator
      (CoherentNamed.add input
        (CoherentNamed.neg input)) state fuel =
      .exhausted final reachable :=
  Obstruction.Zero.ZeroIdentity.attempt_exhausts
    (channel := CoherentNamed.add input
      (CoherentNamed.neg input))
    (Neg.coherentAdd_neg_right input)
    numerator state fuel

end Purelib.Approximation.Gaussian.Division.Obstruction.Symbolic

end
