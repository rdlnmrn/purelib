module
public import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Approximation.Gaussian.Coherent.Additive.Sum

/-- Recursive addition of a literal finite list of productive names. -/
def sumList : List
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed ->
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
  | [] => Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0
  | value :: remaining =>
      Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add value
        (sumList remaining)

/-- Finite list concatenation is operational addition of the two finite sums. -/
def sumList_append (first second : List
  Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent (sumList (first ++ second)).name
      (CoherentNamed.add
        (sumList first)
          (sumList second)).name := by
  induction first with
  | nil =>
      exact NamedEquivalent.symm
        (Add.coherentAdd_zero_left (sumList second))
  | cons value remaining inductionHypothesis =>
      apply NamedEquivalent.trans
      · exact Congruence.coherentAdd_respects
          value value (sumList (remaining ++ second))
          (CoherentNamed.add
            (sumList remaining)
              (sumList second))
          (NamedEquivalent.refl value.name)
          inductionHypothesis
      · exact NamedEquivalent.symm
          (Add.coherentAdd_assoc
            value (sumList remaining)
              (sumList second))
end Purelib.Approximation.Gaussian.Coherent.Additive.Sum

end
