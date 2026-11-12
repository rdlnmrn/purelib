module

import Purelib.Approximation.Gaussian.Division.Prepared.Factor
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

/-!
# Retained factor observations on an exact product

The original exact operands two and three multiply to six. The same finite
factor observation retains their actual witnesses, the original second-factor
bound and a positive lower norm that prepares the original first operand.
-/

namespace TestPurelib.Approximation.Gaussian.FactorPreparation

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original actual product compares to its exact nonzero Gaussian value. -/
private def identity : NamedEquivalent
    (CoherentNamed.mul (Coherence.exact 2) (Coherence.exact 3)).name (Coherence.exact 6).name := by
  have comparison := Exact.Arithmetic.exact_mul (2 : Canonical) 3
  have product : (2 : Canonical) * 3 = 6 := by decide +kernel
  rewrite [product] at comparison
  exact comparison

/-- The original factor observation retains both actual exact operand states and witnesses. -/
private def observed := Prepared.Factor.observe (Coherence.exact 2) (Coherence.exact 3) 6 (by decide +kernel) identity

example : observed.firstWitness = 2 := rfl
example : observed.secondWitness = 3 := rfl
example : observed.first = Coherence.exact 2 := observed.first_eq
example : observed.second = Coherence.exact 3 := observed.second_eq

example : observed.bound = 20 := by
  rewrite [observed.bound_eq]
  decide +kernel

example : observed.norm = 36 := by
  rewrite [observed.norm_eq]
  decide +kernel

example : Prepared (Coherence.exact 2) := observed.prepare

end TestPurelib.Approximation.Gaussian.FactorPreparation
