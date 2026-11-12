module

public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Exponential.E

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Gaussian

public section

/-- The Gaussian input one belongs to the closed unit disk. -/
theorem one_unit : Norm.Basic.normSq (1 : Basic.Canonical) ≤ 1 := by
  rw [Norm.Basic.normSq_one]

/-- The stock finite approximation to e uses the original Horner program at one. -/
@[expose] def hornerApproximation : ApproximationData :=
  Horner.Sequence.approximation 1 one_unit

/-- The factorial-sum sample evaluates the original Taylor recurrence at degree `index + 1`.

The underlying recurrence also admits degree zero. Its shifted sample indices
match the degree of the original Horner samples. -/
@[expose] def factorialSample (index : Nat) : Basic.Canonical :=
  Taylor.Basic.truncatedExp 1 (index + 1)

/-- The original Horner and factorial programs give the same finite sample at each index. -/
theorem horner_sample_eq_factorial (index : Nat) :
    hornerApproximation.sample index = factorialSample index :=
  Horner.Taylor.sample_eq_truncatedExp 1 index

/-- Every finite Horner sample at one has zero imaginary coordinate. -/
theorem horner_sample_im_zero (index : Nat) :
    (hornerApproximation.sample index).im = 0 :=
  Horner.Sample.sample_im_zero 1 rfl index

/-- Every finite factorial sample at one has zero imaginary coordinate. -/
theorem factorial_sample_im_zero (index : Nat) : (factorialSample index).im = 0 := by
  rw [← horner_sample_eq_factorial index]
  exact horner_sample_im_zero index

/-- The factorial samples carry the Horner approximation's finite error and refinement data.

Only the samples are evaluated by the Taylor recurrence. The retained bounds
and request selector are transported pointwise through the exact sample law. -/
@[expose] def factorialApproximation : ApproximationData :=
  { hornerApproximation with
    sample := factorialSample
    later_close := by
      intro earlier later order
      rw [← horner_sample_eq_factorial later, ← horner_sample_eq_factorial earlier]
      exact hornerApproximation.later_close order
    sample_bounded := by
      intro index
      rw [← horner_sample_eq_factorial index]
      exact hornerApproximation.sample_bounded index }

/-- The original Horner approximation as a coherent name for e. -/
@[expose] def horner : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation hornerApproximation

/-- The independently evaluated factorial approximation as a coherent name for e. -/
@[expose] def factorial : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation factorialApproximation

/-- The two retained e names have a uniform operational comparison.

The comparison accepts independent starting indices and every positive squared
tolerance, and bounds every pair of later samples selected by the certificate. -/
@[expose] def factorial_equivalent_horner :
    Equivalence.NamedEquivalent factorial.name horner.name :=
  Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Sequence.Equivalence.approximationEquivalentOfSamplesEq
      factorialApproximation hornerApproximation
      (fun index => (horner_sample_eq_factorial index).symm))

/-- The public automatic exponential at exact one agrees with the stock Horner name.

The automatic range reduction may choose a positive exponent. The comparison
first transports its selected dyadic construction to exponent zero, then uses
the matching finite local and Horner samples. -/
@[expose] def automatic_equivalent_horner :
    Equivalence.NamedEquivalent
      (Progressive.Range.Name.named (Name.Basic.Named.exact 1)) horner.name := by
  let exponent := Name.DyadicReduction.rangeExponent (Name.Basic.Named.exact 1)
  have rangeToLocal : Equivalence.NamedEquivalent
      (Progressive.Range.Exact.exactDyadicExpCoherent exponent 1
        (Progressive.Range.Exact.automaticExactDyadicScale_unit 1)).name
      (Progressive.Local.Exact.exactLocalExpNamed 1 one_unit) := by
    simpa only [Progressive.Range.Exact.exactDyadicExpCoherent,
      Purelib.Data.Gaussian.Dyadic.dyadicScale,
      Name.Arithmetic.Power.squareIterate] using
      (Progressive.Range.Exact.exactDyadicExp_raise_to
        (lower := 0) (upper := exponent) 1 (Nat.zero_le exponent) one_unit)
  have localToHorner : Equivalence.NamedEquivalent
      (Progressive.Local.Exact.exactLocalExpNamed 1 one_unit) horner.name :=
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Sequence.Equivalence.approximationEquivalentOfSamplesEq
        (Progressive.Local.Exact.exactLocalExpApproximation 1 one_unit)
        hornerApproximation (fun _ => rfl))
  exact Equivalence.NamedEquivalent.trans
    (Progressive.Range.Exact.automaticExactExp_toDyadic 1)
    (Equivalence.NamedEquivalent.trans rangeToLocal localToHorner)

end
end Purelib.Approximation.Gaussian.Exponential.E
