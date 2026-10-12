module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.RootContinuation.SquareRootNegation
import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.Value

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.RootContinuation.RootOwnerNegation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cancellation of differential coefficients on the two actual roots

Both denominators are retained operational roots with their own apartness
certificates. The common numerator may be any coherent channel. Exact finite
quotient cancellation is transported through the ordinary division and
addition comparisons, then specialized to the standard differential values.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation.CertifiedSquareRoot

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample (sampledQuotientApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence (coherentDiv_toSampled coherentDiv_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence (coherentAdd_respects)
open Purelib.Approximation.Gaussian.Sequence.Name.Equivalence (named_toSamplingNamed)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate Gaussian)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Algebra in
open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Dividing the same original numerator by a certified root and its negation gives a sum equivalent to zero.

The sampled quotients retain the exact original numerator and opposite denominator samples; their pointwise cancellation
is transported back to coherent names. -/
public def quotient_neg_sum_zero {parameter : Gaussian}
    (source : Certificate parameter) (numerator : Name.Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent
      ((numerator.div source.value source.apart).add
        (numerator.div (SquareRootNegation.Certificate.neg source).value (SquareRootNegation.Certificate.neg
          source).apart)).name
      (Name.Basic.Named.exact 0) := by
  let first := Name.Coherent.Division.Sample.sampledQuotientApproximation numerator source.value source.apart
  let second := Name.Coherent.Division.Sample.sampledQuotientApproximation numerator (SquareRootNegation.Certificate.neg
    source).value (SquareRootNegation.Certificate.neg source).apart
  let zero := Name.Sampling.approximation (Name.Basic.Named.exact 0)
  let firstNamed := Name.Coherent.CoherentNamed.ofApproximation first
  let secondNamed := Name.Coherent.CoherentNamed.ofApproximation second
  let converted := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (numerator.div source.value source.apart) firstNamed
    (numerator.div (SquareRootNegation.Certificate.neg source).value (SquareRootNegation.Certificate.neg source).apart)
      secondNamed
    (Name.Coherent.Division.Equivalence.coherentDiv_toSampled numerator source.value source.apart)
    (Name.Coherent.Division.Equivalence.coherentDiv_toSampled numerator (SquareRootNegation.Certificate.neg
      source).value (SquareRootNegation.Certificate.neg source).apart)
  have pointwise : ∀ index, zero.sample index = first.sample index + second.sample index := by
    intro index
    change 0 = (Name.Sampling.approximation numerator.name).sample index /
        (Name.Sampling.approximation source.value.name).sample index +
      (Name.Sampling.approximation numerator.name).sample index /
        (Name.Sampling.approximation source.value.neg.name).sample index
    rw [SquareRootNegation.neg_sample, Field.ExplicitField.div_neg]
    ring1
  exact converted.trans
    ((Arithmetic.Sampling.addToNamed_equivalent_pointwise first second zero pointwise).trans
      (Sequence.Name.Equivalence.named_toSamplingNamed (Name.Basic.Named.exact 0)).symm)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Quotients with original opposite-equivalent certified roots sum to the exact zero name. -/
def Certificate.quotient_sum_zero {firstParameter secondParameter : Gaussian}
    (first : Certificate firstParameter) (second : Certificate secondParameter) (numerator :
      Name.Coherent.CoherentNamed)
    (negative : Equivalence.NamedEquivalent first.value.neg.name second.value.name) :
    Equivalence.NamedEquivalent
      ((numerator.div first.value first.apart).add
        (numerator.div second.value second.apart)).name
      (Name.Basic.Named.exact 0) := by
  let changed := Name.Coherent.Division.Equivalence.coherentDiv_respects numerator numerator second.value
    (SquareRootNegation.Certificate.neg first).value
    second.apart (SquareRootNegation.Certificate.neg first).apart (Equivalence.NamedEquivalent.refl _) negative.symm
  exact (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (numerator.div first.value first.apart) (numerator.div first.value first.apart)
    (numerator.div second.value second.apart) (numerator.div (SquareRootNegation.Certificate.neg first).value
      (SquareRootNegation.Certificate.neg first).apart)
    (Equivalence.NamedEquivalent.refl _) changed).trans (quotient_neg_sum_zero first numerator)

end Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation.CertifiedSquareRoot

namespace Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation.OwnerFrame

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.Value (differentialValue)
open Purelib.Approximation.Gaussian.Name.Coherent.Power (namedPower)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootOwnerNegation (Negation)

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original differential values at retained opposite-sheet frame owners sum to zero up to named equivalence.

The numerator is the same exact coordinate power, while both denominator certificates and their retained negative-name
comparison remain unchanged. -/
def Negation.differential_sum_zero {genus : Nat} {parameter : Basic.Canonical}
    {frame : OwnerFrame parameter} {index : Fin 2} (data : Negation frame index)
    (differential : Differentials.Basic.Differential genus) (point : Basic.Canonical) :
    let first := (frame.owners index).certificate (frame.owners index).parameterNonzero
    let second := (frame.owners (BranchCutLifts.otherSheet index)).certificate
      (frame.owners (BranchCutLifts.otherSheet index)).parameterNonzero
    Equivalence.NamedEquivalent
      ((Differentials.Value.differentialValue differential point first.value first.apart).add
        (Differentials.Value.differentialValue differential point second.value second.apart)).name
      (Name.Basic.Named.exact 0) :=
  SquareRootDifferentialNegation.CertifiedSquareRoot.Certificate.quotient_sum_zero _ _
    (Name.Coherent.Power.namedPower (Name.Coherent.CoherentNamed.Coherence.exact point) differential.exponent)
      data.equivalent

end Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation.OwnerFrame
