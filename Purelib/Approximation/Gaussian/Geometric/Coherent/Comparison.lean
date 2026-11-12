module
import Purelib.Approximation.Gaussian.Arithmetic.Sampling
public import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Basic
import Mathlib.Algebra.Group.Defs
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Sequence.Name

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

/-- The original exact channel agrees with an actual retained program having that same constant reading. -/
def exact_agreesWith (value : Data.Gaussian.Basic.Canonical) (target : GeometricApproximation)
    (sample_eq : ∀ index, target.sample index = value) :
    NamedEquivalent (CoherentNamed.Coherence.exact value).name target.toApproximation.toNamed :=
  (Sequence.Name.Exact.exact_toConstantNamed value).trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Sequence.Constant.constantApproximation value) target.toApproximation
      (fun index => (sample_eq index).symm)).toNamed)

/-- Original product channels realize an actual retained target with same-index product observations.

The comparison consumes the supplied target program directly. Its bridge
retains both original operand realizations without rebuilding their product.
-/
def mul_agreesWith (left right : CoherentNamed) (first second target : GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed)
    (sample_eq : ∀ index, target.sample index = first.sample index * second.sample index) :
    NamedEquivalent (CoherentNamed.mul left right).name target.toApproximation.toNamed :=
  (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects left (CoherentNamed.ofApproximation
    first.toApproximation) right (CoherentNamed.ofApproximation second.toApproximation) leftEq rightEq).trans
    (Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise first.toApproximation
      second.toApproximation target.toApproximation sample_eq)

set_option genInjectivity false in
/-- One ordered finite power fold retaining each actual named channel, sample program and comparison.

Every positive node retains its previous prefix. Its complete channel and
program equalities authenticate the original named and geometric recurrences
without evaluating those recurrences again at a consuming node.
-/
inductive PowerRealization (input : CoherentNamed) (source : GeometricApproximation) : Nat → Type 1 where
  /-- Retain the actual exact-unit channels, program and comparison at the zero prefix. -/
  | zero (channel : CoherentNamed) (channel_eq : channel = Power.namedPower input 0)
      (result : GeometricApproximation) (result_eq : result = source.pow 0)
      (equivalent : NamedEquivalent channel.name result.toApproximation.toNamed) : PowerRealization input source 0
  /-- Retain the actual previous prefix and its once computed successor channel, program and comparison. -/
  | succ {exponent : Nat} (previous : PowerRealization input source exponent)
      (channel : CoherentNamed) (channel_eq : channel = Power.namedPower input (exponent + 1))
      (result : GeometricApproximation) (result_eq : result = source.pow (exponent + 1))
      (equivalent : NamedEquivalent channel.name result.toApproximation.toNamed) :
      PowerRealization input source (exponent + 1)

constructive_injectivity PowerRealization

namespace PowerRealization

/-- Read the actual original named channel stored at this power prefix. -/
def channel {input source exponent} : PowerRealization input source exponent → CoherentNamed
  | .zero channel _ _ _ _ => channel
  | .succ _ channel _ _ _ _ => channel

/-- Read the same actual geometric program stored at this power prefix. -/
def source {input original exponent} : PowerRealization input original exponent → GeometricApproximation
  | .zero _ _ source _ _ => source
  | .succ _ _ _ source _ _ => source

/-- The cached named channel is the complete original ordered named power. -/
theorem channel_eq {input source exponent} (cache : PowerRealization input source exponent) :
    cache.channel = Power.namedPower input exponent := by
  cases cache with
  | zero _ same _ _ _ => exact same
  | succ _ _ same _ _ _ => exact same

/-- The cached geometric program is the complete original ordered equal-index power. -/
theorem source_eq {input original exponent} (cache : PowerRealization input original exponent) :
    cache.source = original.pow exponent := by
  cases cache with
  | zero _ _ _ same _ => exact same
  | succ _ _ _ _ same _ => exact same

/-- Read the comparison that was computed with this same cached named channel and geometric program. -/
def equivalent {input original exponent} (cache : PowerRealization input original exponent) :
    NamedEquivalent cache.channel.name cache.source.toApproximation.toNamed :=
  match cache with
  | .zero _ _ _ _ equivalent => equivalent
  | .succ _ _ _ _ _ equivalent => equivalent

/-- Compute each power prefix once and compare its actual retained output to the original channel.

Each successor consumes the previous stored channel, program and comparison,
and calls the pointwise product bridge with its same computed output.
-/
def build (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    (exponent : Nat) → PowerRealization input source exponent
  | 0 =>
      let channel := CoherentNamed.Coherence.exact 1
      let result := GeometricApproximation.exact 1
      .zero channel rfl result rfl (exact_agreesWith 1 result (fun _ => rfl))
  | exponent + 1 =>
      let previous := build input source sourceEq exponent
      let channel := CoherentNamed.mul previous.channel input
      let result := previous.source.mul source
      have channelEq : channel = Power.namedPower input (exponent + 1) :=
        congrArg (fun previousChannel => CoherentNamed.mul previousChannel input) previous.channel_eq
      have resultEq : result = source.pow (exponent + 1) :=
        congrArg (fun previousChannel => previousChannel.mul source) previous.source_eq
      let equivalent := mul_agreesWith previous.channel input previous.source source result
        previous.equivalent sourceEq (fun _ => rfl)
      .succ previous channel channelEq result resultEq equivalent

/-- Transport the cached comparison to its authenticated original named power without changing its target program. -/
def original_agrees {input original exponent} (cache : PowerRealization input original exponent) :
    NamedEquivalent (Power.namedPower input exponent).name cache.source.toApproximation.toNamed := by
  rewrite [← cache.channel_eq]
  exact cache.equivalent

end PowerRealization

/-- Original sum channels realize an actual retained target with same-index sum observations. -/
def add_agreesWith (left right : CoherentNamed) (first second target : GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed)
    (sample_eq : ∀ index, target.sample index = first.sample index + second.sample index) :
    NamedEquivalent (CoherentNamed.add left right).name target.toApproximation.toNamed :=
  (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects left (CoherentNamed.ofApproximation
    first.toApproximation) right (CoherentNamed.ofApproximation second.toApproximation) leftEq rightEq).trans
    (Arithmetic.Sampling.addToNamed_equivalent_pointwise first.toApproximation second.toApproximation
      target.toApproximation sample_eq)

/-- A retained constant-reading geometric target realizes the original exact channel in the original direction. -/
def geometricTarget_equivalent_exact (value : Data.Gaussian.Basic.Canonical) (target : GeometricApproximation)
    (sample_eq : ∀ index, target.sample index = value) :
    NamedEquivalent (PeriodMatrix.geometricNamed target).name (Coherence.exact value).name := by
  let constant := Constant.constantApproximation value
  have toConstant : NamedEquivalent (PeriodMatrix.geometricNamed target).name constant.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq target.toApproximation constant sample_eq)
  exact toConstant.trans (Exact.exact_toConstantNamed value).symm

/-- A synchronized constant geometric stream is operationally the ordinary terminating coherent constant. -/
def geometricExact_equivalent_exact (value : Data.Gaussian.Basic.Canonical) :
    NamedEquivalent (PeriodMatrix.geometricNamed (GeometricApproximation.exact value)).name
      (Coherence.exact value).name :=
  geometricTarget_equivalent_exact value (GeometricApproximation.exact value) (fun _ => rfl)

/-- The synchronized geometric zero used by `sumNamed` is operationally the ordinary terminating coherent zero. -/
def geometricZero_equivalent_exact :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.exact
          0)).name
      (Coherence.exact 0).name :=
  geometricExact_equivalent_exact 0

/-- A retained negative-reading target is the operational additive inverse of its original geometric source.

The cancellation bridge consumes the actual supplied target and its scalar
sample law. It never constructs another negative program.
-/
def geometricTarget_equivalent_statefulNeg (source target : GeometricApproximation)
    (sample_eq : ∀ index, target.sample index = -source.sample index) :
    NamedEquivalent (PeriodMatrix.geometricNamed target).name
      (CoherentNamed.neg (PeriodMatrix.geometricNamed source)).name := by
  let value := PeriodMatrix.geometricNamed source
  let candidate := PeriodMatrix.geometricNamed target
  let zero := GeometricApproximation.exact 0
  have cancelToZero : NamedEquivalent (CoherentNamed.add value candidate).name
      zero.toApproximation.toNamed :=
    Sampling.addToNamed_equivalent_pointwise source.toApproximation target.toApproximation zero.toApproximation
      (fun index => by
        change 0 = source.sample index + target.sample index
        rewrite [sample_eq index]
        exact (add_neg_cancel (source.sample index)).symm)
  have cancel : NamedEquivalent (CoherentNamed.add value candidate).name (Coherence.exact 0).name :=
    cancelToZero.trans (geometricTarget_equivalent_exact 0 zero (fun _ => rfl))
  exact Additive.equivalent_neg_of_add_zero value candidate cancel

/-- Equal-index geometric negation agrees with the actual stateful negation of its original source. -/
def geometricNeg_equivalent_statefulNeg (source : GeometricApproximation) :
    NamedEquivalent (PeriodMatrix.geometricNamed source.neg).name
      (CoherentNamed.neg (PeriodMatrix.geometricNamed source)).name :=
  geometricTarget_equivalent_statefulNeg source source.neg (fun _ => rfl)

/-- Original negation realizes an actual retained target with negative same-index readings. -/
def neg_agreesWith (value : CoherentNamed) (source target : GeometricApproximation)
    (equivalent : NamedEquivalent value.name source.toApproximation.toNamed)
    (sample_eq : ∀ index, target.sample index = -source.sample index) :
    NamedEquivalent (CoherentNamed.neg value).name target.toApproximation.toNamed :=
  (Additive.coherentNeg_respects value (PeriodMatrix.geometricNamed source) equivalent).trans
    (geometricTarget_equivalent_statefulNeg source target sample_eq).symm

/-- Stateful negation of any realization of a synchronized geometric source realizes the equal-index geometric negation.
-/
def coherentNeg_equivalent_geometricNeg
    (value : Coherent.CoherentNamed)
    (source : Gaussian.Geometric.GeometricApproximation)
    (equivalent : Gaussian.Equivalence.NamedEquivalent value.name
      (PeriodMatrix.geometricNamed source).name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.neg value).name
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.neg
          source)).name :=
  neg_agreesWith value source source.neg equivalent (fun _ => rfl)

/-- Actual addition realizes equal-index geometric addition whenever both operands realize their synchronized sources.
-/
def coherentAdd_equivalent_geometricAdd
    (left right : Coherent.CoherentNamed)
    (leftSource rightSource :
      Gaussian.Geometric.GeometricApproximation)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent left.name
      (PeriodMatrix.geometricNamed leftSource).name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent right.name
      (PeriodMatrix.geometricNamed rightSource).name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left right).name
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.add
          leftSource rightSource)).name :=
  add_agreesWith left right leftSource rightSource (leftSource.add rightSource)
    leftEquivalent rightEquivalent (fun _ => rfl)

/-- Original subtraction realizes retained negative and sum programs with their actual scalar readbacks.

The original right operand's negative program is supplied separately, so both
that prefix and the final target are consumed without arithmetic rebuilding.
-/
def sub_agreesWith (left right : CoherentNamed) (leftSource rightSource negative target : GeometricApproximation)
    (leftEquivalent : NamedEquivalent left.name leftSource.toApproximation.toNamed)
    (rightEquivalent : NamedEquivalent right.name rightSource.toApproximation.toNamed)
    (negative_eq : ∀ index, negative.sample index = -rightSource.sample index)
    (sample_eq : ∀ index, target.sample index = leftSource.sample index + negative.sample index) :
    NamedEquivalent (CoherentNamed.add left (CoherentNamed.neg right)).name target.toApproximation.toNamed :=
  add_agreesWith left (CoherentNamed.neg right) leftSource negative target leftEquivalent
    (neg_agreesWith right rightSource negative rightEquivalent negative_eq) sample_eq

/-- Actual subtraction realizes equal-index geometric subtraction of its two original sources. -/
def coherentSub_equivalent_geometricSub (left right : CoherentNamed)
    (leftSource rightSource : GeometricApproximation)
    (leftEquivalent : NamedEquivalent left.name (PeriodMatrix.geometricNamed leftSource).name)
    (rightEquivalent : NamedEquivalent right.name (PeriodMatrix.geometricNamed rightSource).name) :
    NamedEquivalent (Additive.subtractName left right).name
      (PeriodMatrix.geometricNamed (GeometricApproximation.sub leftSource rightSource)).name :=
  let negative := rightSource.neg
  let target := leftSource.add negative
  sub_agreesWith left right leftSource rightSource negative target leftEquivalent rightEquivalent
    (fun _ => rfl) (fun _ => rfl)

end Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

end
