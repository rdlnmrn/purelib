module
public import Purelib.Approximation.Gaussian.Arithmetic.Sampling
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
public import Purelib.Polynomial.Approximation.Evaluation
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Field

open Purelib.Approximation.Gaussian.Geometric.Coherent
open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# Finite polynomial evaluation at one retained sample index

Horner arithmetic supplies geometric bounds and an operational certificate.
The executable sample reads its input once and evaluates the cached dense
polynomial directly, with a proof tying it to those same Horner bounds.
-/

namespace Purelib.Polynomial.Approximation.CoherentEvaluation

open _root_.Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open _root_.Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)

open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Sequence.Name.Equivalence (named_toSamplingNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

section
@[expose] public section

/-- The geometric approximation obtained from a coherent name retains an equivalent named process. -/
def named_agrees (input : CoherentNamed)
    (cached : {source : GeometricApproximation // source = GeometricApproximation.ofNamed input.name} :=
      ⟨GeometricApproximation.ofNamed input.name, rfl⟩) : NamedEquivalent
    input.name cached.val.toApproximation.toNamed :=
  (named_toSamplingNamed input.name).trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Name.Sampling.approximation input.name) cached.val.toApproximation (fun index => by
        rewrite [cached.property]
        rfl)).toNamed)

/-- The exact coherent name agrees with the constant geometric approximation. -/
def exact_agrees (value : Gaussian.Basic.Canonical) :
  NamedEquivalent (CoherentNamed.Coherence.exact value).name
    (Geometric.GeometricApproximation.exact value).toApproximation.toNamed :=
  Comparison.exact_agreesWith value (Geometric.GeometricApproximation.exact value) (fun _ => rfl)

/-- Multiplication preserves the supplied equivalences between coherent names and geometric approximations. -/
def mul_agrees (left right : CoherentNamed) (first second :
  Geometric.GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed) :
    NamedEquivalent (CoherentNamed.mul left right).name (first.mul second).toApproximation.toNamed :=
  Comparison.mul_agreesWith left right first second (first.mul second) leftEq rightEq
    (fun _ => rfl)

/-- Original finite named powers realize the equal-index geometric power of the same retained input.

The comparison follows the original previous-power-times-input recurrence.
Every node uses the supplied input realization and the existing exact-unit or
multiplication bridge, without computing an algebraic elimination or changing
the original named power channel.
-/
def pow_agrees (input : CoherentNamed) (source : Geometric.GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    (exponent : Nat) → NamedEquivalent (Name.Coherent.Power.namedPower input exponent).name
      (source.pow exponent).toApproximation.toNamed
  := fun exponent => by
    let cache := Comparison.PowerRealization.build input source sourceEq exponent
    have equivalent := cache.original_agrees
    rewrite [cache.source_eq] at equivalent
    exact equivalent

/-- Addition preserves the supplied equivalences between coherent names and geometric approximations. -/
public def add_agrees (left right : CoherentNamed) (first
  second : Geometric.GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed) :
    NamedEquivalent (CoherentNamed.add left right).name (first.add second).toApproximation.toNamed :=
  Comparison.add_agreesWith left right first second (first.add second) leftEq rightEq
    (fun _ => rfl)

/-- The coherent and geometric Horner loops retain equivalent names for equivalent inputs and initial accumulators. -/
public def loop_agrees (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (initial : CoherentNamed) (start : GeometricApproximation)
    (initialEq : NamedEquivalent initial.name start.toApproximation.toNamed)
    (coefficients : List Canonical)
    (cached : Option (Horner.Accumulations input initial coefficients) := none) :
    NamedEquivalent (Horner.horner input initial coefficients).name
      (Evaluation.loop source start coefficients).toApproximation.toNamed := by
  cases coefficients with
  | nil => exact initialEq
  | cons coefficient remaining =>
      cases cached with
      | none =>
          exact loop_agrees input source sourceEq
            (CoherentNamed.add (CoherentNamed.mul initial input) (Coherence.exact coefficient))
            ((start.mul source).add (.exact coefficient))
            (add_agrees (CoherentNamed.mul initial input) (Coherence.exact coefficient)
              (start.mul source) (.exact coefficient)
              (mul_agrees initial input start source initialEq sourceEq) (exact_agrees coefficient)) remaining
      | some retained =>
          let actual := retained.1
          have scalar := exact_agrees coefficient
          rewrite [← actual.scalar.property] at scalar
          have product := mul_agrees initial input start source initialEq sourceEq
          rewrite [← actual.product.property] at product
          have step := add_agrees actual.product.val actual.scalar.val
            (start.mul source) (.exact coefficient) product scalar
          rewrite [← actual.2.2.property] at step
          have remainingEq := loop_agrees input source sourceEq actual.output
            ((start.mul source).add (.exact coefficient)) step remaining (some retained.2)
          have same := congrArg (fun accumulator => Horner.horner input accumulator remaining) actual.output_eq
          rewrite [same] at remainingEq
          exact remainingEq
termination_by structural coefficients

/-- Coherent Horner evaluation and sampled geometric evaluation give equivalent names on the same retained input.

The supplied source equivalence is transported through every coefficient operation and the final exact sample readback.
-/
def evaluate_agrees (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (input : CoherentNamed) (source :
  Geometric.GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (cached : Option (Horner.Accumulations input (Coherence.exact 0) polynomial.coeffs) := none) :
    NamedEquivalent (Gaussian.Evaluation.Horner.polynomialEval polynomial input).name
      (Evaluation.evaluate polynomial source).toApproximation.toNamed :=
  (loop_agrees input source sourceEq
    (CoherentNamed.Coherence.exact 0) (.exact 0) (exact_agrees 0)
    polynomial.coeffs cached).trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq (Evaluation.loop source (.exact 0)
      polynomial.coeffs).toApproximation
      (Evaluation.evaluate polynomial source).toApproximation (fun index =>
        Evaluation.loop_sample source index _ _)).toNamed)

end

end

/-- Supplying actual original Horner accumulators preserves the complete original comparison procedure.

The two procedures retain identical endpoints, observations, requested starts,
tolerance and paid indices. Structural cache identities transport the same
primitive multiplication/addition comparisons without function extensionality.
-/
theorem loop_agrees_cached_eq_default (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (initial : CoherentNamed) (start : GeometricApproximation)
    (initialEq : NamedEquivalent initial.name start.toApproximation.toNamed)
    (coefficients : List Canonical) (cached : Horner.Accumulations input initial coefficients) :
    loop_agrees input source sourceEq initial start initialEq coefficients (some cached) =
      loop_agrees input source sourceEq initial start initialEq coefficients := by
  cases cached.eq_retain input initial coefficients
  induction coefficients generalizing initial start with
  | nil => rfl
  | cons coefficient remaining ih =>
      let product := CoherentNamed.mul initial input
      let scalar := Coherence.exact coefficient
      let current := CoherentNamed.add product scalar
      let next := (start.mul source).add (.exact coefficient)
      let nextEq := add_agrees product scalar (start.mul source) (.exact coefficient)
        (mul_agrees initial input start source initialEq sourceEq) (exact_agrees coefficient)
      change loop_agrees input source sourceEq current next nextEq remaining
          (some (Horner.retain input current remaining)) =
        loop_agrees input source sourceEq current next nextEq remaining
      exact ih current next nextEq

/-- Cached polynomial evaluation retains the complete original operational comparison and payment. -/
theorem evaluate_agrees_cached_eq_default (polynomial : CoefficientPolynomial) (input : CoherentNamed)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (cached : Horner.Accumulations input (Coherence.exact 0) polynomial.coeffs) :
    evaluate_agrees polynomial input source sourceEq (some cached) =
      evaluate_agrees polynomial input source sourceEq := by
  have same := loop_agrees_cached_eq_default input source sourceEq (Coherence.exact 0)
    (.exact 0) (exact_agrees 0) polynomial.coeffs cached
  exact congrArg (fun relation => relation.trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq (Evaluation.loop source (.exact 0)
      polynomial.coeffs).toApproximation (Evaluation.evaluate polynomial source).toApproximation
      (fun index => Evaluation.loop_sample source index _ _)).toNamed)) same

/-- Actual retained Horner accumulators compare to the same finite polynomial source.

The bridge consumes every cached coefficient/product/updated accumulator and
keeps the actual final cached channel as its endpoint. Its construction equation
transports only the endpoint type, not another Horner execution.
-/
def evaluate_cached_agrees (polynomial : CoefficientPolynomial) (input : CoherentNamed)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (cached : Horner.Accumulations input (Coherence.exact 0) polynomial.coeffs) :
    NamedEquivalent (cached.output input (Coherence.exact 0) polynomial.coeffs).name
      (Evaluation.evaluate polynomial source).toApproximation.toNamed := by
  have agreement := evaluate_agrees polynomial input source sourceEq (some cached)
  change NamedEquivalent (Horner.horner input (Coherence.exact 0) polynomial.coeffs).name
    (Evaluation.evaluate polynomial source).toApproximation.toNamed at agreement
  rewrite [← cached.output_eq input (Coherence.exact 0) polynomial.coeffs] at agreement
  exact agreement

/-- The complete default named-source relation is the original canonical-sampling construction. -/
theorem named_agrees_default (input : CoherentNamed) : named_agrees input =
    (named_toSamplingNamed input.name).trans
      ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
        (Name.Sampling.approximation input.name)
        (GeometricApproximation.ofNamed input.name).toApproximation (fun _ => rfl)).toNamed) := rfl

/-- Negation compares to the actual supplied geometric negative through finite cancellation.

The retained source relation pays the original addition comparison. The
pointwise zero sample certificate keeps the original source and its actual
negative channel, without selecting a second named-source sampler.
-/
def neg_agrees (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (CoherentNamed.neg input).name source.neg.toApproximation.toNamed := by
  let negative := CoherentNamed.ofApproximation source.neg.toApproximation
  let compared := add_agrees input negative source source.neg sourceEq (NamedEquivalent.refl _)
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (source.add source.neg).toApproximation (GeometricApproximation.exact 0).toApproximation
    (fun index => by
      change (source.add source.neg).sample index = (GeometricApproximation.exact 0).sample index
      rewrite [GeometricApproximation.add_sample, GeometricApproximation.neg_sample,
        GeometricApproximation.exact_sample]
      exact add_neg_cancel (source.sample index))
  let cancelled := compared.trans (samples.toNamed.trans (exact_agrees (0 : Canonical)).symm)
  exact (Coherent.Additive.equivalent_neg_of_add_zero input negative cancelled).symm

/-- Pointwise scalar polynomial equality compares their original coherent Horner evaluations.

Both polynomial sample programs use the same retained input sampler and its
original source equivalence. No coefficient extensionality or new input
sampler is needed.
-/
def evaluate_of_eval_eq (first second : CoefficientPolynomial)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (identity : ∀ point : Canonical, first.eval point = second.eval point) :
    NamedEquivalent (Horner.polynomialEval first input).name
      (Horner.polynomialEval second input).name :=
  (evaluate_agrees first input source sourceEq).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate first source).toApproximation
      (Evaluation.evaluate second source).toApproximation
      (fun index => by
        rewrite [GeometricApproximation.toApproximation_sample, GeometricApproximation.toApproximation_sample,
          Evaluation.evaluate_sample, Evaluation.evaluate_sample]
        exact identity (source.sample index))).toNamed).trans
        (evaluate_agrees second input source sourceEq).symm)

/-- A constant dense polynomial evaluates operationally to its exact retained scalar.

The original coherent Horner program is compared to constant samples of the
same retained source, then to the exact terminating scalar channel.
-/
def evaluate_constant_agrees (value : Canonical)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval (DensePolynomial.constant value) input).name
      (Coherence.exact value).name :=
  (evaluate_agrees (DensePolynomial.constant value) input source sourceEq).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate (DensePolynomial.constant value) source).toApproximation
      (GeometricApproximation.exact value).toApproximation
      (fun index => by
        rewrite [GeometricApproximation.toApproximation_sample, GeometricApproximation.toApproximation_sample,
          Evaluation.evaluate_sample, GeometricApproximation.exact_sample]
        exact DensePolynomial.eval_constant value (source.sample index))).toNamed).trans
        (exact_agrees value).symm)

/-- Dense polynomial addition compares operationally with the original ordered coherent sum.

The same original source and both actual coefficient polynomials supply the
pointwise scalar identity. No input or coefficient cache is selected anew.
-/
def evaluate_add_agrees (first second : CoefficientPolynomial)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval (first.add second) input).name
      (CoherentNamed.add (Horner.polynomialEval first input) (Horner.polynomialEval second input)).name := by
  let firstSource := Evaluation.evaluate first source
  let secondSource := Evaluation.evaluate second source
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Evaluation.evaluate (first.add second) source).toApproximation
    (firstSource.add secondSource).toApproximation (fun index => by
      change (Evaluation.evaluate (first.add second) source).sample index =
        (firstSource.add secondSource).sample index
      dsimp only [firstSource, secondSource]
      rewrite [GeometricApproximation.add_sample, Evaluation.evaluate_sample,
        Evaluation.evaluate_sample, Evaluation.evaluate_sample]
      exact DensePolynomial.eval_add first second (source.sample index))
  exact (evaluate_agrees _ input source sourceEq).trans
    (samples.toNamed.trans
      (add_agrees _ _ firstSource secondSource (evaluate_agrees first input source sourceEq)
        (evaluate_agrees second input source sourceEq)).symm)

/-- Dense scalar multiplication compares operationally with its exact coefficient times the same original evaluation. -/
def evaluate_scale_agrees (coefficient : Canonical) (polynomial : CoefficientPolynomial)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval (DensePolynomial.scale coefficient polynomial) input).name
      (CoherentNamed.mul (Coherence.exact coefficient) (Horner.polynomialEval polynomial input)).name := by
  let polynomialSource := Evaluation.evaluate polynomial source
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Evaluation.evaluate (DensePolynomial.scale coefficient polynomial) source).toApproximation
    ((GeometricApproximation.exact coefficient).mul polynomialSource).toApproximation (fun index => by
      change (Evaluation.evaluate (DensePolynomial.scale coefficient polynomial) source).sample index =
        ((GeometricApproximation.exact coefficient).mul polynomialSource).sample index
      dsimp only [polynomialSource]
      rewrite [GeometricApproximation.mul_sample, GeometricApproximation.exact_sample,
        Evaluation.evaluate_sample, Evaluation.evaluate_sample, DensePolynomial.eval_scale]
      rfl)
  exact (evaluate_agrees _ input source sourceEq).trans
    (samples.toNamed.trans
      (mul_agrees _ _ (GeometricApproximation.exact coefficient) polynomialSource
        (exact_agrees coefficient) (evaluate_agrees polynomial input source sourceEq)).symm)

/-- Retain the same finite source multiplication program for one natural power. -/
@[expose] def powerSource (source : GeometricApproximation) : Nat → GeometricApproximation
  | 0 => GeometricApproximation.exact 1
  | exponent + 1 => (powerSource source exponent).mul source

/-- This finite power program reads the original source at the same sample index. -/
theorem powerSource_sample (source : GeometricApproximation) (index : Nat) :
    (exponent : Nat) → (powerSource source exponent).sample index = (source.sample index) ^ exponent
  | 0 => rfl
  | exponent + 1 => by
      change ((powerSource source exponent).mul source).sample index = _
      rewrite [GeometricApproximation.mul_sample, powerSource_sample source index exponent, pow_succ]
      rfl

/-- The coherent finite power consumes the same original input equivalence at every multiplication. -/
private def power_agrees (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    (exponent : Nat) → NamedEquivalent (Name.Coherent.Power.namedPower input exponent).name
      (powerSource source exponent).toApproximation.toNamed
  | 0 => exact_agrees 1
  | exponent + 1 => mul_agrees (Name.Coherent.Power.namedPower input exponent) input
      (powerSource source exponent) source (power_agrees input source sourceEq exponent) sourceEq

/-- The original dense basis power evaluates operationally to the same coherent natural power. -/
def basisPower_agrees (exponent : Nat) (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval
      (DensePolynomial.shift exponent (DensePolynomial.constant 1)) input).name
      (Name.Coherent.Power.namedPower input exponent).name :=
  (evaluate_agrees _ input source sourceEq).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate (DensePolynomial.shift exponent (DensePolynomial.constant 1)) source).toApproximation
      (powerSource source exponent).toApproximation (fun index => by
        rewrite [GeometricApproximation.toApproximation_sample, GeometricApproximation.toApproximation_sample,
          Evaluation.evaluate_sample, DensePolynomial.eval_shift, DensePolynomial.eval_constant,
          one_mul, powerSource_sample]
        rfl)).toNamed).trans
        (power_agrees input source sourceEq exponent).symm)

end Purelib.Polynomial.Approximation.CoherentEvaluation
