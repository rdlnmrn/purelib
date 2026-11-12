module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
open Purelib.Approximation.Gaussian.Sequence.Name

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Stateful multiplication respects operational equality independently in both coherent operands. -/
@[expose] def coherentMul_respects
    (leftOne leftTwo rightOne rightTwo : Coherent.CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        leftOne.name rightOne.name)
      (Named.mul
        leftTwo.name rightTwo.name) :=
  Equivalent.trans
    (Bridge.coherentMul_toSampled leftOne rightOne)
    (Equivalent.trans
      (Congruence.sampledProductApproximation_respects leftEquivalent rightEquivalent)
      (Equivalent.symm (Bridge.coherentMul_toSampled leftTwo rightTwo)))

/-- Multiply a retained comparison against zero by an exact Gaussian coefficient.

The actual stateful multiplication is compared through its original sampled
product bridge. The scalar's exact squared norm, rather than its sampler's
larger default bound, scales the retained input tolerance. Independent output
starts and a separately paid positive accuracy remain in the comparison.
-/
def compare_exact_mul_zero (coefficient : Basic.Canonical) (value : Coherent.CoherentNamed)
    {rightStart : Nat} {target : Fraction.Rational}
    (comparison : Comparison (Sampling.approximation value.name)
      (Sampling.approximation (Named.exact 0)) 0 rightStart target)
    (leftStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Comparison (Sampling.approximation (Named.mul (Named.exact coefficient) value.name))
      (Sampling.approximation (Named.exact 0)) leftStart rightStart
      (4 * (Norm.Basic.normSq coefficient * target) + accuracy) := by
  let scalar := Coherent.CoherentNamed.Coherence.exact coefficient
  let source := Sampling.approximation value.name
  let constant := Sampling.approximation scalar.name
  let zero := Sampling.approximation (Named.exact 0)
  let magnitude := source.centerBound
  let small := accuracy / (8 * (1 + magnitude))
  have magnitudeNonnegative : 0 ≤ magnitude := source.centerBound_nonneg
  have denominatorPositive : 0 < 8 * (1 + magnitude) :=
    Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) magnitudeNonnegative)
  have smallPositive : 0 < small := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have scalarSample (index : Nat) : constant.sample index = coefficient := rfl
  have zeroSample (index : Nat) : zero.sample index = (0 : Basic.Canonical) := rfl
  let scalarEquivalent := Equivalent.of_constant_samples constant constant coefficient scalarSample scalarSample
  let scalarComparison := scalarEquivalent.compare 0 rightStart small smallPositive
  let sampled := sampledProductApproximation scalar.name value.name
  have sampledReading (index : Nat) : sampled.sample index = constant.sample index * source.sample index := rfl
  have zeroReading (index : Nat) : zero.sample index = constant.sample index * zero.sample index := by
    rewrite [zeroSample index, Basic.mul_zero]
    rfl
  let productComparison := Congruence.pointwiseComparison scalarComparison comparison sampledReading zeroReading
    (secondLeftCeiling := ⟨Norm.Basic.normSq coefficient, fun index => by
      rewrite [scalarSample index]
      exact Fraction.Order.Basic.le_refl _⟩)
    (margins := ⟨(small, small), Arithmetic.add_pos_of_pos_of_nonneg_direct smallPositive smallPositive.le⟩)
  let bridge := (Bridge.coherentMul_toSampled scalar value).compare leftStart 0 small smallPositive
  let paid := bridge.trans productComparison
  apply paid.weaken
  have coefficientBound : 4 * magnitude + 6 ≤ 8 * (1 + magnitude) := by
    apply Arithmetic.le_of_sub_nonneg_direct
    have same : 8 * (1 + magnitude) - (4 * magnitude + 6) = 2 + 4 * magnitude := by ring1
    rewrite [same]
    exact add_nonneg (by decide) (Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound smallPositive.le
  have budget : small * (8 * (1 + magnitude)) = accuracy :=
    Fraction.Field.div_mul_cancel_of_ne accuracy _ (by
      intro equal
      rewrite [equal] at denominatorPositive
      exact denominatorPositive.2 (Fraction.Order.Basic.le_refl _))
  have same : 2 * (small +
      (2 * (small * magnitude + Norm.Basic.normSq coefficient * target) + small + small)) =
      4 * (Norm.Basic.normSq coefficient * target) + small * (4 * magnitude + 6) := by ring1
  change 2 * (small +
    (2 * (small * magnitude + Norm.Basic.normSq coefficient * target) + small + small)) ≤ _
  rewrite [same]
  exact (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) scaled).trans_eq (congrArg (fun amount =>
    4 * (Norm.Basic.normSq coefficient * target) + amount) budget)

/-- Compare multiplication by an exact factor with a pointwise scaled approximation.

The coherent name is operationally equivalent to the chart, and the supplied
sample law identifies the scaled chart at every finite index. Compose the
stateful multiplication and pointwise comparisons with that same exact factor.
-/
@[expose] def mulExact_toPointwise (left : Named)
    (coherent : Gaussian.Process.Coherence.Basic.Coherent left.process)
    (chart scaled : ApproximationData) (factor : Data.Gaussian.Basic.Canonical)
    (leftEquivalent : NamedEquivalent left chart.toNamed)
    (samples : ∀ depth, scaled.sample depth =
      chart.sample depth * (Constant.constantApproximation factor).sample depth) :
    NamedEquivalent (Named.mul left (Named.exact factor)) scaled.toNamed :=
  NamedEquivalent.trans
    (coherentMul_respects
      { name := left, coherent := coherent }
      (CoherentNamed.ofApproximation chart)
      (Coherence.exact factor)
      (CoherentNamed.ofApproximation (Constant.constantApproximation factor))
      leftEquivalent (Exact.exact_toConstantNamed factor))
    (Multiplication.Bridge.mulToNamed_equivalent_pointwise chart
      (Constant.constantApproximation factor) scaled samples)

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
