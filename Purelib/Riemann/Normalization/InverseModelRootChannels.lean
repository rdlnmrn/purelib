module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Normalization.InverseModelRootSamples
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Certified operational roots of a retained polynomial model

The finite Newton samples themselves supply the square law and the selected
root channel. Attaching a winding owner preserves that channel. This makes
the root occurrence agree with the polynomial used by downstream primitives,
without identifying an independently prepared continuation by its residual.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelRootSamples (RootSamples)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (parameter_nonzero)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)

variable {polynomial : Polynomial} {box : Box} {model : Model polynomial box} {point : Gaussian}

namespace RootSamples

open Purelib.Approximation in
open Purelib.Data in
/-- A coherent finite approximation of the squared retained root samples.

The original residual scale supplies the shrinking comparison radius and finite refinement procedure, while the retained
root bound controls every squared reading. -/
def squareApproximation (data : RootSamples model point) (inside : box.Contains point) :
    Gaussian.Sequence.ApproximationData where
  sample := fun index => let root := data.sample index; root * root
  radiusSq := Rational.Geometric.Basic.quarterRadius (4 * data.residualScale)
  radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.residualScale_nonnegative)
  later_close := by
    intro earlier later order
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    have identity : data.sample later * data.sample later - data.sample earlier * data.sample earlier =
        (data.sample later * data.sample later - data.parameter) -
          (data.sample earlier * data.sample earlier - data.parameter) := by ring1
    rw [identity]
    calc
      _ ≤ 2 * (normSq (data.sample later * data.sample later - data.parameter) +
          normSq (data.sample earlier * data.sample earlier - data.parameter)) := (by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using (Gaussian.Norm.Bounds.normSq_sub_le_two _ _))
      _ ≤ 2 * (Rational.Geometric.Basic.quarterRadius data.residualScale earlier +
        Rational.Geometric.Basic.quarterRadius data.residualScale earlier) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Rat.Fraction.Order.Arithmetic.add_le_add_direct
            ((data.residual_bound inside later).trans
              (quarterRadius_antitone data.residualScale_nonnegative order))
            (data.residual_bound inside earlier)) (by decide)
      _ = _ := by rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow]; ring1
  refineIndex := fun current target _ => Rational.Geometric.Search.firstQuarterBelow (4 * data.residualScale) current
    target
  refineIndex_ge := fun current target _ => Rational.Geometric.Search.firstQuarterBelow_ge _ current target
  refineIndex_accurate := fun current target positive =>
    Rational.Geometric.Search.firstQuarterBelow_accurate _
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.residualScale_nonnegative) current target
        positive
  centerBound := data.bound ^ 2
  centerBound_nonneg := Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _
  sample_bounded := fun index => by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    rw [Gaussian.Basic.Canonical.normSq_mul, pow_two]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct (data.sample_bounded inside index)
      (data.sample_bounded inside index) (Gaussian.Basic.Canonical.normSq_nonneg _) data.bound_nonnegative

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Compare the squared sample approximation with the original polynomial value.

A finite geometric search gives one common tail beyond both requested stages for every positive error. -/
def squareEquivalent (data : RootSamples model point) (inside : box.Contains point) :
    Gaussian.Equivalence.Equivalent (Normalization.InverseModelRootChannels.RootSamples.squareApproximation data inside)
      (Gaussian.Sequence.Constant.constantApproximation data.parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let index := Rational.Geometric.Search.firstQuarterBelow data.residualScale start target
    have late := Rational.Geometric.Search.firstQuarterBelow_ge data.residualScale start target
    have leftBound : leftStart ≤ start := by
      change leftStart ≤ max leftStart rightStart
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_left _ _
    have rightBound : rightStart ≤ start := by
      change rightStart ≤ max leftStart rightStart
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_right _ _
    refine ⟨index, index, leftBound.trans late, rightBound.trans late, ?_⟩
    intro left right leftLater _rightLater
    simpa only [Normalization.InverseModelRootChannels.RootSamples.squareApproximation,
      Gaussian.Sequence.Constant.constantApproximation, Gaussian.Norm.Basic.normSq_eq_canonical] using
      (data.residual_bound inside left).trans_lt
      ((quarterRadius_antitone data.residualScale_nonnegative leftLater).trans_lt
        (Rational.Geometric.Search.firstQuarterBelow_accurate data.residualScale data.residualScale_nonnegative
          start target positive))

open Purelib.Riemann in
open Purelib.Approximation in
/-- Certify the retained raw root channel's square law from its actual polynomial samples.

The finite residual bound identifies the product channel with the exact polynomial value at the contained point. -/
def square (data : RootSamples model point) (small : model.bound ≤ 1 / 256) (inside : box.Contains point) :
    SquareIdentity (Gaussian.Name.Coherent.CoherentNamed.ofApproximation (data.approximation small inside))
      data.parameter := by
  let source := data.approximation small inside
  let product := Normalization.InverseModelRootChannels.RootSamples.squareApproximation data inside
  have actualToProduct : Gaussian.Equivalence.NamedEquivalent
      (Gaussian.Name.Basic.Named.mul source.toNamed source.toNamed) product.toNamed :=
    Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise source source product (by
      intro index; rfl)
  have productToConstant := Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Normalization.InverseModelRootChannels.RootSamples.squareEquivalent data inside)
  exact actualToProduct.trans (productToConstant.trans
    (Gaussian.Sequence.Name.Exact.exact_toConstantNamed data.parameter).symm)

end RootSamples

open Purelib.Data in
/-- The polynomial value of a retained inverse model is nonzero in its box.

A zero parameter would make its inverse-root residual have quadrance one,
contradicting the original retained bound of at most one sixteenth. -/
theorem parameter_nonzero (model : Model polynomial box) (point : Gaussian) (inside : box.Contains point) :
    polynomial.eval point ≠ 0 := by
  intro zero
  have residual := (model.residualBound point inside).trans model.bound_small
  rw [model.residual_eq,
      zero, Gaussian.Basic.zero_mul, Gaussian.Basic.sub_zero, Gaussian.Basic.Canonical.normSq_one] at residual
  exact (not_lt_of_ge residual) (by decide : (1 / 16 : Coordinate) < 1)

open Purelib.Riemann in
open Purelib.Approximation in
set_option genInjectivity false in
/-- An operational root channel tied to one retained inverse-polynomial sample bank.

The record keeps the model tolerance, containment, prepared denominator, square law and winding-owner attachment for the
same original polynomial value. -/
structure RootChannel (model : Model polynomial box) (point : Gaussian) where
  /-- The inverse model meets the root-sample tolerance of 1/256. -/ small : model.bound ≤ 1 / 256
  /-- The original point lies in the retained model box. -/ inside : box.Contains point
  /-- The retained polynomial root-sample bank at that point. -/ samples : RootSamples model point
  /-- The prepared apart denominator equivalent to the retained sample channel. -/ prepared :
    Approximation.Gaussian.Division.Prepared (Gaussian.Name.Coherent.CoherentNamed.ofApproximation
    (samples.approximation small inside))
  /-- The prepared denominator squares to the original polynomial value. -/ square : SquareIdentity prepared.denominator
    (polynomial.eval point)
  /-- The winding-owner attachment for the same prepared root channel. -/ attachment :
    RootContinuation.SquareRootChannelOwnership.Attachment prepared.denominator (polynomial.eval point)

constructive_injectivity RootChannel

namespace RootChannel

open Purelib.Riemann in
open Purelib.Approximation in
/-- Construct a certified operational root channel from the retained inverse model.

Build its samples once, derive the square law and apartness from them, and attach a winding owner through the same
prepared denominator. -/
def build (model : Model polynomial box) (small : model.bound ≤ 1 / 256) (point : Gaussian) (inside : box.Contains
  point) :
    RootChannel model point := by
  let samples := Normalization.InverseModelRootSamples.RootSamples.build model point
  let square := RootSamples.square samples small inside
  let prepared := RootContinuation.SquareRootProvenance.prepared_of_square square (parameter_nonzero model point inside)
  have preparedSquare : SquareIdentity prepared.denominator (polynomial.eval point) :=
    (Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects prepared.denominator
      (Gaussian.Name.Coherent.CoherentNamed.ofApproximation (samples.approximation small inside)) prepared.denominator
      (Gaussian.Name.Coherent.CoherentNamed.ofApproximation (samples.approximation small inside))
      prepared.equivalent.symm prepared.equivalent.symm).trans square
  let certificate : RootContinuation.CertifiedSquareRoot.Certificate (polynomial.eval point) :=
    ⟨prepared.denominator, prepared.apart, preparedSquare⟩
  exact ⟨small, inside, samples, prepared, preparedSquare, RootContinuation.SquareRootChannelOwnership.attach
    certificate⟩

open Purelib.Riemann in
/-- Read the certified square-root value, apartness and square law from the retained channel. -/
def certificate (channel : RootChannel model point) : RootContinuation.CertifiedSquareRoot.Certificate (polynomial.eval
  point) :=
  ⟨channel.prepared.denominator, channel.prepared.apart, channel.square⟩

open Purelib.Approximation
/-- Compare the actual polynomial samples with the certified channel on finite common tails.

The comparison reuses the original prepared denominator's equivalence for every positive requested error. -/
def samples_equivalent (channel : RootChannel model point) :
    Gaussian.Equivalence.Equivalent (channel.samples.approximation channel.small channel.inside)
      (Gaussian.Name.Sampling.approximation channel.certificate.value.name) :=
  (Gaussian.Equivalence.Equivalent.toNamed_sampling
    (channel.samples.approximation channel.small channel.inside)).symm.trans channel.prepared.equivalent

/-- The retained winding owner names the root determined by the original polynomial samples. -/
def owner_equivalent (channel : RootChannel model point) :
    Gaussian.Equivalence.NamedEquivalent
      (channel.attachment.owner.certificate channel.attachment.owner.parameterNonzero).value.name
        channel.certificate.value.name :=
  channel.attachment.equivalent.symm

end RootChannel
end Purelib.Riemann.Normalization.InverseModelRootChannels
