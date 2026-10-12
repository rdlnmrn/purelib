module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Sequence.Coherence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Arithmetic.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

/-- Three canonical CCL samplers added at one common finite index. -/
@[expose] def sampledTripleSumApproximation (left middle right : Gaussian.Name.Basic.Named) :
    ApproximationData where
  sample index :=
    ((Sampling.approximation left).sample index +
      (Sampling.approximation middle).sample index) +
        (Sampling.approximation right).sample index
  radiusSq := Geometric.Basic.quarterRadius 40
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 40) (by decide)).le
  later_close := by
    intro earlier later order
    let leftSource :=
      Sampling.approximation left
    let middleSource :=
      Sampling.approximation middle
    let rightSource :=
      Sampling.approximation right
    have leftMovement := leftSource.later_close order
    have middleMovement := middleSource.later_close order
    have rightMovement := rightSource.later_close order
    have identity :
        (leftSource.sample later + middleSource.sample later +
              rightSource.sample later) -
            (leftSource.sample earlier + middleSource.sample earlier +
              rightSource.sample earlier) =
          ((leftSource.sample later - leftSource.sample earlier) +
              (middleSource.sample later - middleSource.sample earlier)) +
            (rightSource.sample later - rightSource.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          (((leftSource.sample later - leftSource.sample earlier) +
              (middleSource.sample later - middleSource.sample earlier)) +
            (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              ((leftSource.sample later - leftSource.sample earlier) +
                (middleSource.sample later - middleSource.sample earlier)) +
            Data.Gaussian.Norm.Basic.normSq
              (rightSource.sample later - rightSource.sample earlier)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (2 *
              (Geometric.Basic.quarterRadius 4 earlier +
                Geometric.Basic.quarterRadius 4 earlier) +
            Geometric.Basic.quarterRadius 4 earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftMovement middleMovement) (by decide)))
            rightMovement)
          (by decide)
      _ = Geometric.Basic.quarterRadius 40 earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  refineIndex current target _ :=
    Search.firstQuarterBelow 40 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 40 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 40
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 40) (by decide)).le
  centerBound :=
    2 *
      (2 *
          ((Sampling.approximation left).centerBound +
            (Sampling.approximation middle).centerBound) +
        (Sampling.approximation right).centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Sampling.approximation
              left).centerBound_nonneg
            (Sampling.approximation
              middle).centerBound_nonneg))
        (Sampling.approximation
          right).centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add
          ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add
                ((Sampling.approximation
                  left).sample_bounded index)
                ((Sampling.approximation
                  middle).sample_bounded index))
              (by decide)))
          ((Sampling.approximation
            right).sample_bounded index))
        (by decide))

/-- Sampling the triple-sum approximation adds the three original canonical samples at the same finite index. -/
@[simp] theorem sampledTripleSumApproximation_sample
    (left middle right : Gaussian.Name.Basic.Named) (index : Nat) :
    (Approximation.Gaussian.Arithmetic.Sampling.sampledTripleSumApproximation left middle right).sample index =
      ((Sampling.approximation left).sample index +
        (Sampling.approximation middle).sample index) +
          (Sampling.approximation right).sample
            index :=
  rfl

/-- An actual addition of two approximation-backed coherent names can be normalized to any finite approximation having
their pointwise sum samples. -/
@[expose] def addToNamed_equivalent_pointwise (left right sum : ApproximationData)
    (samples : ∀ index,
      sum.sample index = left.sample index + right.sample index) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        left.toNamed right.toNamed)
      sum.toNamed := by
  let leftNamed :=
    CoherentNamed.ofApproximation left
  let rightNamed :=
    CoherentNamed.ofApproximation right
  let canonical := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.toNamed right.toNamed
  have canonicalToSum :
      Gaussian.Equivalence.Equivalent canonical sum :=
    Congruence.pointwiseSumApproximation_respects
      (Equivalent.toNamed_sampling left)
      (Equivalent.toNamed_sampling right)
      (by intro index; rfl)
      samples
  exact NamedEquivalent.trans
    (by
      simpa only [leftNamed, rightNamed,
        CoherentNamed.ofApproximation] using
        Bridge.coherentAdd_toNamed leftNamed rightNamed)
    (Equivalence.approximationEquivalent_toNamed canonicalToSum)

/-- The common equal-index sampler for the two sides of left distributivity. -/
@[expose] def sampledLeftDistributiveApproximation
    (left middle right : Gaussian.Name.Basic.Named) : Gaussian.Sequence.ApproximationData := by
  let leftProduct := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left middle
  let rightProduct := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left right
  let scale : Fraction.Rational :=
    2 * (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale left middle +
      Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale left right)
  exact
    { sample := fun index =>
        leftProduct.sample index + rightProduct.sample index
      radiusSq := Geometric.Basic.quarterRadius scale
      radiusSq_nonneg :=
        Geometric.Basic.quarterRadius_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale_nonneg left middle)
              (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale_nonneg left right)))
      later_close := by
        intro earlier later order
        have leftMovement := leftProduct.later_close order
        have rightMovement := rightProduct.later_close order
        have identity :
            leftProduct.sample later + rightProduct.sample later -
                (leftProduct.sample earlier + rightProduct.sample earlier) =
              (leftProduct.sample later - leftProduct.sample earlier) +
                (rightProduct.sample later - rightProduct.sample earlier) := by
          apply Data.Gaussian.Basic.ext <;>
            simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
              Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
        rw [identity]
        calc
          Data.Gaussian.Norm.Basic.normSq
              ((leftProduct.sample later - leftProduct.sample earlier) +
                (rightProduct.sample later - rightProduct.sample earlier)) ≤
            2 *
              (Data.Gaussian.Norm.Basic.normSq
                  (leftProduct.sample later - leftProduct.sample earlier) +
                Data.Gaussian.Norm.Basic.normSq
                  (rightProduct.sample later - rightProduct.sample earlier)) :=
            Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ ≤ 2 *
              (Geometric.Basic.quarterRadius
                  (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale left middle) earlier +
                Geometric.Basic.quarterRadius
                  (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale left right) earlier) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add leftMovement rightMovement) (by decide)
          _ = Geometric.Basic.quarterRadius scale earlier := by
            dsimp only [scale]
            rw [Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      refineIndex := fun current target _ =>
        Search.firstQuarterBelow scale current target
      refineIndex_ge := fun current target _ =>
        Search.firstQuarterBelow_ge
          scale current target
      refineIndex_accurate :=
        Search.firstQuarterBelow_accurate scale
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale_nonneg left middle)
              (Gaussian.Sequence.Arithmetic.Product.sampledProductErrorScale_nonneg left right)))
      centerBound := 2 *
        (leftProduct.centerBound + rightProduct.centerBound)
      centerBound_nonneg :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg leftProduct.centerBound_nonneg
            rightProduct.centerBound_nonneg)
      sample_bounded := by
        intro index
        exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.sample_bounded index)
              (rightProduct.sample_bounded index))
            (by decide)) }

/-- Sampling the distributive comparison approximation adds the two products at the same original input sample index. -/
@[simp] theorem sampledLeftDistributiveApproximation_sample
    (left middle right : Gaussian.Name.Basic.Named) (index : Nat) :
    (Approximation.Gaussian.Arithmetic.Sampling.sampledLeftDistributiveApproximation left middle right).sample index =
      (Sampling.approximation left).sample index *
          (Sampling.approximation middle).sample
            index +
        (Sampling.approximation left).sample index *
          (Sampling.approximation right).sample
            index := by
  rfl

end

end Purelib.Approximation.Gaussian.Arithmetic.Sampling
