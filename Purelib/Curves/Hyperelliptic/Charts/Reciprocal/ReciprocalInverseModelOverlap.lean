module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Uniform

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Normalization.InverseModelEdgeOverlap
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Rational.Sign.Interval

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.InverseModelEdgeOverlap

open Purelib.Riemann.Normalization.InverseModelOverlap

@[expose] public section

/-!
# Sheet comparison along the actual reciprocal of an affine path

The reciprocal inverse-root model is multiplied by the root-coordinate
factor before comparison with the source model. Clearing its finite powers
of the coordinate gives a polynomial dot product. A positive squared gap
then fixes its sign on the entire rational source interval, without treating
the inverted arc as a straight edge or choosing signs again at later cuts.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseModelEdgeOverlap (overlapDot)
open Purelib.Riemann.Normalization.InverseModelEdgeOverlap (overlapPolynomial)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial Box Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial (shift eval_shift)

variable {genus : Nat} {curve : HyperellipticCurve genus} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

/-- Transport an inverse-root model, not its root: multiplying by the same factor turns `1/v` into `1/y` when `v =
factor * y`. -/
def value (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox) (point :
      InverseRootPolynomial.Gaussian) : Gaussian :=
  ReciprocalRootNames.factor genus point * right.value.eval point⁻¹

/-- Transport by the exact reciprocal factor preserves the retained inverse-root residual bound at a nonzero source
point. -/
theorem residual (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox)
    {point : InverseRootPolynomial.Gaussian} (nonzero : point ≠ 0) (inside : rightBox.Contains point⁻¹) :
    Data.Gaussian.Norm.Basic.normSq (1 - curve.polynomial.eval point * value curve right point ^ 2) ≤
      right.bound := by
  have identity : 1 - curve.polynomial.eval point * value curve right point ^ 2 =
      1 - (HyperellipticReciprocal.polynomial curve).eval point⁻¹ * (right.value.eval point⁻¹) ^ 2 := by
    rw [← ReciprocalRootNames.factor_identity curve point nonzero]
    dsimp only [value]
    ring1
  rw [identity, ← right.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact right.residualBound _ inside

/-- The coordinate power needed to clear the reciprocal polynomial and original genus factor. -/
private def degree (right : InverseRootPolynomial.Polynomial) (genus : Nat) : Nat := right.natDegree + (genus + 1)

/-- Shift the original source polynomial by the coordinate degree required to clear the reciprocal model. -/
private def clearedLeft (left right : InverseRootPolynomial.Polynomial) (genus : Nat) : Polynomial :=
  DensePolynomial.shift (degree right genus) left

/-- At a nonzero source point, reversing the reciprocal model polynomial evaluates to the transported value times the
clearing power.

The original model polynomial is reversed without changing its coefficient table. The nonzero source coordinate cancels
the retained genus power and leaves exactly the displayed clearing factor. -/
private theorem clearedRight_eval (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve)
  rightBox)
    (point : InverseRootPolynomial.Gaussian) (nonzero : point ≠ 0) :
    (Reciprocal.reversed right.value).eval point =
      point ^ degree right.value genus * value curve right point := by
  rw [Reciprocal.reversed_identity right.value point nonzero]
  dsimp only [value, degree, ReciprocalRootNames.factor]
  rw [pow_add]
  have cancel : point ^ (genus + 1) * (point⁻¹) ^ (genus + 1) = 1 := by
    rw [← Algebra.Semiring.Normalization.product_pow, Algebra.Field.ExplicitField.mul_inv_cancel point nonzero, one_pow]
  calc
    _ = point ^ right.value.natDegree * 1 * right.value.eval point⁻¹ := by ring1
    _ = _ := by rw [← cancel]; ring1

/-- Multiplying both Gaussian arguments by the same factor scales their real dot product by its squared norm. -/
private theorem dot_mul (factor first last : InverseRootPolynomial.Gaussian) :
    InverseModelEdgeOverlap.overlapDot (factor * first) (factor * last) = Data.Gaussian.Norm.Basic.normSq
      factor * InverseModelEdgeOverlap.overlapDot first last := by
  simp only [InverseModelEdgeOverlap.overlapDot, Data.Gaussian.Norm.Basic.normSq, Basic.mul_re, Basic.mul_im]
  ring1

/-- The rational affine-parameter polynomial comparing the two models after clearing their reciprocal coordinate
factors. -/
private def dotPolynomial (left right : InverseRootPolynomial.Polynomial) (genus : Nat) (origin direction :
  InverseRootPolynomial.Gaussian) :=
  InverseModelEdgeOverlap.overlapPolynomial (clearedLeft left right genus) (Reciprocal.reversed right) origin direction

/-- The cleared comparison polynomial equals the original model dot product times the positive coordinate clearing norm.
-/
private theorem dotPolynomial_eval (left : InverseRootPolynomial.Model curve.polynomial leftBox)
    (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox) (origin direction :
      InverseRootPolynomial.Gaussian)
    (parameter : InverseRootPolynomial.Coordinate) (nonzero : Affine.line origin direction parameter ≠ 0) :
    (dotPolynomial left.value right.value genus origin direction).eval parameter =
      Data.Gaussian.Norm.Basic.normSq ((Affine.line origin direction parameter) ^ degree right.value genus) *
        InverseModelEdgeOverlap.overlapDot (left.value.eval (Affine.line origin direction parameter))
          (value curve right (Affine.line origin direction parameter)) := by
  rw [dotPolynomial, InverseModelEdgeOverlap.eval_overlapPolynomial,
    clearedLeft, DensePolynomial.eval_shift, clearedRight_eval right _ nonzero]
  rw [Data.Gaussian.Basic.mul_comm (left.value.eval _)]
  exact dot_mul _ _ _

/-- A Gaussian coordinate with squared norm at least one is nonzero. -/
private theorem nonzero_of_norm_lower {point : InverseRootPolynomial.Gaussian} (lower : 1 ≤
  Data.Gaussian.Norm.Basic.normSq point) : point ≠ 0 := by
  intro zero
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (by decide : ¬((1 : InverseRootPolynomial.Coordinate) ≤ 0)) lower

/-- The positive coordinate clearing factor preserves the sign test of the original inverse-root model comparison.

The clearing factor has positive quadrance because the retained source coordinate has quadrance at least one.
Multiplication by that exact factor preserves the two nonnegative decisions. -/
private theorem dot_sign (left : InverseRootPolynomial.Model curve.polynomial leftBox)
    (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox) (origin direction :
      InverseRootPolynomial.Gaussian)
    (parameter : InverseRootPolynomial.Coordinate) (lower : 1 ≤ Data.Gaussian.Norm.Basic.normSq (Affine.line
      origin direction parameter)) :
    decide (0 ≤ (dotPolynomial left.value right.value genus origin direction).eval parameter) =
      decide (0 ≤ InverseModelEdgeOverlap.overlapDot (left.value.eval (Affine.line origin direction parameter))
        (value curve right (Affine.line origin direction parameter))) := by
  rw [dotPolynomial_eval left right origin direction parameter (nonzero_of_norm_lower lower)]
  have positive : 0 < Data.Gaussian.Norm.Basic.normSq ((Affine.line origin direction parameter) ^ degree
    right.value genus) :=
    Data.Gaussian.Norm.Basic.normSq_pos (Power.pow_ne_zero_direct _ (nonzero_of_norm_lower lower) _)
  by_cases nonnegative : 0 ≤ InverseModelEdgeOverlap.overlapDot (left.value.eval (Affine.line origin direction
    parameter))
      (value curve right (Affine.line origin direction parameter))
  · rw [decide_eq_true nonnegative,
      decide_eq_true (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le nonnegative)]
  · have negative := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (lt_of_not_ge nonnegative)
    rw [Fraction.Field.mul_zero_direct] at negative
    rw [decide_eq_false (not_le_of_gt negative), decide_eq_false nonnegative]

/-- One comparison bit determines the source/reciprocal sheet relation on the entire covered arc. The hypotheses concern
actual path containment and the fixed exterior coordinate margin, not an edge-wide sign certificate.

The original affine interval lies in the source box and its reciprocal lies in the reciprocal box, with quadrance at
least one throughout. Clearing coordinate powers yields a polynomial squared gap, whose sign is constant on that same
interval. -/
theorem flip_eq (left : InverseRootPolynomial.Model curve.polynomial leftBox)
    (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox)
    (origin direction : InverseRootPolynomial.Gaussian) (interval : Data.Rat.Interval.Bounds)
    (leftInside : ∀ parameter, interval.Contains parameter → leftBox.Contains (Affine.line origin direction parameter))
    (rightInside : ∀ parameter, interval.Contains parameter → rightBox.Contains (Affine.line origin direction
      parameter)⁻¹)
    (lower : ∀ parameter, interval.Contains parameter → 1 ≤ Data.Gaussian.Norm.Basic.normSq (Affine.line origin
      direction parameter))
    {first last : InverseRootPolynomial.Coordinate} (firstInside : interval.Contains first) (lastInside :
      interval.Contains last) :
    (SignAlignment.build (left.value.eval (Affine.line origin direction first))
      (value curve right (Affine.line origin direction first))).flip =
    (SignAlignment.build (left.value.eval (Affine.line origin direction last))
      (value curve right (Affine.line origin direction last))).flip := by
  have leftResidual (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (1 - curve.polynomial.eval (Affine.line origin direction parameter) *
        (left.value.eval (Affine.line origin direction parameter)) ^ 2) ≤ left.bound := by
    rw [← left.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact left.residualBound _ (leftInside parameter inside)
  have rightResidual (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :=
    residual right (nonzero_of_norm_lower (lower parameter inside)) (rightInside parameter inside)
  let majorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial leftBox
  have majorantPositive : 0 < majorant := Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _
  have gapPositive : (0 : InverseRootPolynomial.Coordinate) < 1 / (768 * majorant) :=
    Fraction.Order.Field.div_pos_direct (by decide)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) majorantPositive)
  have gap (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      1 / (768 * majorant) ≤ (dotPolynomial left.value right.value genus origin direction).eval parameter ^ 2 := by
    have leftScalar := leftResidual parameter inside
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at leftScalar
    have rightScalar := rightResidual parameter inside
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at rightScalar
    have upperScalar := Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant curve.polynomial (leftInside
      parameter inside)
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at upperScalar
    have raw := SignAlignment.dot_squared_lower
      (SignAlignment.build _ _) leftScalar rightScalar
      left.bound_small right.bound_small majorantPositive upperScalar
    rw [dotPolynomial_eval left right origin direction parameter (nonzero_of_norm_lower (lower parameter inside)),
      Algebra.Semiring.Normalization.product_pow]
    apply raw.trans
    have factorLower : (1 : InverseRootPolynomial.Coordinate) ≤ Data.Gaussian.Norm.Basic.normSq ((Affine.line
      origin direction parameter) ^ degree right.value genus) := by
      rw [Power.normSq_pow]
      simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct
        (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) (lower parameter inside) (degree right.value genus)
    have squareLower := Fraction.Order.Arithmetic.pow_le_pow_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) factorLower 2
    rw [one_pow] at squareLower
    simpa only [Fraction.Field.one_mul] using
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squareLower
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have signs := Uniform.sign_eq_of_squared_lower
    (dotPolynomial left.value right.value genus origin direction) interval gapPositive gap firstInside lastInside
  rw [dot_sign left right origin direction first (lower first firstInside),
    dot_sign left right origin direction last (lower last lastInside)] at signs
  have firstLeftScalar := leftResidual first firstInside
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstLeftScalar
  have firstRightScalar := rightResidual first firstInside
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstRightScalar
  have lastLeftScalar := leftResidual last lastInside
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at lastLeftScalar
  have lastRightScalar := rightResidual last lastInside
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at lastRightScalar
  rw [SignAlignment.flip_eq_dot_sign
      (SignAlignment.build _ _) firstLeftScalar firstRightScalar
      left.bound_small right.bound_small,
    SignAlignment.flip_eq_dot_sign
      (SignAlignment.build _ _) lastLeftScalar lastRightScalar
      left.bound_small right.bound_small, signs]

/-- Two inverse values with sufficiently small mismatch against the same original root are closer with equal signs than
opposite signs. -/
private theorem nearest_of_common_mismatch {root left right : InverseRootPolynomial.Gaussian}
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (1 - root * left) ≤ 1 / 32)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (1 - root * right) ≤ 1 / 32) :
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤ Data.Gaussian.Norm.Basic.normSq (left + right) :=
      by
  have rootNonzero : root ≠ 0 := by
    intro zero
    rw [zero, Basic.zero_mul, Basic.sub_zero, Norm.Basic.normSq_one] at leftSmall
    exact (not_lt_of_ge leftSmall) (by decide +kernel : (1 / 32 : InverseRootPolynomial.Coordinate) < 1)
  have lower : (15 / 32 : InverseRootPolynomial.Coordinate) ≤ Data.Gaussian.Norm.Basic.normSq (root * left) :=
    by
    have bound := Data.Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub (1 : InverseRootPolynomial.Gaussian) (1 - root
      * left)
    rw [show (1 : InverseRootPolynomial.Gaussian) - (1 - root * left) = root * left by ring1,
      Data.Gaussian.Norm.Basic.normSq_one] at bound
    exact (show (15 / 32 : InverseRootPolynomial.Coordinate) = 1 / 2 - 1 / 32 by decide +kernel).trans_le
      ((Fraction.Order.Arithmetic.sub_le_sub_left_direct leftSmall _).trans bound)
  have difference : Data.Gaussian.Norm.Basic.normSq (root * (left - right)) ≤
    Data.Gaussian.Norm.Basic.normSq (root * left) := by
    calc
      _ = Data.Gaussian.Norm.Basic.normSq ((1 - root * right) - (1 - root * left)) := congrArg
        Data.Gaussian.Norm.Basic.normSq (by ring1)
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (1 - root * right) + Data.Gaussian.Norm.Basic.normSq (1
        - root * left)) := Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (1 / 32 + 1 / 32 : InverseRootPolynomial.Coordinate) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add rightSmall leftSmall) (by decide)
      _ ≤ 15 / 32 := by decide +kernel
      _ ≤ _ := lower
  have close : Data.Gaussian.Norm.Basic.normSq (left - right) ≤ Data.Gaussian.Norm.Basic.normSq left
    := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Fraction.Field.mul_comm
      (Data.Gaussian.Norm.Basic.normSq root),
      Fraction.Field.mul_comm (Data.Gaussian.Norm.Basic.normSq root)] at difference
    exact Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct difference (Data.Gaussian.Norm.Basic.normSq_pos
      rootNonzero)
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct (c := Data.Gaussian.Norm.Basic.normSq (left -
    right))
  calc
    _ = 2 * Data.Gaussian.Norm.Basic.normSq (left - right) := by ring1
    _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq left := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      close (by decide)
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq left + Data.Gaussian.Norm.Basic.normSq right) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_right
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)) (by decide)
    _ = _ := by
      simp only [Data.Gaussian.Norm.Basic.normSq, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im];
      ring1

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)

/-- The actual scaled root identification fixes the initial polynomial sign. The finite comparison is proof-only and
permits independently chosen model indices and inexact operational roots on both charts. -/
theorem scaled_equivalent_nearest {sourcePolynomial targetPolynomial : InverseRootPolynomial.Polynomial} {leftCount
  rightCount : Nat}
    {left : ContinuedInverseRoot.ContinuedNeighborhood sourcePolynomial leftCount} {right :
      ContinuedInverseRoot.ContinuedNeighborhood targetPolynomial rightCount}
    {source target factor : InverseRootPolynomial.Gaussian} (first : ContinuedNeighborhood.Point left source)
    (second : ContinuedNeighborhood.Point right target)
    (leftInside : left.box.Contains source) (rightInside : right.box.Contains target)
    (roots : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul (Coherence.exact factor)
      first.certificate.value).name second.certificate.value.name)
    (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((left.base.refine leftIndex).value.eval source - factor *
      (right.base.refine rightIndex).value.eval target) ≤
      Data.Gaussian.Norm.Basic.normSq ((left.base.refine leftIndex).value.eval source + factor *
        (right.base.refine rightIndex).value.eval target) := by
  let firstRoot := first.certificate.value.based (first.residualState (1 / 4096) (by decide +kernel))
  let secondRoot := second.certificate.value.based (second.residualState (1 / 4096) (by decide +kernel))
  have based := (Congruence.coherentMul_respects (Coherence.exact factor) (Coherence.exact factor)
    firstRoot first.certificate.value (NamedEquivalent.refl _)
    (first.certificate.value.basedEquivalent (first.residualState (1 / 4096) (by decide +kernel))).symm).trans
    (roots.trans (second.certificate.value.basedEquivalent (second.residualState (1 / 4096) (by decide +kernel))))
  let product := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (Coherence.exact factor).name
    firstRoot.name
  have toProduct : Gaussian.Equivalence.Equivalent (Sampling.approximation (CoherentNamed.mul (Coherence.exact factor)
    firstRoot).name) product :=
    Equivalent.trans (Bridge.coherentMul_toNamed (Coherence.exact factor) firstRoot)
      (Equivalent.toNamed_sampling product)
  let equivalent := Equivalent.trans toProduct.symm based
  let rightValue := (right.base.refine rightIndex).value.eval target
  let scale := Data.Gaussian.Norm.Basic.normSq rightValue + 1
  have scalePositive : 0 < scale := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  let error : Coordinate := (1 / 128) / scale
  have errorPositive : 0 < error := Fraction.Order.Field.div_pos_direct (by decide +kernel) scalePositive
  let comparison := equivalent.compare 0 0 error errorPositive
  let firstValue := Gaussian.Process.Sampling.witnessAt firstRoot.name.process firstRoot.name.state comparison.leftIndex
  let secondValue := Gaussian.Process.Sampling.witnessAt secondRoot.name.process secondRoot.name.state
    comparison.rightIndex
  have firstPossible := Gaussian.Process.Sampling.witnessAt_possible_start firstRoot.name.process firstRoot.name.state
    comparison.leftIndex
  have secondPossible := Gaussian.Process.Sampling.witnessAt_possible_start secondRoot.name.process
    secondRoot.name.state comparison.rightIndex
  have firstMismatch : Data.Gaussian.Norm.Basic.normSq (1 - firstValue * (left.base.refine
    leftIndex).value.eval source) ≤ 1 / 128 := by
    have scalar := first.polynomial_mismatch leftInside (1 / 4096) (by decide +kernel) le_rfl firstPossible leftIndex
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      ((add_le_add (Geometric.Basic.quarterRadius_le_scale (by decide +kernel) leftIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : InverseRootPolynomial.Coordinate) + 16 * (1 / 4096) = 1 / 128))
  have secondMismatch : Data.Gaussian.Norm.Basic.normSq (1 - secondValue * rightValue) ≤ 1 / 128 := by
    have scalar := second.polynomial_mismatch rightInside (1 / 4096) (by decide +kernel) le_rfl secondPossible
      rightIndex
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      ((add_le_add (Geometric.Basic.quarterRadius_le_scale (by decide +kernel) rightIndex) le_rfl).trans_eq
        (by decide +kernel : (1 / 256 : InverseRootPolynomial.Coordinate) + 16 * (1 / 4096) = 1 / 128))
  have close : Data.Gaussian.Norm.Basic.normSq (factor * firstValue - secondValue) ≤ error := (comparison.close
    (Nat.le_refl _) (Nat.le_refl _)).le
  have multiplied : Data.Gaussian.Norm.Basic.normSq ((factor * firstValue - secondValue) * rightValue) ≤ 1 /
    128 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    calc
      _ ≤ error * Data.Gaussian.Norm.Basic.normSq rightValue :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct close (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      _ ≤ error * scale := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)) errorPositive.le
      _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ scalePositive.ne'
  apply nearest_of_common_mismatch (firstMismatch.trans (by decide +kernel))
  calc
    _ = Data.Gaussian.Norm.Basic.normSq ((1 - secondValue * rightValue) - (factor * firstValue - secondValue) *
      rightValue) := congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (1 - secondValue * rightValue) +
      Data.Gaussian.Norm.Basic.normSq ((factor * firstValue - secondValue) * rightValue)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (1 / 128 + 1 / 128 : InverseRootPolynomial.Coordinate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add secondMismatch multiplied) (by decide)
    _ = 1 / 32 := by decide +kernel

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
