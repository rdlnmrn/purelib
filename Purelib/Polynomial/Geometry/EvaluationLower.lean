module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Reverse
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.DropWhile.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplication
public import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra.Gaussian.Energy (NonzeroGaussianVector)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Geometry-backed finite surface energy

The second bilinear relation consumes lower sums on finitely many rational
surface boxes.  This module prevents those lower sums from being supplied as
unattached pairs of rational numbers: every raw cell names one face of the
explicit hyperelliptic cell complex, carries one proper rational box, uses its
exact rational content as area, proves the curve denominator apart throughout
that box, and verifies a lower bound for the displayed algebraic differential
density.

The remaining global comparison is precisely the finite cut-surface
second-relation calculation: the sum of these checked local contributions is
bounded by the synchronized A/B period pairing.  Once that comparison and the
already finite normalization comparison are displayed, the generic transport
layer derives pointwise positivity.
-/

namespace Purelib.Polynomial.Geometry.EvaluationLower

/-- The original finite dense Gaussian polynomial representation. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A finite indexed Gaussian coefficient vector. -/
abbrev GaussianVector (size : Nat) :=
  LinearAlgebra.Gaussian.Energy.GaussianVector size
/-- A finite indexed exact rational coefficient vector. -/
abbrev RationalVector (size : Nat) :=
  LinearAlgebra.Gaussian.QuadraticForm.RationalVector size
/-- The original explicit nonzero-coordinate predicate on a rational coefficient vector. -/
abbrev NonzeroVector {size : Nat} (vector :
  RationalVector size) :=
  LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector

/-- Dense numerator polynomial of a Gaussian-rational combination of the
standard basis `dx/y, x dx/y, ...`.  Dense polynomials store their finite
coefficients in high-to-low order, hence the explicit reversal. -/
def coefficientPolynomial {genus : Nat}
    (coefficients : GaussianVector genus) : GaussianPolynomial where
  coeffs := (List.ofFn coefficients).reverse

/-- The dense coefficient table is exactly the reversal of the finite indexed coefficient enumeration. -/
@[simp] theorem coefficientPolynomial_coeffs {genus : Nat}
    (coefficients : GaussianVector genus) :
    (coefficientPolynomial coefficients).coeffs =
      (List.ofFn coefficients).reverse := rfl

/-- A displayed nonzero differential coefficient remains present in the finite dense numerator.

The original Fin index supplies its occurrence in the unchanged List.ofFn
enumeration. Reversing that same table preserves the coefficient witness. -/
theorem coefficientPolynomial_contains_nonzero {genus : Nat}
    {coefficients : GaussianVector genus}
    (nonzero : NonzeroGaussianVector coefficients) :
    exists coefficient,
      coefficient ∈ (coefficientPolynomial coefficients).coeffs /\
        coefficient ≠ 0 := by
  refine ⟨coefficients nonzero.index, ?_, nonzero.coefficient_nonzero⟩
  change coefficients nonzero.index ∈ (List.ofFn coefficients).reverse
  exact (Data.List.Reverse.mem_reverse _).mpr
    (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨nonzero.index, rfl⟩)

/-- Removing initial zeros cannot empty a coefficient list containing a displayed nonzero coefficient.

Each retained Boolean predicate branch either keeps the original nonempty
tail or discards a zero head. The displayed nonzero occurrence survives every discarded head. -/
private theorem dropWhile_not_empty_of_mem_nonzero
    (coefficients : List Gaussian.Basic.Canonical) {coefficient : Gaussian.Basic.Canonical}
    (member : coefficient ∈ coefficients) (nonzero : coefficient ≠ 0) :
    (coefficients.dropWhile (· = 0)).isEmpty = false := by
  induction coefficients with
  | nil => nomatch member
  | cons head tail inductionHypothesis =>
      cases selected : decide (head = 0) with
      | false =>
          exact congrArg (fun values : List Gaussian.Basic.Canonical => values.isEmpty)
            (Data.List.DropWhile.cons_of_false (fun value : Gaussian.Basic.Canonical => decide (value = 0)) head tail
              selected)
      | true =>
          cases member with
          | head => exact (nonzero (of_decide_eq_true selected)).elim
          | tail _ tailMember =>
              exact (congrArg (fun values : List Gaussian.Basic.Canonical => values.isEmpty)
                (Data.List.DropWhile.cons_of_true (fun value : Gaussian.Basic.Canonical => decide (value = 0)) head tail
                  selected)).trans
                  (inductionHypothesis tailMember)

/-- A nonzero coefficient witness proves that the finite dense numerator is
not the zero polynomial, by direct inspection of the stored coefficient list. -/
theorem coefficientPolynomial_nonzero {genus : Nat}
    {coefficients : GaussianVector genus}
    (nonzero : NonzeroGaussianVector coefficients) :
    (coefficientPolynomial coefficients).isZero = false := by
  rcases coefficientPolynomial_contains_nonzero nonzero with
    ⟨coefficient, member, coefficientNonzero⟩
  exact dropWhile_not_empty_of_mem_nonzero
    (coefficientPolynomial coefficients).coeffs member coefficientNonzero

set_option genInjectivity false in
/-- A finite bounded scan finds a rational point at which both the numerator
combination and the curve polynomial are nonzero. -/
structure ClearEvaluation {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : GaussianVector genus) where
  /-- The retained exact Gaussian point found by the finite product scan. -/ point : Gaussian.Basic.Canonical
  /-- The original differential numerator polynomial is nonzero at the retained point. -/ numerator_nonzero :
    (coefficientPolynomial coefficients).eval point ≠ 0
  /-- The original curve polynomial is nonzero at the same retained point. -/ denominator_nonzero :
    curve.polynomial.eval point ≠ 0

constructive_injectivity ClearEvaluation

/-- Compute a common clear point by scanning the bounded candidate list of
the finite product polynomial. -/
def findClearEvaluation {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : GaussianVector genus)
    (nonzero : NonzeroGaussianVector coefficients) :
    ClearEvaluation curve coefficients := by
  let numerator := coefficientPolynomial coefficients
  let product := numerator * curve.polynomial
  have numeratorNonzero : numerator.isZero = false :=
    coefficientPolynomial_nonzero nonzero
  have productNonzero : product.isZero = false :=
    Dense.Gaussian.Multiplication.product_isZero_false numeratorNonzero
      curve.nonzero
  let evaluation :=
    Dense.Gaussian.NonzeroEvaluation.findNonzeroEvaluation product productNonzero
  have productValueNonzero :
      numerator.eval evaluation.point *
          curve.polynomial.eval evaluation.point ≠ 0 := by
    simpa only [product,
      Dense.Basic.DensePolynomial.eval_mul] using
      evaluation.valueNonzero
  refine
    { point := evaluation.point
      numerator_nonzero := ?_
      denominator_nonzero := ?_ }
  · intro numeratorZero
    apply productValueNonzero
    rw [numeratorZero]
    exact zero_mul _
  · intro denominatorZero
    apply productValueNonzero
    rw [denominatorZero]
    exact mul_zero _

/-- Square-root-free uniform lower bound for the squared norm of a finite
dense polynomial on one rational box.  It is computed from the value at the
fixed lower-left anchor and the finite Horner Lipschitz scan. -/
def uniformNormLower (polynomial :
  GaussianPolynomial) (box : Box) :
    Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor) / 2 -
    Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial box * box.diagonalSq

/-- The computed anchor-minus-oscillation quantity bounds the norm throughout the rational box.

The original anchor and point lie in the same box. Its exact squared diagonal
bounds their polynomial movement, and subtracting that larger movement bound
retains the original half-norm difference estimate. -/
theorem uniformNormLower_le (polynomial :
  GaussianPolynomial) {box : Box}
    {point : Gaussian.Basic.Canonical} (inside : box.Contains point) :
    uniformNormLower polynomial box <=
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
  have anchorInside : box.Contains box.anchor := box.contains_anchor
  have distance :
      Data.Gaussian.Norm.Basic.normSq (box.anchor - point) <=
        box.diagonalSq := by
    have reverseDistance := box.normSq_sub_anchor_le inside
    have reverse : box.anchor - point = -(point - box.anchor) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im] <;> ring1
    rw [reverse, Gaussian.Norm.Basic.normSq_neg]
    exact reverseDistance
  have differenceBound :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval box.anchor - polynomial.eval point) <=
        Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial box *
          box.diagonalSq :=
    (Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
      polynomial anchorInside inside).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos polynomial box).le)
  have triangle :=
    Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (polynomial.eval box.anchor) (polynomial.eval point)
  have rearranged : Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor) / 2 -
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor - polynomial.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
    calc
      _ = (Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor) / 2 -
          Data.Gaussian.Norm.Basic.normSq (polynomial.eval point)) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor - polynomial.eval point)) := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor - polynomial.eval point) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor - polynomial.eval point)) :=
        Fraction.Order.Arithmetic.add_le_add_direct triangle le_rfl
      _ = Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by ring1
  unfold uniformNormLower
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct differenceBound
    (Data.Gaussian.Norm.Basic.normSq (polynomial.eval box.anchor) / 2)).trans rearranged

/-- Uniform norm lower bound based on an arbitrary displayed sample and an
ambient box.  This form supports constructing a smaller positive box while
reusing one finite Lipschitz scan of its ambient box. -/
def sampledNormLower (polynomial :
  GaussianPolynomial) (sample : Gaussian.Basic.Canonical)
    (ambient cell : Box) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample) / 2 -
    Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient *
      cell.diagonalSq

/-- The sample-based lower bound is valid throughout the refined cell.

The original sample and point belong to the same cell inside the retained
ambient box. Its cached Lipschitz bound and the cell's exact squared diagonal
pay the movement subtracted from the sample's half squared norm. -/
theorem sampledNormLower_le (polynomial :
  GaussianPolynomial)
    (sample : Gaussian.Basic.Canonical) {ambient cell : Box}
    (sampleInside : cell.Contains sample) (refines : cell.Refines ambient)
    {point : Gaussian.Basic.Canonical} (inside : cell.Contains point) :
    sampledNormLower polynomial sample ambient cell <=
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
  have sampleAmbient := refines.contains sampleInside
  have pointAmbient := refines.contains inside
  have differenceBound :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval sample - polynomial.eval point) <=
        Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient *
          cell.diagonalSq :=
    (Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
      polynomial sampleAmbient pointAmbient).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (cell.normSq_sub_le_diagonalSq sampleInside inside)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos
            polynomial ambient).le)
  have triangle :=
    Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (polynomial.eval sample) (polynomial.eval point)
  have rearranged : Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample) / 2 -
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample - polynomial.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
    calc
      _ = (Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample) / 2 -
          Data.Gaussian.Norm.Basic.normSq (polynomial.eval point)) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample - polynomial.eval point)) := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample - polynomial.eval point) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample - polynomial.eval point)) :=
        Fraction.Order.Arithmetic.add_le_add_direct triangle le_rfl
      _ = Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) := by ring1
  unfold sampledNormLower
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct differenceBound
    (Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample) / 2)).trans rearranged

/-- Positive radius threshold used for a sampled polynomial norm. -/
def sampledSafeRadius (valueNorm lipschitz : Fraction.Rational) :
  Fraction.Rational :=
  valueNorm / (8 * lipschitz) / 4

/-- A positive radius below the unit and sampled safe-radius caps makes the anchor-minus-variation lower bound positive.
-/
public theorem sampledNormLower_positive_of_radius
    {valueNorm lipschitz radius : Fraction.Rational}
    (valuePositive : 0 < valueNorm) (lipschitzPositive : 0 < lipschitz)
    (radiusPositive : 0 < radius) (radius_le_one : radius <= 1)
    (radius_le_safe : radius <= sampledSafeRadius valueNorm lipschitz) :
    0 < valueNorm / 2 - lipschitz * (8 * radius ^ 2) := open Purelib.Algebra.Field in by
  have radiusSq_le_radius : radius ^ 2 <= radius := by
    rw [pow_two]
    calc
      radius * radius <= radius * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radius_le_one radiusPositive.le
      _ = radius := by ring1
  have eightLipschitzPositive : 0 < 8 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have error_le_quarter :
      lipschitz * (8 * radius ^ 2) <= valueNorm / 4 := by
    calc
      lipschitz * (8 * radius ^ 2) =
          (8 * lipschitz) * radius ^ 2 := by ring1
      _ <= (8 * lipschitz) * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSq_le_radius eightLipschitzPositive.le
      _ <= (8 * lipschitz) * sampledSafeRadius valueNorm lipschitz :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radius_le_safe eightLipschitzPositive.le
      _ = valueNorm / 4 := by
        unfold sampledSafeRadius
        calc
          (8 * lipschitz) * (valueNorm / (8 * lipschitz) / 4) =
              (valueNorm / (8 * lipschitz) * (8 * lipschitz)) / 4 := by
            simp only [Fraction.Field.div_eq_mul_inv_direct]
            ring1
          _ = valueNorm / 4 := by
            rw [ExplicitField.div_mul_cancel valueNorm
              (ne_of_gt eightLipschitzPositive)]
  have quarter_lt_half : valueNorm / 4 < valueNorm / 2 := by
    apply (Fraction.Order.Field.div_lt_iff_pos
      (by decide : (0 : Fraction.Rational) < 4)).2
    calc
      valueNorm = valueNorm * 1 := by ring1
      _ < valueNorm * 2 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          valuePositive (by decide)
      _ = (valueNorm / 2) * 4 := by
        calc
          valueNorm * 2 =
              (valueNorm / 2 * 2) * 2 := by
            rw [ExplicitField.div_mul_cancel valueNorm
              (by decide : (2 : Fraction.Rational) ≠ 0)]
          _ = (valueNorm / 2) * 4 := by ring1
  exact Fraction.Order.Arithmetic.sub_pos_direct
    (error_le_quarter.trans_lt quarter_lt_half)

end Purelib.Polynomial.Geometry.EvaluationLower

end
