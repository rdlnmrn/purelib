module
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Cast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Radial.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Uniform bounds for the cached reciprocal cap factor

The regular inverse-root ceiling and the fixed monomial bound control
G(w) at every finite Newton stage. Radial integration takes place inside
the original inner rectangle and gives the same bound for both parities.
No norm of a growing refined coefficient list is used in the budget.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Gaussian.Cast
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Primitive
open Purelib.Riemann.Comparison
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (degree Sample)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Cast.Path (ofCoordinate)
open Purelib.Geometry.Rational.Affine (line)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}

namespace FactorBounds

/-- Embedding a rational parameter as a Gaussian value commutes with finite powers. -/
private theorem coordinate_power (parameter : InverseRootPolynomial.Coordinate) (exponent : Nat) :
    Path.ofCoordinate (parameter ^ exponent) = (Path.ofCoordinate parameter) ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent previous =>
      rw [pow_succ, pow_succ, ← previous]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Path.ofCoordinate, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1

/-- Every nonnegative unit-interval radial power contraction remains inside the original reciprocal collar box. -/
private theorem radial_inside {point : InverseRootPolynomial.Gaussian} (inside : collar.box.Contains point)
    {parameter : InverseRootPolynomial.Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) (exponent : Nat) :
    collar.box.Contains (point * (Path.ofCoordinate parameter) ^ exponent) := by
  have zeroInside : collar.box.Contains 0 := by
    rw [collar.box_eq]
    exact ⟨(by
        have ordered := Fraction.Order.Arithmetic.neg_le_neg_direct
          (ReciprocalExteriorCollar.innerRadius_positive curve).le
        change -(ReciprocalExteriorCollar.innerRadius curve) ≤ 0 at ordered
        exact ordered),
      (ReciprocalExteriorCollar.innerRadius_positive curve).le,
      (by
        have ordered := Fraction.Order.Arithmetic.neg_le_neg_direct
          (ReciprocalExteriorCollar.innerRadius_positive curve).le
        change -(ReciprocalExteriorCollar.innerRadius curve) ≤ 0 at ordered
        exact ordered),
      (ReciprocalExteriorCollar.innerRadius_positive curve).le⟩
  have powered : 0 ≤ parameter ^ exponent ∧ parameter ^ exponent ≤ 1 :=
    ⟨Fraction.Order.Arithmetic.pow_nonneg_direct unit.1 _,
      (Fraction.Order.Arithmetic.pow_le_pow_direct unit.1 unit.2 exponent).trans_eq (one_pow _)⟩
  have contained := Rational.Box.contains_line zeroInside inside powered
  simpa only [Affine.line, Data.Gaussian.Basic.zero_add, Data.Gaussian.Basic.sub_zero,
    coordinate_power, Data.Gaussian.Basic.mul_comm] using
    contained

end FactorBounds

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
namespace FactorBounds

/-- The radial primitive parity degree equals the original cap coordinate degree. -/
private theorem radial_degree :
    Parity.degree (decide (HyperellipticReciprocal.originOrder curve = 1)) = degree curve := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rewrite [degree, regular]
    exact Eq.refl _
  · rewrite [degree, branch]
    exact Eq.refl _

/-- The squared Gaussian norm of either cap coordinate degree is at most four. -/
private theorem degree_norm : Data.Gaussian.Norm.Basic.normSq (degree curve : InverseRootPolynomial.Gaussian) ≤
  4 := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [degree, regular]
    decide
  · rw [degree, branch]
    decide

end FactorBounds

end

set_option genInjectivity false in
/-- Cache the fixed numerator and its box norm together with the regular inverse ceiling. This data is independent of
the primitive's Newton index. -/
structure FactorBounds (cap : ReciprocalInnerInverse.Data curve collar) (differential : Differentials.Basic.Differential
  genus) where
  /-- The cached fixed reversed-differential monomial polynomial. -/ numerator : InverseRootPolynomial.Polynomial
  /-- The cached numerator evaluates to the exact original reversed-differential coordinate power. -/ numerator_eq : ∀
    point, numerator.eval point = point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent
  /-- The retained numerator and inverse-root ceilings on the original cap-clearance box. -/ base :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds cap.clearance numerator

constructive_injectivity FactorBounds

namespace FactorBounds

/-- Cache the fixed differential monomial and its original cap-box comparison bounds once. -/
@[expose] public def build (cap : ReciprocalInnerInverse.Data curve collar) (differential :
  Differentials.Basic.Differential genus) : FactorBounds cap
  differential :=
  let numerator := DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
    (DensePolynomial.constant 1)
  ⟨numerator, fun point => by rw [DensePolynomial.eval_shift, DensePolynomial.eval_constant,
    Data.Gaussian.Basic.one_mul], PrimitiveOverlapBounds.build cap.clearance numerator⟩

variable {differential : Differential genus}

/-- Eight times the retained numerator and inverse-root ceilings bounds the cached primitive factor. -/
@[expose] public def bound (bounds : FactorBounds cap
  differential) : Coordinate := 8 * bounds.base.numeratorUpper * bounds.base.inverseUpper

/-- The retained uniform primitive-factor ceiling is nonnegative. -/
theorem bound_nonnegative (bounds : FactorBounds cap
  differential) : 0 ≤ bounds.bound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.base.numeratorUpper_nonnegative)
      bounds.base.inverseUpper_positive.le

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives in
/-- The same factor ceiling holds throughout the original inner box at every finite primitive stage, including its
branch origin. -/
theorem factor_le (bounds : FactorBounds cap differential)
  {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) {point : InverseRootPolynomial.Gaussian} (inside :
      collar.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (sample.factor.eval point) ≤ bounds.bound := by
  have estimate := Radial.Bounds.factor_bound sample.factor point
    (decide (HyperellipticReciprocal.originOrder curve = 1))
    (4 * bounds.base.numeratorUpper * bounds.base.inverseUpper) (by
      intro parameter unit
      rw [radial_degree]
      let coordinate := point * (Path.ofCoordinate parameter) ^ degree curve
      have contained : collar.box.Contains coordinate :=
        radial_inside inside unit _
      have productScalar := bounds.base.numerator_inverse_le sample.inverse contained
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at productScalar
      change Data.Gaussian.Norm.Basic.normSq (sample.factor.eval coordinate + (degree curve :
        InverseRootPolynomial.Gaussian) * coordinate *
        (GCD.derivative sample.factor).eval coordinate) ≤ _
      rw [sample.factor_derivative]
      calc
        _ = Data.Gaussian.Norm.Basic.normSq (degree curve : InverseRootPolynomial.Gaussian) *
          Data.Gaussian.Norm.Basic.normSq (bounds.numerator.eval coordinate * sample.inverse.value.eval
          coordinate) := by
          rw [bounds.numerator_eq, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul,
            Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul]
          ring1
        _ ≤ 4 * (bounds.base.numeratorUpper * bounds.base.inverseUpper) :=
          Fraction.Order.Arithmetic.mul_le_mul_direct
            degree_norm
            productScalar (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
        _ = _ := by ring1)
  exact estimate.trans_eq (by unfold bound; ring1)

end FactorBounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
