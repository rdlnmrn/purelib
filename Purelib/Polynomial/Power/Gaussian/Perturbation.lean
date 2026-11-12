module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
public import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Polynomial.Power.Gaussian.Perturbation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-! ## Constant-coefficient Rouché moves -/

/-- The exact constant perturbation taking `Z^d-source` to `Z^d-target`. -/
def parameterPerturbation (source target :
  Gaussian.Basic.Canonical) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  DensePolynomial.constant (source - target)
end Purelib.Polynomial.Power.Gaussian.Perturbation

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Polynomial.Power.Gaussian.Perturbation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The parameter-perturbation polynomial evaluates to the exact source-minus-target constant. -/
@[simp] theorem parameterPerturbation_eval
    (source target point : Gaussian.Basic.Canonical) :
    (parameterPerturbation source target).eval point = source - target := by
  exact DensePolynomial.eval_constant (source - target) point
end Purelib.Polynomial.Power.Gaussian.Perturbation

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Polynomial.Power.Gaussian.Perturbation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Adding the retained constant perturbation gives exactly the target power polynomial's normalized coefficient table.
-/
theorem polynomial_target_eq_add_perturbation
    (source target : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree =
      Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree + parameterPerturbation
        source
        target := by
  apply Dense.Extensionality.normalized_eq_of_sub_isZero
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial_normalized target degree)
    (DensePolynomial.normalize_add _ _)
  apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point _member
  rw [DensePolynomial.eval_add, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
    Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
    parameterPerturbation, DensePolynomial.eval_constant]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
    ring1

/-- Scaling the retained parameter perturbation gives exactly the power polynomial on the original affine chord.

The equality concerns the complete normalized coefficient table for every
rational parameter, without an interval or squarefreeness assumption.
-/
theorem polynomial_affine_eq_add_scaled_perturbation
    (source target : Gaussian.Basic.Canonical) (degree : Nat.Positive.RootDegree)
    (time : Rat.Fraction.Rational) :
    Power.Gaussian.rootPolynomial
        (Geometry.Rational.Affine.line source (target - source) time) degree =
      Power.Gaussian.rootPolynomial source degree +
        DensePolynomial.scale (⟨time, 0⟩ : Gaussian.Basic.Canonical)
          (parameterPerturbation source target) := by
  apply Dense.Extensionality.normalized_eq_of_sub_isZero
    (Power.Gaussian.rootPolynomial_normalized _ degree)
    (DensePolynomial.normalize_add _ _)
  apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point _member
  rw [DensePolynomial.eval_add, DensePolynomial.eval_scale,
    Power.Gaussian.rootPolynomial_eval, Power.Gaussian.rootPolynomial_eval,
    parameterPerturbation_eval]
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.Rational.Affine.line, Gaussian.Cast.ofCoordinate_re,
      Gaussian.Cast.ofCoordinate_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

end Purelib.Polynomial.Power.Gaussian.Perturbation

end
