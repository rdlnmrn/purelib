module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Nat.Subtraction
public import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Charts.Infinity
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials.Basic

open Purelib.Data.Gaussian

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

@[expose] public section

/-!
# The finite reciprocal chart for both hyperelliptic degree shapes

Coefficient reversal and the displayed degree shape construct
`q(w) = w^(2g+2) p(1/w)`. No affine constant coefficient is assumed nonzero.
The original root candidate is scaled, not replaced by an unrelated root;
its full equation residual is transported exactly. The basis differential
coefficient is the negative reversed basis coefficient in this chart.

These are the algebraic laws consumed by finite reciprocal path transport,
not a declaration of a completed surface or an integration equality.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial (shift eval_shift)

/-- Exact Gaussian rational coordinates in the reciprocal chart. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials for the chart radicand. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

/-- Reverse the normalized coefficients of the original Gaussian polynomial. -/
abbrev reversed := Reciprocal.reversed

/-- Select the reciprocal origin factor: one for odd degree and zero for even degree. -/
def originOrder {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : Nat :=
  match curve.degreeShape with
  | .odd _ => 1
  | .even _ => 0

/-- The affine polynomial degree plus the selected origin order is twice the genus plus two. -/
theorem degree_balance {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    curve.polynomial.natDegree + originOrder curve = 2 *
      genus + 2 := by
  cases shape : curve.degreeShape with
  | odd equal =>
    rw [originOrder, shape]; change
      curve.polynomial.natDegree + 1 = _; omega
  | even equal =>
    rw [originOrder, shape]; change
      curve.polynomial.natDegree + 0 = _; omega

/-- A dense finite polynomial, usable by the existing finite root machinery. Reversal keeps zero affine constant terms;
no degree-preservation shortcut is used to discard them. -/
def polynomial {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : GaussianPolynomial :=
  DensePolynomial.shift (originOrder curve)
    (reversed curve.polynomial)

/-- The reciprocal chart polynomial evaluates to the reversed polynomial times its retained origin power. -/
theorem polynomial_eval {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (point :
  Gaussian) :
    (polynomial curve).eval point =
      (reversed curve.polynomial).eval point * point ^
      originOrder curve :=
  DensePolynomial.eval_shift _ _ _

/-- Away from zero, the chart radicand is the affine radicand at the inverse point scaled by the degree-balancing power.
-/
theorem polynomial_identity {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (point : Gaussian) (pointNonzero : point ≠ 0) :
    (polynomial curve).eval point = point ^ (2 * genus +
      2) * curve.polynomial.eval point⁻¹ := by
  rw [polynomial_eval, Reciprocal.reversed_identity
    curve.polynomial point pointNonzero,
    ← degree_balance curve, pow_add]
  ring1

/-- At the missing affine endpoint the chart is regular (even degree), or has a single displayed factor `w` with nonzero
remaining value (odd degree). -/
theorem origin_factor {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    (reversed curve.polynomial).eval 0 ≠ 0 ∧
      (originOrder curve = 0 ∨
      originOrder curve = 1) := by
  refine ⟨?_, ?_⟩
  · rw [Reciprocal.reversed_origin]
    exact DensePolynomial.leadingCoeff_ne_zero curve.nonzero
  · cases shape : curve.degreeShape with
    | odd => exact Or.inr (by rw [originOrder, shape])
    | even => exact Or.inl (by rw [originOrder, shape])

/-- Scale the original sheet coordinate by the reciprocal parameter to the genus-plus-one power. -/
def rootCoordinate (genus : Nat) (point root : Gaussian)
  : Gaussian := point ^ (genus + 1) * root

/-- Reciprocal coordinate scaling preserves negation of the original sheet value. -/
theorem rootCoordinate_neg (genus : Nat) (point root :
  Gaussian) :
    rootCoordinate genus point (-root) =
      -rootCoordinate genus point root := mul_neg _ _

/-- Reciprocal scaling multiplies the original finite root-equation residual by its clearing power.

The displayed nonzero chart supplies the inverse point. Both the original
candidate and its equation residual are retained, including inexact candidates. -/
theorem residual_identity {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (point root :
  Gaussian)
    (pointNonzero : point ≠ 0) :
    rootCoordinate genus point root ^ 2 -
      (polynomial curve).eval point =
      point ^ (2 * genus + 2) * (root ^ 2 - curve.polynomial.eval point⁻¹) := by
  rw [rootCoordinate,
    Algebra.Semiring.Normalization.product_pow, ← pow_mul, show (genus + 1) * 2 = 2 * genus + 2 by omega,
    polynomial_identity curve point pointNonzero]
  ring1

/-- An exact affine sheet equation transports to the reciprocal chart equation away from parameter zero.

The residual identity specializes the same root candidate and inverse point.
Its zero Gaussian difference identifies the two retained chart readings. -/
theorem root_equation {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (point root :
  Gaussian)
    (pointNonzero : point ≠ 0) (equation : root ^ 2 = curve.polynomial.eval point⁻¹) :
    rootCoordinate genus point root ^ 2 =
      (polynomial curve).eval point := by
  have identity := residual_identity curve point root
    pointNonzero
  rw [equation, Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.mul_zero] at identity
  exact Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero identity

/-- Reverse the finite holomorphic differential index in the retained genus.

The original finite index bounds the same natural value `genus - 1 - exponent`.
A zero genus has no index; a successor genus bounds its truncated difference directly. -/
def reversedDifferential {genus : Nat} (differential : Differentials.Basic.Differential genus) :
  Differentials.Basic.Differential genus :=
  ⟨⟨genus - 1 - differential.exponent, by
    cases genus with
    | zero => exact (Nat.not_lt_zero _ differential.index.isLt).elim
    | succ genus =>
        change genus - differential.index.val < genus + 1
        exact Nat.lt_succ_of_le (Nat.sub_le _ _)⟩⟩

/-- The original and reversed differential exponents satisfy the reciprocal degree balance.

The retained finite index is at most the predecessor of its genus. Adding
back its bounded natural difference recovers that same predecessor exactly. -/
theorem differential_balance {genus : Nat} (differential : Differentials.Basic.Differential genus) :
    differential.exponent + 2 + (reversedDifferential
      differential).exponent = genus + 1 := by
  cases genus with
  | zero => exact (Nat.not_lt_zero _ differential.index.isLt).elim
  | succ genus =>
      change differential.index.val + 2 + (genus - differential.index.val) = genus + 1 + 1
      rw [Nat.add_right_comm _ 2,
        Data.Nat.Subtraction.add_sub_of_le (Nat.le_of_lt_succ differential.index.isLt)]

/-- Evaluate the monomial differential coefficient divided by the retained sheet value. -/
def coefficient {genus : Nat} (differential : Differentials.Basic.Differential genus) (point root :
  Gaussian) : Gaussian :=
  point ^ differential.exponent / root

/-- The exact differential coefficient law holds on the reciprocal overlap.

The nonzero point and root allow cancellation of the original scaled sheet
coordinate. Inversion retains its minus sign and the same reversed finite
basis index, with the exponent identity supplying the cleared coordinate power. -/
theorem coefficient_transport {genus : Nat} (differential : Differentials.Basic.Differential genus) (point root :
  Gaussian)
    (pointNonzero : point ≠ 0) (rootNonzero : root ≠ 0) :
    -coefficient
      (reversedDifferential differential) point⁻¹
      (rootCoordinate genus point⁻¹ root) =
      -(point ^ 2 * coefficient differential point root)
        := by
  have reciprocalNonzero : point⁻¹ ≠ 0 := Algebra.Field.ExplicitField.inv_ne_zero pointNonzero
  have scaledNonzero : rootCoordinate genus point⁻¹ root
    ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct (Power.pow_ne_zero_direct _ reciprocalNonzero _) rootNonzero
  have powers : point ^ (differential.exponent + 2) * (point⁻¹) ^ (genus + 1) =
      (point⁻¹) ^ (reversedDifferential
        differential).exponent := by
    rw [← differential_balance differential, pow_add]
    calc
      _ = (point ^ (differential.exponent + 2) * (point⁻¹) ^ (differential.exponent + 2)) *
          (point⁻¹) ^ (reversedDifferential
            differential).exponent := by ring1
      _ = _ := by
        rw [← Algebra.Semiring.Normalization.product_pow, Algebra.Field.ExplicitField.mul_inv_cancel point pointNonzero,
          one_pow, Data.Gaussian.Basic.one_mul]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne scaledNonzero
  rw [coefficient, neg_mul,
    Algebra.Field.ExplicitField.div_mul_cancel _ scaledNonzero]
  change _ = -(point ^ 2 * (point ^ differential.exponent / root)) * ((point⁻¹) ^ (genus + 1) * root)
  calc
    _ = -(point ^ (differential.exponent + 2) * (point⁻¹) ^ (genus + 1)) := congrArg Neg.neg powers.symm
    _ = -((point ^ differential.exponent / root * root) * point ^ 2 * (point⁻¹) ^ (genus + 1)) := by
      rw [Algebra.Field.ExplicitField.div_mul_cancel _ rootNonzero, pow_add]
    _ = _ := by ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
