module

import Purelib.Polynomial.Dense.Gaussian.Degree
public import Purelib.Polynomial.Dense.Gaussian.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Order.Lattice
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction

open Purelib.Data
open Purelib.Polynomial

/-!
# Splitting the leading coefficient from a dense polynomial

The original leading monomial and normalized lower coefficient tail retain
the displayed high-to-low order. Direct finite lists certify their exact sum.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit

/-- Executable leading monomial `a_d Z^d` for positive dense degree.

The nonzero leading coefficient multiplies the original coordinate-power
factor. The positive-degree convention retains the predecessor exponent
used by that factor and its high-to-low coefficient order. -/
@[expose] public def leadingMonomial (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Constants.gaussianConstant p.leadingCoeff *
    Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1)

/-- Exact finite coefficient list of the displayed leading monomial.

Positive degree makes the leading coefficient nonzero, so normalization
retains that coefficient followed by exactly the degree-many zero entries. -/
public theorem leadingMonomial_coeffs {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreePositive : 0 < p.natDegree) :
    (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).coeffs =
      p.leadingCoeff :: List.replicate p.natDegree 0 := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  unfold Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial Dense.Gaussian.Constants.gaussianConstant
  change (List.foldl
    (fun value a => Dense.Basic.DensePolynomial.shift 1 value + Dense.Basic.DensePolynomial.scale a
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1)))
    0 [p.leadingCoeff]).coeffs = _
  simp only [List.foldl_cons, List.foldl_nil, Dense.Basic.DensePolynomial.shift_zero,
    Dense.Basic.DensePolynomial.zero_add_normalize, Dense.Basic.DensePolynomial.normalize_scale]
  rw [Dense.Basic.DensePolynomial.scale_coeffs_of_ne_zero leadingNonzero]
  have coordinateNormalized :
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1)).normalize =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1) := by
    apply Dense.Basic.DensePolynomial.ext
    change ((Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1)).coeffs.dropWhile
      (· = 0)) = (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (p.natDegree - 1)).coeffs
    rewrite [Dense.Gaussian.Power.Coordinate.coordinatePositivePower_coeffs]
    exact List.DropWhile.cons_of_false
      (fun value : Gaussian.Basic.Canonical => decide (value = 0)) 1 _
      (decide_eq_false Gaussian.BoundaryCanonical.one_ne_zero)
  rewrite [coordinateNormalized, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_coeffs,
    List.map_cons, List.Replicate.map_replicate, Gaussian.Basic.mul_one,
    Gaussian.Basic.mul_zero]
  have restored : p.natDegree - 1 + 1 = p.natDegree :=
    (Nat.add_comm (p.natDegree - 1) 1).trans
      (Nat.Subtraction.add_sub_of_le degreePositive)
  exact congrArg (fun count => p.leadingCoeff :: List.replicate count 0) restored

/-- For positive degree, the leading monomial evaluates to the leading coefficient times the degree power.

The positive-degree assumption identifies the predecessor coordinate
power with the polynomial degree. The retained constant factor supplies
the leading coefficient in the displayed scalar product. -/
public theorem leadingMonomial_eval {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreePositive : 0 < p.natDegree) (z : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z =
      p.leadingCoeff * z ^ p.natDegree := by
  rw [Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial, Dense.Basic.DensePolynomial.eval_mul,
    Dense.Gaussian.Constants.gaussianConstant_eval,
    Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
  have exponent : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [exponent]

/-- Exact finite Horner split into the leading monomial and normalized lower
coefficient tail.

The normalized coefficient list starts with the leading coefficient and
continues with the retained lower tail. Horner expansion separates these
two contributions without changing their order. -/
public theorem leadingMonomial_add_lowerTerms_eval
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    (z : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z +
      (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z =
      p.eval z := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  obtain ⟨tail, coefficients, tailLength⟩ :=
    Dense.Basic.DensePolynomial.normalized_coeffs_shape polynomialNonzero
  rw [Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_eval degreePositive]
  change p.leadingCoeff * z ^ p.natDegree +
      Dense.Basic.DensePolynomial.evalCoeffs z (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p) = p.eval z
  rw [← Dense.Basic.DensePolynomial.eval_normalize p z]
  change _ = Dense.Basic.DensePolynomial.evalCoeffs z p.normalize.coeffs
  rw [coefficients, Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion]
  unfold Dense.Gaussian.Coefficients.Tail.lowerCoefficients
  rw [coefficients]
  simp only [List.tail_cons]
  rw [tailLength]

/-- The leading/lower split is an exact equality of finite normalized
coefficient lists.  This is stronger than evaluation equality and uses no
polynomial extensionality over a field.

Positive degree retains the nonzero leading entry. Padding the lower
tail with a single leading zero and adding the matching lists recovers
the exact normalized high-to-low coefficient sequence. -/
public theorem leadingMonomial_add_lowerTerms_eq_normalize
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p + Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p
      = p.normalize := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  obtain ⟨tail, coefficients, tailLength⟩ :=
    Dense.Basic.DensePolynomial.normalized_coeffs_shape polynomialNonzero
  apply Dense.Basic.DensePolynomial.ext
  have leadingEquality : Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p =
      ⟨p.leadingCoeff :: List.replicate p.natDegree 0⟩ := by
    apply Dense.Basic.DensePolynomial.ext
    exact Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_coeffs degreePositive
  rw [leadingEquality]
  change (Dense.Gaussian.Arithmetic.add ⟨p.leadingCoeff :: List.replicate p.natDegree 0⟩
    ⟨Dense.Gaussian.Coefficients.Tail.lowerCoefficients p⟩).coeffs = p.normalize.coeffs
  unfold Dense.Gaussian.Coefficients.Tail.lowerCoefficients
  rw [coefficients]
  simp only [List.tail_cons]
  unfold Dense.Gaussian.Arithmetic.add Dense.Basic.DensePolynomial.add
    Dense.Basic.DensePolynomial.padLeft Dense.Basic.DensePolynomial.normalize
  simp only [List.length_cons, List.Replicate.length_replicate, tailLength]
  have maximum : max (p.natDegree + 1) p.natDegree = p.natDegree + 1 :=
    (Nat.Order.max_eq_natMax _ _).trans
      (Nat.max_def.trans (if_neg (Nat.not_succ_le_self p.natDegree)))
  rewrite [maximum, Nat.sub_self, Nat.Subtraction.add_sub_cancel_left]
  change ((List.zipWith (· + ·)
      (p.leadingCoeff :: List.replicate p.natDegree 0)
      (0 :: tail)).dropWhile (· = 0)) = p.leadingCoeff :: tail
  rewrite [List.zipWith_cons_cons, Gaussian.Basic.add_zero, ← tailLength,
    Dense.Basic.DensePolynomial.zipWith_replicate_zero_add]
  exact List.DropWhile.cons_of_false
    (fun value : Gaussian.Basic.Canonical => decide (value = 0)) p.leadingCoeff tail
    (decide_eq_false leadingNonzero)

end Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
