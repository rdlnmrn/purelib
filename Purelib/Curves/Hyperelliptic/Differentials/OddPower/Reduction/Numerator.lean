module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction
import Purelib.Algebra.Quadratic.Pair.Polynomial.Primitive
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.Bool.Decide
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
import Purelib.Polynomial.Dense.Gaussian.Derivative.Degree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Division.CancelLead
public import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Polynomial numerators modulo exact sheet primitives

The finite operation `T_F(B) = B′F + BF′/2` is the numerator of the exact
primitive `B*Y`, represented by the original odd expression `BF/Y`.
Leading-term cancellation retains the original curve derivative and leading
coefficient throughout one coefficient-count-bounded run. Its final numerator
has at most `deg(F)-1` coefficients. A nonzero constant curve produces zero
remainder by the same run; the original squarefree preparation excludes zero.

This coefficient reduction supplies an original derivative specification and
operational agreement on the same admitted sheet. It supplies no compact
cohomology independence, residue condition, infinity parity or geometric
period transport.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction.Numerator

open Purelib
open Purelib.Polynomial
open Purelib.Algebra.Field (ExplicitField)
open Dense.Basic.DensePolynomial
open Dense.Leading (LeadingTerm)
open Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Derivative
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The exact monomial used by a displayed leading cancellation. -/
@[expose] def monomial (exponent : Nat) : CoefficientPolynomial := shift exponent (constant 1)

/-- The numerator of the derivative of the original sheet product `B*Y`.

The supplied curve derivative is an actual retained cache; the original
finite derivative program computes the monomial or polynomial derivative. -/
@[expose] def image (polynomial polynomialDerivative primitive : CoefficientPolynomial) : CoefficientPolynomial :=
  GCD.derivative primitive * polynomial + (primitive * polynomialDerivative).scale (1 / 2)

/-- The leading weight is computed from the displayed integer `2k+d`, avoiding recursive numeral casts. -/
@[expose] def weight (degree exponent : Nat) : Canonical :=
  (⟨Fraction.Cast.fromInt (Int.ofNat (2 * exponent + degree)), 0⟩ : Canonical) / 2

/-- The direct integer weight agrees with `k+d/2` in the original Gaussian field. -/
theorem weight_eq (degree exponent : Nat) :
    weight degree exponent = (exponent : Canonical) + (degree : Canonical) / 2 := by
  have integerCast : (⟨Fraction.Cast.fromInt (Int.ofNat (2 * exponent + degree)), 0⟩ : Canonical) =
      ((2 * exponent + degree : Nat) : Canonical) := by
    apply Data.Gaussian.Basic.ext
    · rewrite [Data.Gaussian.Cast.natCast_re, Fraction.Cast.natCast_eq_fromInt]
      rfl
    · rewrite [Data.Gaussian.Cast.natCast_im]
      rfl
  unfold weight
  rewrite [integerCast, Algebra.NatCast.add, Algebra.NatCast.mul,
    ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
  have half : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
  calc
    _ = (exponent : Canonical) * (2 * (2 : Canonical)⁻¹) +
        (degree : Canonical) * (2 : Canonical)⁻¹ := by ring1
    _ = _ := by rewrite [half, Data.Gaussian.Basic.mul_one]; rfl

/-- Every positive displayed cancellation weight is nonzero. -/
theorem weight_nonzero {degree exponent : Nat} (positive : 0 < 2 * exponent + degree) :
    weight degree exponent ≠ 0 := by
  have integerCast : (⟨Fraction.Cast.fromInt (Int.ofNat (2 * exponent + degree)), 0⟩ : Canonical) =
      ((2 * exponent + degree : Nat) : Canonical) := by
    apply Data.Gaussian.Basic.ext
    · rewrite [Data.Gaussian.Cast.natCast_re, Fraction.Cast.natCast_eq_fromInt]
      rfl
    · rewrite [Data.Gaussian.Cast.natCast_im]
      rfl
  unfold weight
  rewrite [integerCast]
  exact div_ne_zero_direct
    (Degree.gaussian_natCast_ne_zero positive)
    (by decide +kernel : (2 : Canonical) ≠ 0)

/-- The finite derivative image of zero evaluates to zero for every supplied curve cache. -/
theorem image_zero_eval (polynomial polynomialDerivative : CoefficientPolynomial) (point : Canonical) :
    (image polynomial polynomialDerivative 0).eval point = 0 := by
  unfold image
  rewrite [GCD.derivative, Dense.Derivative.derivative_zero,
    eval_add, eval_mul, eval_scale, eval_mul, eval_zero]
  ring1

/-- Addition of primitive polynomials adds their original derivative-image readings. -/
theorem image_add_eval (polynomial polynomialDerivative left right : CoefficientPolynomial) (point : Canonical) :
    (image polynomial polynomialDerivative (left + right)).eval point =
      (image polynomial polynomialDerivative left).eval point +
        (image polynomial polynomialDerivative right).eval point := by
  simp only [image, GCD.derivative, eval_add, eval_mul, eval_scale,
    Dense.Derivative.eval_derivative_add, -eq_self, -iff_self]
  ring1

/-- Scaling a primitive scales the same original derivative-image reading. -/
theorem image_scale_eval (polynomial polynomialDerivative primitive : CoefficientPolynomial)
    (factor point : Canonical) :
    (image polynomial polynomialDerivative (primitive.scale factor)).eval point =
      factor * (image polynomial polynomialDerivative primitive).eval point := by
  simp only [image, GCD.derivative, eval_add, eval_mul, eval_scale,
    Dense.Derivative.eval_derivative_scale, -eq_self, -iff_self]
  ring1

/-- Subtracting two primitive polynomials subtracts their same retained derivative-image readings. -/
theorem image_sub_eval (polynomial polynomialDerivative left right : CoefficientPolynomial) (point : Canonical) :
    (image polynomial polynomialDerivative (left - right)).eval point =
      (image polynomial polynomialDerivative left).eval point -
        (image polynomial polynomialDerivative right).eval point := by
  simp only [image, GCD.derivative, eval_add, eval_mul, eval_scale, eval_sub,
    Dense.Derivative.eval_derivative_sub, -eq_self, -iff_self]
  ring1

/-- A displayed monomial has its exact normalized leading term. -/
theorem monomial_leading (exponent : Nat) : LeadingTerm (monomial exponent) exponent (1 : Canonical) := by
  have shifted := (LeadingTerm.constant (by decide +kernel : (1 : Canonical) ≠ 0)).shift exponent
  exact LeadingTerm.of_equal rfl (Nat.zero_add exponent).symm rfl shifted

/-- The derivative image of a nonzero polynomial has its exact degree and weighted leading coefficient.

The actual curve derivative cache is retained. Its leading term and the
primitive derivative's leading term add with positive characteristic-zero
weight `k+d/2`; constant-curve and constant-primitive edges use the same rule.
-/
theorem image_leading {polynomial polynomialDerivative primitive : CoefficientPolynomial}
    {degree exponent : Nat} {leading coefficient : Canonical}
    (curve : LeadingTerm polynomial degree leading)
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (source : LeadingTerm primitive exponent coefficient) (positive : 0 < 2 * exponent + degree) :
    LeadingTerm (image polynomial polynomialDerivative primitive)
      (exponent + degree - 1) (weight degree exponent * (coefficient * leading)) := by
  have halfNonzero : (1 / 2 : Canonical) ≠ 0 := by decide +kernel
  have weightedNonzero := Data.Gaussian.Field.mul_ne_zero_direct (weight_nonzero positive)
    (Data.Gaussian.Field.mul_ne_zero_direct source.coefficient_ne_zero curve.coefficient_ne_zero)
  cases degree with
  | zero =>
      have constantEq : polynomial = constant leading := by
        have readback := normalize_eq_constant_leadingCoeff_of_degree_zero curve.nonzero curve.degree_eq
        rewrite [curve.normalized, curve.coefficient_eq] at readback
        exact readback
      have derivativeZero : polynomialDerivative = 0 := by
        rewrite [derivativeEq, constantEq, GCD.derivative, Dense.Derivative.derivative_constant]
        rfl
      cases exponent with
      | zero => exact False.elim (Nat.not_lt_zero 0 positive)
      | succ exponent =>
          have sourceDerivative := Degree.derivative_leading source.nonzero
            (by rewrite [source.degree_eq]; exact Nat.zero_lt_succ _)
          have first := sourceDerivative.mul curve
          have imageEq : image polynomial polynomialDerivative primitive =
              GCD.derivative primitive * polynomial := by
            unfold image
            rewrite [derivativeZero, mul_eq_zero_of_isZero_right (p := primitive) (q := 0) (by rfl), scale_zero_right,
              add_zero_normalize, normalize_mul]
            rfl
          apply LeadingTerm.of_equal imageEq (by rewrite [source.degree_eq]; omega0) ?_ first
          rewrite [source.degree_eq, source.coefficient_eq, weight_eq, ExplicitField.div_eq_mul_inv]
          ring1
  | succ degree =>
      have curveDerivative := Degree.derivative_leading curve.nonzero
        (by rewrite [curve.degree_eq]; exact Nat.zero_lt_succ _)
      have retainedDerivative : LeadingTerm polynomialDerivative degree
          (((degree + 1 : Nat) : Canonical) * leading) := by
        apply LeadingTerm.of_equal derivativeEq rfl rfl
        change LeadingTerm (Dense.Derivative.derivative polynomial) degree
          (((degree + 1 : Nat) : Canonical) * leading)
        rewrite [curve.degree_eq, curve.coefficient_eq] at curveDerivative
        exact curveDerivative
      cases exponent with
      | zero =>
          have sourceEq : primitive = constant coefficient := by
            have readback := normalize_eq_constant_leadingCoeff_of_degree_zero source.nonzero source.degree_eq
            rewrite [source.normalized, source.coefficient_eq] at readback
            exact readback
          have second := (source.mul retainedDerivative).scale halfNonzero
          have imageEq : image polynomial polynomialDerivative primitive =
              (primitive * polynomialDerivative).scale (1 / 2) := by
            unfold image
            rewrite [sourceEq, GCD.derivative, Dense.Derivative.derivative_constant,
              mul_eq_zero_of_isZero_left (p := 0) (q := polynomial) (by rfl), zero_add_normalize, normalize_scale]
            rfl
          apply LeadingTerm.of_equal imageEq (by omega0) ?_ second
          rewrite [weight_eq, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
          ring1
      | succ exponent =>
          have sourceDerivative := Degree.derivative_leading source.nonzero
            (by rewrite [source.degree_eq]; exact Nat.zero_lt_succ _)
          have first : LeadingTerm (GCD.derivative primitive * polynomial)
              (exponent + degree + 1) ((((exponent + 1 : Nat) : Canonical) * coefficient) * leading) := by
            have original := sourceDerivative.mul curve
            rewrite [source.degree_eq, source.coefficient_eq] at original
            exact LeadingTerm.of_equal rfl (by omega0) rfl original
          have second : LeadingTerm ((primitive * polynomialDerivative).scale (1 / 2))
              (exponent + degree + 1)
              ((1 / 2 : Canonical) * (coefficient * (((degree + 1 : Nat) : Canonical) * leading))) := by
            have original := (source.mul retainedDerivative).scale halfNonzero
            exact LeadingTerm.of_equal rfl (by omega0) rfl original
          have sumEq : ((((exponent + 1 : Nat) : Canonical) * coefficient) * leading) +
              (1 / 2 : Canonical) * (coefficient * (((degree + 1 : Nat) : Canonical) * leading)) =
              weight (degree + 1) (exponent + 1) * (coefficient * leading) := by
            rewrite [weight_eq, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
            ring1
          have sumNonzero : ((((exponent + 1 : Nat) : Canonical) * coefficient) * leading) +
              (1 / 2 : Canonical) * (coefficient * (((degree + 1 : Nat) : Canonical) * leading)) ≠ 0 := by
            rewrite [sumEq]
            exact weightedNonzero
          exact LeadingTerm.of_equal rfl (by omega0) sumEq.symm (first.add second sumNonzero)

/-- The original monomial image is the specialization of the complete polynomial leading-term rule. -/
theorem image_monomial_leading {polynomial polynomialDerivative : CoefficientPolynomial}
    {degree : Nat} {leading : Canonical} (curve : LeadingTerm polynomial degree leading)
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial) (exponent : Nat)
    (positive : 0 < 2 * exponent + degree) :
    LeadingTerm (image polynomial polynomialDerivative (monomial exponent))
      (exponent + degree - 1) (weight degree exponent * leading) := by
  have original := image_leading curve derivativeEq (monomial_leading exponent) positive
  rewrite [Data.Gaussian.Basic.one_mul] at original
  exact original

/-- Normalizing the curve and primitive preserves the complete normalized image polynomial.

The original derivative cache is unchanged. Finite Gaussian coefficient-grid
comparison identifies the two normalized image outputs from their exact
Horner evaluation and derivative-normalization laws.
-/
theorem image_normalize (polynomial polynomialDerivative primitive : CoefficientPolynomial) :
    image polynomial.normalize polynomialDerivative primitive.normalize =
      image polynomial polynomialDerivative primitive := by
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq (normalize_add _ _) (normalize_add _ _)
  intro point
  simp only [GCD.derivative, eval_add, eval_mul, eval_scale, eval_normalize,
    Dense.Derivative.derivative_normalize, -eq_self, -iff_self]
  rfl

/-- A nonzero primitive on a positive-degree curve has the same exact leading rule without normalization assumptions. -/
theorem image_leading_of_nonzero {polynomial polynomialDerivative primitive : CoefficientPolynomial}
    (curveNonzero : polynomial.isZero = false) (positive : 0 < polynomial.natDegree)
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (primitiveNonzero : primitive.isZero = false) :
    LeadingTerm (image polynomial polynomialDerivative primitive)
      (primitive.natDegree + polynomial.natDegree - 1)
      (weight polynomial.natDegree primitive.natDegree * (primitive.leadingCoeff * polynomial.leadingCoeff)) := by
  have cached : polynomialDerivative = GCD.derivative polynomial.normalize := by
    change polynomialDerivative = Dense.Derivative.derivative polynomial.normalize
    rewrite [Dense.Derivative.derivative_normalize]
    exact derivativeEq
  have weightPositive : 0 < 2 * primitive.natDegree + polynomial.natDegree := by omega0
  have original := image_leading (LeadingTerm.normalizeSelf curveNonzero) cached
    (LeadingTerm.normalizeSelf primitiveNonzero) weightPositive
  exact LeadingTerm.of_equal (image_normalize polynomial polynomialDerivative primitive).symm rfl rfl original

/-- A finite doubled operator certificate identifies the original normalized target with its exact image.

The supplied derivative cache belongs to the original polynomial. Division by
two is discharged by its closed exact inverse law before finite coefficient
extensionality; semantic equality alone is not treated as literal coefficients.
-/
theorem image_eq_of_operator_identity {polynomial polynomialDerivative primitive target : CoefficientPolynomial}
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (identity : (target.scale 2 -
      ((polynomial * GCD.derivative primitive).scale 2 + GCD.derivative polynomial * primitive)).isZero = true) :
    target.normalize = image polynomial polynomialDerivative primitive := by
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq (normalize_normalize _) (normalize_add _ _)
  intro point
  have zero := eval_eq_zero_of_isZero identity point
  simp only [eval_sub, eval_scale, eval_add, eval_mul] at zero
  rewrite [eval_normalize]
  apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  have half : (2 : Canonical) * (1 / 2 : Canonical) = 1 := by decide +kernel
  simp only [derivativeEq, eval_add, eval_mul, eval_scale]
  calc
    _ = (2 * target.eval point -
        (2 * (polynomial.eval point * (GCD.derivative primitive).eval point) +
          (GCD.derivative polynomial).eval point * primitive.eval point)) +
      2 * polynomial.eval point * (GCD.derivative primitive).eval point +
        (GCD.derivative polynomial).eval point * primitive.eval point := by ring1
    _ = 2 * polynomial.eval point * (GCD.derivative primitive).eval point +
        (GCD.derivative polynomial).eval point * primitive.eval point := by rewrite [zero]; ring1
    _ = 2 * polynomial.eval point * (GCD.derivative primitive).eval point +
        (2 * (1 / 2 : Canonical)) *
          ((GCD.derivative polynomial).eval point * primitive.eval point) := by rewrite [half]; ring1
    _ = _ := by ring1

/-- No nonzero polynomial image lies below the curve's affine remainder degree threshold.

The exact leading coefficient cannot cancel in characteristic zero. Comparing
the actual coefficient count with the same normalized target forces the
primitive and target zero tests to succeed.
-/
theorem small_image_zero {polynomial polynomialDerivative primitive target : CoefficientPolynomial}
    (curveNonzero : polynomial.isZero = false) (positive : 0 < polynomial.natDegree)
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (small : target.degreeCount ≤ polynomial.natDegree - 1)
    (identity : target.normalize = image polynomial polynomialDerivative primitive) :
    primitive.isZero = true ∧ target.isZero = true := by
  have primitiveZero : primitive.isZero = true := by
    by_cases zero : primitive.isZero = true
    · exact zero
    · have leading := image_leading_of_nonzero curveNonzero positive derivativeEq
        (Data.Bool.Decide.bool_eq_false_of_not_eq_true _ zero)
      have count := congrArg (fun p : CoefficientPolynomial => p.degreeCount) identity
      rewrite [degreeCount_normalize, leading.count_eq] at count
      omega0
  refine ⟨primitiveZero, ?_⟩
  apply Dense.Gaussian.Extensionality.isZero_of_eval_eq_zero
  intro point
  have same := congrArg (fun p : CoefficientPolynomial => p.eval point) identity
  rewrite [eval_normalize] at same
  rewrite [same, ← image_normalize polynomial polynomialDerivative primitive,
    normalize_eq_zero_of_isZero primitiveZero]
  exact image_zero_eval polynomial.normalize polynomialDerivative point

/-- An affine reduced numerator exact through an admitted original rational primitive is zero.

The rational-primitive theorem first constructs the actual polynomial
primitive coefficient. The retained preparation supplies the same curve
derivative cache for its image; the exact leading-degree rule then rules out
every nonzero reduced relation.
-/
theorem reduced_exact_zero {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (curveNonzero : polynomial.isZero = false)
    (positive : 0 < polynomial.natDegree) (target : CoefficientPolynomial)
    (small : target.degreeCount ≤ polynomial.natDegree - 1)
    (primitive : Expression polynomial) (denominatorNonzero : primitive.denominator.isZero = false)
    (exactDerivative : primitive.derivative.Equal (Expression.oddReciprocal polynomial 0 target)) :
    target.isZero = true := by
  obtain ⟨coefficient, _, operator⟩ := Expression.primitive_polynomial_operator primitive target denominatorNonzero
    curveNonzero certificate exactDerivative
  have imageEq := image_eq_of_operator_identity preparation.polynomialDerivative_eq operator
  exact (small_image_zero curveNonzero positive preparation.polynomialDerivative_eq small imageEq).2

/-- The retained coefficient run returns its accumulated primitive, current remainder and cancellation count.

One successor unit either returns the same small numerator or computes the
monomial image, scalar ratio, scaled correction and next numerator once.
The completed predecessor run supplies the identical final caches. -/
@[expose] def run (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical) :
    Nat → CoefficientPolynomial → CoefficientPolynomial → CoefficientPolynomial × CoefficientPolynomial × Nat :=
  Nat.rec
    (fun current primitive => ⟨primitive, current, 0⟩)
    (fun _ recursive current primitive =>
      if current.degreeCount ≤ degree - 1 then ⟨primitive, current, 0⟩
      else
        let exponent := current.natDegree + 1 - degree
        let unit := monomial exponent
        let unitImage := image polynomial polynomialDerivative unit
        let ratio := current.leadingCoeff / (weight degree exponent * leading)
        let contribution := unit.scale ratio
        let correction := unitImage.scale ratio
        let next := current - correction
        let result := recursive next (primitive + contribution)
        ⟨result.1, result.2.1, result.2.2 + 1⟩)

/-- Zero fuel retains the actual original accumulator and current coefficient table. -/
theorem run_zero (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical)
    (current primitive : CoefficientPolynomial) :
    run polynomial polynomialDerivative degree leading 0 current primitive = ⟨primitive, current, 0⟩ := rfl

/-- One fuel unit preserves the original stopping guard and all once-computed cancellation caches. -/
theorem run_succ (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical)
    (fuel : Nat) (current primitive : CoefficientPolynomial) :
    run polynomial polynomialDerivative degree leading (fuel + 1) current primitive =
      if current.degreeCount ≤ degree - 1 then ⟨primitive, current, 0⟩
      else
        let exponent := current.natDegree + 1 - degree
        let unit := monomial exponent
        let unitImage := image polynomial polynomialDerivative unit
        let ratio := current.leadingCoeff / (weight degree exponent * leading)
        let contribution := unit.scale ratio
        let correction := unitImage.scale ratio
        let next := current - correction
        let result := run polynomial polynomialDerivative degree leading fuel next (primitive + contribution)
        ⟨result.1, result.2.1, result.2.2 + 1⟩ := rfl

/-- The remainder of a successor run is the current numerator on stopping, or the identical recursive remainder. -/
theorem run_succ_remainder (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat)
    (leading : Canonical) (fuel : Nat) (current primitive : CoefficientPolynomial) :
    (run polynomial polynomialDerivative degree leading (fuel + 1) current primitive).2.1 =
      if current.degreeCount ≤ degree - 1 then current
      else
        let exponent := current.natDegree + 1 - degree
        let unit := monomial exponent
        let ratio := current.leadingCoeff / (weight degree exponent * leading)
        (run polynomial polynomialDerivative degree leading fuel
          (current - (image polynomial polynomialDerivative unit).scale ratio)
          (primitive + unit.scale ratio)).2.1 := by
  rewrite [run_succ]
  split <;> rfl

/-- One actual image cancellation is the original leading-cancellation operation and strictly decreases the count. -/
theorem cancellation_decreases {polynomial polynomialDerivative current : CoefficientPolynomial}
    {degree : Nat} {leading : Canonical} (curve : LeadingTerm polynomial degree leading)
    (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (normalized : current.normalize = current) (large : ¬current.degreeCount ≤ degree - 1) :
    let exponent := current.natDegree + 1 - degree
    let ratio := current.leadingCoeff / (weight degree exponent * leading)
    (current - (image polynomial polynomialDerivative (monomial exponent)).scale ratio).degreeCount <
      current.degreeCount := by
  have nonzero : current.isZero = false := by
    cases zero : current.isZero with
    | false => rfl
    | true =>
        have zeroCount : current.degreeCount = 0 := by
          rewrite [degreeCount, normalize_eq_zero_of_isZero zero]
          rfl
        exact False.elim (large (by rewrite [zeroCount]; exact Nat.zero_le _))
  let exponent := current.natDegree + 1 - degree
  have count := natDegree_add_one_eq_degreeCount nonzero
  have degreeBound : degree ≤ current.natDegree + 1 := by omega0
  have exponentPositive : 0 < 2 * exponent + degree := by dsimp only [exponent]; omega0
  have equalDegree : exponent + degree - 1 = current.natDegree := by dsimp only [exponent]; omega0
  have operator := image_monomial_leading curve derivativeEq exponent exponentPositive
  have operatorDegree : (image polynomial polynomialDerivative (monomial exponent)).natDegree = current.natDegree :=
    operator.degree_eq.trans equalDegree
  have nextEq : current - (image polynomial polynomialDerivative (monomial exponent)).scale
      (current.leadingCoeff / (weight degree exponent * leading)) =
      cancelLead current (image polynomial polynomialDerivative (monomial exponent)) := by
    unfold cancelLead
    rewrite [operatorDegree, Nat.sub_self, shift_zero_exponent, normalize_scale, operator.coefficient_eq]
    rfl
  change (current - (image polynomial polynomialDerivative (monomial exponent)).scale
    (current.leadingCoeff / (weight degree exponent * leading))).degreeCount < _
  rewrite [nextEq]
  exact cancelLead_degreeCount_lt nonzero operator.nonzero normalized operator.normalized
    (by rewrite [operatorDegree]; exact Nat.le_refl _)

/-- The current numerator plus the accumulated derivative image is invariant throughout every finite run. -/
theorem run_identity (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical)
    (fuel : Nat) (current primitive : CoefficientPolynomial) (point : Canonical) :
    current.eval point + (image polynomial polynomialDerivative primitive).eval point =
      (run polynomial polynomialDerivative degree leading fuel current primitive).2.1.eval point +
        (image polynomial polynomialDerivative
          (run polynomial polynomialDerivative degree leading fuel current primitive).1).eval point := by
  induction fuel generalizing current primitive with
  | zero => rfl
  | succ fuel ih =>
      rewrite [run_succ]
      split
      · rfl
      · dsimp only
        let exponent := current.natDegree + 1 - degree
        let unit := monomial exponent
        let ratio := current.leadingCoeff / (weight degree exponent * leading)
        have later := ih (current - (image polynomial polynomialDerivative unit).scale ratio)
          (primitive + unit.scale ratio)
        calc
          _ = (current - (image polynomial polynomialDerivative unit).scale ratio).eval point +
              (image polynomial polynomialDerivative (primitive + unit.scale ratio)).eval point := by
                rewrite [eval_sub, eval_scale, image_add_eval, image_scale_eval]
                ring1
          _ = _ := later

/-- Every retained remainder is normalized when the original current numerator was normalized. -/
theorem run_normalized (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical)
    (fuel : Nat) (current primitive : CoefficientPolynomial) (normalized : current.normalize = current) :
    (run polynomial polynomialDerivative degree leading fuel current primitive).2.1.normalize =
      (run polynomial polynomialDerivative degree leading fuel current primitive).2.1 := by
  induction fuel generalizing current primitive with
  | zero => exact normalized
  | succ fuel ih =>
      rewrite [run_succ]
      split
      · exact normalized
      · dsimp only
        exact ih _ _ (normalize_sub _ _)

/-- The finite cancellation count never exceeds its displayed natural fuel. -/
theorem run_steps_le (polynomial polynomialDerivative : CoefficientPolynomial) (degree : Nat) (leading : Canonical)
    (fuel : Nat) (current primitive : CoefficientPolynomial) :
    (run polynomial polynomialDerivative degree leading fuel current primitive).2.2 ≤ fuel := by
  induction fuel generalizing current primitive with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rewrite [run_succ]
      split
      · exact Nat.zero_le _
      · dsimp only
        exact Nat.succ_le_succ (ih _ _)

/-- Coefficient-count-sized fuel reaches the strict numerator degree bound, including zero and constant remainders. -/
theorem run_small {polynomial polynomialDerivative : CoefficientPolynomial} {degree : Nat} {leading : Canonical}
    (curve : LeadingTerm polynomial degree leading) (derivativeEq : polynomialDerivative = GCD.derivative polynomial)
    (fuel : Nat) (current primitive : CoefficientPolynomial) (normalized : current.normalize = current)
    (sufficient : current.degreeCount ≤ fuel) :
    (run polynomial polynomialDerivative degree leading fuel current primitive).2.1.degreeCount ≤ degree - 1 := by
  induction fuel generalizing current primitive with
  | zero =>
      exact sufficient.trans (Nat.zero_le _)
  | succ fuel ih =>
      rewrite [run_succ_remainder]
      split
      · assumption
      · rename_i large
        dsimp only
        apply ih _ _ (normalize_sub _ _)
        have decrease := cancellation_decreases curve derivativeEq normalized large
        exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le decrease sufficient)

/-- The complete ownership, derivative-cache, coefficient and degree invariants of a numerator reduction. -/
@[expose] def ReducedIdentity {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial)
    (degree : Nat) (leading : Canonical) (data : CoefficientPolynomial × Nat)
    (primitive : OddPowerDifferential polynomial) (specification : Derivative.Specification polynomial primitive)
    (remainder : OddPowerDifferential polynomial) : Prop :=
  input.denominatorPairs = 0 ∧ degree = polynomial.natDegree ∧ leading = polynomial.leadingCoeff ∧
    primitive = OddPowerDifferential.ofCoefficients polynomial (data.1 * polynomial) 0 input.scale ∧
    specification.polynomialDerivative = preparation.polynomialDerivative ∧
    remainder.denominatorPairs = 0 ∧ remainder.scale = input.scale ∧
    remainder.numerator.normalize = remainder.numerator ∧
    remainder.numerator.coeffs.length ≤ degree - 1 ∧ data.2 ≤ input.numerator.degreeCount ∧
    ∀ point : Canonical,
      input.numerator.eval point = remainder.numerator.eval point +
        (GCD.derivative data.1).eval point * polynomial.eval point +
          (1 / 2 : Canonical) * data.1.eval point * preparation.polynomialDerivative.eval point

/-- Retained original sheet primitive, derivative specification and strictly reduced polynomial numerator.

The leading coefficient and degree are cached once, while the original
preparation supplies its already computed curve derivative. The distinct
invariant is polynomial degree lowering at denominator `Y`; the existing
successor-pair Step and its denominator-lowering identity are unchanged. -/
@[expose] def Reduced {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial) : Type :=
  (degree : Nat) × (leading : Canonical) × (data : CoefficientPolynomial × Nat) ×
    (primitive : OddPowerDifferential polynomial) ×
      (specification : Derivative.Specification polynomial primitive) ×
        {remainder : OddPowerDifferential polynomial //
          ReducedIdentity preparation input degree leading data primitive specification remainder}

namespace Reduced

variable {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
  {preparation : Preparation polynomial certificate} {input : OddPowerDifferential polynomial}

/-- The original curve's retained natural degree. -/
@[expose] def degree (reduced : Reduced preparation input) : Nat := reduced.1
/-- The original curve's retained leading coefficient. -/
@[expose] def leading (reduced : Reduced preparation input) : Canonical := reduced.2.1
/-- The actual polynomial multiplying the original selected sheet in the exact primitive. -/
@[expose] def polynomialPrimitive (reduced : Reduced preparation input) : CoefficientPolynomial := reduced.2.2.1.1
/-- The actual number of leading cancellations performed. -/
@[expose] def steps (reduced : Reduced preparation input) : Nat := reduced.2.2.1.2
/-- The original odd representation `BF/Y` of the retained exact sheet primitive. -/
@[expose] def primitive (reduced : Reduced preparation input) : OddPowerDifferential polynomial := reduced.2.2.2.1
/-- The complete original derivative specification of that exact primitive. -/
@[expose] def specification (reduced : Reduced preparation input) :
    Derivative.Specification polynomial reduced.primitive := reduced.2.2.2.2.1
/-- The original zero-pair differential retaining the final numerator. -/
@[expose] def remainder (reduced : Reduced preparation input) : OddPowerDifferential polynomial :=
  reduced.2.2.2.2.2.val

/-- The complete retained numerator-reduction invariants. -/
theorem identity (reduced : Reduced preparation input) :
    ReducedIdentity preparation input reduced.degree reduced.leading ⟨reduced.polynomialPrimitive, reduced.steps⟩
      reduced.primitive reduced.specification reduced.remainder := reduced.2.2.2.2.2.property

/-- The original input already has denominator `Y`. -/
theorem input_pairs (reduced : Reduced preparation input) : input.denominatorPairs = 0 := reduced.identity.1
/-- The cached degree is the original complete natural-degree readback. -/
theorem degree_eq (reduced : Reduced preparation input) : reduced.degree = polynomial.natDegree :=
  reduced.identity.2.1
/-- The cached leading coefficient is the original complete readback. -/
theorem leading_eq (reduced : Reduced preparation input) : reduced.leading = polynomial.leadingCoeff :=
  reduced.identity.2.2.1
/-- The retained primitive uses the actual computed polynomial times the original curve. -/
theorem primitive_eq (reduced : Reduced preparation input) :
    reduced.primitive = OddPowerDifferential.ofCoefficients polynomial
      (reduced.polynomialPrimitive * polynomial) 0 input.scale := reduced.identity.2.2.2.1
/-- The derivative specification consumes the identical preparation cache. -/
theorem polynomialDerivative_eq (reduced : Reduced preparation input) :
    reduced.specification.polynomialDerivative = preparation.polynomialDerivative := reduced.identity.2.2.2.2.1
/-- The remainder has the same denominator `Y`. -/
theorem remainder_pairs (reduced : Reduced preparation input) : reduced.remainder.denominatorPairs = 0 :=
  reduced.identity.2.2.2.2.2.1
/-- The final differential retains the original scalar. -/
theorem remainder_scale (reduced : Reduced preparation input) : reduced.remainder.scale = input.scale :=
  reduced.identity.2.2.2.2.2.2.1
/-- The final coefficient list is already normalized. -/
theorem remainder_normalized (reduced : Reduced preparation input) :
    reduced.remainder.numerator.normalize = reduced.remainder.numerator := reduced.identity.2.2.2.2.2.2.2.1
/-- The final numerator has at most `deg(F)-1` retained coefficients. -/
theorem remainder_small (reduced : Reduced preparation input) :
    reduced.remainder.numerator.coeffs.length ≤ polynomial.natDegree - 1 := by
  have bound := reduced.identity.2.2.2.2.2.2.2.2.1
  rewrite [reduced.degree_eq] at bound
  exact bound
/-- The cancellation count is bounded by the original normalized numerator count. -/
theorem steps_le (reduced : Reduced preparation input) : reduced.steps ≤ input.numerator.degreeCount :=
  reduced.identity.2.2.2.2.2.2.2.2.2.1
/-- The original numerator is the reduced numerator plus `T_F(B)` at every finite coefficient probe. -/
theorem numerator_eq (reduced : Reduced preparation input) (point : Canonical) :
    input.numerator.eval point = reduced.remainder.numerator.eval point +
      (GCD.derivative reduced.polynomialPrimitive).eval point * polynomial.eval point +
        (1 / 2 : Canonical) * reduced.polynomialPrimitive.eval point * preparation.polynomialDerivative.eval point :=
  reduced.identity.2.2.2.2.2.2.2.2.2.2 point

/-- Two reductions of the same original input retain the same complete normalized remainder numerator.

Their actual primitive difference has image equal to the difference of the
retained small remainders. The general nonzero-image degree rule excludes this
relation, and finite normalized coefficient comparison identifies the tables.
-/
theorem remainder_numerator_eq (left right : Reduced preparation input)
    (positive : 0 < polynomial.natDegree) : left.remainder.numerator = right.remainder.numerator := by
  let difference := left.remainder.numerator - right.remainder.numerator
  let primitive := right.polynomialPrimitive - left.polynomialPrimitive
  have small : difference.degreeCount ≤ polynomial.natDegree - 1 := by
    apply (degreeCount_sub_le_of_normalized left.remainder_normalized).trans
    exact Data.Nat.Order.max_le
      ((degreeCount_le_coeffs_length _).trans left.remainder_small)
      ((degreeCount_le_coeffs_length _).trans right.remainder_small)
  have imageEq : difference.normalize = image polynomial preparation.polynomialDerivative primitive := by
    apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq (normalize_normalize _) (normalize_add _ _)
    intro point
    have leftImage : input.numerator.eval point = left.remainder.numerator.eval point +
        (image polynomial preparation.polynomialDerivative left.polynomialPrimitive).eval point := by
      rewrite [left.numerator_eq point]
      simp only [image, eval_add, eval_mul, eval_scale]
      ring1
    have rightImage : input.numerator.eval point = right.remainder.numerator.eval point +
        (image polynomial preparation.polynomialDerivative right.polynomialPrimitive).eval point := by
      rewrite [right.numerator_eq point]
      simp only [image, eval_add, eval_mul, eval_scale]
      ring1
    have same := leftImage.symm.trans rightImage
    rewrite [eval_normalize]
    change (left.remainder.numerator - right.remainder.numerator).eval point =
      (image polynomial preparation.polynomialDerivative
        (right.polynomialPrimitive - left.polynomialPrimitive)).eval point
    rewrite [eval_sub, image_sub_eval]
    calc
      _ = (left.remainder.numerator.eval point +
          (image polynomial preparation.polynomialDerivative left.polynomialPrimitive).eval point) -
        (right.remainder.numerator.eval point +
          (image polynomial preparation.polynomialDerivative right.polynomialPrimitive).eval point) +
        (image polynomial preparation.polynomialDerivative right.polynomialPrimitive).eval point -
        (image polynomial preparation.polynomialDerivative left.polynomialPrimitive).eval point := by ring1
      _ = _ := by rewrite [same]; ring1
  have zero := (small_image_zero (Squarefree.Basic.polynomial_nonzero certificate) positive
    preparation.polynomialDerivative_eq small imageEq).2
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq
    left.remainder_normalized right.remainder_normalized
  intro point
  have reading := eval_eq_zero_of_isZero zero point
  change (left.remainder.numerator - right.remainder.numerator).eval point = 0 at reading
  rewrite [eval_sub] at reading
  calc
    _ = (left.remainder.numerator.eval point - right.remainder.numerator.eval point) +
      right.remainder.numerator.eval point := by ring1
    _ = _ := by rewrite [reading, zero_add]; rfl

/-- Two reductions of the same original input retain the same complete remainder differential cache.

The normalized numerator identity, original pair count and original scalar
identify the same coefficient specification. The literal original nominal
records then agree, including their stored coefficient expressions.
-/
theorem remainder_eq (left right : Reduced preparation input)
    (positive : 0 < polynomial.natDegree) : left.remainder = right.remainder := by
  have numeratorSame := left.remainder_numerator_eq right positive
  have pairsSame := left.remainder_pairs.trans right.remainder_pairs.symm
  have scaleSame := left.remainder_scale.trans right.remainder_scale.symm
  have coefficientSame : left.remainder.coefficient = right.remainder.coefficient := by
    rewrite [left.remainder.coefficient_eq, right.remainder.coefficient_eq,
      numeratorSame, pairsSame, scaleSame]
    rfl
  cases leftValue : left.remainder with
  | mk leftNumerator leftPairs leftScale leftCoefficient leftIdentity =>
      cases rightValue : right.remainder with
      | mk rightNumerator rightPairs rightScale rightCoefficient rightIdentity =>
          rewrite [leftValue, rightValue] at numeratorSame pairsSame scaleSame coefficientSame
          cases numeratorSame
          cases pairsSame
          cases scaleSame
          cases coefficientSame
          rfl

/-- The original cleared input is the reduced numerator plus its actual retained spatial derivative.

The original derivative product rule for `BF` consumes the identical curve
cache. Clearing denominators multiplies by `F`; it does not cancel `F` or
identify its zero locus with an operational pole statement. -/
theorem coefficient_eq (reduced : Reduced preparation input) (point : Canonical) :
    (input.scale * input.numerator.eval point) * polynomial.eval point =
      (reduced.remainder.scale * reduced.remainder.numerator.eval point) * polynomial.eval point +
        reduced.specification.differential.scale * reduced.specification.differential.numerator.eval point := by
  have primitiveNumerator : reduced.primitive.numerator = reduced.polynomialPrimitive * polynomial :=
    congrArg OddPowerDifferential.numerator reduced.primitive_eq
  have primitiveScale : reduced.primitive.scale = input.scale := by
    have same := congrArg OddPowerDifferential.scale reduced.primitive_eq
    exact same
  have primitivePairs : reduced.primitive.denominatorPairs = 0 :=
    congrArg OddPowerDifferential.denominatorPairs reduced.primitive_eq
  have primitiveExponent : Derivative.exponentCoefficient reduced.primitive = 1 := by
    change Derivative.oddCoefficient reduced.primitive.denominatorPairs = 1
    rewrite [primitivePairs]
    rfl
  have derivative := reduced.specification.coefficient_eq point
  rewrite [reduced.specification.first_eq, reduced.specification.last_eq,
    reduced.specification.numeratorDerivative_eq, primitiveNumerator, primitiveScale, primitiveExponent,
    reduced.polynomialDerivative_eq, preparation.polynomialDerivative_eq] at derivative
  change _ = input.scale * (GCD.derivative (reduced.polynomialPrimitive * polynomial)).eval point *
      polynomial.eval point - (input.scale * 1 / 2) *
        ((reduced.polynomialPrimitive * polynomial) * GCD.derivative polynomial).eval point at derivative
  rewrite [GCD.derivative, Dense.Derivative.eval_derivative_mul, eval_mul, eval_mul] at derivative
  have half : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
  have complement : (1 : Canonical) - (2 : Canonical)⁻¹ = (2 : Canonical)⁻¹ := by
    calc
      _ = 2 * (2 : Canonical)⁻¹ - (2 : Canonical)⁻¹ :=
        congrArg (fun value : Canonical => value - (2 : Canonical)⁻¹) half.symm
      _ = _ := by ring1
  have derivativeImage : reduced.specification.differential.scale *
      reduced.specification.differential.numerator.eval point =
      input.scale * ((GCD.derivative reduced.polynomialPrimitive).eval point * polynomial.eval point +
        (1 / 2 : Canonical) * reduced.polynomialPrimitive.eval point *
          preparation.polynomialDerivative.eval point) * polynomial.eval point := by
    rewrite [derivative, preparation.polynomialDerivative_eq,
      ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    dsimp only [GCD.derivative]
    calc
      _ = input.scale * (Dense.Derivative.derivative reduced.polynomialPrimitive).eval point *
          polynomial.eval point * polynomial.eval point +
            input.scale * reduced.polynomialPrimitive.eval point *
              (Dense.Derivative.derivative polynomial).eval point * polynomial.eval point *
                (1 - (2 : Canonical)⁻¹) := by ring1
      _ = _ := by rewrite [complement]; ring1
  rewrite [reduced.remainder_scale, derivativeImage]
  have original := reduced.numerator_eq point
  calc
    _ = input.scale * (reduced.remainder.numerator.eval point +
        (GCD.derivative reduced.polynomialPrimitive).eval point * polynomial.eval point +
          (1 / 2 : Canonical) * reduced.polynomialPrimitive.eval point * preparation.polynomialDerivative.eval point) *
          polynomial.eval point :=
            congrArg (fun value : Canonical => input.scale * value * polynomial.eval point) original
    _ = _ := by ring1

/-- The original input, remainder and retained derivative caches satisfy exact cross-denominator equality. -/
theorem coefficient_equal (reduced : Reduced preparation input) :
    input.coefficient.Equal (reduced.remainder.coefficient.add reduced.specification.differential.coefficient) := by
  have primitivePairs : reduced.primitive.denominatorPairs = 0 := by rewrite [reduced.primitive_eq]; rfl
  have derivativePairs : reduced.specification.differential.denominatorPairs = 1 := by
    rewrite [reduced.specification.differential_eq, primitivePairs]
    rfl
  rewrite [input.coefficient_eq, reduced.remainder.coefficient_eq, reduced.specification.differential.coefficient_eq]
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.add,
      Pair.scale, Pair.add_re, eval_mul, eval_add, eval_zero]
    ring1
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.add,
      Pair.scale, Pair.add_im, eval_mul, eval_add, eval_scale, Dense.Power.eval_power]
    rewrite [reduced.input_pairs, reduced.remainder_pairs, derivativePairs]
    simp only [pow_succ]
    have cleared := reduced.coefficient_eq point
    calc
      _ = ((input.scale * input.numerator.eval point) * polynomial.eval point) *
          (polynomial.eval point * polynomial.eval point) := by ring1
      _ = ((reduced.remainder.scale * reduced.remainder.numerator.eval point) * polynomial.eval point +
          reduced.specification.differential.scale * reduced.specification.differential.numerator.eval point) *
          (polynomial.eval point * polynomial.eval point) := congrArg (fun value : Canonical =>
            value * (polynomial.eval point * polynomial.eval point)) cleared
      _ = _ := by ring1

/-- The primitive's actual original coefficient cache equals the polynomial-scaled formal sheet generator. -/
theorem primitive_coefficient_equal (reduced : Reduced preparation input) :
    reduced.primitive.coefficient.Equal
      ((Expression.scalar (radicand := polynomial) (reduced.polynomialPrimitive.scale input.scale)).mul
        Expression.generator) := by
  rewrite [reduced.primitive_eq]
  change (Basic.coefficientSpec polynomial (reduced.polynomialPrimitive * polynomial) 0 input.scale).Equal _
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.scalar, Expression.generator,
      Expression.mul, Pair.mul_re, Pair.scalar, eval_mul, eval_sub, eval_scale, eval_zero, eval_constant,
      Dense.Power.eval_power, -eq_self, -iff_self]
    ring1
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.scalar, Expression.generator,
      Expression.mul, Pair.mul_im, Pair.scalar, eval_mul, eval_add, eval_scale, eval_zero, eval_constant,
      Dense.Power.eval_power, -eq_self, -iff_self]
    ring1

/-- The actual retained `BF/Y` primitive agrees with `B*Y` at the same original coordinate and admitted sheet. -/
def primitive_agrees (reduced : Reduced preparation input) (point : Canonical) (sheet : CoherentNamed)
    (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    NamedEquivalent (reduced.primitive.value point sheet apart).name
      (CoherentNamed.mul (Coherence.exact (input.scale * reduced.polynomialPrimitive.eval point)) sheet).name := by
  let identity := PowerIdentity.ofSquare square
  let source := reduced.primitive.interpret point sheet identity apart
  let scalar : Expression polynomial := Expression.scalar (reduced.polynomialPrimitive.scale input.scale)
  let generator : Expression polynomial := Expression.generator
  have scalarDefined := Expression.defined_scalar (radicand := polynomial)
    (reduced.polynomialPrimitive.scale input.scale) point
  have generatorDefined := Expression.defined_generator (radicand := polynomial) point
  have targetDefined := Expression.defined_mul scalar generator point scalarDefined generatorDefined
  have equal := reduced.primitive_coefficient_equal.denote_equivalent point sheet source.defined targetDefined
  have multiplication := Expression.denote_mul scalar generator point sheet identity scalarDefined generatorDefined
  have scalarComparison := Expression.denote_scalar (radicand := polynomial)
    (reduced.polynomialPrimitive.scale input.scale) point sheet
  rewrite [eval_scale] at scalarComparison
  have generatorComparison := Expression.denote_generator (radicand := polynomial) point sheet
  have arithmetic := Product.Congruence.coherentMul_respects (scalar.denote point sheet)
    (Coherence.exact (input.scale * reduced.polynomialPrimitive.eval point)) (generator.denote point sheet) sheet
    scalarComparison generatorComparison
  have interpreted : NamedEquivalent source.channel.name
      (CoherentNamed.mul (scalar.denote point sheet) (generator.denote point sheet)).name := by
    rewrite [source.channel_readback]
    exact equal.trans multiplication.symm
  exact (reduced.primitive.reciprocal_power_equivalent point sheet identity apart).trans
    (interpreted.trans arithmetic)

/-- The original input agrees with the reduced channel plus the retained exact derivative on the same admitted sheet. -/
def agrees (reduced : Reduced preparation input) (point : Canonical) (sheet : CoherentNamed)
    (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    NamedEquivalent (input.value point sheet apart).name
      (CoherentNamed.add (reduced.remainder.value point sheet apart)
        (reduced.specification.differential.value point sheet apart)).name :=
  OddPowerDifferential.agrees_add input reduced.remainder reduced.specification.differential
    reduced.coefficient_equal point sheet apart square

end Reduced

/-- Reduce the original zero-pair numerator with coefficient-count-sized natural fuel.

The original preparation supplies its actual curve derivative. The original
curve is normalized once, its degree and leading coefficient are retained
once, and every recursive call receives those identical caches. The original
spatial-derivative builder receives the same curve derivative when constructing
the actual primitive `BF/Y`; the original input and final differential owners
are retained under their original curve index. -/
@[expose] def build {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial)
    (inputPairs : input.denominatorPairs = 0) : Reduced preparation input := by
  let curve := polynomial.normalize
  let degree := curve.coeffs.length - 1
  let leading := curve.coeffs.headD 0
  let numerator := input.numerator.normalize
  let budget := numerator.coeffs.length
  let result := run curve preparation.polynomialDerivative degree leading budget numerator 0
  let primitive := OddPowerDifferential.ofCoefficients polynomial (result.1 * polynomial) 0 input.scale
  let specification := Derivative.Specification.build polynomial primitive
    preparation.polynomialDerivative preparation.polynomialDerivative_eq
  let remainder := OddPowerDifferential.ofCoefficients polynomial result.2.1 0 input.scale
  have curveLeading : LeadingTerm curve degree leading :=
    LeadingTerm.normalizeSelf (Squarefree.Basic.polynomial_nonzero certificate)
  have curveDerivative : preparation.polynomialDerivative = GCD.derivative curve := by
    rewrite [preparation.polynomialDerivative_eq]
    change Dense.Derivative.derivative polynomial =
      Dense.Derivative.derivative polynomial.normalize
    exact (Dense.Derivative.derivative_normalize polynomial).symm
  have remainderNormalized := run_normalized curve preparation.polynomialDerivative degree leading
    budget numerator 0 (normalize_normalize _)
  have remainderBound := run_small curveLeading curveDerivative input.numerator.degreeCount
    input.numerator.normalize 0 (normalize_normalize _)
    (by rewrite [degreeCount_normalize]; exact Nat.le_refl _)
  have stepBound := run_steps_le curve preparation.polynomialDerivative degree leading
    budget numerator 0
  refine ⟨degree, leading, ⟨result.1, result.2.2⟩, primitive, specification,
    ⟨remainder, inputPairs, rfl, rfl, rfl, rfl, rfl, rfl, remainderNormalized, ?_, stepBound, ?_⟩⟩
  · change result.2.1.coeffs.length ≤ degree - 1
    have countEq : result.2.1.degreeCount = result.2.1.coeffs.length := by
      rewrite [degreeCount, remainderNormalized]
      rfl
    change result.2.1.degreeCount ≤ degree - 1 at remainderBound
    rewrite [countEq] at remainderBound
    exact remainderBound
  · intro point
    have identity := run_identity curve preparation.polynomialDerivative degree leading
      budget numerator 0 point
    rewrite [eval_normalize, image_zero_eval, Data.Gaussian.Basic.add_zero] at identity
    change input.numerator.eval point = result.2.1.eval point +
      (GCD.derivative result.1).eval point * polynomial.eval point +
        (1 / 2 : Canonical) * result.1.eval point * preparation.polynomialDerivative.eval point
    calc
      _ = result.2.1.eval point + (image curve preparation.polynomialDerivative result.1).eval point := identity
      _ = _ := by
        unfold image
        rewrite [eval_add, eval_mul, eval_scale, eval_mul, eval_normalize]
        ring1

/-- Lower the retained numerator of an already completed original denominator chain.

The complete chain remains the source owner of the new input. Its actual
zero-pair remainder is passed directly to the same numerator builder, which
consumes the identical supplied preparation without replaying the chain. -/
@[expose] def ofChain {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    {input : OddPowerDifferential polynomial} {pairs : Nat}
    (preparation : Preparation polynomial certificate) (chain : Chain polynomial input pairs) :
    Reduced preparation chain.remainder := build preparation chain.remainder chain.remainder_pairs

/-- The complete two-stage reduction preserves the original coefficient after clearing one extra curve factor. -/
theorem ofChain_coefficient_eq {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    {input : OddPowerDifferential polynomial} {pairs : Nat} (preparation : Preparation polynomial certificate)
    (chain : Chain polynomial input pairs) (point : Canonical) :
    (input.scale * input.numerator.eval point) * polynomial.eval point =
      ((ofChain preparation chain).remainder.scale * (ofChain preparation chain).remainder.numerator.eval point) *
          polynomial.eval point ^ (pairs + 1) +
        ((ofChain preparation chain).specification.differential.scale *
          (ofChain preparation chain).specification.differential.numerator.eval point) * polynomial.eval point ^ pairs +
        chain.exactCoefficient point * polynomial.eval point := by
  have denominator := chain.coefficient_eq point
  have numerator := (ofChain preparation chain).coefficient_eq point
  rewrite [pow_succ]
  calc
    _ = ((chain.remainder.scale * chain.remainder.numerator.eval point) * polynomial.eval point ^ pairs +
        chain.exactCoefficient point) * polynomial.eval point :=
      congrArg (fun value : Canonical => value * polynomial.eval point) denominator
    _ = ((chain.remainder.scale * chain.remainder.numerator.eval point) * polynomial.eval point) *
        polynomial.eval point ^ pairs + chain.exactCoefficient point * polynomial.eval point := by ring1
    _ = (((ofChain preparation chain).remainder.scale *
        (ofChain preparation chain).remainder.numerator.eval point) * polynomial.eval point +
          (ofChain preparation chain).specification.differential.scale *
            (ofChain preparation chain).specification.differential.numerator.eval point) *
              polynomial.eval point ^ pairs + chain.exactCoefficient point * polynomial.eval point :=
      congrArg (fun value : Canonical => value * polynomial.eval point ^ pairs +
        chain.exactCoefficient point * polynomial.eval point) numerator
    _ = _ := by ring1

/-- A built reduction passes the identical preparation derivative to its original spatial-derivative specification. -/
theorem build_polynomialDerivative {polynomial : CoefficientPolynomial}
    {certificate : SquarefreeCertificate polynomial} (preparation : Preparation polynomial certificate)
    (input : OddPowerDifferential polynomial) (inputPairs : input.denominatorPairs = 0) :
    (build preparation input inputPairs).specification.polynomialDerivative = preparation.polynomialDerivative := rfl

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction.Numerator

end
