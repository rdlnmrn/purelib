module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Coprime.Power
import Purelib.Polynomial.Dense.Gaussian.Derivative.Degree
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Factors
import Purelib.Polynomial.Dense.Gaussian.Multiplication
public import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Power
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-!
# Polynomial coordinates of admitted rational quadratic primitives

The original expression retains its displayed denominator and its coordinate
admission guard. Finite product cancellation and the original squarefree
multiplicity basis rule out every positive-degree denominator factor in the
generator coordinate of a primitive of `R dx/Y`. No polynomial-primitive
assumption, irreducible factor selection or root enumeration is used.
-/

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Polynomial.Dense.Gaussian.Coprime

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Factorization.Identity (ProductIdentity)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Algebra.Field (ExplicitField)

variable {radicand : Coefficients}

/-- The original derivative numerator equals twice the target numerator times the source denominator square.

This finite zero-coefficient predicate records only the cleared generator
coordinate. It does not admit a quotient: the original nonzero-denominator
certificate is required by elimination, and each readback retains `Defined`.
-/
public abbrev PrimitiveIdentity (value : Expression radicand) (numerator : Coefficients) : Prop :=
  ((numerator * (value.denominator * value.denominator)).scale 2 -
    value.derivative.numerator.im).isZero = true

/-- Read the exact cleared derivative identity at one supplied Gaussian coordinate. -/
public theorem PrimitiveIdentity.eval {value : Expression radicand} {numerator : Coefficients}
    (identity : value.PrimitiveIdentity numerator) (point : Canonical) :
    2 * numerator.eval point * value.denominator.eval point * value.denominator.eval point =
      2 * radicand.eval point *
        ((Dense.Derivative.derivative value.numerator.im).eval point * value.denominator.eval point -
          value.numerator.im.eval point * (Dense.Derivative.derivative value.denominator).eval point) +
        (Dense.Derivative.derivative radicand).eval point *
          value.numerator.im.eval point * value.denominator.eval point := by
  have zero := DensePolynomial.eval_eq_zero_of_isZero identity point
  change ((numerator * (value.denominator * value.denominator)).scale 2 -
    (radicand.scale 2 *
      (Dense.Derivative.derivative value.numerator.im * value.denominator -
        value.numerator.im * Dense.Derivative.derivative value.denominator) +
      Dense.Derivative.derivative radicand * value.numerator.im * value.denominator)).eval point = 0 at zero
  simp only [DensePolynomial.eval_sub, DensePolynomial.eval_add,
    DensePolynomial.eval_mul, DensePolynomial.eval_scale] at zero
  calc
    _ = (2 * (numerator.eval point * (value.denominator.eval point * value.denominator.eval point)) -
        (2 * radicand.eval point *
          ((Dense.Derivative.derivative value.numerator.im).eval point * value.denominator.eval point -
            value.numerator.im.eval point * (Dense.Derivative.derivative value.denominator).eval point) +
          (Dense.Derivative.derivative radicand).eval point *
            value.numerator.im.eval point * value.denominator.eval point)) +
      (2 * radicand.eval point *
        ((Dense.Derivative.derivative value.numerator.im).eval point * value.denominator.eval point -
          value.numerator.im.eval point * (Dense.Derivative.derivative value.denominator).eval point) +
        (Dense.Derivative.derivative radicand).eval point *
          value.numerator.im.eval point * value.denominator.eval point) := by ring1
    _ = _ := by rewrite [zero, zero_add]; rfl

/-- A derivative cross-identity gives its finite cleared numerator identity when the radicand is nonzero.

Cancellation uses the original nonzero polynomial on the finite probe grid,
rather than scalar division at all coordinates. Quotient admission remains a
separate input to the resulting denominator theorem.
-/
public theorem primitiveIdentity_of_derivative_equal (value : Expression radicand)
    (numerator : Coefficients) (radicandNonzero : radicand.isZero = false)
    (equal : value.derivative.Equal (oddReciprocal radicand 0 numerator)) :
    value.PrimitiveIdentity numerator := by
  have cancelled := Multiplication.cancel_left_eval
    (factor := radicand)
    (left := (numerator * (value.denominator * value.denominator)).scale 2)
    (right := value.derivative.numerator.im) radicandNonzero (by
      intro point
      have cross := equal.imaginary_cross point
      change value.derivative.numerator.im.eval point * (Dense.Power.power radicand 1).eval point =
        numerator.eval point * value.derivative.denominator.eval point at cross
      change value.derivative.numerator.im.eval point * (Dense.Power.power radicand 1).eval point =
        numerator.eval point * (radicand.scale 2 *
          (value.denominator * value.denominator)).eval point at cross
      simp only [Dense.Power.eval_power, pow_one, DensePolynomial.eval_mul, DensePolynomial.eval_scale] at cross
      simp only [DensePolynomial.eval_mul, DensePolynomial.eval_scale]
      calc
        radicand.eval point * (2 * (numerator.eval point *
            (value.denominator.eval point * value.denominator.eval point))) =
          numerator.eval point * (2 * radicand.eval point *
            (value.denominator.eval point * value.denominator.eval point)) := by ring1
        _ = value.derivative.numerator.im.eval point * radicand.eval point := cross.symm
        _ = _ := by ring1)
  apply Extensionality.isZero_of_eval_eq_zero
  intro point
  rewrite [DensePolynomial.eval_sub, cancelled point]
  exact sub_self _

/-- The all-input scalar form of the original primitive's cleared generator equation. -/
private abbrev Cleared (f b c r : Coefficients) : Prop :=
  ∀ point : Canonical,
    2 * r.eval point * c.eval point * c.eval point =
      2 * f.eval point *
        ((Dense.Derivative.derivative b).eval point * c.eval point -
          b.eval point * (Dense.Derivative.derivative c).eval point) +
        (Dense.Derivative.derivative f).eval point * b.eval point * c.eval point

/-- The ordinary positive multiplicity weight is nonzero in the actual Gaussian coefficient field. -/
private theorem even_weight_nonzero (index : Nat) : (2 * ((index : Canonical) + 1)) ≠ 0 := by
  have positive := Gaussian.Derivative.Degree.gaussian_natCast_ne_zero (Nat.zero_lt_succ index)
  rewrite [Nat.cast_succ] at positive
  exact ExplicitField.mul_ne_zero (by decide : (2 : Canonical) ≠ 0) positive

/-- The ramified positive multiplicity weight is an explicit positive odd natural cast. -/
private theorem odd_weight_nonzero (index : Nat) : (2 * (index : Canonical) + 1) ≠ 0 := by
  have positive := Gaussian.Derivative.Degree.gaussian_natCast_ne_zero
    (Nat.zero_lt_succ (2 * index))
  have castIdentity : ((2 * index + 1 : Nat) : Canonical) = 2 * (index : Canonical) + 1 := by
    rewrite [Purelib.Algebra.NatCast.add, Purelib.Algebra.NatCast.mul]
    rfl
  rewrite [castIdentity] at positive
  exact positive

/-- One original focused denominator factor is coprime to the reduced numerator. -/
private def numeratorCoprime
    {b c h tail : Coefficients} (coprime : CoprimeCertificate b c)
    (nonzero : h.isZero = false) (factorization : ProductIdentity c h tail) :
    CoprimeCertificate h b :=
  Coprime.Factors.coprimeLeftFactor
    (Operations.CoprimeCertificate.symm coprime) nonzero factorization

/-- The five actual coprimality identities rule out a positive-degree divisor of their weighted product. -/
private theorem weighted_product_obstruction
    {h f b u : Coefficients} (weight : Canonical) (weightNonzero : weight ≠ 0)
    (hNonzero : h.isZero = false) (hPositive : 0 < h.natDegree)
    (squarefree : SquarefreeCertificate h) (fCoprime : CoprimeCertificate h f)
    (bCoprime : CoprimeCertificate h b) (uCoprime : CoprimeCertificate h u)
    (cofactor : Coefficients)
    (factorization : ProductIdentity
      ((((DensePolynomial.constant weight) * f) * b) * GCD.derivative h * u) h cofactor) : False := by
  let weighted := Operations.CoprimeCertificate.mulRight hNonzero
    (Operations.CoprimeCertificate.mulRight hNonzero
      (Operations.CoprimeCertificate.mulRight hNonzero
        (Operations.CoprimeCertificate.mulRight hNonzero
          (Operations.CoprimeCertificate.constantRightOfNe hNonzero weight weightNonzero)
          fCoprime)
        bCoprime)
      squarefree)
    uCoprime
  have degreeZero := Coprime.Factors.natDegree_eq_zero_of_divides weighted hNonzero factorization
  rewrite [degreeZero] at hPositive
  exact Nat.lt_irrefl 0 hPositive

/-- A squarefree denominator factor coprime to the radicand cannot occur with positive multiplicity. -/
private theorem ordinary_obstruction
    {f b c r h u : Coefficients} (index : Nat)
    (identity : Cleared f b c r) (hNonzero : h.isZero = false)
    (hPositive : 0 < h.natDegree) (squarefree : SquarefreeCertificate h)
    (fCoprime : CoprimeCertificate h f) (bCoprime : CoprimeCertificate h b)
    (uCoprime : CoprimeCertificate h u)
    (factorization : ProductIdentity c (Gaussian.Power.polynomialPower h (index + 1)) u) : False := by
  let cofactor :=
    (f * (Dense.Derivative.derivative b * u - b * Dense.Derivative.derivative u)).scale 2 +
      Dense.Derivative.derivative f * b * u -
      (r * Gaussian.Power.polynomialPower h (index + 1) * u * u).scale 2
  let weighted :=
    (((DensePolynomial.constant (2 * ((index : Canonical) + 1))) * f) * b) * GCD.derivative h * u
  have cancelled : ∀ point : Canonical, weighted.eval point = (h * cofactor).eval point := by
    apply Multiplication.cancel_left_eval (factor := Gaussian.Power.polynomialPower h index)
      (Gaussian.Power.polynomialPower_nonzero hNonzero index)
    intro point
    have original := identity point
    have source := Factorization.Identity.eval_factorization factorization point
    have slope := Factorization.Identity.eval_derivative_factorization factorization point
    change (Dense.Derivative.derivative c).eval point =
      (Dense.Derivative.derivative (Gaussian.Power.polynomialPower h (index + 1) * u)).eval point at slope
    rewrite [Dense.Derivative.eval_derivative_mul, Gaussian.Power.eval_polynomialPower,
      Gaussian.Power.eval_derivative_polynomialPower_succ] at slope
    simp only [source, Gaussian.Power.eval_polynomialPower, slope] at original
    dsimp only [weighted, cofactor]
    simp only [DensePolynomial.eval_mul, DensePolynomial.eval_constant, DensePolynomial.eval_sub,
      DensePolynomial.eval_add, DensePolynomial.eval_scale, Gaussian.Power.eval_polynomialPower, GCD.derivative]
    simp only [pow_succ] at original ⊢
    calc
      _ = -(2 * f.eval point *
          ((Dense.Derivative.derivative b).eval point * (h.eval point ^ index * h.eval point * u.eval point) -
            b.eval point * (((index : Canonical) + 1) * h.eval point ^ index *
              (Dense.Derivative.derivative h).eval point * u.eval point +
              (h.eval point ^ index * h.eval point) * (Dense.Derivative.derivative u).eval point)) +
        (Dense.Derivative.derivative f).eval point * b.eval point *
          (h.eval point ^ index * h.eval point * u.eval point) -
        2 * r.eval point * (h.eval point ^ index * h.eval point * u.eval point) *
          (h.eval point ^ index * h.eval point * u.eval point)) +
        h.eval point ^ index * (h.eval point *
          (2 * (f.eval point * ((Dense.Derivative.derivative b).eval point * u.eval point -
              b.eval point * (Dense.Derivative.derivative u).eval point)) +
            (Dense.Derivative.derivative f).eval point * b.eval point * u.eval point -
            2 * (r.eval point * (h.eval point ^ index * h.eval point) * u.eval point * u.eval point))) := by ring1
      _ = _ := by rewrite [← original]; ring1
  have divides : ProductIdentity weighted h cofactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    exact (cancelled point).trans (DensePolynomial.eval_mul h cofactor point)
  exact weighted_product_obstruction _ (even_weight_nonzero index)
    hNonzero hPositive squarefree fCoprime bCoprime uCoprime cofactor divides

/-- A squarefree denominator factor dividing a squarefree radicand cannot occur with positive multiplicity. -/
private theorem ramified_obstruction
    {f b c r h g u : Coefficients} (index : Nat)
    (identity : Cleared f b c r) (hNonzero : h.isZero = false)
    (hPositive : 0 < h.natDegree) (squarefree : SquarefreeCertificate h)
    (gCoprime : CoprimeCertificate h g) (bCoprime : CoprimeCertificate h b)
    (uCoprime : CoprimeCertificate h u)
    (radicandFactorization : ProductIdentity f h g)
    (factorization : ProductIdentity c (Gaussian.Power.polynomialPower h (index + 1)) u) : False := by
  let cofactor :=
    (g * (Dense.Derivative.derivative b * u - b * Dense.Derivative.derivative u)).scale 2 +
      Dense.Derivative.derivative g * b * u -
      (r * Gaussian.Power.polynomialPower h index * u * u).scale 2
  let weighted :=
    (((DensePolynomial.constant (2 * (index : Canonical) + 1)) * g) * b) * GCD.derivative h * u
  have cancelled : ∀ point : Canonical, weighted.eval point = (h * cofactor).eval point := by
    apply Multiplication.cancel_left_eval (factor := Gaussian.Power.polynomialPower h (index + 1))
      (Gaussian.Power.polynomialPower_nonzero hNonzero (index + 1))
    intro point
    have original := identity point
    have source := Factorization.Identity.eval_factorization factorization point
    have slope := Factorization.Identity.eval_derivative_factorization factorization point
    change (Dense.Derivative.derivative c).eval point =
      (Dense.Derivative.derivative (Gaussian.Power.polynomialPower h (index + 1) * u)).eval point at slope
    rewrite [Dense.Derivative.eval_derivative_mul, Gaussian.Power.eval_polynomialPower,
      Gaussian.Power.eval_derivative_polynomialPower_succ] at slope
    have curve := Factorization.Identity.eval_factorization radicandFactorization point
    have curveSlope := Factorization.Identity.eval_derivative_factorization radicandFactorization point
    change (Dense.Derivative.derivative f).eval point = (Dense.Derivative.derivative (h * g)).eval point at curveSlope
    rewrite [Dense.Derivative.eval_derivative_mul] at curveSlope
    simp only [source, Gaussian.Power.eval_polynomialPower, slope, curve, curveSlope] at original
    dsimp only [weighted, cofactor]
    simp only [DensePolynomial.eval_mul, DensePolynomial.eval_constant, DensePolynomial.eval_sub,
      DensePolynomial.eval_add, DensePolynomial.eval_scale, Gaussian.Power.eval_polynomialPower, GCD.derivative]
    simp only [pow_succ] at original ⊢
    calc
      _ = -(2 * (h.eval point * g.eval point) *
          ((Dense.Derivative.derivative b).eval point * (h.eval point ^ index * h.eval point * u.eval point) -
            b.eval point * (((index : Canonical) + 1) * h.eval point ^ index *
              (Dense.Derivative.derivative h).eval point * u.eval point +
              (h.eval point ^ index * h.eval point) * (Dense.Derivative.derivative u).eval point)) +
        ((Dense.Derivative.derivative h).eval point * g.eval point +
          h.eval point * (Dense.Derivative.derivative g).eval point) * b.eval point *
          (h.eval point ^ index * h.eval point * u.eval point) -
        2 * r.eval point * (h.eval point ^ index * h.eval point * u.eval point) *
          (h.eval point ^ index * h.eval point * u.eval point)) +
        (h.eval point ^ index * h.eval point) * (h.eval point *
          (2 * (g.eval point * ((Dense.Derivative.derivative b).eval point * u.eval point -
              b.eval point * (Dense.Derivative.derivative u).eval point)) +
            (Dense.Derivative.derivative g).eval point * b.eval point * u.eval point -
            2 * (r.eval point * h.eval point ^ index * u.eval point * u.eval point))) := by ring1
      _ = _ := by rewrite [← original]; ring1
  have divides : ProductIdentity weighted h cofactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    exact (cancelled point).trans (DensePolynomial.eval_mul h cofactor point)
  exact weighted_product_obstruction _ (odd_weight_nonzero index)
    hNonzero hPositive squarefree gCoprime bCoprime uCoprime cofactor divides

/-- A positive squarefree denominator factor coprime to the radicand contradicts the exact cleared identity.

The full multiplicity power and complementary polynomial are the supplied
original coefficient factors. All four coprimality certificates concern these
same inputs; this coefficient obstruction does not by itself admit a quotient.
-/
public theorem no_ordinary_factor_of_primitiveIdentity
    (value : Expression radicand) (numerator h u : Coefficients) (index : Nat)
    (identity : value.PrimitiveIdentity numerator)
    (hNonzero : h.isZero = false) (hPositive : 0 < h.natDegree)
    (squarefree : SquarefreeCertificate h) (curveCoprime : CoprimeCertificate h radicand)
    (numeratorCoprime : CoprimeCertificate h value.numerator.im)
    (cofactorCoprime : CoprimeCertificate h u)
    (factorization : ProductIdentity value.denominator (Gaussian.Power.polynomialPower h (index + 1)) u) :
    False :=
  ordinary_obstruction index identity.eval hNonzero hPositive squarefree
    curveCoprime numeratorCoprime cofactorCoprime factorization

/-- A positive squarefree denominator factor dividing the radicand contradicts the exact cleared identity.

The radicand factorization retains its actual complementary polynomial, and
the same denominator multiplicity retains its original cofactor. The positive
odd weight rules out the factor without dividing at its scalar zero values.
-/
public theorem no_ramified_factor_of_primitiveIdentity
    (value : Expression radicand) (numerator h g u : Coefficients) (index : Nat)
    (identity : value.PrimitiveIdentity numerator)
    (hNonzero : h.isZero = false) (hPositive : 0 < h.natDegree)
    (squarefree : SquarefreeCertificate h) (curveCoprime : CoprimeCertificate h g)
    (numeratorCoprime : CoprimeCertificate h value.numerator.im)
    (cofactorCoprime : CoprimeCertificate h u)
    (curveFactorization : ProductIdentity radicand h g)
    (factorization : ProductIdentity value.denominator (Gaussian.Power.polynomialPower h (index + 1)) u) :
    False :=
  ramified_obstruction index identity.eval hNonzero hPositive squarefree
    curveCoprime numeratorCoprime cofactorCoprime curveFactorization factorization

/-- Removing one copy from a positive finite power retains its exact coefficient factorization. -/
private theorem one_factor_of_power {c h u : Coefficients} (index : Nat)
    (factorization : ProductIdentity c (Gaussian.Power.polynomialPower h (index + 1)) u) :
    ProductIdentity c h (Gaussian.Power.polynomialPower h index * u) := by
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rewrite [Factorization.Identity.eval_factorization factorization point,
    DensePolynomial.eval_mul, Gaussian.Power.eval_polynomialPower,
    Gaussian.Power.eval_polynomialPower, pow_succ]
  ring1

/-- One actual multiplicity factor is impossible after its computed gcd split against the radicand. -/
private theorem positive_factor_obstruction
    {f b c r u : Coefficients} (index : Nat)
    (identity : Cleared f b c r) (coprime : CoprimeCertificate b c)
    (squarefree : SquarefreeCertificate f)
    (factor : Squarefree.Decomposition.Basic.Factor)
    (uCoprime : CoprimeCertificate factor.polynomial u)
    (factorization : ProductIdentity c (Gaussian.Power.polynomialPower factor.polynomial (index + 1)) u) :
    False := by
  let numerator := numeratorCoprime coprime factor.nonzero (one_factor_of_power index factorization)
  match Coprime.Decision.coprimeOutcome factor.polynomial f (Or.inl factor.nonzero) with
  | .coprime fCoprime =>
      exact ordinary_obstruction index identity factor.nonzero factor.degreePositive factor.squarefree
        fCoprime numerator uCoprime factorization
  | .commonDivisor common =>
      have factorSplit : ProductIdentity factor.polynomial common.divisor common.leftFactor := by
        apply Factorization.Identity.factorizationOfCandidateEvals
        intro point _
        exact common.leftIdentity point
      have curveSplit : ProductIdentity f common.divisor common.rightFactor := by
        apply Factorization.Identity.factorizationOfCandidateEvals
        intro point _
        exact common.rightIdentity point
      let nextCofactor := Gaussian.Power.polynomialPower common.leftFactor (index + 1) * u
      have nextFactorization :
          ProductIdentity c (Gaussian.Power.polynomialPower common.divisor (index + 1)) nextCofactor := by
        apply Factorization.Identity.factorizationOfCandidateEvals
        intro point _
        dsimp only [nextCofactor]
        rewrite [Factorization.Identity.eval_factorization factorization point]
        simp only [Gaussian.Power.eval_polynomialPower, DensePolynomial.eval_mul]
        rewrite [common.leftIdentity point, Purelib.Data.Gaussian.Power.mul_pow]
        ring1
      let divisorSquarefree := Squarefree.Factors.leftFactorSquarefree
        factor.squarefree common.nonzero factorSplit
      let divisorRemainder := Coprime.Factors.factorsCoprime factor.squarefree common.nonzero factorSplit
      let divisorOther := Coprime.Factors.coprimeLeftFactor uCoprime common.nonzero factorSplit
      let divisorCofactor := Operations.CoprimeCertificate.mulRight common.nonzero
        (Coprime.Power.polynomialPowerRightCoprime common.nonzero divisorRemainder (index + 1)) divisorOther
      let divisorNumerator := numeratorCoprime coprime common.nonzero
        (one_factor_of_power index nextFactorization)
      let divisorCurve := Coprime.Factors.factorsCoprime squarefree common.nonzero curveSplit
      exact ramified_obstruction index identity common.nonzero common.positiveDegree divisorSquarefree
        divisorCurve divisorNumerator divisorCofactor curveSplit nextFactorization

/-- The original complete multiplicity decomposition rules out every nonconstant reduced denominator. -/
private theorem denominator_degree_zero
    {f b c r : Coefficients} (identity : Cleared f b c r)
    (cNonzero : c.isZero = false) (cNormalized : c.normalize = c)
    (coprime : CoprimeCertificate b c) (squarefree : SquarefreeCertificate f) :
    c.natDegree = 0 := by
  by_cases degreeZero : c.natDegree = 0
  · exact degreeZero
  · let decomposition := Squarefree.Decomposition.Compute.decomposeNormalized
      c cNormalized cNonzero (Nat.pos_of_ne_zero degreeZero)
    cases entriesEq : decomposition.positiveMultiplicityEntries with
    | nil => exact (decomposition.positiveMultiplicityEntries_nonempty entriesEq).elim
    | cons head tail =>
        let context : PositiveContext decomposition.positiveMultiplicityEntries :=
          ⟨[], head, tail, entriesEq⟩
        let cofactor := context.otherPolynomial decomposition
        let coprimeOther := context.otherCoprime decomposition
          decomposition.positiveMultiplicityEntries_pairwise
        have factorization := context.multiplicityFactorization decomposition rfl
        have exponentIdentity : head.multiplicity - 1 + 1 = head.multiplicity :=
          Purelib.Data.Nat.Subtraction.sub_add_cancel head.multiplicityPositive
        change ProductIdentity c (Gaussian.Power.polynomialPower head.part.polynomial head.multiplicity)
          cofactor at factorization
        rewrite [← exponentIdentity] at factorization
        exact (positive_factor_obstruction (head.multiplicity - 1) identity coprime squarefree
          head.factor coprimeOther factorization).elim

/-- An admitted primitive with coprime generator numerator and denominator has constant denominator.

The original nonzero-denominator certificate excludes an invalid quotient.
Every positive-degree factor from the actual finite multiplicity decomposition
contradicts either the ordinary or the ramified cleared derivative equation.
-/
public theorem primitive_denominator_degree_zero (value : Expression radicand)
    (numerator : Coefficients) (denominatorNonzero : value.denominator.isZero = false)
    (normalized : value.denominator.normalize = value.denominator)
    (coprime : CoprimeCertificate value.numerator.im value.denominator)
    (squarefree : SquarefreeCertificate radicand) (identity : value.PrimitiveIdentity numerator) :
    value.denominator.natDegree = 0 :=
  denominator_degree_zero identity.eval denominatorNonzero normalized coprime squarefree

/-- The cached original coordinate gcd cancels from the exact cleared derivative equation.

The original two coefficient factorizations retain both numerator and
denominator parents. Cancelling the nonzero square of this same gcd uses
finite polynomial multiplication, without assuming it is nonzero everywhere.
-/
private theorem cofactor_cleared (value : Expression radicand) (numerator : Coefficients)
    (point : Canonical) (defined : value.Defined point)
    (result : Dense.GCD.BezoutResult value.numerator.im value.denominator)
    (identity : value.PrimitiveIdentity numerator) :
    Cleared radicand result.pFactor result.qFactor numerator := by
  let reduced : Expression radicand := ⟨⟨0, result.pFactor⟩, result.qFactor⟩
  have numeratorFactorization : ProductIdentity value.numerator.im result.gcd result.pFactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro argument _
    exact result.pIdentity argument
  have denominatorFactorization : ProductIdentity value.denominator result.gcd result.qFactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro argument _
    exact result.qIdentity argument
  have gcdNonzero := result.nonzero (Or.inr defined.denominator_nonzero)
  have cancelled := Multiplication.cancel_left_eval (factor := result.gcd * result.gcd)
    (left := (numerator * (result.qFactor * result.qFactor)).scale 2)
    (right := reduced.derivative.numerator.im)
    (DensePolynomial.isZero_mul_eq_false gcdNonzero gcdNonzero) (by
      intro argument
      have original := identity.eval argument
      have numeratorSlope := Factorization.Identity.eval_derivative_factorization numeratorFactorization argument
      have denominatorSlope := Factorization.Identity.eval_derivative_factorization denominatorFactorization argument
      change (Dense.Derivative.derivative value.numerator.im).eval argument =
        (Dense.Derivative.derivative (result.gcd * result.pFactor)).eval argument at numeratorSlope
      change (Dense.Derivative.derivative value.denominator).eval argument =
        (Dense.Derivative.derivative (result.gcd * result.qFactor)).eval argument at denominatorSlope
      rewrite [Dense.Derivative.eval_derivative_mul] at numeratorSlope denominatorSlope
      rewrite [result.pIdentity argument, result.qIdentity argument, numeratorSlope, denominatorSlope] at original
      change (result.gcd * result.gcd).eval argument *
          ((numerator * (result.qFactor * result.qFactor)).scale 2).eval argument =
        (result.gcd * result.gcd).eval argument *
          (radicand.scale 2 * (Dense.Derivative.derivative result.pFactor * result.qFactor -
              result.pFactor * Dense.Derivative.derivative result.qFactor) +
            Dense.Derivative.derivative radicand * result.pFactor * result.qFactor).eval argument
      simp only [DensePolynomial.eval_mul, DensePolynomial.eval_scale, DensePolynomial.eval_add,
        DensePolynomial.eval_sub]
      calc
        _ = 2 * numerator.eval argument * (result.gcd.eval argument * result.qFactor.eval argument) *
            (result.gcd.eval argument * result.qFactor.eval argument) := by ring1
        _ = 2 * radicand.eval argument *
            (((Dense.Derivative.derivative result.gcd).eval argument * result.pFactor.eval argument +
                result.gcd.eval argument * (Dense.Derivative.derivative result.pFactor).eval argument) *
                (result.gcd.eval argument * result.qFactor.eval argument) -
              (result.gcd.eval argument * result.pFactor.eval argument) *
                ((Dense.Derivative.derivative result.gcd).eval argument * result.qFactor.eval argument +
                  result.gcd.eval argument * (Dense.Derivative.derivative result.qFactor).eval argument)) +
            (Dense.Derivative.derivative radicand).eval argument *
              (result.gcd.eval argument * result.pFactor.eval argument) *
              (result.gcd.eval argument * result.qFactor.eval argument) := original
        _ = _ := by ring1)
  intro argument
  have readback := cancelled argument
  change ((numerator * (result.qFactor * result.qFactor)).scale 2).eval argument =
    (radicand.scale 2 * (Dense.Derivative.derivative result.pFactor * result.qFactor -
        result.pFactor * Dense.Derivative.derivative result.qFactor) +
      Dense.Derivative.derivative radicand * result.pFactor * result.qFactor).eval argument at readback
  simp only [DensePolynomial.eval_mul, DensePolynomial.eval_scale, DensePolynomial.eval_add,
    DensePolynomial.eval_sub] at readback
  calc
    _ = 2 * (numerator.eval argument * (result.qFactor.eval argument * result.qFactor.eval argument)) := by ring1
    _ = _ := readback

/-- Every admitted rational primitive of `R dx/Y` has a polynomial generator coefficient.

The original expression and its nonzero denominator remain the quotient owner.
One retained original coordinate gcd gives normalized coprime cofactors; their
constant denominator yields the displayed polynomial witness and the exact
all-input numerator identity. A bounded original coefficient-count search
constructs an actual admitted point from the same nonzero denominator. No
assertion is made about the expression's real coordinate.
-/
public theorem primitive_imaginary_polynomial (value : Expression radicand)
    (numerator : Coefficients) (denominatorNonzero : value.denominator.isZero = false)
    (radicandNonzero : radicand.isZero = false) (squarefree : SquarefreeCertificate radicand)
    (equal : value.derivative.Equal (oddReciprocal radicand 0 numerator)) :
    ∃ coefficient : Coefficients, ∀ argument : Canonical,
      value.numerator.im.eval argument = coefficient.eval argument * value.denominator.eval argument := by
  let admitted := NonzeroEvaluation.findNonzeroEvaluation value.denominator denominatorNonzero
  let point := admitted.point
  have defined : value.Defined point := admitted.valueNonzero
  let result := Gaussian.GCD.extendedGCD value.numerator.im value.denominator
  let reduced : Expression radicand := ⟨⟨0, result.pFactor⟩, result.qFactor⟩
  have reducedDefined : reduced.Defined point := by
    intro zero
    apply defined
    rewrite [result.qIdentity point, zero, mul_zero]
    rfl
  have coprime : CoprimeCertificate result.pFactor result.qFactor :=
    Coprime.Evaluation.coprimeCertificateOfIdentity result.pFactor result.qFactor
      (Or.inr reducedDefined.denominator_nonzero)
      result.factorLeft result.factorRight result.factorIdentity
  have cleared := cofactor_cleared value numerator point defined result
    (primitiveIdentity_of_derivative_equal value numerator radicandNonzero equal)
  have degreeZero := denominator_degree_zero cleared reducedDefined.denominator_nonzero
    result.qFactorNormalized coprime squarefree
  have constant : result.qFactor = DensePolynomial.constant result.qFactor.leadingCoeff :=
    result.qFactorNormalized.symm.trans
      (DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
        reducedDefined.denominator_nonzero degreeZero)
  have unitNonzero := DensePolynomial.leadingCoeff_ne_zero reducedDefined.denominator_nonzero
  refine ⟨result.pFactor.scale result.qFactor.leadingCoeff⁻¹, ?_⟩
  intro argument
  have constantEval : result.qFactor.eval argument = result.qFactor.leadingCoeff :=
    (congrArg (fun polynomial : Coefficients => polynomial.eval argument) constant).trans
      (DensePolynomial.eval_constant _ argument)
  rewrite [DensePolynomial.eval_scale, result.qIdentity argument, constantEval]
  calc
    value.numerator.im.eval argument = result.gcd.eval argument * result.pFactor.eval argument :=
      result.pIdentity argument
    _ = (result.qFactor.leadingCoeff * result.qFactor.leadingCoeff⁻¹) *
        (result.gcd.eval argument * result.pFactor.eval argument) := by
      rewrite [ExplicitField.mul_inv_cancel _ unitNonzero, one_mul]
      rfl
    _ = _ := by ring1

/-- The polynomial generator coefficient reads back on every coordinate admitted by the original expression. -/
public theorem primitive_imaginary_readback (value : Expression radicand)
    (numerator : Coefficients) (denominatorNonzero : value.denominator.isZero = false)
    (radicandNonzero : radicand.isZero = false) (squarefree : SquarefreeCertificate radicand)
    (equal : value.derivative.Equal (oddReciprocal radicand 0 numerator)) :
    ∃ coefficient : Coefficients, ∀ argument : Canonical, value.Defined argument →
      (value.evaluate argument).im = coefficient.eval argument := by
  obtain ⟨coefficient, identity⟩ := primitive_imaginary_polynomial value numerator denominatorNonzero
    radicandNonzero squarefree equal
  refine ⟨coefficient, ?_⟩
  intro argument admitted
  change value.numerator.im.eval argument / value.denominator.eval argument = coefficient.eval argument
  rewrite [identity argument]
  exact ExplicitField.mul_div_cancel_right _ _ admitted

/-- A polynomial generator coefficient gives the exact numerator operator identity for the same admitted primitive.

Differentiating the finite coefficient factorization and cancelling the square
of the original nonzero denominator yields `2R=2FB'+F'B`. The result is checked
as zero coefficients on the original finite Gaussian probe grid.
-/
public theorem primitive_operator_identity (value : Expression radicand)
    (numerator coefficient : Coefficients) (denominatorNonzero : value.denominator.isZero = false)
    (identity : value.PrimitiveIdentity numerator)
    (coefficientIdentity : ∀ argument : Canonical,
      value.numerator.im.eval argument = coefficient.eval argument * value.denominator.eval argument) :
    (numerator.scale 2 -
      ((radicand * Dense.Derivative.derivative coefficient).scale 2 +
        Dense.Derivative.derivative radicand * coefficient)).isZero = true := by
  have factorization : ProductIdentity value.numerator.im coefficient value.denominator := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro argument _
    exact coefficientIdentity argument
  have cancelled := Multiplication.cancel_left_eval
    (factor := value.denominator * value.denominator) (left := numerator.scale 2)
    (right := (radicand * Dense.Derivative.derivative coefficient).scale 2 +
      Dense.Derivative.derivative radicand * coefficient)
    (DensePolynomial.isZero_mul_eq_false denominatorNonzero denominatorNonzero) (by
      intro argument
      have original := identity.eval argument
      have slope := Factorization.Identity.eval_derivative_factorization factorization argument
      change (Dense.Derivative.derivative value.numerator.im).eval argument =
        (Dense.Derivative.derivative (coefficient * value.denominator)).eval argument at slope
      rewrite [Dense.Derivative.eval_derivative_mul] at slope
      rewrite [coefficientIdentity argument, slope] at original
      simp only [DensePolynomial.eval_mul, DensePolynomial.eval_scale, DensePolynomial.eval_add]
      calc
        _ = 2 * numerator.eval argument * value.denominator.eval argument *
            value.denominator.eval argument := by ring1
        _ = 2 * radicand.eval argument *
            (((Dense.Derivative.derivative coefficient).eval argument * value.denominator.eval argument +
                coefficient.eval argument * (Dense.Derivative.derivative value.denominator).eval argument) *
                value.denominator.eval argument -
              (coefficient.eval argument * value.denominator.eval argument) *
                (Dense.Derivative.derivative value.denominator).eval argument) +
            (Dense.Derivative.derivative radicand).eval argument *
              (coefficient.eval argument * value.denominator.eval argument) *
              value.denominator.eval argument := original
        _ = _ := by ring1)
  apply Extensionality.isZero_of_eval_eq_zero
  intro argument
  rewrite [DensePolynomial.eval_sub, cancelled argument]
  exact sub_self _

/-- Every admitted rational primitive gives an actual polynomial witness for the cleared numerator operator.

The same witness retains the original generator-coordinate cross identity and
satisfies `2R=2FB'+F'B` as a finite zero-coefficient certificate. This supplies
the rational-primitive elimination step before any separate degree argument.
The original nonzero-denominator certificate supplies actual admission by a
bounded original Gaussian search, without a caller-selected point.
-/
public theorem primitive_polynomial_operator (value : Expression radicand)
    (numerator : Coefficients) (denominatorNonzero : value.denominator.isZero = false)
    (radicandNonzero : radicand.isZero = false) (squarefree : SquarefreeCertificate radicand)
    (equal : value.derivative.Equal (oddReciprocal radicand 0 numerator)) :
    ∃ coefficient : Coefficients,
      (∀ argument : Canonical,
        value.numerator.im.eval argument = coefficient.eval argument * value.denominator.eval argument) ∧
      (numerator.scale 2 -
        ((radicand * Dense.Derivative.derivative coefficient).scale 2 +
          Dense.Derivative.derivative radicand * coefficient)).isZero = true := by
  obtain ⟨coefficient, coefficientIdentity⟩ := primitive_imaginary_polynomial value numerator denominatorNonzero
    radicandNonzero squarefree equal
  exact ⟨coefficient, coefficientIdentity,
    primitive_operator_identity value numerator coefficient denominatorNonzero
      (primitiveIdentity_of_derivative_equal value numerator radicandNonzero equal) coefficientIdentity⟩

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression
