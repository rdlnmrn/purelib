import FTA.DenseDerivative
import FTA.DenseGCD
import Mathlib.Algebra.Squarefree.Basic

/-!
# Executable coprimality and squarefreeness certificates

The extended Euclidean program returns a common divisor together with dense
Bézout coefficients.  When that divisor is a nonzero constant, scaling the
coefficients by its inverse produces the displayed identity `U * p + V * q =
1`.  Otherwise the same run returns a checked nonconstant common divisor.
Specializing the second input to the executable formal derivative gives the
finite squarefreeness decision used by the Sturm layer.
-/

namespace FTA.DenseSquarefree

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseDerivative
open FTA.DenseGCD

abbrev RatPolynomial := DensePolynomial ℚ

/-- Finite dense Bézout data displaying coprimality. -/
structure CoprimeCertificate (p q : RatPolynomial) where
  left : RatPolynomial
  right : RatPolynomial
  polynomialIdentity : left.toPolynomial * p.toPolynomial +
    right.toPolynomial * q.toPolynomial = 1

theorem CoprimeCertificate.identity {p q : RatPolynomial}
    (certificate : CoprimeCertificate p q) (x : ℚ) :
    certificate.left.eval x * p.eval x + certificate.right.eval x * q.eval x = 1 := by
  have h := congrArg (Polynomial.eval x) certificate.polynomialIdentity
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    eval_toPolynomial] using h

/-- Swap the two members of a displayed dense Bézout identity. -/
def CoprimeCertificate.swap {p q : RatPolynomial}
    (certificate : CoprimeCertificate p q) : CoprimeCertificate q p where
  left := certificate.right
  right := certificate.left
  polynomialIdentity := by
    rw [add_comm]
    exact certificate.polynomialIdentity

/-- Transport a displayed Bézout identity through one signed Euclidean step.
If `p = remainder + q * quotient` and `next = -remainder`, then
`(left * quotient + right) * q - left * next = 1`. -/
def CoprimeCertificate.signedStep {p q : RatPolynomial}
    (certificate : CoprimeCertificate p q) :
    CoprimeCertificate q (-((divMod p q).remainder)) where
  left := certificate.left * (divMod p q).quotient + certificate.right
  right := -certificate.left
  polynomialIdentity := by
    rw [toPolynomial_add, toPolynomial_mul, toPolynomial_neg, toPolynomial_neg]
    calc
      (certificate.left.toPolynomial * (divMod p q).quotient.toPolynomial +
            certificate.right.toPolynomial) * q.toPolynomial +
          -certificate.left.toPolynomial * -(divMod p q).remainder.toPolynomial =
        certificate.left.toPolynomial * p.toPolynomial +
          certificate.right.toPolynomial * q.toPolynomial := by
        rw [divMod_toPolynomial_equation p q]
        ring
      _ = 1 := certificate.polynomialIdentity

/-- The pointwise dense certificate is an exact sparse-polynomial coprimality
certificate, not merely a test on sampled rational points. -/
theorem CoprimeCertificate.isCoprime {p q : RatPolynomial}
    (certificate : CoprimeCertificate p q) :
    IsCoprime p.toPolynomial q.toPolynomial := by
  refine ⟨certificate.left.toPolynomial, certificate.right.toPolynomial, ?_⟩
  exact certificate.polynomialIdentity

theorem toPolynomial_eq_C_leadingCoeff_of_natDegree_eq_zero
    {p : RatPolynomial} (hp : p.isZero = false) (hdegree : p.natDegree = 0) :
    p.toPolynomial = Polynomial.C p.leadingCoeff := by
  have hspecDegree : p.toPolynomial.natDegree = 0 := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hspecDegree
  have hcoefficient : p.toPolynomial.coeff 0 = p.leadingCoeff := by
    calc
      p.toPolynomial.coeff 0 = p.toPolynomial.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hspecDegree]
      _ = p.leadingCoeff := leadingCoeff_toPolynomial hp
  exact hconstant.trans (congrArg Polynomial.C hcoefficient)

/-- A nonzero dense polynomial of natural degree zero evaluates everywhere to
its normalized leading coefficient. -/
theorem eval_eq_leadingCoeff_of_natDegree_eq_zero {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree = 0) (x : ℚ) :
    p.eval x = p.leadingCoeff := by
  have hspecDegree : p.toPolynomial.natDegree = 0 := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  let c := p.toPolynomial.coeff 0
  have hconstant : p.toPolynomial = Polynomial.C c :=
    Polynomial.eq_C_of_natDegree_eq_zero hspecDegree
  calc
    p.eval x = Polynomial.eval x p.toPolynomial := (eval_toPolynomial p x).symm
    _ = Polynomial.eval x (Polynomial.C c) := congrArg (Polynomial.eval x) hconstant
    _ = c := by simp
    _ = p.toPolynomial.coeff 0 := rfl
    _ = p.toPolynomial.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hspecDegree]
    _ = p.leadingCoeff := leadingCoeff_toPolynomial hp

/-- Normalize a nonzero constant Euclidean result to the displayed Bézout
identity for one. -/
def certificateOfConstantGCD {p q : RatPolynomial}
    (result : BezoutResult p q) (hnonzero : result.gcd.isZero = false)
    (hdegree : result.gcd.natDegree = 0) : CoprimeCertificate p q where
  left := scale result.gcd.leadingCoeff⁻¹ result.left
  right := scale result.gcd.leadingCoeff⁻¹ result.right
  polynomialIdentity := by
    rw [toPolynomial_scale, toPolynomial_scale]
    have hconstant := toPolynomial_eq_C_leadingCoeff_of_natDegree_eq_zero
      hnonzero hdegree
    have hleading : result.gcd.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hnonzero
    calc
      Polynomial.C result.gcd.leadingCoeff⁻¹ * result.left.toPolynomial * p.toPolynomial +
          Polynomial.C result.gcd.leadingCoeff⁻¹ * result.right.toPolynomial * q.toPolynomial =
          Polynomial.C result.gcd.leadingCoeff⁻¹ * result.gcd.toPolynomial := by
        rw [result.polynomialIdentity]
        ring
      _ = Polynomial.C result.gcd.leadingCoeff⁻¹ *
          Polynomial.C result.gcd.leadingCoeff := by rw [hconstant]
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hleading, map_one]

/-- An explicit negative result from the same Euclidean run. -/
structure NonconstantCommonDivisor (p q : RatPolynomial) where
  divisor : RatPolynomial
  nonzero : divisor.isZero = false
  positiveDegree : 0 < divisor.natDegree
  dividesLeft : divisor.toPolynomial ∣ p.toPolynomial
  dividesRight : divisor.toPolynomial ∣ q.toPolynomial

/-- Exact exhaustive result of the finite coprimality decision. -/
inductive CoprimeOutcome (p q : RatPolynomial) where
  | coprime (certificate : CoprimeCertificate p q)
  | commonDivisor (certificate : NonconstantCommonDivisor p q)

/-- Extended Euclid decides coprimality whenever at least one input is
nonzero.  No proposition-valued search is hidden in either branch. -/
def coprimeOutcome (p q : RatPolynomial)
    (hnonzero : p.isZero = false ∨ q.isZero = false) : CoprimeOutcome p q :=
  let result := extendedGCD p q
  have hgcd : result.gcd.isZero = false := result.nonzero hnonzero
  if hdegree : result.gcd.natDegree = 0 then
    .coprime (certificateOfConstantGCD result hgcd hdegree)
  else
    .commonDivisor
      { divisor := result.gcd
        nonzero := hgcd
        positiveDegree := Nat.pos_of_ne_zero hdegree
        dividesLeft := gcd_toPolynomial_dvd_left p q
        dividesRight := gcd_toPolynomial_dvd_right p q }

/-- Recover the proof-bearing executable Bézout certificate from the complete
dense Euclidean decision when sparse coprimality has already been proved and
at least one input is represented nonzero. -/
def certificateOfIsCoprimeNonzero (p q : RatPolynomial)
    (hnonzero : p.isZero = false ∨ q.isZero = false)
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial) :
    CoprimeCertificate p q := by
  cases houtcome : coprimeOutcome p q hnonzero with
  | coprime certificate => exact certificate
  | commonDivisor common =>
      have hunit := hcoprime.isUnit_of_dvd' common.dividesLeft common.dividesRight
      have hdegree := Polynomial.natDegree_eq_zero_of_isUnit hunit
      rw [natDegree_toPolynomial common.nonzero] at hdegree
      exact (Nat.ne_of_gt common.positiveDegree hdegree).elim

/-- Left-nonzero convenience wrapper retained for derivative squarefreeness
and other oriented calls. -/
def certificateOfIsCoprime (p q : RatPolynomial) (hp : p.isZero = false)
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial) :
    CoprimeCertificate p q :=
  certificateOfIsCoprimeNonzero p q (Or.inl hp) hcoprime

/-- Recover finite dense Bézout data from the weaker factor-theoretic
statement that every common divisor is a unit.  This avoids routing
squarefree factor splits through separability or a polynomial PID instance. -/
def certificateOfIsRelPrimeNonzero (p q : RatPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false)
    (relPrime : IsRelPrime p.toPolynomial q.toPolynomial) :
    CoprimeCertificate p q := by
  let result := extendedGCD p q
  have gcdNonzero : result.gcd.isZero = false := result.nonzero someNonzero
  have gcdUnit : IsUnit result.gcd.toPolynomial :=
    relPrime ⟨result.pFactor.toPolynomial, result.pPolynomialIdentity⟩
      ⟨result.qFactor.toPolynomial, result.qPolynomialIdentity⟩
  have sparseDegreeZero : result.gcd.toPolynomial.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit gcdUnit
  have denseDegreeZero : result.gcd.natDegree = 0 := by
    rwa [natDegree_toPolynomial gcdNonzero] at sparseDegreeZero
  exact certificateOfConstantGCD result gcdNonzero denseDegreeZero

/-- Decidable Boolean view, convenient for finite computation and examples. -/
def coprimeCheck (p q : RatPolynomial) : Bool :=
  let result := extendedGCD p q
  !result.gcd.isZero && decide (result.gcd.natDegree = 0)

/-- A squarefreeness certificate is the Bézout certificate for a polynomial
and its executable derivative. -/
abbrev SquarefreeCertificate (p : RatPolynomial) :=
  CoprimeCertificate p (derivative p)

/-! ## Executable squarefree part -/

/-- The quotient of a polynomial by the common gcd with its derivative.  The
coefficient-order-independent gcd reduction is the same first member used by
the finite Cauchy--Sturm chain. -/
def squarefreePart (p : RatPolynomial) : RatPolynomial :=
  symmetricRightFactor (derivative p) p

/-- The complementary gcd factor, so that `p = repeatedPart p *
squarefreePart p` exactly in the sparse specification and at every rational
evaluation point. -/
def repeatedPart (p : RatPolynomial) : RatPolynomial :=
  symmetricGCD (derivative p) p

theorem squarefreePart_isZero_false {p : RatPolynomial}
    (hp : p.isZero = false) : (squarefreePart p).isZero = false :=
  symmetricRightFactor_isZero_false hp

theorem repeatedPart_isZero_false {p : RatPolynomial}
    (hp : p.isZero = false) : (repeatedPart p).isZero = false :=
  symmetricGCD_isZero_false (Or.inr hp)

theorem repeatedPart_mul_squarefreePart_toPolynomial (p : RatPolynomial) :
    p.toPolynomial = (repeatedPart p).toPolynomial *
      (squarefreePart p).toPolynomial :=
  symmetricRightFactor_toPolynomial_identity (derivative p) p

theorem repeatedPart_mul_squarefreePart_eval (p : RatPolynomial) (x : ℚ) :
    p.eval x = (repeatedPart p).eval x * (squarefreePart p).eval x :=
  symmetricRightFactor_eval_identity (derivative p) p x

theorem repeatedPart_eval_ne_zero_of_eval_ne_zero {p : RatPolynomial} {x : ℚ}
    (hp : p.eval x ≠ 0) : (repeatedPart p).eval x ≠ 0 := by
  intro hrepeated
  apply hp
  rw [repeatedPart_mul_squarefreePart_eval, hrepeated, zero_mul]

theorem squarefreePart_eval_ne_zero_of_eval_ne_zero {p : RatPolynomial} {x : ℚ}
    (hp : p.eval x ≠ 0) : (squarefreePart p).eval x ≠ 0 := by
  intro hsquarefree
  apply hp
  rw [repeatedPart_mul_squarefreePart_eval, hsquarefree, mul_zero]

/-- A nonconstant characteristic-zero polynomial has a nonconstant
squarefree part.  This follows constructively from strict derivative degree
descent and the exact degree balance of the two executable gcd quotients. -/
theorem squarefreePart_natDegree_ne_zero {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    (squarefreePart p).natDegree ≠ 0 := by
  have hlt := symmetricFactor_natDegree_lt
    (derivative_isZero_false hp hdegree) hp
    (derivative_natDegree_lt hp hdegree)
  dsimp only [squarefreePart]
  omega

theorem repeatedPart_natDegree_add_squarefreePart_natDegree
    {p : RatPolynomial} (hp : p.isZero = false) :
    (repeatedPart p).natDegree + (squarefreePart p).natDegree = p.natDegree := by
  have hrepeated := repeatedPart_isZero_false hp
  have hsquarefree := squarefreePart_isZero_false hp
  have hdegree := congrArg Polynomial.natDegree
    (repeatedPart_mul_squarefreePart_toPolynomial p)
  rw [Polynomial.natDegree_mul
      (toPolynomial_ne_zero_of_isZero_false hrepeated)
      (toPolynomial_ne_zero_of_isZero_false hsquarefree),
    natDegree_toPolynomial hp, natDegree_toPolynomial hrepeated,
    natDegree_toPolynomial hsquarefree] at hdegree
  exact hdegree.symm

theorem repeatedPart_natDegree_lt {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    (repeatedPart p).natDegree < p.natDegree := by
  have hsum := repeatedPart_natDegree_add_squarefreePart_natDegree hp
  have hsquarefree := squarefreePart_natDegree_ne_zero hp hdegree
  omega

theorem repeatedPart_toPolynomial_dvd_derivative (p : RatPolynomial) :
    (repeatedPart p).toPolynomial ∣ p.toPolynomial.derivative := by
  rw [← toPolynomial_derivative]
  exact symmetricGCD_toPolynomial_dvd_left (derivative p) p

private theorem derivativeGCD_quotient_squarefree
    {P G Q : Polynomial ℚ} (pNonzero : P ≠ 0) (factorization : P = G * Q)
    (greatest : ∀ {d : Polynomial ℚ}, d ∣ P.derivative → d ∣ P → d ∣ G) :
    Squarefree Q := by
  intro d squareDivides
  by_cases dZero : d = 0
  · have qZero : Q = 0 := by simpa [dZero] using squareDivides
    exact (pNonzero (by rw [factorization, qZero, mul_zero])).elim
  by_cases dUnit : IsUnit d
  · exact dUnit
  have dDegreePositive : 0 < d.natDegree := by
    apply Nat.pos_of_ne_zero
    intro degreeZero
    apply dUnit
    have coefficientNonzero : d.coeff 0 ≠ 0 := by
      intro coefficientZero
      apply dZero
      rw [Polynomial.eq_C_of_natDegree_eq_zero degreeZero,
        coefficientZero, map_zero]
    rw [Polynomial.eq_C_of_natDegree_eq_zero degreeZero]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr coefficientNonzero)
  have gNonzero : G ≠ 0 := by
    intro gZero
    apply pNonzero
    rw [factorization, gZero, zero_mul]
  have powerDividesG : ∀ n : ℕ, d ^ n ∣ G := by
    intro n
    induction n with
    | zero => simp
    | succ n inductionHypothesis =>
        have higherPowerDividesP : d ^ (n + 2) ∣ P := by
          rw [factorization]
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
            mul_dvd_mul inductionHypothesis squareDivides
        have nextPowerDividesDerivative : d ^ (n + 1) ∣ P.derivative := by
          simpa using
            (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd higherPowerDividesP)
        have nextPowerDividesP : d ^ (n + 1) ∣ P :=
          (pow_dvd_pow d (by omega : n + 1 ≤ n + 2)).trans higherPowerDividesP
        exact greatest nextPowerDividesDerivative nextPowerDividesP
  have degreeBound := Polynomial.natDegree_le_of_dvd
    (powerDividesG (G.natDegree + 1)) gNonzero
  rw [Polynomial.natDegree_pow] at degreeBound
  nlinarith

/-- The ordinary right quotient in the derivative-first Euclidean run is
squarefree. -/
private theorem rightFactor_derivative_squarefree {p : RatPolynomial}
    (hp : p.isZero = false) :
    Squarefree (rightFactor (derivative p) p).toPolynomial := by
  apply derivativeGCD_quotient_squarefree
    (toPolynomial_ne_zero_of_isZero_false hp)
    (rightFactor_toPolynomial_identity (derivative p) p)
  intro d dividesDerivative dividesP
  apply gcd_toPolynomial_isGreatest
  · rwa [toPolynomial_derivative]
  · exact dividesP

/-- The same statement for the polynomial-first Euclidean run. -/
private theorem leftFactor_derivative_squarefree {p : RatPolynomial}
    (hp : p.isZero = false) :
    Squarefree (leftFactor p (derivative p)).toPolynomial := by
  apply derivativeGCD_quotient_squarefree
    (toPolynomial_ne_zero_of_isZero_false hp)
    (leftFactor_toPolynomial_identity p (derivative p))
  intro d dividesDerivative dividesP
  apply gcd_toPolynomial_isGreatest
  · exact dividesP
  · rwa [toPolynomial_derivative]

/-- The coefficient-order-independent executable quotient is squarefree over
the rationals. -/
theorem squarefreePart_sparse_squarefree {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    Squarefree (squarefreePart p).toPolynomial := by
  have hderivativeNe : derivative p ≠ p := by
    intro heq
    have hlt := derivative_natDegree_lt hp hdegree
    rw [heq] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  have hpDerivativeNe : p ≠ derivative p := Ne.symm hderivativeNe
  rcases lt_trichotomy (derivative p).coeffs p.coeffs with hlt | heq | hgt
  · simpa [squarefreePart, symmetricRightFactor, hderivativeNe, hlt] using
      rightFactor_derivative_squarefree hp
  · exact (hderivativeNe (DensePolynomial.ext heq)).elim
  · have hnforward : ¬(derivative p).coeffs < p.coeffs := not_lt_of_ge hgt.le
    simpa [squarefreePart, symmetricRightFactor, hderivativeNe,
      hpDerivativeNe, hnforward] using leftFactor_derivative_squarefree hp

/-- Turn a sparse squarefreeness proof into the finite dense Bézout
certificate used by the executable Sturm layer.  The recursion follows the
strict degree drop of the computed gcd.  If that gcd had positive degree, its
recursively obtained derivative certificate would make it divide the quotient
as well, contradicting the displayed squarefreeness of the input. -/
def certificateOfSparseSquarefree (p : RatPolynomial)
    (nonzero : p.isZero = false) (squarefree : Squarefree p.toPolynomial) :
    SquarefreeCertificate p :=
  let result := extendedGCD p (derivative p)
  have gcdNonzero : result.gcd.isZero = false := result.nonzero (Or.inl nonzero)
  if degreeZero : result.gcd.natDegree = 0 then
    certificateOfConstantGCD result gcdNonzero degreeZero
  else by
    have gcdDividesP : result.gcd.toPolynomial ∣ p.toPolynomial :=
      ⟨result.pFactor.toPolynomial, result.pPolynomialIdentity⟩
    have gcdDividesDerivative :
        result.gcd.toPolynomial ∣ p.toPolynomial.derivative := by
      rw [← toPolynomial_derivative]
      exact ⟨result.qFactor.toPolynomial, result.qPolynomialIdentity⟩
    have pDegreeNonzero : p.natDegree ≠ 0 := by
      have degreeLe := Polynomial.natDegree_le_of_dvd gcdDividesP
        (toPolynomial_ne_zero_of_isZero_false nonzero)
      rw [natDegree_toPolynomial gcdNonzero,
        natDegree_toPolynomial nonzero] at degreeLe
      omega
    have derivativeNonzero := derivative_isZero_false nonzero pDegreeNonzero
    have gcdDividesDerivativeDense : result.gcd.toPolynomial ∣
        (derivative p).toPolynomial := by
      rw [toPolynomial_derivative]
      exact gcdDividesDerivative
    have gcdDegreeLeDerivative :
        result.gcd.natDegree ≤ (derivative p).natDegree := by
      have degreeLe := Polynomial.natDegree_le_of_dvd
        gcdDividesDerivativeDense
        (toPolynomial_ne_zero_of_isZero_false derivativeNonzero)
      rwa [natDegree_toPolynomial gcdNonzero,
        natDegree_toPolynomial derivativeNonzero] at degreeLe
    have gcdDegreeLt : result.gcd.natDegree < p.natDegree :=
      gcdDegreeLeDerivative.trans_lt
        (derivative_natDegree_lt nonzero pDegreeNonzero)
    have gcdCountLt : result.gcd.degreeCount < p.degreeCount := by
      have gcdCount := natDegree_add_one_eq_degreeCount gcdNonzero
      have pCount := natDegree_add_one_eq_degreeCount nonzero
      omega
    have gcdSquarefree : Squarefree result.gcd.toPolynomial :=
      squarefree.squarefree_of_dvd gcdDividesP
    let gcdCertificate := certificateOfSparseSquarefree result.gcd
      gcdNonzero gcdSquarefree
    have gcdCoprimeDerivative : IsCoprime result.gcd.toPolynomial
        result.gcd.toPolynomial.derivative := by
      have coprime := gcdCertificate.isCoprime
      rwa [toPolynomial_derivative] at coprime
    have gcdDividesDerivativeTimesFactor : result.gcd.toPolynomial ∣
        result.gcd.toPolynomial.derivative * result.pFactor.toPolynomial := by
      rw [result.pPolynomialIdentity, Polynomial.derivative_mul,
        dvd_add_left (dvd_mul_right result.gcd.toPolynomial
          result.pFactor.toPolynomial.derivative)] at gcdDividesDerivative
      exact gcdDividesDerivative
    have gcdDividesFactor : result.gcd.toPolynomial ∣
        result.pFactor.toPolynomial :=
      gcdCoprimeDerivative.dvd_of_dvd_mul_left gcdDividesDerivativeTimesFactor
    have gcdSquareDivides : result.gcd.toPolynomial * result.gcd.toPolynomial ∣
        p.toPolynomial := by
      rw [result.pPolynomialIdentity]
      exact mul_dvd_mul_left result.gcd.toPolynomial gcdDividesFactor
    have gcdUnit := squarefree result.gcd.toPolynomial gcdSquareDivides
    have sparseDegreeZero := Polynomial.natDegree_eq_zero_of_isUnit gcdUnit
    have denseDegreeZero : result.gcd.natDegree = 0 := by
      rwa [natDegree_toPolynomial gcdNonzero] at sparseDegreeZero
    exact (degreeZero denseDegreeZero).elim
termination_by p.degreeCount
decreasing_by exact gcdCountLt

/-- Recover the fully explicit dense Bézout certificate for the computed
squarefree part. -/
def squarefreePartCertificate {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    SquarefreeCertificate (squarefreePart p) := by
  exact certificateOfSparseSquarefree (squarefreePart p)
    (squarefreePart_isZero_false hp) (squarefreePart_sparse_squarefree hp hdegree)

/-- A dense squarefreeness certificate has precisely the sparse derivative
coprimality meaning used in the paper. -/
theorem SquarefreeCertificate.isCoprimeDerivative {p : RatPolynomial}
    (certificate : SquarefreeCertificate p) :
    IsCoprime p.toPolynomial p.toPolynomial.derivative := by
  have h := certificate.isCoprime
  rw [toPolynomial_derivative] at h
  exact h

/-- The exact Bézout derivative certificate also gives squarefreeness
directly: a displayed square divisor divides both the polynomial and its
derivative, and hence must be a unit. -/
theorem SquarefreeCertificate.sparseSquarefree {p : RatPolynomial}
    (certificate : SquarefreeCertificate p) : Squarefree p.toPolynomial := by
  intro factor factorSquareDivides
  apply certificate.isCoprimeDerivative.isUnit_of_dvd'
  · exact (dvd_mul_right factor factor).trans factorSquareDivides
  · have powerDivides : factor ^ 2 ∣ p.toPolynomial := by
      simpa [pow_two] using factorSquareDivides
    simpa using
      (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd powerDivides)

/-- Finite squarefreeness decision for every represented nonzero polynomial. -/
def squarefreeOutcome (p : RatPolynomial) (hp : p.isZero = false) :
    CoprimeOutcome p (derivative p) :=
  coprimeOutcome p (derivative p) (Or.inl hp)

/-- Executable squarefreeness check. -/
def squarefreeCheck (p : RatPolynomial) : Bool :=
  coprimeCheck p (derivative p)

/-- `T² - 1` is certified squarefree by the complete executable path. -/
theorem squarefreeCheck_quadratic_example :
    squarefreeCheck ⟨[1, 0, -1]⟩ = true := by
  native_decide

/-- `(T - 1)²` returns its positive-degree common factor with its derivative. -/
theorem squarefreeCheck_repeated_example :
    squarefreeCheck ⟨[1, -2, 1]⟩ = false := by
  native_decide

/-- The same repeated-factor example becomes squarefree after the computed
gcd quotient, exercising the complete executable decision path. -/
theorem squarefreeCheck_squarefreePart_repeated_example :
    squarefreeCheck (squarefreePart ⟨[1, -2, 1]⟩) = true := by
  native_decide

end FTA.DenseSquarefree
