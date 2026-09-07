import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Factorization

/-!
# Squarefreeness inherited by finite displayed factors

An explicit Bézout identity is converted back into the executable Euclidean
coprimality certificate by checking only the finite candidate list of one
coefficient difference.  The direct derivative product rule then transports
a squarefree certificate through either side of a displayed factorization.

This is the algebraic bridge needed to split overlapping squarefree
occurrences while retaining proof-bearing inputs for the numerical RFAP.
-/

namespace RFAP.SquarefreeFactors

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Factorization := RFAP.Factorization.ProductIdentity
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading

/-- A finite zero coefficient difference gives the corresponding pointwise
factorization identity. -/
theorem eval_factorization
    {p left right : GaussianPolynomial}
    (factorization : Factorization p left right) (point : Gaussian) :
    p.eval point = left.eval point * right.eval point := by
  have differenceZero := eval_eq_zero_of_isZero factorization point
  rw [eval_sub, sub_eq_zero] at differenceZero
  simpa only [eval_mul] using differenceZero

/-- The same finite coefficient identity gives equality of the automatic
derivatives, without polynomial extensionality over an infinite carrier. -/
theorem eval_derivative_factorization
    {p left right : GaussianPolynomial}
    (factorization : Factorization p left right) (point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative p).eval point =
      (RFAP.ConstructiveGCD.derivative (left * right)).eval point :=
  RFAP.ComputableDerivative.eval_derivative_eq_of_sub_isZero
    factorization point

/-- Swap the two displayed factors by checking the commuted evaluation
identity only on the finite candidate list of the new difference. -/
theorem factorization_swap
    {p left right : GaussianPolynomial}
    (factorization : Factorization p left right) :
    Factorization p right left := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  rw [eval_factorization factorization point]
  exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

/-- Convert any displayed finite Bézout identity into the executable
Euclidean coprimality certificate.  Equality of the auxiliary product is
checked only on its bounded coefficient-derived candidate list. -/
def coprimeCertificateOfIdentity
    (p q : GaussianPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false)
    (left right : GaussianPolynomial)
    (identity : ∀ point : Gaussian,
      1 = left.eval point * p.eval point +
        right.eval point * q.eval point) :
    CoprimeCertificate p q := by
  let result := RFAP.ConstructiveGCD.extendedGCD p q
  let cofactor := left * result.pFactor + right * result.qFactor
  have oneLeading :
      LeadingTerm (constant (1 : Gaussian)) 0 1 :=
    LeadingTerm.constant one_ne_zero
  have factorization :
      Factorization (constant 1) result.gcd cofactor := by
    apply RFAP.Factorization.factorizationOfCandidateEvals
    intro point _
    simp only [eval_constant]
    have original := identity point
    rw [result.pIdentity point, result.qIdentity point] at original
    dsimp only [cofactor]
    simp only [eval_add, eval_mul]
    calc
      1 = left.eval point *
            (result.gcd.eval point * result.pFactor.eval point) +
          right.eval point *
            (result.gcd.eval point * result.qFactor.eval point) := original
      _ = result.gcd.eval point *
          (left.eval point * result.pFactor.eval point +
            right.eval point * result.qFactor.eval point) := by ring1
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero someNonzero
  have cofactorNonzero : cofactor.isZero = false :=
    RFAP.Factorization.right_isZero_false
      oneLeading.nonzero oneLeading.normalized factorization
  have degreeBalance :
      result.gcd.natDegree + cofactor.natDegree =
        (constant (1 : Gaussian)).natDegree :=
    RFAP.Factorization.factor_natDegree_add
      oneLeading.nonzero oneLeading.normalized gcdNonzero
        cofactorNonzero factorization
  have gcdDegreeZero : result.gcd.natDegree = 0 := by
    rw [oneLeading.degree_eq] at degreeBalance
    exact Nat.eq_zero_of_le_zero
      ((Nat.le_add_right result.gcd.natDegree cofactor.natDegree).trans_eq
        degreeBalance)
  exact RFAP.Squarefree.certificateOfConstantGCD
    p q gcdNonzero gcdDegreeZero

/-- Every displayed nonzero left factor of a squarefree polynomial is
squarefree. -/
def leftFactorSquarefree
    {p left right : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p)
    (leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate left := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * RFAP.ConstructiveGCD.derivative right
  let derivativeCoefficient := squarefree.right * right
  apply coprimeCertificateOfIdentity left
    (RFAP.ConstructiveGCD.derivative left) (Or.inl leftNonzero)
      leftCoefficient derivativeCoefficient
  intro point
  have valueIdentity := eval_factorization factorization point
  have derivativeIdentity :=
    eval_derivative_factorization factorization point
  have original := squarefree.identity point
  rw [valueIdentity, derivativeIdentity] at original
  simp only [RFAP.ConstructiveGCD.derivative] at original
  rw [RFAP.ComputableDerivative.eval_derivative_mul] at original
  dsimp only [leftCoefficient, derivativeCoefficient]
  simp only [eval_add, eval_mul]
  calc
    1 = squarefree.left.eval point *
          (left.eval point * right.eval point) +
        squarefree.right.eval point *
          ((RFAP.ConstructiveGCD.derivative left).eval point *
              right.eval point +
            left.eval point *
              (RFAP.ConstructiveGCD.derivative right).eval point) := original
    _ = (squarefree.left.eval point * right.eval point +
          squarefree.right.eval point *
            (RFAP.ConstructiveGCD.derivative right).eval point) *
            left.eval point +
        (squarefree.right.eval point * right.eval point) *
          (RFAP.ConstructiveGCD.derivative left).eval point := by ring1

/-- The two nonzero displayed factors of a squarefree product are coprime. -/
def factorsCoprime
    {p left right : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p)
    (leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate left right := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * RFAP.ConstructiveGCD.derivative right
  let rightCoefficient :=
    squarefree.right * RFAP.ConstructiveGCD.derivative left
  apply coprimeCertificateOfIdentity left right (Or.inl leftNonzero)
    leftCoefficient rightCoefficient
  intro point
  have valueIdentity := eval_factorization factorization point
  have derivativeIdentity :=
    eval_derivative_factorization factorization point
  have original := squarefree.identity point
  rw [valueIdentity, derivativeIdentity] at original
  simp only [RFAP.ConstructiveGCD.derivative] at original
  rw [RFAP.ComputableDerivative.eval_derivative_mul] at original
  dsimp only [leftCoefficient, rightCoefficient]
  simp only [eval_add, eval_mul]
  calc
    1 = squarefree.left.eval point *
          (left.eval point * right.eval point) +
        squarefree.right.eval point *
          ((RFAP.ConstructiveGCD.derivative left).eval point *
              right.eval point +
            left.eval point *
              (RFAP.ConstructiveGCD.derivative right).eval point) := original
    _ = (squarefree.left.eval point * right.eval point +
          squarefree.right.eval point *
            (RFAP.ConstructiveGCD.derivative right).eval point) *
            left.eval point +
        (squarefree.right.eval point *
            (RFAP.ConstructiveGCD.derivative left).eval point) *
          right.eval point := by ring1

/-- A displayed nonzero left divisor inherits coprimality with the other
polynomial. -/
def coprimeLeftFactor
    {p q left right : GaussianPolynomial}
    (coprime : CoprimeCertificate p q)
    (leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate left q := by
  let leftCoefficient := coprime.left * right
  apply coprimeCertificateOfIdentity left q (Or.inl leftNonzero)
    leftCoefficient coprime.right
  intro point
  have original := coprime.identity point
  rw [eval_factorization factorization point] at original
  dsimp only [leftCoefficient]
  simp only [eval_mul]
  calc
    1 = coprime.left.eval point *
          (left.eval point * right.eval point) +
        coprime.right.eval point * q.eval point := original
    _ = (coprime.left.eval point * right.eval point) *
          left.eval point + coprime.right.eval point * q.eval point := by
      ring1

/-- A displayed nonzero right divisor inherits coprimality with the other
polynomial. -/
def coprimeRightFactor
    {p q left right : GaussianPolynomial}
    (coprime : CoprimeCertificate p q)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate right q :=
  coprimeLeftFactor coprime rightNonzero
    (factorization_swap factorization)

/-- Coprimality data is symmetric by exchanging its finite Bézout
coefficients. -/
def CoprimeCertificate.symm
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q) :
    CoprimeCertificate q p := by
  have someNonzero : q.isZero = false ∨ p.isZero = false := by
    by_cases pZero : p.isZero = true
    · by_cases qZero : q.isZero = true
      · have pEvalZero := eval_eq_zero_of_isZero pZero (0 : Gaussian)
        have qEvalZero := eval_eq_zero_of_isZero qZero (0 : Gaussian)
        have impossible := coprime.identity (0 : Gaussian)
        simp only [pEvalZero, qEvalZero, mul_zero, zero_add] at impossible
        exact (one_ne_zero impossible).elim
      · exact Or.inl (by simpa using qZero)
    · exact Or.inr (by simpa using pZero)
  apply coprimeCertificateOfIdentity q p someNonzero
    coprime.right coprime.left
  intro point
  have original := coprime.identity point
  calc
    1 = coprime.left.eval point * p.eval point +
        coprime.right.eval point * q.eval point := original
    _ = coprime.right.eval point * q.eval point +
        coprime.left.eval point * p.eval point :=
      RFAP.ConstructiveGaussian.Gaussian.add_comm _ _

/-- Every displayed nonzero polynomial is coprime to a displayed nonzero
constant. -/
def CoprimeCertificate.constantRightOfNe
    {p : GaussianPolynomial} (pNonzero : p.isZero = false)
    (value : Gaussian) (valueNonzero : value ≠ 0) :
    CoprimeCertificate p (constant value) := by
  apply coprimeCertificateOfIdentity p (constant value) (Or.inl pNonzero)
    0 (constant value⁻¹)
  intro point
  simp only [eval_zero, zero_mul, eval_constant, zero_add]
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
  exact (RFAP.ExplicitField.mul_inv_cancel value valueNonzero).symm

/-- Every displayed nonzero polynomial is coprime to the constant one. -/
def CoprimeCertificate.constantRight
    {p : GaussianPolynomial} (pNonzero : p.isZero = false) :
    CoprimeCertificate p (constant 1) :=
  CoprimeCertificate.constantRightOfNe pNonzero 1 one_ne_zero

/-- If one displayed polynomial is separately coprime to two right factors,
it is coprime to their product.  Multiplying the two finite Bézout
identities supplies the new certificate directly. -/
def CoprimeCertificate.mulRight
    {p q r : GaussianPolynomial} (pNonzero : p.isZero = false)
    (leftCoprime : CoprimeCertificate p q)
    (rightCoprime : CoprimeCertificate p r) :
    CoprimeCertificate p (q * r) := by
  let leftCoefficient :=
    leftCoprime.left * rightCoprime.left * p +
      leftCoprime.left * rightCoprime.right * r +
      leftCoprime.right * rightCoprime.left * q
  let rightCoefficient := leftCoprime.right * rightCoprime.right
  apply coprimeCertificateOfIdentity p (q * r) (Or.inl pNonzero)
    leftCoefficient rightCoefficient
  intro point
  have leftIdentity := leftCoprime.identity point
  have rightIdentity := rightCoprime.identity point
  dsimp only [leftCoefficient, rightCoefficient]
  simp only [eval_add, eval_mul]
  calc
    1 = 1 * 1 := by ring1
    _ = (leftCoprime.left.eval point * p.eval point +
          leftCoprime.right.eval point * q.eval point) *
        (rightCoprime.left.eval point * p.eval point +
          rightCoprime.right.eval point * r.eval point) := by
      rw [← leftIdentity, ← rightIdentity]
    _ = ((leftCoprime.left.eval point * rightCoprime.left.eval point *
            p.eval point +
          leftCoprime.left.eval point * rightCoprime.right.eval point *
            r.eval point +
          leftCoprime.right.eval point * rightCoprime.left.eval point *
            q.eval point) * p.eval point) +
        (leftCoprime.right.eval point * rightCoprime.right.eval point) *
          (q.eval point * r.eval point) := by ring1

/-- Every displayed nonzero right factor of a squarefree polynomial is
squarefree. -/
def rightFactorSquarefree
    {p left right : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate right := by
  have swapped : Factorization p right left := by
    exact factorization_swap factorization
  exact leftFactorSquarefree squarefree rightNonzero swapped

end RFAP.SquarefreeFactors
