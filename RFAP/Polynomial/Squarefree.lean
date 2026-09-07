import mathlib.RFAP.ConstructiveGCD

/-!
# Finite coprimality and squarefree certificates

A certificate records that the output of executable extended Euclid is one
displayed nonzero constant.  Rescaling its returned Bézout coefficients gives
an identity equal to `1` at every queried point.  No root set, coefficient
extensionality over an infinite carrier, or sparse polynomial is used.
-/

namespace RFAP.Squarefree

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

/-- A finite certificate that two dense Gaussian polynomials are coprime. -/
structure CoprimeCertificate (p q : GaussianPolynomial) where
  unit : Gaussian
  unit_ne_zero : unit ≠ 0
  gcd_eq_constant : (RFAP.ConstructiveGCD.extendedGCD p q).gcd = constant unit

namespace CoprimeCertificate

def left {p q : GaussianPolynomial} (certificate : CoprimeCertificate p q) :
    GaussianPolynomial :=
  scale certificate.unit⁻¹ (RFAP.ConstructiveGCD.extendedGCD p q).left

def right {p q : GaussianPolynomial} (certificate : CoprimeCertificate p q) :
    GaussianPolynomial :=
  scale certificate.unit⁻¹ (RFAP.ConstructiveGCD.extendedGCD p q).right

/-- The normalized finite Bézout identity. -/
theorem identity {p q : GaussianPolynomial}
    (certificate : CoprimeCertificate p q) (z : Gaussian) :
    1 = certificate.left.eval z * p.eval z +
      certificate.right.eval z * q.eval z := by
  have raw := (RFAP.ConstructiveGCD.extendedGCD p q).identity z
  rw [certificate.gcd_eq_constant, eval_constant] at raw
  calc
    1 = certificate.unit⁻¹ * certificate.unit := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
      exact (RFAP.ExplicitField.mul_inv_cancel certificate.unit
        certificate.unit_ne_zero).symm
    _ = certificate.unit⁻¹ *
        ((RFAP.ConstructiveGCD.extendedGCD p q).left.eval z * p.eval z +
          (RFAP.ConstructiveGCD.extendedGCD p q).right.eval z * q.eval z) := by
      rw [raw]
    _ = certificate.left.eval z * p.eval z +
        certificate.right.eval z * q.eval z := by
      simp only [left, right, eval_scale]
      exact (RFAP.ConstructiveGaussian.Gaussian.left_distrib
        certificate.unit⁻¹
        ((RFAP.ConstructiveGCD.extendedGCD p q).left.eval z * p.eval z)
        ((RFAP.ConstructiveGCD.extendedGCD p q).right.eval z * q.eval z)).trans
        (congrArg₂ (· + ·)
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm)

theorem eval_ne_zero {p q : GaussianPolynomial}
    (certificate : CoprimeCertificate p q) (z : Gaussian) :
    p.eval z ≠ 0 ∨ q.eval z ≠ 0 := by
  by_cases hp : p.eval z = 0
  · right
    intro hq
    have h := certificate.identity z
    simp only [hp, hq, mul_zero, zero_add] at h
    exact one_ne_zero h
  · exact Or.inl hp

end CoprimeCertificate

/-- Squarefreeness is the finite coprimality certificate for a polynomial
and its automatic derivative. -/
abbrev SquarefreeCertificate (p : GaussianPolynomial) :=
  CoprimeCertificate p (RFAP.ConstructiveGCD.derivative p)

/-- Normalize a checked constant Euclidean gcd into the finite coprimality
certificate consumed by the numerical proof. -/
def certificateOfConstantGCD
    (p q : GaussianPolynomial)
    (nonzero : (RFAP.ConstructiveGCD.extendedGCD p q).gcd.isZero = false)
    (degreeZero :
      (RFAP.ConstructiveGCD.extendedGCD p q).gcd.natDegree = 0) :
    CoprimeCertificate p q := by
  let result := RFAP.ConstructiveGCD.extendedGCD p q
  exact
    { unit := result.gcd.leadingCoeff
      unit_ne_zero := leadingCoeff_ne_zero nonzero
      gcd_eq_constant := by
        calc
          result.gcd = result.gcd.normalize := result.normalized.symm
          _ = constant result.gcd.leadingCoeff :=
            normalize_eq_constant_leadingCoeff_of_degree_zero nonzero
              degreeZero }

/-- The negative branch of the same finite Euclidean decision: a displayed
nonconstant common divisor and both quotient identities. -/
structure NonconstantCommonDivisor (p q : GaussianPolynomial) where
  result : RFAP.ComputableGCD.BezoutResult p q
  nonzero : result.gcd.isZero = false
  positiveDegree : 0 < result.gcd.natDegree

namespace NonconstantCommonDivisor

def divisor {p q : GaussianPolynomial}
    (common : NonconstantCommonDivisor p q) : GaussianPolynomial :=
  common.result.gcd

def leftFactor {p q : GaussianPolynomial}
    (common : NonconstantCommonDivisor p q) : GaussianPolynomial :=
  common.result.pFactor

def rightFactor {p q : GaussianPolynomial}
    (common : NonconstantCommonDivisor p q) : GaussianPolynomial :=
  common.result.qFactor

theorem leftIdentity {p q : GaussianPolynomial}
    (common : NonconstantCommonDivisor p q)
    (z : Gaussian) :
    p.eval z = common.divisor.eval z * common.leftFactor.eval z :=
  common.result.pIdentity z

theorem rightIdentity {p q : GaussianPolynomial}
    (common : NonconstantCommonDivisor p q)
    (z : Gaussian) :
    q.eval z = common.divisor.eval z * common.rightFactor.eval z :=
  common.result.qIdentity z

end NonconstantCommonDivisor

/-- Exhaustive result of one finite coprimality computation. -/
inductive CoprimeOutcome (p q : GaussianPolynomial) where
  | coprime (certificate : CoprimeCertificate p q)
  | commonDivisor (certificate : NonconstantCommonDivisor p q)

/-- Decide coprimality by inspecting the executable Euclidean gcd. -/
def coprimeOutcome
    (p q : GaussianPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false) :
    CoprimeOutcome p q := by
  let result := RFAP.ConstructiveGCD.extendedGCD p q
  have gcdNonzero : result.gcd.isZero = false := result.nonzero someNonzero
  if degreeZero : result.gcd.natDegree = 0 then
    exact .coprime (certificateOfConstantGCD p q gcdNonzero degreeZero)
  else
    exact .commonDivisor
      { result := result
        nonzero := gcdNonzero
        positiveDegree := Nat.pos_of_ne_zero degreeZero }

/-- The corresponding complete finite squarefreeness decision. -/
abbrev SquarefreeOutcome (p : GaussianPolynomial) :=
  CoprimeOutcome p (RFAP.ConstructiveGCD.derivative p)

def squarefreeOutcome
    (p : GaussianPolynomial) (nonzero : p.isZero = false) :
    SquarefreeOutcome p :=
  coprimeOutcome p (RFAP.ConstructiveGCD.derivative p) (Or.inl nonzero)

/-- Executable Boolean view of the same finite squarefreeness decision. -/
def squarefreeCheck (p : GaussianPolynomial) : Bool :=
  let result := RFAP.ConstructiveGCD.extendedGCD p
    (RFAP.ConstructiveGCD.derivative p)
  !result.gcd.isZero && decide (result.gcd.natDegree = 0)

theorem value_or_derivative_ne_zero {p : GaussianPolynomial}
    (certificate : SquarefreeCertificate p) (z : Gaussian) :
    p.eval z ≠ 0 ∨ (RFAP.ConstructiveGCD.derivative p).eval z ≠ 0 :=
  certificate.eval_ne_zero z

end RFAP.Squarefree
