import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ComputablePolynomial

/-!
# Finite extended Euclid for dense polynomials

The certificate in this module is stated directly in terms of the executable
Horner evaluator.  It neither maps to sparse polynomials nor derives
coefficient equality from evaluation over an infinite carrier.
-/

namespace RFAP.ComputableGCD

open RFAP.ComputablePolynomial
open RFAP.ComputablePolynomial.DensePolynomial

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

abbrev Polynomial (K : Type*) := DensePolynomial K

/-- Output of finite extended Euclid, with the three identities needed by
root and common-factor arguments exposed pointwise through Horner evaluation. -/
structure BezoutResult (p q : Polynomial K) where
  gcd : Polynomial K
  normalized : gcd.normalize = gcd
  degreeLeLeft : p.isZero = false → gcd.natDegree ≤ p.natDegree
  degreeLeRight : q.isZero = false → gcd.natDegree ≤ q.natDegree
  left : Polynomial K
  right : Polynomial K
  pFactor : Polynomial K
  pFactorNormalized : pFactor.normalize = pFactor
  qFactor : Polynomial K
  qFactorNormalized : qFactor.normalize = qFactor
  factorLeft : Polynomial K
  factorRight : Polynomial K
  identity : ∀ x : K,
    gcd.eval x = left.eval x * p.eval x + right.eval x * q.eval x
  pIdentity : ∀ x : K, p.eval x = gcd.eval x * pFactor.eval x
  qIdentity : ∀ x : K, q.eval x = gcd.eval x * qFactor.eval x
  factorIdentity : ∀ x : K,
    1 = factorLeft.eval x * pFactor.eval x +
      factorRight.eval x * qFactor.eval x
  nonzero : p.isZero = false ∨ q.isZero = false → gcd.isZero = false

/-- Terminal certificate when the right input is the zero polynomial. -/
private def zeroRightResult (p q : Polynomial K) (qZero : q.isZero = true) :
    BezoutResult p q :=
  { gcd := p.normalize
    normalized := normalize_normalize p
    degreeLeLeft := by
      intro _
      simp only [natDegree_normalize]
      exact le_rfl
    degreeLeRight := by
      intro qNonzero
      rw [qZero] at qNonzero
      exact Bool.noConfusion qNonzero
    left := constant 1
    right := 0
    pFactor := (constant 1).normalize
    pFactorNormalized := normalize_normalize _
    qFactor := 0
    qFactorNormalized := normalize_zero
    factorLeft := constant 1
    factorRight := 0
    identity := by
      intro x
      simp only [eval_normalize, eval_constant, eval_zero, one_mul, zero_mul,
        add_zero]
    pIdentity := by
      intro x
      simp only [eval_normalize, eval_constant, mul_one]
    qIdentity := by
      intro x
      rw [eval_eq_zero_of_isZero qZero]
      simp only [eval_normalize, eval_zero, mul_zero]
    factorIdentity := by
      intro x
      simp only [eval_normalize, eval_constant, eval_zero, one_mul, zero_mul,
        add_zero]
    nonzero := by
      intro inputsNonzero
      have pNonzero : p.isZero = false := by
        rcases inputsNonzero with pNonzero | qNonzero
        · exact pNonzero
        · rw [qZero] at qNonzero
          exact Bool.noConfusion qNonzero
      change p.normalize.isZero = false
      exact (isZero_normalize p).trans pNonzero }

/-- Extended Euclid with an explicit natural fuel certificate.  Recursive
calls consume one unit of fuel, while the strict remainder-degree theorem
shows that the remaining coefficient count still fits.  Keeping this finite
descent structural avoids Lean's well-founded-recursion congruence proof. -/
private def extendedGCDFuel (fuel : Nat) :
    (p q : Polynomial K) → q.degreeCount ≤ fuel → BezoutResult p q := by
  induction fuel with
  | zero =>
      intro p q enough
      have qDegreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
      exact zeroRightResult p q
        (isZero_true_of_degreeCount_eq_zero qDegreeZero)
  | succ fuel recursiveCall =>
      intro p q enough
      by_cases qZero : q.isZero = true
      · exact zeroRightResult p q qZero
      · have qNonzero : q.isZero = false :=
          Bool.eq_false_of_not_eq_true qZero
        let dm := divMod p q
        have remainderBound : dm.remainder.degreeCount ≤ fuel := by
          apply Nat.le_of_lt_succ
          exact (divMod_remainder_degreeCount_lt p q qNonzero).trans_le enough
        let recursiveResult := recursiveCall q dm.remainder remainderBound
        exact
          { gcd := recursiveResult.gcd
            normalized := recursiveResult.normalized
            degreeLeLeft := by
              intro pNonzero
              by_cases remainderZero : dm.remainder.isZero = true
              · have qDegreeLe : q.natDegree ≤ p.natDegree := by
                  by_cases pSmaller : p.natDegree < q.natDegree
                  · have remainderEq : dm.remainder = p.normalize :=
                      (divMod_of_natDegree_lt (p := p) (q := q) pSmaller).2
                    have normalizedNonzero : p.normalize.isZero = false := by
                      exact (isZero_normalize p).trans pNonzero
                    have remainderNonzero : dm.remainder.isZero = false := by
                      exact (congrArg
                        (fun polynomial : Polynomial K => polynomial.isZero)
                        remainderEq).trans normalizedNonzero
                    rw [remainderZero] at remainderNonzero
                    exact Bool.noConfusion remainderNonzero
                  · exact Nat.le_of_not_gt pSmaller
                exact (recursiveResult.degreeLeLeft qNonzero).trans qDegreeLe
              · have remainderNonzero : dm.remainder.isZero = false :=
                    Bool.eq_false_of_not_eq_true remainderZero
                have remainderCountLe :
                    dm.remainder.degreeCount ≤ p.degreeCount := by
                  exact divMod_remainder_degreeCount_le p q
                have remainderCount :=
                  natDegree_add_one_eq_degreeCount remainderNonzero
                have pCount := natDegree_add_one_eq_degreeCount pNonzero
                exact (recursiveResult.degreeLeRight remainderNonzero).trans (by
                  omega)
            degreeLeRight := by
              intro qNonzeroProof
              exact recursiveResult.degreeLeLeft qNonzeroProof
            left := recursiveResult.right
            right := recursiveResult.left - recursiveResult.right * dm.quotient
            pFactor := recursiveResult.qFactor +
              recursiveResult.pFactor * dm.quotient
            pFactorNormalized := normalize_add _ _
            qFactor := recursiveResult.pFactor
            qFactorNormalized := recursiveResult.pFactorNormalized
            factorLeft := recursiveResult.factorRight
            factorRight := recursiveResult.factorLeft -
              recursiveResult.factorRight * dm.quotient
            identity := by
              intro x
              rw [eval_sub, eval_mul]
              calc
                recursiveResult.gcd.eval x =
                    recursiveResult.left.eval x * q.eval x +
                      recursiveResult.right.eval x * dm.remainder.eval x :=
                  recursiveResult.identity x
                _ = recursiveResult.right.eval x * p.eval x +
                    (recursiveResult.left.eval x -
                      recursiveResult.right.eval x * dm.quotient.eval x) *
                      q.eval x := by
                  rw [← divMod_eval_equation p q x]
                  ring1
            pIdentity := by
              intro x
              rw [eval_add, eval_mul, ← divMod_eval_equation p q x,
                recursiveResult.pIdentity x, recursiveResult.qIdentity x]
              ring1
            qIdentity := recursiveResult.pIdentity
            factorIdentity := by
              intro x
              rw [eval_add, eval_mul, eval_sub, eval_mul]
              calc
                1 = recursiveResult.factorLeft.eval x *
                      recursiveResult.pFactor.eval x +
                    recursiveResult.factorRight.eval x *
                      recursiveResult.qFactor.eval x :=
                  recursiveResult.factorIdentity x
                _ = recursiveResult.factorRight.eval x *
                      (recursiveResult.qFactor.eval x +
                        recursiveResult.pFactor.eval x * dm.quotient.eval x) +
                    (recursiveResult.factorLeft.eval x -
                      recursiveResult.factorRight.eval x * dm.quotient.eval x) *
                      recursiveResult.pFactor.eval x := by ring1
            nonzero := by
              intro _
              apply recursiveResult.nonzero
              exact Or.inl qNonzero }

/-- Extended Euclid driven by the finite coefficient count of its right
input. -/
@[irreducible] def extendedGCD (p q : Polynomial K) : BezoutResult p q :=
  extendedGCDFuel q.degreeCount p q le_rfl

def gcd (p q : Polynomial K) : Polynomial K := (extendedGCD p q).gcd

def leftCoefficient (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).left

def rightCoefficient (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).right

def leftFactor (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).pFactor

def rightFactor (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).qFactor

def factorLeftCoefficient (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).factorLeft

def factorRightCoefficient (p q : Polynomial K) : Polynomial K :=
  (extendedGCD p q).factorRight

theorem gcd_eval_identity (p q : Polynomial K) (x : K) :
    (gcd p q).eval x =
      (leftCoefficient p q).eval x * p.eval x +
        (rightCoefficient p q).eval x * q.eval x :=
  (extendedGCD p q).identity x

theorem leftFactor_eval_identity (p q : Polynomial K) (x : K) :
    p.eval x = (gcd p q).eval x * (leftFactor p q).eval x :=
  (extendedGCD p q).pIdentity x

theorem rightFactor_eval_identity (p q : Polynomial K) (x : K) :
    q.eval x = (gcd p q).eval x * (rightFactor p q).eval x :=
  (extendedGCD p q).qIdentity x

theorem reducedFactors_eval_identity (p q : Polynomial K) (x : K) :
    1 = (factorLeftCoefficient p q).eval x * (leftFactor p q).eval x +
      (factorRightCoefficient p q).eval x * (rightFactor p q).eval x :=
  (extendedGCD p q).factorIdentity x

theorem gcd_isZero_false {p q : Polynomial K}
    (hnonzero : p.isZero = false ∨ q.isZero = false) :
    (gcd p q).isZero = false :=
  (extendedGCD p q).nonzero hnonzero

end RFAP.ComputableGCD
