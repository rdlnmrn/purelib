module

-- The exposed Euclidean builder retains this Boolean proof certificate.
public import Purelib.Data.Bool.Decide

import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
-- Existing public consumers use the retained order transport API through this owner.
public import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite extended Euclid for dense polynomials

The certificate in this module is stated directly in terms of the executable
Horner evaluator.  It neither maps to sparse polynomials nor derives
coefficient equality from evaluation over an infinite carrier.
-/

namespace Purelib.Polynomial.Dense.GCD

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Data.Bool

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The descending dense polynomial representation used by the finite Euclidean algorithm. -/
public abbrev CoefficientPolynomial (K : Type*) := DensePolynomial K

set_option genInjectivity false in
/-- Output of finite extended Euclid, with the three identities needed by
root and common-factor arguments exposed pointwise through Horner evaluation.

The original common factor and two original cofactors retain normalization, degree and nonzero certificates. Their
ordered coefficient polynomials certify both input factorizations and the same unit Bezout combination of the retained
cofactors. -/
public structure BezoutResult (p q : CoefficientPolynomial K) where
  /-- The normalized polynomial common factor retained by the algorithm. -/ gcd : CoefficientPolynomial K
  /-- The retained common factor is already normalized. -/ normalized : gcd.normalize = gcd
  /-- A nonzero left input bounds the natural degree of the common factor. -/ degreeLeLeft : p.isZero = false →
    gcd.natDegree ≤ p.natDegree
  /-- A nonzero right input bounds the natural degree of the common factor. -/ degreeLeRight : q.isZero = false →
    gcd.natDegree ≤ q.natDegree
  /-- The coefficient multiplying the left input in the common-factor identity. -/ left : CoefficientPolynomial K
  /-- The coefficient multiplying the right input in the common-factor identity. -/ right : CoefficientPolynomial K
  /-- The retained cofactor of the left input. -/ pFactor : CoefficientPolynomial K
  /-- The retained left cofactor is already normalized. -/ pFactorNormalized : pFactor.normalize = pFactor
  /-- The retained cofactor of the right input. -/ qFactor : CoefficientPolynomial K
  /-- The retained right cofactor is already normalized. -/ qFactorNormalized : qFactor.normalize = qFactor
  /-- The coefficient multiplying the left cofactor in their unit Bezout identity. -/ factorLeft :
    CoefficientPolynomial K
  /-- The coefficient multiplying the right cofactor in their unit Bezout identity. -/ factorRight :
    CoefficientPolynomial K
  /-- At each point, the common factor is the retained linear combination of the input polynomials. -/ identity : ∀ x :
    K,
    gcd.eval x = left.eval x * p.eval x + right.eval x * q.eval x
  /-- At each point, the left input factors through the retained common factor and left cofactor. -/ pIdentity : ∀ x :
    K, p.eval x = gcd.eval x * pFactor.eval x
  /-- At each point, the right input factors through the retained common factor and right cofactor. -/ qIdentity : ∀ x :
    K, q.eval x = gcd.eval x * qFactor.eval x
  /-- At each point, the displayed combination of the two cofactors equals one. -/ factorIdentity : ∀ x : K,
    1 = factorLeft.eval x * pFactor.eval x +
      factorRight.eval x * qFactor.eval x
  /-- At least one nonzero input forces the retained common factor to be nonzero. -/ nonzero : p.isZero = false ∨
    q.isZero = false → gcd.isZero = false

constructive_injectivity BezoutResult

namespace BezoutResult.mk

end BezoutResult.mk

namespace BezoutResult.mk

end BezoutResult.mk

/-- Extended Euclid driven by the finite coefficient count of its right
input.

The original normalized terminal record is retained when the right input is zero. Otherwise the original completed
division record supplies its retained remainder to the predecessor-fuel run, and the same quotient transports the
completed factors and ordered Bezout coefficients. -/
@[expose, irreducible] public def extendedGCD (p q : CoefficientPolynomial K) : BezoutResult p q := by
  let zeroResult (p q : CoefficientPolynomial K) (qZero : q.isZero = true) :
      BezoutResult p q :=
    { gcd := p.normalize
      normalized := DensePolynomial.normalize_normalize p
      degreeLeLeft := by
        intro _
        rewrite [DensePolynomial.natDegree_normalize]
        exact Nat.le_refl _
      degreeLeRight := by
        intro qNonzero
        rw [qZero] at qNonzero
        exact Bool.noConfusion qNonzero
      left := DensePolynomial.constant 1
      right := 0
      pFactor := (DensePolynomial.constant 1).normalize
      pFactorNormalized := DensePolynomial.normalize_normalize _
      qFactor := 0
      qFactorNormalized := DensePolynomial.normalize_zero
      factorLeft := DensePolynomial.constant 1
      factorRight := 0
      identity := by
        intro x
        rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_constant,
          DensePolynomial.eval_zero, one_mul, zero_mul, add_zero]
        exact Eq.refl _
      pIdentity := by
        intro x
        rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_normalize,
          DensePolynomial.eval_constant, mul_one]
        exact Eq.refl _
      qIdentity := by
        intro x
        rewrite [DensePolynomial.eval_eq_zero_of_isZero qZero,
          DensePolynomial.eval_normalize, DensePolynomial.eval_zero, mul_zero]
        exact Eq.refl _
      factorIdentity := by
        intro x
        rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_constant,
          DensePolynomial.eval_zero, one_mul, zero_mul, add_zero]
        exact Eq.refl _
      nonzero := by
        intro inputsNonzero
        have pNonzero : p.isZero = false := by
          rcases inputsNonzero with pNonzero | qNonzero
          · exact pNonzero
          · rw [qZero] at qNonzero
            exact Bool.noConfusion qNonzero
        change p.normalize.isZero = false
        exact (DensePolynomial.isZero_normalize p).trans pNonzero }
  let fuelResult : (fuel : Nat) →
      (left right : CoefficientPolynomial K) → right.degreeCount ≤ fuel →
        BezoutResult left right := fun fuel => by
      induction fuel with
      | zero =>
          intro p q enough
          have qDegreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
          exact zeroResult p q
            (DensePolynomial.isZero_true_of_degreeCount_eq_zero qDegreeZero)
      | succ fuel recursiveCall =>
          intro p q enough
          by_cases qZero : q.isZero = true
          · exact zeroResult p q qZero
          · have qNonzero : q.isZero = false :=
              Decide.bool_eq_false_of_not_eq_true q.isZero qZero
            let dm := DensePolynomial.divMod p q
            have remainderBound : dm.remainder.degreeCount ≤ fuel := by
              apply Nat.le_of_lt_succ
              exact Nat.lt_of_lt_of_le
                (DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero) enough
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
                          (DensePolynomial.divMod_of_natDegree_lt (p := p) (q := q) pSmaller).2
                        have normalizedNonzero : p.normalize.isZero = false := by
                          exact (DensePolynomial.isZero_normalize p).trans pNonzero
                        have remainderNonzero : dm.remainder.isZero = false := by
                          exact (congrArg
                            (fun polynomial : CoefficientPolynomial K => polynomial.isZero)
                            remainderEq).trans normalizedNonzero
                        rw [remainderZero] at remainderNonzero
                        exact Bool.noConfusion remainderNonzero
                      · exact Nat.le_of_not_gt pSmaller
                    exact (recursiveResult.degreeLeLeft qNonzero).trans qDegreeLe
                  · have remainderNonzero : dm.remainder.isZero = false :=
                        Decide.bool_eq_false_of_not_eq_true dm.remainder.isZero remainderZero
                    have remainderCountLe :
                        dm.remainder.degreeCount ≤ p.degreeCount := by
                      exact DensePolynomial.divMod_remainder_degreeCount_le p q
                    have remainderCount :=
                      DensePolynomial.natDegree_add_one_eq_degreeCount remainderNonzero
                    have pCount := DensePolynomial.natDegree_add_one_eq_degreeCount pNonzero
                    have degreeLe : dm.remainder.natDegree ≤ p.natDegree := by
                      rewrite [← remainderCount, ← pCount] at remainderCountLe
                      exact Nat.le_of_succ_le_succ remainderCountLe
                    exact (recursiveResult.degreeLeRight remainderNonzero).trans degreeLe
                degreeLeRight := by
                  intro qNonzeroProof
                  exact recursiveResult.degreeLeLeft qNonzeroProof
                left := recursiveResult.right
                right := recursiveResult.left - recursiveResult.right * dm.quotient
                pFactor := recursiveResult.qFactor +
                  recursiveResult.pFactor * dm.quotient
                pFactorNormalized := DensePolynomial.normalize_add _ _
                qFactor := recursiveResult.pFactor
                qFactorNormalized := recursiveResult.pFactorNormalized
                factorLeft := recursiveResult.factorRight
                factorRight := recursiveResult.factorLeft -
                  recursiveResult.factorRight * dm.quotient
                identity := by
                  intro x
                  rw [DensePolynomial.eval_sub, DensePolynomial.eval_mul]
                  calc
                    recursiveResult.gcd.eval x =
                        recursiveResult.left.eval x * q.eval x +
                          recursiveResult.right.eval x * dm.remainder.eval x :=
                      recursiveResult.identity x
                    _ = recursiveResult.right.eval x * p.eval x +
                        (recursiveResult.left.eval x -
                          recursiveResult.right.eval x * dm.quotient.eval x) *
                          q.eval x := by
                      rw [← DensePolynomial.divMod_eval_equation p q x]
                      ring1
                pIdentity := by
                  intro x
                  rw [DensePolynomial.eval_add, DensePolynomial.eval_mul, ← DensePolynomial.divMod_eval_equation p q x,
                    recursiveResult.pIdentity x, recursiveResult.qIdentity x]
                  ring1
                qIdentity := recursiveResult.pIdentity
                factorIdentity := by
                  intro x
                  rw [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_sub,
                    DensePolynomial.eval_mul]
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
  exact fuelResult q.degreeCount p q (Nat.le_refl _)

/-- Return the normalized common factor retained by the executable extended Euclidean algorithm. -/
@[expose] public def gcd (p q : CoefficientPolynomial K) : CoefficientPolynomial K := (extendedGCD p q).gcd

/-- Return the coefficient of the left input in the retained Bezout identity. -/
@[expose] public def leftCoefficient (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).left

/-- Return the coefficient of the right input in the retained Bezout identity. -/
@[expose] public def rightCoefficient (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).right

/-- Return the retained cofactor expressing the left input as the common factor times this polynomial. -/
@[expose] public def leftFactor (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).pFactor

/-- Return the retained cofactor expressing the right input as the common factor times this polynomial. -/
@[expose] public def rightFactor (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).qFactor

/-- Return the left coefficient in the retained Bezout identity for the two cofactors. -/
@[expose] public def factorLeftCoefficient (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).factorLeft

/-- Return the right coefficient in the retained Bezout identity for the two cofactors. -/
@[expose] public def factorRightCoefficient (p q : CoefficientPolynomial K) : CoefficientPolynomial K :=
  (extendedGCD p q).factorRight

/-- The retained common-factor value is the displayed linear combination of the two input values. -/
public theorem gcd_eval_identity (p q : CoefficientPolynomial K) (x : K) :
    (gcd p q).eval x =
      (leftCoefficient p q).eval x * p.eval x +
        (rightCoefficient p q).eval x * q.eval x :=
  (extendedGCD p q).identity x

/-- The left input evaluates as the retained common factor times its retained cofactor. -/
public theorem leftFactor_eval_identity (p q : CoefficientPolynomial K) (x : K) :
    p.eval x = (gcd p q).eval x * (leftFactor p q).eval x :=
  (extendedGCD p q).pIdentity x

/-- The right input evaluates as the retained common factor times its retained cofactor. -/
public theorem rightFactor_eval_identity (p q : CoefficientPolynomial K) (x : K) :
    q.eval x = (gcd p q).eval x * (rightFactor p q).eval x :=
  (extendedGCD p q).qIdentity x

/-- The retained cofactors have a displayed pointwise Bezout combination equal to one. -/
public theorem reducedFactors_eval_identity (p q : CoefficientPolynomial K) (x : K) :
    1 = (factorLeftCoefficient p q).eval x * (leftFactor p q).eval x +
      (factorRightCoefficient p q).eval x * (rightFactor p q).eval x :=
  (extendedGCD p q).factorIdentity x

/-- The retained common factor is nonzero whenever at least one input is represented as nonzero. -/
public theorem gcd_isZero_false {p q : CoefficientPolynomial K}
    (hnonzero : p.isZero = false ∨ q.isZero = false) :
    (gcd p q).isZero = false :=
  (extendedGCD p q).nonzero hnonzero

end Purelib.Polynomial.Dense.GCD
