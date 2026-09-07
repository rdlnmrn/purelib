import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ComputableDerivative
import mathlib.RFAP.ComputableGCD
import RFAP.Isolation.SafeCandidates

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace RFAP.SturmRootCount

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev CoprimeCertificate :=
  RFAP.PathClearance.CoprimeCertificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.Sturm

/-- Numerator after the finite Euclidean program removes the common gcd. -/
def reducedNumerator (numerator denominator : Polynomial) : Polynomial :=
  RFAP.ComputableGCD.leftFactor numerator denominator

/-- Denominator after the finite Euclidean program removes the common gcd. -/
def reducedDenominator (numerator denominator : Polynomial) : Polynomial :=
  RFAP.ComputableGCD.rightFactor numerator denominator

/-- The quotient factors returned by extended Euclid retain an explicit
Bézout identity, in denominator--numerator order. -/
def reducedPairCoprime
    (numerator denominator : Polynomial) :
    CoprimeCertificate (reducedDenominator numerator denominator)
      (reducedNumerator numerator denominator) where
  left := RFAP.ComputableGCD.factorRightCoefficient numerator denominator
  right := RFAP.ComputableGCD.factorLeftCoefficient numerator denominator
  identity := by
    intro parameter
    have identity := RFAP.ComputableGCD.reducedFactors_eval_identity
      numerator denominator parameter
    calc
      1 =
          (RFAP.ComputableGCD.factorLeftCoefficient numerator denominator).eval
              parameter *
              (reducedNumerator numerator denominator).eval parameter +
            (RFAP.ComputableGCD.factorRightCoefficient numerator denominator).eval
              parameter *
              (reducedDenominator numerator denominator).eval parameter := by
        simpa only [reducedNumerator, reducedDenominator] using identity
      _ =
          (RFAP.ComputableGCD.factorRightCoefficient numerator denominator).eval
              parameter *
              (reducedDenominator numerator denominator).eval parameter +
            (RFAP.ComputableGCD.factorLeftCoefficient numerator denominator).eval
              parameter *
              (reducedNumerator numerator denominator).eval parameter :=
        RFAP.ConstructiveFraction.add_comm _ _

/-- A finite coefficient-count search supplies one displayed nonzero value
of every represented nonzero coordinate polynomial. -/
def nonzeroParameter (p : Polynomial) (nonzero : p.isZero = false) :
    Coordinate :=
  RFAP.SafeCandidates.centralSearchValue p p.natDegree
    (a := 0) (b := 1) (by decide) nonzero (Nat.le_refl _)

theorem eval_nonzeroParameter
    (p : Polynomial) (nonzero : p.isZero = false) :
    p.eval (nonzeroParameter p nonzero) ≠ 0 :=
  (RFAP.SafeCandidates.centralSearchValue_spec p p.natDegree
    (a := 0) (b := 1) (by decide) nonzero (Nat.le_refl _)).1

/-- A nonzero original numerator has a represented nonzero reduced
numerator factor. -/
theorem reducedNumerator_isZero_false
    {numerator denominator : Polynomial}
    (nonzero : numerator.isZero = false) :
    (reducedNumerator numerator denominator).isZero = false := by
  cases factorZero : (reducedNumerator numerator denominator).isZero with
  | false => rfl
  | true =>
      let parameter := nonzeroParameter numerator nonzero
      have factorEvalZero :
          (reducedNumerator numerator denominator).eval parameter = 0 :=
        eval_eq_zero_of_isZero factorZero parameter
      have identity :=
        (RFAP.ComputableGCD.extendedGCD numerator denominator).pIdentity
          parameter
      change numerator.eval parameter =
        (RFAP.ComputableGCD.gcd numerator denominator).eval parameter *
          (reducedNumerator numerator denominator).eval parameter at identity
      rw [factorEvalZero,
        RFAP.ConstructiveFraction.mul_zero_direct] at identity
      exact (eval_nonzeroParameter numerator nonzero identity).elim

/-- A nonzero original denominator has a represented nonzero reduced
denominator factor. -/
theorem reducedDenominator_isZero_false
    {numerator denominator : Polynomial}
    (nonzero : denominator.isZero = false) :
    (reducedDenominator numerator denominator).isZero = false := by
  cases factorZero : (reducedDenominator numerator denominator).isZero with
  | false => rfl
  | true =>
      let parameter := nonzeroParameter denominator nonzero
      have factorEvalZero :
          (reducedDenominator numerator denominator).eval parameter = 0 :=
        eval_eq_zero_of_isZero factorZero parameter
      have identity :=
        (RFAP.ComputableGCD.extendedGCD numerator denominator).qIdentity
          parameter
      change denominator.eval parameter =
        (RFAP.ComputableGCD.gcd numerator denominator).eval parameter *
          (reducedDenominator numerator denominator).eval parameter at identity
      rw [factorEvalZero,
        RFAP.ConstructiveFraction.mul_zero_direct] at identity
      exact (eval_nonzeroParameter denominator nonzero identity).elim

theorem reducedDenominator_eval_ne_zero
    {numerator denominator : Polynomial} {parameter : Coordinate}
    (nonzero : denominator.eval parameter ≠ 0) :
    (reducedDenominator numerator denominator).eval parameter ≠ 0 := by
  intro factorZero
  have identity :=
    (RFAP.ComputableGCD.extendedGCD numerator denominator).qIdentity parameter
  change denominator.eval parameter =
    (RFAP.ComputableGCD.gcd numerator denominator).eval parameter *
      (reducedDenominator numerator denominator).eval parameter at identity
  rw [factorZero, RFAP.ConstructiveFraction.mul_zero_direct] at identity
  exact nonzero identity

/-- For an explicitly coprime polynomial/derivative pair, the reduced Sturm
denominator has exactly the same displayed zeros as the original
polynomial.  The reverse implication uses only the two finite factor
identities and the supplied Bézout identity. -/
theorem denominator_eval_ne_zero_of_reduced_of_coprime
    {polynomial : Polynomial} {parameter : Coordinate}
    (coprime : CoprimeCertificate polynomial
      (RFAP.ComputableDerivative.derivative polynomial))
    (reducedNonzero :
      (reducedDenominator
        (RFAP.ComputableDerivative.derivative polynomial) polynomial).eval
          parameter ≠ 0) :
    polynomial.eval parameter ≠ 0 := by
  intro polynomialZero
  have derivativeNonzero :
      (RFAP.ComputableDerivative.derivative polynomial).eval parameter ≠ 0 := by
    intro derivativeZero
    have identity := coprime.identity parameter
    rw [polynomialZero, derivativeZero,
      RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add] at identity
    exact RFAP.ConstructiveFraction.zero_ne_one identity.symm
  have gcdNonzero :
      (RFAP.ComputableGCD.gcd
        (RFAP.ComputableDerivative.derivative polynomial) polynomial).eval
          parameter ≠ 0 := by
    intro gcdZero
    have derivativeIdentity := RFAP.ComputableGCD.leftFactor_eval_identity
      (RFAP.ComputableDerivative.derivative polynomial) polynomial parameter
    rw [gcdZero, RFAP.ConstructiveFraction.zero_mul_direct]
      at derivativeIdentity
    exact derivativeNonzero derivativeIdentity
  have polynomialIdentity := RFAP.ComputableGCD.rightFactor_eval_identity
    (RFAP.ComputableDerivative.derivative polynomial) polynomial parameter
  change polynomial.eval parameter =
    (RFAP.ComputableGCD.gcd
      (RFAP.ComputableDerivative.derivative polynomial) polynomial).eval
        parameter *
      (reducedDenominator
        (RFAP.ComputableDerivative.derivative polynomial) polynomial).eval
          parameter at polynomialIdentity
  have productNonzero := RFAP.ConstructiveFraction.mul_ne_zero_direct
    gcdNonzero reducedNonzero
  exact productNonzero (polynomialIdentity.symm.trans polynomialZero)

/-- A supplied Bézout identity prevents the executable common gcd from
vanishing at any displayed coordinate. -/
theorem gcd_eval_ne_zero_of_coprime
    {numerator denominator : Polynomial} {parameter : Coordinate}
    (coprime : CoprimeCertificate denominator numerator) :
    (RFAP.ComputableGCD.gcd numerator denominator).eval parameter ≠ 0 := by
  intro gcdZero
  have numeratorIdentity := RFAP.ComputableGCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := RFAP.ComputableGCD.rightFactor_eval_identity
    numerator denominator parameter
  rw [gcdZero, RFAP.ConstructiveFraction.zero_mul_direct]
    at numeratorIdentity denominatorIdentity
  have identity := coprime.identity parameter
  rw [denominatorIdentity, numeratorIdentity,
    RFAP.ConstructiveFraction.mul_zero_direct,
    RFAP.ConstructiveFraction.mul_zero_direct,
    RFAP.ConstructiveFraction.zero_add] at identity
  exact RFAP.ConstructiveFraction.zero_ne_one identity.symm

private theorem self_mul_pos_of_ne_zero
    {value : Coordinate} (nonzero : value ≠ 0) : 0 < value * value := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · exact RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
      negative negative
  · exact RFAP.ConstructiveFraction.mul_pos_direct positive positive

/-- Removing the executable common gcd preserves a strict negative product.
The proof uses only the two displayed factor identities and the pointwise
nonvanishing supplied by finite Bézout data. -/
theorem reduced_product_neg_of_original
    {numerator denominator : Polynomial} {parameter : Coordinate}
    (coprime : CoprimeCertificate denominator numerator)
    (negative : numerator.eval parameter * denominator.eval parameter < 0) :
    (reducedNumerator numerator denominator).eval parameter *
        (reducedDenominator numerator denominator).eval parameter < 0 := by
  let gcdValue :=
    (RFAP.ComputableGCD.gcd numerator denominator).eval parameter
  let numeratorValue :=
    (reducedNumerator numerator denominator).eval parameter
  let denominatorValue :=
    (reducedDenominator numerator denominator).eval parameter
  have gcdNonzero : gcdValue ≠ 0 :=
    gcd_eval_ne_zero_of_coprime coprime
  have gcdSquarePositive : 0 < gcdValue * gcdValue :=
    self_mul_pos_of_ne_zero gcdNonzero
  have numeratorIdentity := RFAP.ComputableGCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := RFAP.ComputableGCD.rightFactor_eval_identity
    numerator denominator parameter
  have factored :
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) < 0 := by
    calc
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) =
          numerator.eval parameter * denominator.eval parameter := by
        dsimp only [gcdValue, numeratorValue, denominatorValue,
          reducedNumerator, reducedDenominator]
        rw [numeratorIdentity, denominatorIdentity]
        ring1
      _ < 0 := negative
  rcases lt_trichotomy (numeratorValue * denominatorValue) 0 with
      reducedNegative | reducedZero | reducedPositive
  · exact reducedNegative
  · rw [reducedZero, RFAP.ConstructiveFraction.mul_zero_direct] at factored
    exact (lt_irrefl 0 factored).elim
  · have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
      gcdSquarePositive reducedPositive
    exact (lt_asymm productPositive factored).elim

/-- Removing the executable common gcd likewise preserves a strict positive
product. -/
theorem reduced_product_pos_of_original
    {numerator denominator : Polynomial} {parameter : Coordinate}
    (coprime : CoprimeCertificate denominator numerator)
    (positive : 0 < numerator.eval parameter * denominator.eval parameter) :
    0 < (reducedNumerator numerator denominator).eval parameter *
      (reducedDenominator numerator denominator).eval parameter := by
  let gcdValue :=
    (RFAP.ComputableGCD.gcd numerator denominator).eval parameter
  let numeratorValue :=
    (reducedNumerator numerator denominator).eval parameter
  let denominatorValue :=
    (reducedDenominator numerator denominator).eval parameter
  have gcdNonzero : gcdValue ≠ 0 :=
    gcd_eval_ne_zero_of_coprime coprime
  have gcdSquarePositive : 0 < gcdValue * gcdValue :=
    self_mul_pos_of_ne_zero gcdNonzero
  have numeratorIdentity := RFAP.ComputableGCD.leftFactor_eval_identity
    numerator denominator parameter
  have denominatorIdentity := RFAP.ComputableGCD.rightFactor_eval_identity
    numerator denominator parameter
  have factored : 0 <
      (gcdValue * gcdValue) * (numeratorValue * denominatorValue) := by
    calc
      0 < numerator.eval parameter * denominator.eval parameter := positive
      _ = (gcdValue * gcdValue) *
          (numeratorValue * denominatorValue) := by
        dsimp only [gcdValue, numeratorValue, denominatorValue,
          reducedNumerator, reducedDenominator]
        rw [numeratorIdentity, denominatorIdentity]
        ring1
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct factored
    gcdSquarePositive.le

/-- Signed chain used by the gcd-reduced Cauchy--Sturm calculation. -/
def reducedChain (numerator denominator : Polynomial) : List Polynomial :=
  signedRemainderChain (reducedDenominator numerator denominator)
    (reducedNumerator numerator denominator)

/-- Gcd-reduced doubled Cauchy index. -/
def reducedCauchyIndex2
    (numerator denominator : Polynomial) (lower upper : Coordinate) : Int :=
  cauchyIndex2 (reducedNumerator numerator denominator)
    (reducedDenominator numerator denominator) lower upper

/-- Doubled Sturm count for the squarefree part of a displayed polynomial. -/
def sturmRootCount2 (p : Polynomial) (lower upper : Coordinate) : Int :=
  reducedCauchyIndex2 (RFAP.ComputableDerivative.derivative p) p lower upper

theorem reducedCauchyIndex2_add
    (numerator denominator : Polynomial) (lower middle upper : Coordinate) :
    reducedCauchyIndex2 numerator denominator lower upper =
      reducedCauchyIndex2 numerator denominator lower middle +
        reducedCauchyIndex2 numerator denominator middle upper :=
  cauchyIndex2_add _ _ _ _ _

theorem reducedCauchyIndex2_reverse
    (numerator denominator : Polynomial) (lower upper : Coordinate) :
    reducedCauchyIndex2 numerator denominator upper lower =
      -reducedCauchyIndex2 numerator denominator lower upper :=
  cauchyIndex2_reverse _ _ _ _

theorem sturmRootCount2_add
    (p : Polynomial) (lower middle upper : Coordinate) :
    sturmRootCount2 p lower upper =
      sturmRootCount2 p lower middle + sturmRootCount2 p middle upper :=
  reducedCauchyIndex2_add _ _ _ _ _

theorem sturmRootCount2_reverse
    (p : Polynomial) (lower upper : Coordinate) :
    sturmRootCount2 p upper lower = -sturmRootCount2 p lower upper :=
  reducedCauchyIndex2_reverse _ _ _ _

@[simp] theorem sturmRootCount2_refl
    (p : Polynomial) (parameter : Coordinate) :
    sturmRootCount2 p parameter parameter = 0 := by
  unfold sturmRootCount2 reducedCauchyIndex2
  simp only [cauchyIndex2, sub_self]

/-- At a clear endpoint of the original denominator, the reduced signed
chain has even doubled variation. -/
theorem endpointVariation2_reducedChain_even
    {numerator denominator : Polynomial}
    {parameter : Coordinate} (clear : denominator.eval parameter ≠ 0) :
    Even ((endpointVariation2 (reducedChain numerator denominator)
      parameter : Nat) : Int) := by
  have reducedDenominatorNonzero :
      (reducedDenominator numerator denominator).eval parameter ≠ 0 :=
    reducedDenominator_eval_ne_zero clear
  have coprime := (reducedPairCoprime numerator denominator).noCommonZero
  cases numeratorZero : (reducedNumerator numerator denominator).isZero with
  | true =>
      have chain : reducedChain numerator denominator =
          [reducedDenominator numerator denominator] := by
        unfold reducedChain signedRemainderChain
        rw [signedRemainderChainWF_eq]
        simp only [numeratorZero, ↓reduceIte]
      rw [chain]
      exact ⟨0, by simp [endpointVariation2]⟩
  | false =>
      have parity := endpointVariation2_sub_firstZeroFlag_even
        numeratorZero coprime parameter
      simpa only [reducedChain, reducedDenominatorNonzero,
        ↓reduceIte, sub_zero] using parity

/-- Clear rational endpoints make the doubled reduced count even. -/
theorem reducedCauchyIndex2_even
    {numerator denominator : Polynomial}
    {lower upper : Coordinate}
    (lowerClear : denominator.eval lower ≠ 0)
    (upperClear : denominator.eval upper ≠ 0) :
    Even (reducedCauchyIndex2 numerator denominator lower upper) := by
  rcases endpointVariation2_reducedChain_even lowerClear with
    ⟨left, leftEven⟩
  rcases endpointVariation2_reducedChain_even upperClear with
    ⟨right, rightEven⟩
  refine ⟨left - right, ?_⟩
  unfold reducedCauchyIndex2 cauchyIndex2
  change
    (endpointVariation2 (reducedChain numerator denominator) lower : Int) -
        endpointVariation2 (reducedChain numerator denominator) upper =
      (left - right) + (left - right)
  rw [leftEven, rightEven]
  ring1

theorem sturmRootCount2_even
    {p : Polynomial}
    {lower upper : Coordinate}
    (lowerClear : p.eval lower ≠ 0) (upperClear : p.eval upper ≠ 0) :
    Even (sturmRootCount2 p lower upper) :=
  reducedCauchyIndex2_even lowerClear upperClear

/-! ## One finite safe cut for a reduced chain -/

/-- Dense product of a finite polynomial list. -/
def polynomialProduct : List Polynomial → Polynomial
  | [] => constant 1
  | p :: polynomials => p * polynomialProduct polynomials

@[simp] theorem eval_polynomialProduct
    (polynomials : List Polynomial) (parameter : Coordinate) :
    (polynomialProduct polynomials).eval parameter =
      (polynomials.map fun p => p.eval parameter).prod := by
  induction polynomials with
  | nil => simp [polynomialProduct]
  | cons p polynomials inductionHypothesis =>
      simp [polynomialProduct, inductionHypothesis]

theorem polynomialProduct_isZero_false
    {polynomials : List Polynomial}
    (allNonzero : polynomials.Forall (fun p => p.isZero = false)) :
    (polynomialProduct polynomials).isZero = false := by
  induction polynomials with
  | nil =>
      change (constant (1 : Coordinate)).isZero = false
      change ([1].dropWhile (fun value : Coordinate => value = 0)).isEmpty =
        false
      rw [List.dropWhile_cons_of_neg (by decide)]
      rfl
  | cons p polynomials inductionHypothesis =>
      simp only [List.forall_cons] at allNonzero
      rw [polynomialProduct]
      exact isZero_mul_eq_false allNonzero.1
        (inductionHypothesis allNonzero.2)

theorem eval_ne_zero_of_mem_of_polynomialProduct
    {polynomials : List Polynomial} {p : Polynomial}
    {parameter : Coordinate} (member : p ∈ polynomials)
    (productNonzero : (polynomialProduct polynomials).eval parameter ≠ 0) :
    p.eval parameter ≠ 0 := by
  induction polynomials with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [polynomialProduct, eval_mul] at productNonzero
      have headNonzero : head.eval parameter ≠ 0 := by
        intro headZero
        apply productNonzero
        rw [headZero, RFAP.ConstructiveFraction.zero_mul_direct]
      have tailNonzero : (polynomialProduct tail).eval parameter ≠ 0 := by
        intro tailZero
        apply productNonzero
        rw [tailZero, RFAP.ConstructiveFraction.mul_zero_direct]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact headNonzero
      · exact inductionHypothesis tailMember tailNonzero

theorem reducedChain_all_nonzero
    {numerator denominator : Polynomial}
    (denominatorNonzero : denominator.isZero = false) :
    (reducedChain numerator denominator).Forall
      (fun p => p.isZero = false) := by
  have reducedDenominatorNonzero :=
    reducedDenominator_isZero_false (numerator := numerator)
      denominatorNonzero
  cases numeratorZero : (reducedNumerator numerator denominator).isZero with
  | false =>
      exact signedRemainderChain_all_nonzero
        reducedDenominatorNonzero numeratorZero
  | true =>
      have chain : reducedChain numerator denominator =
          [reducedDenominator numerator denominator] := by
        unfold reducedChain signedRemainderChain
        rw [signedRemainderChainWF_eq]
        simp only [numeratorZero, ↓reduceIte]
      rw [chain]
      simp only [List.forall_cons]
      constructor
      · exact reducedDenominatorNonzero
      · simp

/-- One guard polynomial vanishing wherever any member of the finite reduced
chain vanishes. -/
def chainGuard (numerator denominator : Polynomial) : Polynomial :=
  polynomialProduct (reducedChain numerator denominator)

theorem chainGuard_isZero_false
    {numerator denominator : Polynomial}
    (denominatorNonzero : denominator.isZero = false) :
    (chainGuard numerator denominator).isZero = false :=
  polynomialProduct_isZero_false
    (reducedChain_all_nonzero denominatorNonzero)

/-- Bounded central-third scan for a cut avoiding every reduced-chain
event. -/
def safeCut
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Interval) (proper : interval.lower < interval.upper) :
    Coordinate :=
  RFAP.SafeCandidates.centralSearchValue
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero)
    (Nat.le_refl _)

theorem safeCut_spec
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Interval) (proper : interval.lower < interval.upper) :
    (chainGuard numerator denominator).eval
        (safeCut numerator denominator denominatorNonzero
          interval proper) ≠ 0 ∧
      interval.lower <
        safeCut numerator denominator denominatorNonzero
          interval proper ∧
      safeCut numerator denominator denominatorNonzero
          interval proper < interval.upper := by
  exact RFAP.SafeCandidates.centralSearchValue_spec
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero)
    (Nat.le_refl _)

theorem safeCut_avoids_chain
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Interval) (proper : interval.lower < interval.upper)
    {member : Polynomial} (membership :
      member ∈ reducedChain numerator denominator) :
    member.eval
        (safeCut numerator denominator denominatorNonzero
          interval proper) ≠ 0 :=
  eval_ne_zero_of_mem_of_polynomialProduct membership
    (safeCut_spec numerator denominator denominatorNonzero
      interval proper).1

/-- Both children of the safe cut contract by the fixed central-third
factor, independently of coefficient degree. -/
theorem safeCut_contraction
    (numerator denominator : Polynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Interval) (proper : interval.lower < interval.upper) :
    safeCut numerator denominator denominatorNonzero interval proper -
          interval.lower <
        (2 / 3 : Coordinate) * (interval.upper - interval.lower) ∧
      interval.upper -
          safeCut numerator denominator denominatorNonzero interval proper <
        (2 / 3 : Coordinate) *
          (interval.upper - interval.lower) := by
  exact RFAP.SafeCandidates.centralSearchValue_contraction
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero) (Nat.le_refl _)

end RFAP.SturmRootCount
