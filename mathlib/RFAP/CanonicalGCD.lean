import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import mathlib.Tactic.QuotientFreeOmega

/-!
# Structurally recursive certified greatest common divisors

This module supplies the finite arithmetic certificate needed by the
quotient-free rational carrier.  Its Euclidean algorithm recurses on an
explicit natural-number fuel argument.  In particular, its correctness proof
does not use the well-founded-recursion equation theorem through which the
upstream `Nat.gcd` proof API currently acquires `Quot.sound`.
-/

namespace RFAP.CanonicalGCD

/-- The computational output of the extended Euclidean algorithm. -/
structure Result where
  gcd : Nat
  left : Int
  right : Int
deriving DecidableEq

/-- One structurally recursive run of the extended Euclidean algorithm.

The correctness theorem below requires `rightInput < fuel`.  The otherwise
unreachable zero-fuel branch returns the left input so that the definition is
total and executable on every input. -/
def computeAux : Nat → Nat → Nat → Result
  | 0, leftInput, _ => ⟨leftInput, 1, 0⟩
  | _ + 1, leftInput, 0 => ⟨leftInput, 1, 0⟩
  | fuel + 1, leftInput, rightInput + 1 =>
      let previous :=
        computeAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
      ⟨previous.gcd, previous.right,
        previous.left - (leftInput / (rightInput + 1) : Nat) * previous.right⟩

/-- Tail-recursive extended Euclidean execution.  The two coefficient pairs
express the current left and right remainders in terms of the original
inputs.  Unlike `computeAux`, no result is rebuilt while recursion unwinds,
so exact normalization of large finite rationals uses constant call stack. -/
def computeTailAux : Nat -> Nat -> Nat -> Int -> Int -> Int -> Int -> Result
  | 0, leftInput, _rightInput, leftLeft, leftRight, _rightLeft, _rightRight =>
      ⟨leftInput, leftLeft, leftRight⟩
  | _fuel + 1, leftInput, 0, leftLeft, leftRight, _rightLeft, _rightRight =>
      ⟨leftInput, leftLeft, leftRight⟩
  | fuel + 1, leftInput, rightInput + 1,
      leftLeft, leftRight, rightLeft, rightRight =>
      let quotient := leftInput / (rightInput + 1)
      computeTailAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
        rightLeft rightRight
        (leftLeft - (quotient : Int) * rightLeft)
        (leftRight - (quotient : Int) * rightRight)

/-- The extended Euclidean result for two natural inputs. -/
def compute (leftInput rightInput : Nat) : Result :=
  computeTailAux (rightInput + 1) leftInput rightInput 1 0 0 1

/-- A Bézout certificate for coprimality.  Unlike `Nat.Coprime`, the
certificate stores the finite integer coefficients used by later
calculations. -/
structure CoprimeCertificate (leftInput rightInput : Nat) where
  left : Int
  right : Int
  identity : left * (leftInput : Int) + right * (rightInput : Int) = 1

theorem computeAux_spec (fuel leftInput rightInput : Nat)
    (enoughFuel : rightInput < fuel) :
    let result := computeAux fuel leftInput rightInput
    (result.gcd : Int) =
        result.left * (leftInput : Int) +
          result.right * (rightInput : Int) ∧
      result.gcd ∣ leftInput ∧ result.gcd ∣ rightInput := by
  induction fuel generalizing leftInput rightInput with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          change
            (leftInput : Int) =
                1 * (leftInput : Int) + 0 * (0 : Int) ∧
              leftInput ∣ leftInput ∧ leftInput ∣ 0
          exact
            ⟨by simp only [one_mul, zero_mul, add_zero],
              Nat.dvd_refl leftInput, Nat.dvd_zero leftInput⟩
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 ≤ fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          have previousSpec := inductionHypothesis
            (rightInput + 1) (leftInput % (rightInput + 1))
            remainderBelowFuel
          let previous :=
            computeAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
          have previousIdentity :
              (previous.gcd : Int) =
                previous.left * ((rightInput + 1 : Nat) : Int) +
                  previous.right *
                    ((leftInput % (rightInput + 1) : Nat) : Int) :=
            previousSpec.1
          have divisionIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) +
                  ((rightInput + 1 : Nat) : Int) *
                    ((leftInput / (rightInput + 1) : Nat) : Int) =
                (leftInput : Int) := by
            have naturalIdentity :=
              congrArg (fun value : Nat => (value : Int))
                (Nat.mod_add_div leftInput (rightInput + 1))
            simpa only [Int.natCast_add, Int.natCast_mul] using naturalIdentity
          have currentIdentity :
              (previous.gcd : Int) =
                previous.right * (leftInput : Int) +
                  (previous.left -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      previous.right) *
                    ((rightInput + 1 : Nat) : Int) := by
            rw [previousIdentity]
            have productCommutes :
                previous.right *
                    (((rightInput + 1 : Nat) : Int) *
                      ((leftInput / (rightInput + 1) : Nat) : Int)) =
                  (((leftInput / (rightInput + 1) : Nat) : Int) *
                    previous.right) * ((rightInput + 1 : Nat) : Int) := by
              simp only [mul_assoc, mul_comm]
            have productCancels :
                (((leftInput / (rightInput + 1) : Nat) : Int) *
                    previous.right) * ((rightInput + 1 : Nat) : Int) +
                    (previous.left * ((rightInput + 1 : Nat) : Int) -
                      (((leftInput / (rightInput + 1) : Nat) : Int) *
                        previous.right) *
                        ((rightInput + 1 : Nat) : Int)) =
                  previous.left * ((rightInput + 1 : Nat) : Int) := by
              rw [sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero]
            calc
              previous.left * ((rightInput + 1 : Nat) : Int) +
                    previous.right *
                      ((leftInput % (rightInput + 1) : Nat) : Int) =
                  previous.right *
                      (((leftInput % (rightInput + 1) : Nat) : Int) +
                        ((rightInput + 1 : Nat) : Int) *
                          ((leftInput / (rightInput + 1) : Nat) : Int)) +
                    (previous.left -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        previous.right) *
                      ((rightInput + 1 : Nat) : Int) := by
                        rw [mul_add, sub_mul, productCommutes]
                        calc
                          previous.left * ((rightInput + 1 : Nat) : Int) +
                                previous.right *
                                  ((leftInput % (rightInput + 1) : Nat) : Int) =
                              previous.right *
                                  ((leftInput % (rightInput + 1) : Nat) : Int) +
                                previous.left *
                                  ((rightInput + 1 : Nat) : Int) :=
                            add_comm _ _
                          _ = previous.right *
                                  ((leftInput % (rightInput + 1) : Nat) : Int) +
                                ((((leftInput / (rightInput + 1) : Nat) : Int) *
                                      previous.right) *
                                    ((rightInput + 1 : Nat) : Int) +
                                  (previous.left *
                                      ((rightInput + 1 : Nat) : Int) -
                                    (((leftInput / (rightInput + 1) : Nat) : Int) *
                                      previous.right) *
                                      ((rightInput + 1 : Nat) : Int))) := by
                            rw [productCancels]
                          _ = (previous.right *
                                  ((leftInput % (rightInput + 1) : Nat) : Int) +
                                (((leftInput / (rightInput + 1) : Nat) : Int) *
                                  previous.right) *
                                  ((rightInput + 1 : Nat) : Int)) +
                              (previous.left *
                                  ((rightInput + 1 : Nat) : Int) -
                                (((leftInput / (rightInput + 1) : Nat) : Int) *
                                  previous.right) *
                                  ((rightInput + 1 : Nat) : Int)) :=
                            (add_assoc _ _ _).symm
              _ = previous.right * (leftInput : Int) +
                    (previous.left -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        previous.right) *
                      ((rightInput + 1 : Nat) : Int) := by
                    rw [divisionIdentity]
          have dividesLeftInput : previous.gcd ∣ leftInput := by
            have dividesProduct :
                previous.gcd ∣
                  (rightInput + 1) * (leftInput / (rightInput + 1)) :=
              Nat.dvd_mul_right_of_dvd previousSpec.2.1 _
            have dividesSum :
                previous.gcd ∣
                  leftInput % (rightInput + 1) +
                    (rightInput + 1) * (leftInput / (rightInput + 1)) :=
              Nat.dvd_add previousSpec.2.2 dividesProduct
            rw [Nat.mod_add_div] at dividesSum
            exact dividesSum
          change
            (previous.gcd : Int) =
                previous.right * (leftInput : Int) +
                  (previous.left -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      previous.right) *
                    ((rightInput + 1 : Nat) : Int) ∧
              previous.gcd ∣ leftInput ∧ previous.gcd ∣ rightInput + 1
          exact ⟨currentIdentity, dividesLeftInput, previousSpec.2.1⟩

/-- The tail-recursive coefficient state retains its displayed linear
combination of the two original inputs. -/
theorem computeTailAux_identity (fuel leftInput rightInput : Nat)
    (leftLeft leftRight rightLeft rightRight : Int)
    (originalLeft originalRight : Nat)
    (enoughFuel : rightInput < fuel)
    (leftIdentity : (leftInput : Int) =
      leftLeft * (originalLeft : Int) +
        leftRight * (originalRight : Int))
    (rightIdentity : (rightInput : Int) =
      rightLeft * (originalLeft : Int) +
        rightRight * (originalRight : Int)) :
    let result := computeTailAux fuel leftInput rightInput leftLeft leftRight
      rightLeft rightRight
    (result.gcd : Int) =
      result.left * (originalLeft : Int) +
        result.right * (originalRight : Int) := by
  induction fuel generalizing leftInput rightInput leftLeft leftRight
      rightLeft rightRight with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          change (leftInput : Int) =
            leftLeft * (originalLeft : Int) +
              leftRight * (originalRight : Int)
          exact leftIdentity
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 <= fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          have divisionIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) +
                  ((rightInput + 1 : Nat) : Int) *
                    ((leftInput / (rightInput + 1) : Nat) : Int) =
                (leftInput : Int) := by
            have naturalIdentity :=
              congrArg (fun value : Nat => (value : Int))
                (Nat.mod_add_div leftInput (rightInput + 1))
            simpa only [Int.natCast_add, Int.natCast_mul] using naturalIdentity
          have remainderIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) =
                (leftLeft -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      rightLeft) *
                    (originalLeft : Int) +
                  (leftRight -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      rightRight) *
                    (originalRight : Int) := by
            calc
              ((leftInput % (rightInput + 1) : Nat) : Int) =
                  (leftInput : Int) -
                    ((rightInput + 1 : Nat) : Int) *
                      ((leftInput / (rightInput + 1) : Nat) : Int) := by
                rw [<- divisionIdentity]
                ring1
              _ = (leftLeft -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        rightLeft) *
                      (originalLeft : Int) +
                    (leftRight -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        rightRight) *
                      (originalRight : Int) := by
                rw [leftIdentity, rightIdentity]
                ring1
          exact inductionHypothesis (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
            remainderBelowFuel rightIdentity remainderIdentity

/-- The gcd returned by the tail-recursive state divides both current
remainders, independently of the accumulated Bézout coefficients. -/
theorem computeTailAux_dvd (fuel leftInput rightInput : Nat)
    (leftLeft leftRight rightLeft rightRight : Int)
    (enoughFuel : rightInput < fuel) :
    let result := computeTailAux fuel leftInput rightInput leftLeft leftRight
      rightLeft rightRight
    result.gcd ∣ leftInput /\ result.gcd ∣ rightInput := by
  induction fuel generalizing leftInput rightInput leftLeft leftRight
      rightLeft rightRight with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          exact ⟨Nat.dvd_refl leftInput, Nat.dvd_zero leftInput⟩
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 <= fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          let result := computeTailAux fuel (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
          have recursive := inductionHypothesis (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
            remainderBelowFuel
          have dividesProduct : result.gcd ∣
              (rightInput + 1) * (leftInput / (rightInput + 1)) :=
            Nat.dvd_mul_right_of_dvd recursive.1 _
          have dividesLeft : result.gcd ∣ leftInput := by
            have dividesSum := Nat.dvd_add recursive.2 dividesProduct
            rw [Nat.mod_add_div] at dividesSum
            exact dividesSum
          exact ⟨dividesLeft, recursive.1⟩

theorem compute_spec (leftInput rightInput : Nat) :
    let result := compute leftInput rightInput
    (result.gcd : Int) =
        result.left * (leftInput : Int) +
          result.right * (rightInput : Int) ∧
      result.gcd ∣ leftInput ∧ result.gcd ∣ rightInput :=
  by
    let result := compute leftInput rightInput
    have identity := computeTailAux_identity (rightInput + 1) leftInput
      rightInput 1 0 0 1 leftInput rightInput
      (Nat.lt_succ_self rightInput) (by ring1) (by ring1)
    have divides := computeTailAux_dvd (rightInput + 1) leftInput rightInput
      1 0 0 1 (Nat.lt_succ_self rightInput)
    exact ⟨identity, divides⟩

theorem compute_gcd_positive_right (leftInput : Nat) {rightInput : Nat}
    (rightPositive : 0 < rightInput) :
    0 < (compute leftInput rightInput).gcd :=
  Nat.pos_of_dvd_of_pos (compute_spec leftInput rightInput).2.2 rightPositive

/-- Every displayed common divisor divides the computed Euclidean result.
The explicit Bézout coefficients are the certificate; no property of
upstream `Nat.gcd` is used. -/
theorem commonDivisor_dvd_compute_gcd
    (leftInput rightInput commonDivisor : Nat)
    (dividesLeft : commonDivisor ∣ leftInput)
    (dividesRight : commonDivisor ∣ rightInput) :
    commonDivisor ∣ (compute leftInput rightInput).gcd := by
  let result := compute leftInput rightInput
  have specification := compute_spec leftInput rightInput
  have castDividesLeft : (commonDivisor : Int) ∣ (leftInput : Int) := by
    rw [Int.ofNat_dvd]
    exact dividesLeft
  have castDividesRight : (commonDivisor : Int) ∣ (rightInput : Int) := by
    rw [Int.ofNat_dvd]
    exact dividesRight
  have dividesIdentity : (commonDivisor : Int) ∣
      result.left * (leftInput : Int) + result.right * (rightInput : Int) :=
    Int.dvd_add (dvd_mul_of_dvd_right castDividesLeft result.left)
      (dvd_mul_of_dvd_right castDividesRight result.right)
  rw [← specification.1] at dividesIdentity
  rw [← Int.ofNat_dvd]
  exact dividesIdentity

/-- The certified Euclidean result for a zero left input is the right
input.  Both inequalities are explicit divisibility certificates. -/
theorem compute_gcd_zero_left (rightInput : Nat) :
    (compute 0 rightInput).gcd = rightInput := by
  have resultDividesRight := (compute_spec 0 rightInput).2.2
  have rightDividesResult := commonDivisor_dvd_compute_gcd
    0 rightInput rightInput (Nat.dvd_zero rightInput) (Nat.dvd_refl rightInput)
  exact Nat.dvd_antisymm resultDividesRight rightDividesResult

/-- The certified Euclidean result for a zero right input is the left
input. -/
theorem compute_gcd_zero_right (leftInput : Nat) :
    (compute leftInput 0).gcd = leftInput := by
  have resultDividesLeft := (compute_spec leftInput 0).2.1
  have leftDividesResult := commonDivisor_dvd_compute_gcd
    leftInput 0 leftInput (Nat.dvd_refl leftInput) (Nat.dvd_zero leftInput)
  exact Nat.dvd_antisymm resultDividesLeft leftDividesResult

/-- Subtracting the left input from the larger right input preserves the
certified gcd. -/
theorem compute_gcd_sub_right {leftInput rightInput : Nat}
    (ordered : leftInput ≤ rightInput) :
    (compute leftInput (rightInput - leftInput)).gcd =
      (compute leftInput rightInput).gcd := by
  let reduced := compute leftInput (rightInput - leftInput)
  let whole := compute leftInput rightInput
  have reducedSpec := compute_spec leftInput (rightInput - leftInput)
  have wholeSpec := compute_spec leftInput rightInput
  have reducedDividesRight : reduced.gcd ∣ rightInput := by
    have dividesSum := Nat.dvd_add reducedSpec.2.1 reducedSpec.2.2
    have reconstructed : leftInput + (rightInput - leftInput) = rightInput := by
      omega0
    rw [reconstructed] at dividesSum
    exact dividesSum
  have reducedDividesWhole : reduced.gcd ∣ whole.gcd :=
    commonDivisor_dvd_compute_gcd leftInput rightInput reduced.gcd
      reducedSpec.2.1 reducedDividesRight
  have wholeDividesDifference : whole.gcd ∣ rightInput - leftInput :=
    Nat.dvd_sub wholeSpec.2.2 wholeSpec.2.1
  have wholeDividesReduced : whole.gcd ∣ reduced.gcd :=
    commonDivisor_dvd_compute_gcd leftInput (rightInput - leftInput)
      whole.gcd wholeSpec.2.1 wholeDividesDifference
  exact Nat.dvd_antisymm reducedDividesWhole wholeDividesReduced

/-- Subtracting the right input from the larger left input preserves the
certified gcd. -/
theorem compute_gcd_sub_left {leftInput rightInput : Nat}
    (ordered : rightInput ≤ leftInput) :
    (compute (leftInput - rightInput) rightInput).gcd =
      (compute leftInput rightInput).gcd := by
  let reduced := compute (leftInput - rightInput) rightInput
  let whole := compute leftInput rightInput
  have reducedSpec := compute_spec (leftInput - rightInput) rightInput
  have wholeSpec := compute_spec leftInput rightInput
  have reducedDividesLeft : reduced.gcd ∣ leftInput := by
    have dividesSum := Nat.dvd_add reducedSpec.2.1 reducedSpec.2.2
    have reconstructed : leftInput - rightInput + rightInput = leftInput := by
      omega0
    rw [reconstructed] at dividesSum
    exact dividesSum
  have reducedDividesWhole : reduced.gcd ∣ whole.gcd :=
    commonDivisor_dvd_compute_gcd leftInput rightInput reduced.gcd
      reducedDividesLeft reducedSpec.2.2
  have wholeDividesDifference : whole.gcd ∣ leftInput - rightInput :=
    Nat.dvd_sub wholeSpec.2.1 wholeSpec.2.2
  have wholeDividesReduced : whole.gcd ∣ reduced.gcd :=
    commonDivisor_dvd_compute_gcd (leftInput - rightInput) rightInput
      whole.gcd wholeDividesDifference wholeSpec.2.2
  exact Nat.dvd_antisymm reducedDividesWhole wholeDividesReduced

/-- Scaling both Euclidean inputs scales the computed gcd.  Both directions
are obtained from the stored divisibility and Bézout certificates. -/
theorem compute_gcd_mul_left (factor leftInput rightInput : Nat) :
    (compute (factor * leftInput) (factor * rightInput)).gcd =
      factor * (compute leftInput rightInput).gcd := by
  let base := compute leftInput rightInput
  let scaled := compute (factor * leftInput) (factor * rightInput)
  have baseSpec := compute_spec leftInput rightInput
  have scaledSpec := compute_spec
    (factor * leftInput) (factor * rightInput)
  have factorBaseDividesLeft : factor * base.gcd ∣ factor * leftInput := by
    rcases baseSpec.2.1 with ⟨leftQuotient, leftEquation⟩
    refine ⟨leftQuotient, ?_⟩
    rw [leftEquation]
    change factor * (base.gcd * leftQuotient) =
      (factor * base.gcd) * leftQuotient
    exact (Nat.mul_assoc factor base.gcd leftQuotient).symm
  have factorBaseDividesRight : factor * base.gcd ∣ factor * rightInput := by
    rcases baseSpec.2.2 with ⟨rightQuotient, rightEquation⟩
    refine ⟨rightQuotient, ?_⟩
    rw [rightEquation]
    change factor * (base.gcd * rightQuotient) =
      (factor * base.gcd) * rightQuotient
    exact (Nat.mul_assoc factor base.gcd rightQuotient).symm
  have factorBaseDividesScaled : factor * base.gcd ∣ scaled.gcd :=
    commonDivisor_dvd_compute_gcd
      (factor * leftInput) (factor * rightInput) (factor * base.gcd)
      factorBaseDividesLeft factorBaseDividesRight
  have scaledDividesFactorBase : scaled.gcd ∣ factor * base.gcd := by
    have scaledDividesLeftInt : (scaled.gcd : Int) ∣
        ((factor * leftInput : Nat) : Int) := by
      rw [Int.ofNat_dvd]
      exact scaledSpec.2.1
    have scaledDividesRightInt : (scaled.gcd : Int) ∣
        ((factor * rightInput : Nat) : Int) := by
      rw [Int.ofNat_dvd]
      exact scaledSpec.2.2
    have dividesCombination : (scaled.gcd : Int) ∣
        base.left * ((factor * leftInput : Nat) : Int) +
          base.right * ((factor * rightInput : Nat) : Int) :=
      Int.dvd_add (dvd_mul_of_dvd_right scaledDividesLeftInt base.left)
        (dvd_mul_of_dvd_right scaledDividesRightInt base.right)
    have combinationEquals :
        base.left * ((factor * leftInput : Nat) : Int) +
            base.right * ((factor * rightInput : Nat) : Int) =
          ((factor * base.gcd : Nat) : Int) := by
      calc
        base.left * ((factor * leftInput : Nat) : Int) +
              base.right * ((factor * rightInput : Nat) : Int) =
            (factor : Int) *
              (base.left * (leftInput : Int) +
                base.right * (rightInput : Int)) := by
                  simp only [Int.natCast_mul]
                  ring1
        _ = (factor : Int) * (base.gcd : Int) := by rw [← baseSpec.1]
        _ = ((factor * base.gcd : Nat) : Int) := by
          rw [Int.natCast_mul]
    rw [combinationEquals] at dividesCombination
    rw [← Int.ofNat_dvd]
    exact dividesCombination
  exact Nat.dvd_antisymm scaledDividesFactorBase factorBaseDividesScaled

/-- Dividing both inputs by the certified gcd produces an explicit Bézout
certificate for the two quotients. -/
def quotientCoprimeCertificate (leftInput : Nat) {rightInput : Nat}
    (rightPositive : 0 < rightInput) :
    CoprimeCertificate
      (leftInput / (compute leftInput rightInput).gcd)
      (rightInput / (compute leftInput rightInput).gcd) := by
  let result := compute leftInput rightInput
  have specification := compute_spec leftInput rightInput
  have gcdPositive : 0 < result.gcd :=
    compute_gcd_positive_right leftInput rightPositive
  have gcdNonzero : (result.gcd : Int) ≠ 0 := by
    intro castZero
    have gcdZero : result.gcd = 0 := Int.ofNat.inj castZero
    exact (Nat.ne_of_gt gcdPositive) gcdZero
  have leftFactorizationNat :
      leftInput / result.gcd * result.gcd = leftInput :=
    Nat.div_mul_cancel specification.2.1
  have rightFactorizationNat :
      rightInput / result.gcd * result.gcd = rightInput :=
    Nat.div_mul_cancel specification.2.2
  have leftFactorization :
      ((leftInput / result.gcd : Nat) : Int) * (result.gcd : Int) =
        (leftInput : Int) := by
    have castEquality :=
      congrArg (fun value : Nat => (value : Int)) leftFactorizationNat
    simpa only [Int.natCast_mul] using castEquality
  have rightFactorization :
      ((rightInput / result.gcd : Nat) : Int) * (result.gcd : Int) =
        (rightInput : Int) := by
    have castEquality :=
      congrArg (fun value : Nat => (value : Int)) rightFactorizationNat
    simpa only [Int.natCast_mul] using castEquality
  have factoredIdentity :
      (result.gcd : Int) =
        (result.gcd : Int) *
          (result.left * ((leftInput / result.gcd : Nat) : Int) +
            result.right * ((rightInput / result.gcd : Nat) : Int)) := by
    calc
      (result.gcd : Int) =
          result.left * (leftInput : Int) +
            result.right * (rightInput : Int) := specification.1
      _ = result.left *
              (((leftInput / result.gcd : Nat) : Int) *
                (result.gcd : Int)) +
            result.right *
              (((rightInput / result.gcd : Nat) : Int) *
                (result.gcd : Int)) := by
          rw [leftFactorization, rightFactorization]
      _ = (result.left * ((leftInput / result.gcd : Nat) : Int) +
              result.right * ((rightInput / result.gcd : Nat) : Int)) *
            (result.gcd : Int) := by
          rw [← mul_assoc, ← mul_assoc, add_mul]
      _ = (result.gcd : Int) *
            (result.left * ((leftInput / result.gcd : Nat) : Int) +
              result.right * ((rightInput / result.gcd : Nat) : Int)) :=
          mul_comm _ _
  refine ⟨result.left, result.right, ?_⟩
  apply Int.eq_of_mul_eq_mul_left gcdNonzero
  calc
    (result.gcd : Int) *
          (result.left * ((leftInput / result.gcd : Nat) : Int) +
            result.right * ((rightInput / result.gcd : Nat) : Int)) =
        (result.gcd : Int) := factoredIdentity.symm
    _ = (result.gcd : Int) * 1 := (mul_one _).symm

/-- A Bézout certificate cancels a factor on its left input. -/
theorem CoprimeCertificate.dvd_of_dvd_mul_right
    {leftInput rightInput value : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (dividesProduct : leftInput ∣ value * rightInput) :
    leftInput ∣ value := by
  have castDividesProduct :
      (leftInput : Int) ∣ (value : Int) * (rightInput : Int) := by
    rw [← Int.natCast_mul, Int.ofNat_dvd]
    exact dividesProduct
  have dividesFirstTerm :
      (leftInput : Int) ∣
        ((value : Int) * certificate.left) * (leftInput : Int) :=
    Int.dvd_mul_left _ _
  have dividesSecondTerm :
      (leftInput : Int) ∣
        certificate.right * ((value : Int) * (rightInput : Int)) :=
    dvd_mul_of_dvd_right castDividesProduct certificate.right
  have dividesSum :
      (leftInput : Int) ∣
        ((value : Int) * certificate.left) * (leftInput : Int) +
          certificate.right * ((value : Int) * (rightInput : Int)) :=
    Int.dvd_add dividesFirstTerm dividesSecondTerm
  have sumEquals :
      ((value : Int) * certificate.left) * (leftInput : Int) +
          certificate.right * ((value : Int) * (rightInput : Int)) =
        (value : Int) := by
    calc
      ((value : Int) * certificate.left) * (leftInput : Int) +
            certificate.right * ((value : Int) * (rightInput : Int)) =
          (value : Int) *
            (certificate.left * (leftInput : Int) +
              certificate.right * (rightInput : Int)) := by
          rw [mul_add]
          apply congrArg₂ (· + ·)
          · exact mul_assoc _ _ _
          · calc
              certificate.right *
                    ((value : Int) * (rightInput : Int)) =
                  (certificate.right * (value : Int)) *
                    (rightInput : Int) := (mul_assoc _ _ _).symm
              _ = ((value : Int) * certificate.right) *
                    (rightInput : Int) := by
                  rw [mul_comm certificate.right (value : Int)]
              _ = (value : Int) *
                    (certificate.right * (rightInput : Int)) :=
                  mul_assoc _ _ _
      _ = (value : Int) * 1 := by rw [certificate.identity]
      _ = (value : Int) := mul_one _
  rw [sumEquals] at dividesSum
  exact Int.ofNat_dvd.mp dividesSum

/-- Repeatedly cancel a certified coprime right factor.  This is the
power-specific form needed by the rational-root divisibility calculation and
keeps the finite Bézout certificate visible throughout the proof. -/
theorem CoprimeCertificate.dvd_of_dvd_mul_right_pow
    {leftInput rightInput value : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) :
    ∀ exponent : Nat, leftInput ∣ value * rightInput ^ exponent →
      leftInput ∣ value
  | 0 => by
      intro divides
      simpa only [pow_zero, Nat.mul_one] using divides
  | exponent + 1 => by
      intro divides
      have grouped :
          leftInput ∣ (value * rightInput ^ exponent) * rightInput := by
        simpa only [pow_succ, Nat.mul_assoc] using divides
      have previous : leftInput ∣ value * rightInput ^ exponent :=
        certificate.dvd_of_dvd_mul_right grouped
      exact certificate.dvd_of_dvd_mul_right_pow exponent previous

/-- A displayed common natural divisor of both sides of a Bézout certificate
is one. -/
theorem CoprimeCertificate.eq_one_of_dvd
    {leftInput rightInput divisor : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (dividesLeft : divisor ∣ leftInput)
    (dividesRight : divisor ∣ rightInput) : divisor = 1 := by
  have castDividesLeft : (divisor : Int) ∣ (leftInput : Int) := by
    rw [Int.ofNat_dvd]
    exact dividesLeft
  have castDividesRight : (divisor : Int) ∣ (rightInput : Int) := by
    rw [Int.ofNat_dvd]
    exact dividesRight
  have dividesFirst : (divisor : Int) ∣
      certificate.left * (leftInput : Int) :=
    dvd_mul_of_dvd_right castDividesLeft certificate.left
  have dividesSecond : (divisor : Int) ∣
      certificate.right * (rightInput : Int) :=
    dvd_mul_of_dvd_right castDividesRight certificate.right
  have dividesOneInteger : (divisor : Int) ∣ 1 := by
    rw [← certificate.identity]
    exact Int.dvd_add dividesFirst dividesSecond
  have dividesOne : divisor ∣ 1 := by
    rw [← Int.ofNat_dvd]
    exact dividesOneInteger
  exact Nat.eq_one_of_dvd_one dividesOne

/-- Swapping the two inputs swaps the two stored Bézout coefficients. -/
def CoprimeCertificate.symm {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) :
    CoprimeCertificate rightInput leftInput :=
  ⟨certificate.right, certificate.left, by
    rw [add_comm]
    exact certificate.identity⟩

/-- If the left input of a certified coprime pair is zero, the right input is
one. -/
theorem CoprimeCertificate.right_eq_one_of_left_eq_zero
    {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput)
    (leftZero : leftInput = 0) : rightInput = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [← Int.ofNat_dvd]
  refine ⟨certificate.right, ?_⟩
  have castLeftZero : (leftInput : Int) = 0 := by
    exact congrArg (fun value : Nat => (value : Int)) leftZero
  have identityZero :
      certificate.right * (rightInput : Int) = 1 := by
    calc
      certificate.right * (rightInput : Int) =
          certificate.left * (0 : Int) +
            certificate.right * (rightInput : Int) := by
              simp only [mul_zero, zero_add]
      _ = certificate.left * (leftInput : Int) +
            certificate.right * (rightInput : Int) := by rw [castLeftZero]
      _ = 1 := certificate.identity
  calc
    (1 : Int) = certificate.right * (rightInput : Int) := identityZero.symm
    _ = (rightInput : Int) * certificate.right := mul_comm _ _

end RFAP.CanonicalGCD
