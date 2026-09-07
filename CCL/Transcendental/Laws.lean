import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FiniteExp
import CCL.Transcendental.FiniteComplexLog
import CCL.Arithmetic.OperationalEquivalence

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace CCL.TranscendentalLaws

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent

open RFAP.ConstructiveGaussian.Gaussian

/-! ## The finite Horner program as a bounded Taylor polynomial -/

/-- Executable factorial used only as finite coefficient data. -/
def factorial : Nat → Nat
  | 0 => 1
  | degree + 1 => factorial degree * (degree + 1)

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl

@[simp] theorem factorial_succ (degree : Nat) :
    factorial (degree + 1) = factorial degree * (degree + 1) := rfl

theorem factorial_pos : ∀ degree : Nat, 0 < factorial degree
  | 0 => by decide
  | degree + 1 =>
      Nat.mul_pos (factorial_pos degree) (Nat.zero_lt_succ degree)

/-- Pascal's finite binomial coefficients, defined without finite-set or
cardinality machinery. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | row + 1, column + 1 =>
      choose row column + choose row (column + 1)

@[simp] theorem choose_zero_right (row : Nat) : choose row 0 = 1 := by
  cases row <;> rfl

@[simp] theorem choose_zero_succ (column : Nat) :
    choose 0 (column + 1) = 0 := rfl

@[simp] theorem choose_succ_succ (row column : Nat) :
    choose (row + 1) (column + 1) =
      choose row column + choose row (column + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {row column : Nat},
    row < column → choose row column = 0
  | _, 0, impossible => (Nat.not_lt_zero _ impossible).elim
  | 0, _ + 1, _ => rfl
  | row + 1, column + 1, order => by
      rw [choose_succ_succ,
        choose_eq_zero_of_lt (Nat.lt_of_succ_lt_succ order),
        choose_eq_zero_of_lt (Nat.lt_of_succ_lt order), Nat.zero_add]

@[simp] theorem choose_self : ∀ row : Nat, choose row row = 1
  | 0 => rfl
  | row + 1 => by
      rw [choose_succ_succ, choose_self,
        choose_eq_zero_of_lt (Nat.lt_succ_self row), Nat.add_zero]

/-- The finite factorial cancellation behind the exponential Cauchy product.
This is proved directly from Pascal recursion; no combinatorial cardinality
interpretation is used. -/
theorem choose_mul_factorials : ∀ (row column : Nat), column ≤ row →
    choose row column * factorial column * factorial (row - column) =
      factorial row
  | 0, 0, _ => rfl
  | 0, column + 1, order => (Nat.not_succ_le_zero column order).elim
  | row + 1, 0, _ => by
      simp only [choose_zero_right, factorial_zero, Nat.mul_one,
        Nat.sub_zero, Nat.one_mul]
  | row + 1, column + 1, order => by
      have columnLe : column ≤ row := Nat.le_of_succ_le_succ order
      by_cases boundary : column = row
      · subst column
        simp only [choose_self, factorial_zero, Nat.sub_self,
          Nat.mul_one, Nat.one_mul]
      · have columnLt : column < row := Nat.lt_of_le_of_ne columnLe boundary
        have successorLe : column + 1 ≤ row := columnLt
        have leftIdentity := choose_mul_factorials row column columnLe
        have rightIdentity := choose_mul_factorials row (column + 1) successorLe
        have subtractionIdentity :
            row - column = (row - (column + 1)) + 1 := by omega
        have leftTerm :
            choose row column * factorial (column + 1) *
                factorial (row - column) =
              (column + 1) * factorial row := by
          rw [factorial_succ]
          calc
            choose row column * (factorial column * (column + 1)) *
                factorial (row - column) =
                (choose row column * factorial column *
                  factorial (row - column)) * (column + 1) := by ring1
            _ = factorial row * (column + 1) := by rw [leftIdentity]
            _ = (column + 1) * factorial row := Nat.mul_comm _ _
        have rightTerm :
            choose row (column + 1) * factorial (column + 1) *
                factorial (row - column) =
              (row - column) * factorial row := by
          conv_lhs =>
            rw [subtractionIdentity, factorial_succ]
          calc
            choose row (column + 1) * factorial (column + 1) *
                (factorial (row - (column + 1)) *
                  (row - (column + 1) + 1)) =
                (choose row (column + 1) * factorial (column + 1) *
                  factorial (row - (column + 1))) *
                    (row - (column + 1) + 1) := by ring1
            _ = factorial row * (row - (column + 1) + 1) := by
              rw [rightIdentity]
            _ = factorial row * (row - column) := by
              rw [subtractionIdentity]
            _ = (row - column) * factorial row := Nat.mul_comm _ _
        rw [choose_succ_succ, Nat.succ_sub_succ_eq_sub,
          Nat.add_mul, Nat.add_mul, leftTerm, rightTerm, factorial_succ]
        calc
          (column + 1) * factorial row +
              (row - column) * factorial row =
              ((column + 1) + (row - column)) * factorial row := by
                simp only [Nat.add_mul]
          _ = (row + 1) * factorial row := by
            congr 1
            omega
          _ = factorial row * (row + 1) := Nat.mul_comm _ _

/-- Product of `count` consecutive positive-denominator factors beginning at
`denominator`. -/
def consecutiveProduct : Nat → Nat → Nat
  | _, 0 => 1
  | denominator, count + 1 =>
      denominator * consecutiveProduct (denominator + 1) count

@[simp] theorem consecutiveProduct_zero (denominator : Nat) :
    consecutiveProduct denominator 0 = 1 := rfl

@[simp] theorem consecutiveProduct_succ_head
    (denominator count : Nat) :
    consecutiveProduct denominator (count + 1) =
      denominator * consecutiveProduct (denominator + 1) count := rfl

/-- The same consecutive product, exposed from its final rather than initial
factor. -/
theorem consecutiveProduct_succ_tail (denominator : Nat) :
    ∀ count : Nat,
      consecutiveProduct denominator (count + 1) =
        consecutiveProduct denominator count * (denominator + count)
  | 0 => by simp only [consecutiveProduct_zero,
      consecutiveProduct_succ_head, Nat.add_zero, Nat.mul_one, Nat.one_mul]
  | count + 1 => by
      calc
        consecutiveProduct denominator (count + 1 + 1) =
            denominator *
              consecutiveProduct (denominator + 1) (count + 1) := rfl
        _ = denominator *
            (consecutiveProduct (denominator + 1) count *
              (denominator + 1 + count)) := by
          rw [consecutiveProduct_succ_tail (denominator + 1) count]
        _ = consecutiveProduct denominator (count + 1) *
            (denominator + (count + 1)) := by
          rw [consecutiveProduct_succ_head]
          simp only [Nat.mul_assoc]
          congr 2
          rw [Nat.add_assoc, Nat.one_add]

theorem consecutiveProduct_one_eq_factorial : ∀ degree : Nat,
    consecutiveProduct 1 degree = factorial degree
  | 0 => rfl
  | degree + 1 => by
      rw [consecutiveProduct_succ_tail, factorial_succ,
        consecutiveProduct_one_eq_factorial degree]
      congr 1
      exact Nat.one_add degree

/-- One ordinary displayed Taylor monomial `x^degree / degree!`. -/
def taylorTerm (x : Gaussian) (degree : Nat) : Gaussian :=
  CCL.FiniteExp.scale
    (1 / (factorial degree : Coordinate)) (x ^ degree)

/-- The bounded Taylor polynomial through the displayed degree. -/
def truncatedExp (x : Gaussian) : Nat → Gaussian
  | 0 => 1
  | degree + 1 => truncatedExp x degree + taylorTerm x (degree + 1)

@[simp] theorem truncatedExp_zero (x : Gaussian) : truncatedExp x 0 = 1 := rfl

@[simp] theorem truncatedExp_succ (x : Gaussian) (degree : Nat) :
    truncatedExp x (degree + 1) =
      truncatedExp x degree + taylorTerm x (degree + 1) := rfl

/-- The final nested monomial contributed by a Horner program. -/
def hornerTerm (x : Gaussian) : Nat → Nat → Gaussian
  | _, 0 => 1
  | denominator, degree + 1 =>
      CCL.FiniteExp.scale
        (1 / (denominator : Coordinate))
        (x * hornerTerm x (denominator + 1) degree)

@[simp] theorem hornerTerm_zero (x : Gaussian) (denominator : Nat) :
    hornerTerm x denominator 0 = 1 := rfl

@[simp] theorem hornerTerm_succ (x : Gaussian)
    (denominator degree : Nat) :
    hornerTerm x denominator (degree + 1) =
      CCL.FiniteExp.scale
        (1 / (denominator : Coordinate))
        (x * hornerTerm x (denominator + 1) degree) := rfl

private theorem one_div_mul_one_div (left right : Coordinate) :
    (1 / left) * (1 / right) = 1 / (left * right) := by
  calc
    (1 / left) * (1 / right) = (1 * 1) / (left * right) :=
      RFAP.ConstructiveFraction.div_mul_div_direct 1 left 1 right
    _ = 1 / (left * right) := by
      rw [RFAP.ConstructiveFraction.one_mul]

/-- The nested Horner contribution is exactly one displayed monomial with a
finite consecutive-product denominator. -/
theorem hornerTerm_eq_scaled_power (x : Gaussian) :
    ∀ (degree denominator : Nat),
      hornerTerm x denominator degree =
        CCL.FiniteExp.scale
          (1 / (consecutiveProduct denominator degree : Coordinate))
          (x ^ degree)
  | 0, denominator => by
      rw [hornerTerm_zero, consecutiveProduct_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, pow_zero, one_re, one_im] <;>
        change _ = (1 / (1 : Coordinate)) * _ <;>
        rw [show (1 / (1 : Coordinate)) = 1 by decide,
          RFAP.ConstructiveFraction.one_mul]
  | degree + 1, denominator => by
      rw [hornerTerm_succ,
        hornerTerm_eq_scaled_power x degree (denominator + 1),
        consecutiveProduct_succ_head, Nat.cast_mul, pow_succ]
      have coefficient :
          1 / ((denominator : Coordinate) *
                (consecutiveProduct (denominator + 1) degree : Coordinate)) =
            (1 / (denominator : Coordinate)) *
              (1 / (consecutiveProduct (denominator + 1) degree : Coordinate)) :=
        (one_div_mul_one_div _ _).symm
      rw [coefficient]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem hornerTerm_one_eq_taylorTerm (x : Gaussian) (degree : Nat) :
    hornerTerm x 1 degree = taylorTerm x degree := by
  rw [hornerTerm_eq_scaled_power, taylorTerm,
    consecutiveProduct_one_eq_factorial]

/-- Increasing a finite Horner depth appends exactly its final displayed
monomial. -/
theorem horner_succ_eq_add_hornerTerm (x : Gaussian) :
    ∀ (degree denominator : Nat),
      CCL.FiniteExp.horner x denominator (degree + 1) =
        CCL.FiniteExp.horner x denominator degree +
          hornerTerm x denominator (degree + 1)
  | 0, denominator => by
      rw [CCL.FiniteExp.horner_succ,
        CCL.FiniteExp.horner_zero,
        CCL.FiniteExp.horner_zero,
        CCL.FiniteExp.step_eq, hornerTerm_succ, hornerTerm_zero]
  | degree + 1, denominator => by
      calc
        CCL.FiniteExp.horner x denominator (degree + 1 + 1) =
            CCL.FiniteExp.step x denominator
              (CCL.FiniteExp.horner x (denominator + 1)
                (degree + 1)) := rfl
        _ = CCL.FiniteExp.step x denominator
              (CCL.FiniteExp.horner x (denominator + 1) degree +
                hornerTerm x (denominator + 1) (degree + 1)) := by
          rw [horner_succ_eq_add_hornerTerm x degree (denominator + 1)]
        _ = CCL.FiniteExp.step x denominator
              (CCL.FiniteExp.horner x (denominator + 1) degree) +
            hornerTerm x denominator (degree + 1 + 1) := by
          rw [CCL.FiniteExp.step_eq,
            CCL.FiniteExp.step_eq]
          change
            1 + CCL.FiniteExp.scale
                (1 / (denominator : Coordinate))
                (x * (CCL.FiniteExp.horner x
                    (denominator + 1) degree +
                  hornerTerm x (denominator + 1) (degree + 1))) =
              (1 + CCL.FiniteExp.scale
                (1 / (denominator : Coordinate))
                (x * CCL.FiniteExp.horner x
                  (denominator + 1) degree)) +
                CCL.FiniteExp.scale
                  (1 / (denominator : Coordinate))
                  (x * hornerTerm x (denominator + 1) (degree + 1))
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [CCL.FiniteExp.scale_re,
              CCL.FiniteExp.scale_im, add_re, add_im, mul_re,
              mul_im, one_re, one_im] <;> ring1
        _ = CCL.FiniteExp.horner x denominator (degree + 1) +
            hornerTerm x denominator (degree + 1 + 1) := rfl

/-- The nested Horner program is exactly the bounded Taylor polynomial, not
merely close to it. -/
theorem horner_one_eq_truncatedExp (x : Gaussian) : ∀ degree : Nat,
    CCL.FiniteExp.horner x 1 degree = truncatedExp x degree
  | 0 => rfl
  | degree + 1 => by
      rw [horner_succ_eq_add_hornerTerm,
        horner_one_eq_truncatedExp x degree,
        hornerTerm_one_eq_taylorTerm, truncatedExp_succ]

/-- Paper-facing finite polynomial identification:
`e_depth(x) = sum_{k ≤ depth+1} x^k/k!`, where `truncatedExp` is bounded
natural recursion rather than an infinite series. -/
theorem sample_eq_truncatedExp (x : Gaussian) (depth : Nat) :
    CCL.FiniteExp.sample x depth = truncatedExp x (depth + 1) := by
  change CCL.FiniteExp.horner x 1 (depth + 1) = _
  exact horner_one_eq_truncatedExp x (depth + 1)

/-! ## Choice-free finite binomial and Cauchy sums -/

/-- Sum exactly the terms with natural indices strictly below `count`. -/
def finiteSum (term : Nat → Gaussian) : Nat → Gaussian
  | 0 => 0
  | count + 1 => finiteSum term count + term count

@[simp] theorem finiteSum_zero (term : Nat → Gaussian) :
    finiteSum term 0 = 0 := rfl

@[simp] theorem finiteSum_succ (term : Nat → Gaussian) (count : Nat) :
    finiteSum term (count + 1) = finiteSum term count + term count := rfl

theorem finiteSum_congr {left right : Nat → Gaussian}
    (equal : ∀ index, left index = right index) : ∀ count,
    finiteSum left count = finiteSum right count
  | 0 => rfl
  | count + 1 => by rw [finiteSum_succ, finiteSum_succ,
      finiteSum_congr equal count, equal count]

theorem finiteSum_congr_lt {left right : Nat → Gaussian} : ∀ count,
    (∀ index, index < count → left index = right index) →
      finiteSum left count = finiteSum right count
  | 0, equal => rfl
  | count + 1, equal => by
      rw [finiteSum_succ, finiteSum_succ,
        finiteSum_congr_lt count (fun index order =>
          equal index (order.trans (Nat.lt_succ_self count))),
        equal count (Nat.lt_succ_self count)]

theorem finiteSum_add (left right : Nat → Gaussian) : ∀ count,
    finiteSum (fun index => left index + right index) count =
      finiteSum left count + finiteSum right count
  | 0 => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [finiteSum_zero, zero_re, zero_im, add_re, add_im] <;> ring1
  | count + 1 => by
      rw [finiteSum_succ, finiteSum_succ, finiteSum_succ,
        finiteSum_add left right count]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im] <;> ring1

theorem mul_finiteSum_left (factor : Gaussian) (term : Nat → Gaussian) :
    ∀ count,
      factor * finiteSum term count =
        finiteSum (fun index => factor * term index) count
  | 0 => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [finiteSum_zero, mul_re, mul_im, zero_re, zero_im] <;> ring1
  | count + 1 => by
      rw [finiteSum_succ, finiteSum_succ,
        ← mul_finiteSum_left factor term count]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

theorem finiteSum_mul_right (term : Nat → Gaussian) (factor : Gaussian) :
    ∀ count,
      finiteSum term count * factor =
        finiteSum (fun index => term index * factor) count
  | 0 => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [finiteSum_zero, mul_re, mul_im, zero_re, zero_im] <;> ring1
  | count + 1 => by
      rw [finiteSum_succ, finiteSum_succ,
        ← finiteSum_mul_right term factor count]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

/-- Split a nonempty bounded sum at its first rather than final index. -/
theorem finiteSum_succ_front (term : Nat → Gaussian) : ∀ count,
    finiteSum term (count + 1) =
      term 0 + finiteSum (fun index => term (index + 1)) count
  | 0 => by
      rw [finiteSum_succ, finiteSum_zero, finiteSum_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, zero_re, zero_im] <;> ring1
  | count + 1 => by
      calc
        finiteSum term (count + 1 + 1) =
            finiteSum term (count + 1) + term (count + 1) := rfl
        _ = (term 0 + finiteSum (fun index => term (index + 1)) count) +
            term (count + 1) := by
          rw [finiteSum_succ_front term count]
        _ = term 0 +
            finiteSum (fun index => term (index + 1)) (count + 1) := by
          rw [finiteSum_succ]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im] <;> ring1

def binomialTerm (x y : Gaussian) (row column : Nat) : Gaussian :=
  x ^ column * y ^ (row - column) * (choose row column : Gaussian)

def binomialSum (x y : Gaussian) (row : Nat) : Gaussian :=
  finiteSum (binomialTerm x y row) (row + 1)

theorem binomialTerm_zero (x y : Gaussian) (row : Nat) :
    binomialTerm x y row 0 = y ^ row := by
  rw [binomialTerm, choose_zero_right, Nat.sub_zero, pow_zero]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [mul_re, mul_im, one_re, one_im, Nat.cast_one] <;> ring1

theorem binomialTerm_beyond (x y : Gaussian) (row : Nat) :
    binomialTerm x y row (row + 1) = 0 := by
  rw [binomialTerm, choose_eq_zero_of_lt (Nat.lt_succ_self row)]
  change _ * (0 : Gaussian) = 0
  exact RFAP.ConstructiveGaussian.Gaussian.mul_zero _

theorem binomialTerm_pascal (x y : Gaussian) (row column : Nat)
    (order : column ≤ row) :
    binomialTerm x y (row + 1) (column + 1) =
      x * binomialTerm x y row column +
        y * binomialTerm x y row (column + 1) := by
  by_cases endpoint : column = row
  · subst column
    rw [binomialTerm_beyond]
    simp only [binomialTerm, choose_self, Nat.sub_self,
      pow_zero, pow_succ]
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.add_zero]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [mul_re, mul_im, one_re, one_im, Nat.cast_one] <;> ring1
  · have strict : column < row := Nat.lt_of_le_of_ne order endpoint
    have subtractionIdentity :
        row - column = (row - (column + 1)) + 1 := by omega
    rw [binomialTerm, binomialTerm, binomialTerm, choose_succ_succ,
      Nat.succ_sub_succ_eq_sub, pow_succ, subtractionIdentity, pow_succ,
      Nat.cast_add]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, mul_re, mul_im] <;> ring1

theorem binomialSum_succ (x y : Gaussian) (row : Nat) :
    binomialSum x y (row + 1) = (x + y) * binomialSum x y row := by
  rw [binomialSum, binomialSum, finiteSum_succ_front,
    binomialTerm_zero]
  have pascalSum :
      finiteSum
          (fun index => binomialTerm x y (row + 1) (index + 1))
          (row + 1) =
        finiteSum
          (fun index =>
            x * binomialTerm x y row index +
              y * binomialTerm x y row (index + 1))
          (row + 1) :=
    finiteSum_congr_lt (row + 1)
      (fun index order =>
        binomialTerm_pascal x y row index (Nat.le_of_lt_succ order))
  have shiftedEnd :
      finiteSum (fun index => binomialTerm x y row (index + 1)) (row + 1) =
        finiteSum (fun index => binomialTerm x y row (index + 1)) row := by
    rw [finiteSum_succ, binomialTerm_beyond,
      RFAP.ConstructiveGaussian.Gaussian.add_zero]
  rw [pascalSum, finiteSum_add,
    ← mul_finiteSum_left x (binomialTerm x y row),
    ← mul_finiteSum_left y
      (fun index => binomialTerm x y row (index + 1)),
    shiftedEnd,
    finiteSum_succ_front (binomialTerm x y row), binomialTerm_zero, pow_succ]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im, mul_re, mul_im] <;> ring1

/-- Pure bounded-recursion binomial theorem over Gaussian rationals. -/
theorem binomial_theorem (x y : Gaussian) : ∀ row : Nat,
    binomialSum x y row = (x + y) ^ row
  | 0 => by
      rw [binomialSum, finiteSum_succ, finiteSum_zero,
        binomialTerm_zero, pow_zero, pow_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, zero_re, zero_im, one_re, one_im] <;> ring1
  | row + 1 => by
      rw [binomialSum_succ, binomial_theorem x y row, pow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

theorem scale_finiteSum (factor : Coordinate) (term : Nat → Gaussian) :
    ∀ count,
      CCL.FiniteExp.scale factor (finiteSum term count) =
        finiteSum
          (fun index => CCL.FiniteExp.scale factor (term index))
          count
  | 0 => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [finiteSum_zero, CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, zero_re, zero_im] <;> ring1
  | count + 1 => by
      rw [finiteSum_succ, finiteSum_succ,
        ← scale_finiteSum factor term count]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im] <;> ring1

theorem coordinate_div_eq_div_of_cross
    (leftNumerator leftDenominator rightNumerator rightDenominator : Coordinate)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (cross : leftNumerator * rightDenominator =
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator = rightNumerator / rightDenominator := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (RFAP.ConstructiveFraction.mul_ne_zero_direct leftNonzero rightNonzero)
  calc
    leftNumerator / leftDenominator *
          (leftDenominator * rightDenominator) =
        (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator := by ring1
    _ = leftNumerator * rightDenominator :=
      congrArg (fun value : Coordinate => value * rightDenominator)
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          leftNumerator leftDenominator leftNonzero)
    _ = rightNumerator * leftDenominator := cross
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator :=
      congrArg (fun value : Coordinate => value * leftDenominator)
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          rightNumerator rightDenominator rightNonzero).symm
    _ = rightNumerator / rightDenominator *
        (leftDenominator * rightDenominator) := by ring1

private theorem scale_mul_scale (left right : Coordinate) (x y : Gaussian) :
    CCL.FiniteExp.scale left x *
        CCL.FiniteExp.scale right y =
      CCL.FiniteExp.scale (left * right) (x * y) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem reciprocal_factorial_product (row column : Nat)
    (order : column ≤ row) :
    (1 / (factorial column : Coordinate)) *
        (1 / (factorial (row - column) : Coordinate)) =
      (choose row column : Coordinate) / (factorial row : Coordinate) := by
  rw [one_div_mul_one_div]
  have leftNonzero :
      ((factorial column : Coordinate) *
        (factorial (row - column) : Coordinate)) ≠ 0 :=
    RFAP.ConstructiveFraction.mul_ne_zero_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (factorial_pos column)).ne'
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (factorial_pos (row - column))).ne'
  have rightNonzero : (factorial row : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (factorial_pos row)).ne'
  apply coordinate_div_eq_div_of_cross 1 _ (choose row column : Coordinate) _
    leftNonzero rightNonzero
  have castIdentity := congrArg (fun value : Nat => (value : Coordinate))
    (choose_mul_factorials row column order)
  simp only [Nat.cast_mul] at castIdentity
  calc
    (1 : Coordinate) * (factorial row : Coordinate) =
        (factorial row : Coordinate) :=
      RFAP.ConstructiveFraction.one_mul _
    _ = (choose row column : Coordinate) *
          (factorial column : Coordinate) *
            (factorial (row - column) : Coordinate) := castIdentity.symm
    _ = (choose row column : Coordinate) *
          ((factorial column : Coordinate) *
            (factorial (row - column) : Coordinate)) := by ring1

def cauchyTerm (x y : Gaussian) (row column : Nat) : Gaussian :=
  taylorTerm x column * taylorTerm y (row - column)

theorem cauchyTerm_eq_scaled_binomial (x y : Gaussian) (row column : Nat)
    (order : column ≤ row) :
    cauchyTerm x y row column =
      CCL.FiniteExp.scale
        (1 / (factorial row : Coordinate)) (binomialTerm x y row column) := by
  rw [cauchyTerm, taylorTerm, taylorTerm, scale_mul_scale,
    binomialTerm]
  have coefficient := reciprocal_factorial_product row column order
  have coefficient' :
      (1 / (factorial column : Coordinate)) *
          (1 / (factorial (row - column) : Coordinate)) =
        (1 / (factorial row : Coordinate)) * (choose row column : Coordinate) :=
    coefficient.trans (by
      change (choose row column : Coordinate) *
          (factorial row : Coordinate)⁻¹ =
        (1 * (factorial row : Coordinate)⁻¹) *
          (choose row column : Coordinate)
      rw [RFAP.ConstructiveFraction.one_mul]
      exact RFAP.ConstructiveFraction.mul_comm _ _)
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im,
      natCast_re, natCast_im] <;>
    rw [coefficient'] <;> ring1

def cauchyDiagonal (x y : Gaussian) (row : Nat) : Gaussian :=
  finiteSum (cauchyTerm x y row) (row + 1)

/-- Each complete finite Cauchy-product diagonal is exactly the corresponding
Taylor monomial at `x + y`. -/
theorem cauchyDiagonal_eq_taylorTerm (x y : Gaussian) (row : Nat) :
    cauchyDiagonal x y row = taylorTerm (x + y) row := by
  rw [cauchyDiagonal]
  calc
    finiteSum (cauchyTerm x y row) (row + 1) =
        finiteSum
          (fun column => CCL.FiniteExp.scale
            (1 / (factorial row : Coordinate))
            (binomialTerm x y row column)) (row + 1) :=
      finiteSum_congr_lt (row + 1)
        (fun column order => cauchyTerm_eq_scaled_binomial x y row column
          (Nat.le_of_lt_succ order))
    _ = CCL.FiniteExp.scale
        (1 / (factorial row : Coordinate)) (binomialSum x y row) := by
      rw [binomialSum, scale_finiteSum]
    _ = CCL.FiniteExp.scale
        (1 / (factorial row : Coordinate)) ((x + y) ^ row) := by
      rw [binomial_theorem]
    _ = taylorTerm (x + y) row := rfl

@[simp] theorem taylorTerm_zero (x : Gaussian) : taylorTerm x 0 = 1 := by
  rw [taylorTerm, factorial_zero, pow_zero]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, one_re, one_im] <;>
    rw [show ((1 : Nat) : Coordinate) = 1 by rfl,
      show (1 / (1 : Coordinate)) = 1 by decide] <;> ring1

theorem truncatedExp_eq_finiteSum (x : Gaussian) : ∀ degree : Nat,
    truncatedExp x degree = finiteSum (taylorTerm x) (degree + 1)
  | 0 => by
      rw [truncatedExp_zero, finiteSum_succ, finiteSum_zero, taylorTerm_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
  | degree + 1 => by
      calc
        truncatedExp x (degree + 1) =
            truncatedExp x degree + taylorTerm x (degree + 1) := rfl
        _ = finiteSum (taylorTerm x) (degree + 1) +
            taylorTerm x (degree + 1) := by
          rw [truncatedExp_eq_finiteSum x degree]
        _ = finiteSum (taylorTerm x) (degree + 1 + 1) := rfl

/-- Split a displayed bounded sum after `firstCount` terms. -/
theorem finiteSum_append (term : Nat → Gaussian) (firstCount : Nat) :
    ∀ extraCount,
      finiteSum term (firstCount + extraCount) =
        finiteSum term firstCount +
          finiteSum (fun index => term (firstCount + index)) extraCount
  | 0 => by
      rw [Nat.add_zero, finiteSum_zero,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
  | extraCount + 1 => by
      rw [show firstCount + (extraCount + 1) =
          firstCount + extraCount + 1 from
            (Nat.add_assoc firstCount extraCount 1).symm,
        finiteSum_succ, finiteSum_succ,
        finiteSum_append term firstCount extraCount]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im] <;> ring1

def cauchyRectangle (x y : Gaussian) (degree : Nat) : Gaussian :=
  finiteSum
    (fun leftDegree =>
      finiteSum
        (fun rightDegree =>
          taylorTerm x leftDegree * taylorTerm y rightDegree)
        (degree + 1))
    (degree + 1)

theorem finiteSum_product (left right : Nat → Gaussian)
    (leftCount rightCount : Nat) :
    finiteSum left leftCount * finiteSum right rightCount =
      finiteSum
        (fun leftIndex =>
          finiteSum
            (fun rightIndex => left leftIndex * right rightIndex)
            rightCount)
        leftCount := by
  rw [finiteSum_mul_right]
  apply finiteSum_congr
  intro leftIndex
  exact mul_finiteSum_left (left leftIndex) right rightCount

theorem truncatedExp_mul_eq_cauchyRectangle
    (x y : Gaussian) (degree : Nat) :
    truncatedExp x degree * truncatedExp y degree =
      cauchyRectangle x y degree := by
  rw [truncatedExp_eq_finiteSum, truncatedExp_eq_finiteSum,
    cauchyRectangle, finiteSum_product]

def cauchyTriangle (x y : Gaussian) (degree : Nat) : Gaussian :=
  finiteSum
    (fun leftDegree =>
      finiteSum
        (fun rightDegree =>
          taylorTerm x leftDegree * taylorTerm y rightDegree)
        (degree - leftDegree + 1))
    (degree + 1)

/-- The portion of the square Cauchy product strictly above total degree
`degree`.  Row `leftDegree` contains exactly `leftDegree` displayed terms. -/
def cauchyUpperTail (x y : Gaussian) (degree : Nat) : Gaussian :=
  finiteSum
    (fun leftDegree =>
      finiteSum
        (fun offset =>
          taylorTerm x leftDegree *
            taylorTerm y (degree - leftDegree + 1 + offset))
        leftDegree)
    (degree + 1)

theorem cauchyRectangle_eq_triangle_add_upper
    (x y : Gaussian) (degree : Nat) :
    cauchyRectangle x y degree =
      cauchyTriangle x y degree + cauchyUpperTail x y degree := by
  rw [cauchyRectangle, cauchyTriangle, cauchyUpperTail]
  calc
    finiteSum
        (fun leftDegree =>
          finiteSum
            (fun rightDegree =>
              taylorTerm x leftDegree * taylorTerm y rightDegree)
            (degree + 1))
        (degree + 1) =
      finiteSum
        (fun leftDegree =>
          finiteSum
              (fun rightDegree =>
                taylorTerm x leftDegree * taylorTerm y rightDegree)
              (degree - leftDegree + 1) +
            finiteSum
              (fun offset =>
                taylorTerm x leftDegree *
                  taylorTerm y (degree - leftDegree + 1 + offset))
              leftDegree)
        (degree + 1) := by
      apply finiteSum_congr_lt
      intro leftDegree leftOrder
      have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ leftOrder
      have countIdentity :
          degree + 1 = degree - leftDegree + 1 + leftDegree := by
        calc
          degree + 1 = (degree - leftDegree + leftDegree) + 1 :=
            congrArg (fun value => value + 1)
              (Nat.sub_add_cancel leftLe).symm
          _ = degree - leftDegree + 1 + leftDegree :=
            Nat.add_right_comm (degree - leftDegree) leftDegree 1
      rw [countIdentity, finiteSum_append]
    _ = finiteSum
          (fun leftDegree =>
            finiteSum
              (fun rightDegree =>
                taylorTerm x leftDegree * taylorTerm y rightDegree)
              (degree - leftDegree + 1))
          (degree + 1) +
        finiteSum
          (fun leftDegree =>
            finiteSum
              (fun offset =>
                taylorTerm x leftDegree *
                  taylorTerm y (degree - leftDegree + 1 + offset))
              leftDegree)
          (degree + 1) :=
      finiteSum_add _ _ (degree + 1)

theorem cauchyTriangle_succ (x y : Gaussian) (degree : Nat) :
    cauchyTriangle x y (degree + 1) =
      cauchyTriangle x y degree + cauchyDiagonal x y (degree + 1) := by
  rw [cauchyTriangle, cauchyTriangle, cauchyDiagonal, finiteSum_succ]
  have rowSplit :
      finiteSum
          (fun leftDegree =>
            finiteSum
              (fun rightDegree =>
                taylorTerm x leftDegree * taylorTerm y rightDegree)
              (degree + 1 - leftDegree + 1))
          (degree + 1) =
        finiteSum
          (fun leftDegree =>
            finiteSum
                (fun rightDegree =>
                  taylorTerm x leftDegree * taylorTerm y rightDegree)
                (degree - leftDegree + 1) +
              cauchyTerm x y (degree + 1) leftDegree)
          (degree + 1) := by
    apply finiteSum_congr_lt
    intro leftDegree leftOrder
    have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ leftOrder
    have countIdentity :
        degree + 1 - leftDegree + 1 = degree - leftDegree + 1 + 1 := by
      rw [Nat.succ_sub leftLe]
    rw [countIdentity, finiteSum_succ, cauchyTerm]
    rw [show degree - leftDegree + 1 =
      degree + 1 - leftDegree from (Nat.succ_sub leftLe).symm]
  rw [rowSplit, finiteSum_add]
  have finalRow :
      finiteSum
          (fun rightDegree =>
            taylorTerm x (degree + 1) * taylorTerm y rightDegree)
          (degree + 1 - (degree + 1) + 1) =
        cauchyTerm x y (degree + 1) (degree + 1) := by
    simp only [Nat.sub_self, Nat.zero_add, finiteSum_succ, finiteSum_zero,
      cauchyTerm, RFAP.ConstructiveGaussian.Gaussian.zero_add]
  rw [finalRow]
  have diagonalSucc :
      finiteSum (cauchyTerm x y (degree + 1)) (degree + 1 + 1) =
        finiteSum (cauchyTerm x y (degree + 1)) (degree + 1) +
          cauchyTerm x y (degree + 1) (degree + 1) := rfl
  rw [diagonalSucc]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im] <;> ring1

/-- The lower triangular finite Cauchy product is exactly the Taylor
polynomial at the sum. -/
theorem cauchyTriangle_eq_truncatedExp (x y : Gaussian) : ∀ degree : Nat,
    cauchyTriangle x y degree = truncatedExp (x + y) degree
  | 0 => by
      change (0 : Gaussian) +
          ((0 : Gaussian) + taylorTerm x 0 * taylorTerm y 0) = 1
      rw [taylorTerm_zero, taylorTerm_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
  | degree + 1 => by
      rw [cauchyTriangle_succ, cauchyTriangle_eq_truncatedExp x y degree,
        cauchyDiagonal_eq_taylorTerm, truncatedExp_succ]

/-- Exact finite decomposition of the exponential product error into only
the displayed high-total-degree terms of the square Cauchy product. -/
theorem truncatedExp_mul_sub_truncatedExp_eq_upper
    (x y : Gaussian) (degree : Nat) :
    truncatedExp x degree * truncatedExp y degree -
        truncatedExp (x + y) degree =
      cauchyUpperTail x y degree := by
  rw [truncatedExp_mul_eq_cauchyRectangle,
    cauchyRectangle_eq_triangle_add_upper,
    cauchyTriangle_eq_truncatedExp]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;> ring1

/-! ## Explicit high-degree remainder bounds -/

theorem hornerTerm_normSq_le_quarter_pow {x : Gaussian}
    (unitInput : normSq x ≤ 1) :
    ∀ (degree denominator : Nat), 2 ≤ denominator →
      normSq (hornerTerm x denominator degree) ≤
        (1 / 4 : Coordinate) ^ degree
  | 0, denominator, atLeastTwo => by
      rw [hornerTerm_zero, normSq_one, pow_zero]
  | degree + 1, denominator, atLeastTwo => by
      rw [hornerTerm_succ, CCL.FiniteExp.normSq_scale, normSq_mul,
        pow_succ]
      have reciprocal :=
        CCL.FiniteExp.reciprocal_nat_sq_le_quarter atLeastTwo
      have tail := hornerTerm_normSq_le_quarter_pow unitInput degree
        (denominator + 1) (by omega)
      have inner :
          normSq x * normSq (hornerTerm x (denominator + 1) degree) ≤
            1 * (1 / 4 : Coordinate) ^ degree :=
        RFAP.ConstructiveFraction.mul_le_mul_direct unitInput tail
          (normSq_nonneg _) (by decide)
      calc
        (1 / (denominator : Coordinate)) ^ 2 *
            (normSq x * normSq
              (hornerTerm x (denominator + 1) degree)) ≤
          (1 / 4 : Coordinate) *
            (1 * (1 / 4 : Coordinate) ^ degree) :=
          RFAP.ConstructiveFraction.mul_le_mul_direct reciprocal inner
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (normSq_nonneg x) (normSq_nonneg _))
            (by decide)
        _ = (1 / 4 : Coordinate) ^ degree * (1 / 4) := by ring1

theorem taylorTerm_succ_normSq_le {x : Gaussian}
    (unitInput : normSq x ≤ 1) (degree : Nat) :
    normSq (taylorTerm x (degree + 1)) ≤
      (1 / 4 : Coordinate) ^ degree := by
  rw [← hornerTerm_one_eq_taylorTerm, hornerTerm_succ,
    CCL.FiniteExp.normSq_scale, normSq_mul]
  have scalar : (1 / ((1 : Nat) : Coordinate)) ^ 2 = 1 := by decide
  rw [scalar, RFAP.ConstructiveFraction.one_mul]
  have tail := hornerTerm_normSq_le_quarter_pow unitInput degree 2 (by decide)
  have product := RFAP.ConstructiveFraction.mul_le_mul_direct unitInput tail
    (normSq_nonneg _) (by decide : (0 : Coordinate) ≤ 1)
  simpa only [RFAP.ConstructiveFraction.one_mul] using product

private theorem quarter_pow_succ_le (degree : Nat) :
    (1 / 4 : Coordinate) ^ (degree + 1) ≤ (1 / 4 : Coordinate) ^ degree := by
  rw [pow_succ]
  calc
    (1 / 4 : Coordinate) ^ degree * (1 / 4) ≤
        (1 / 4 : Coordinate) ^ degree * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (show (1 / 4 : Coordinate) ≤ 1 by decide)
        (show 0 ≤ (1 / 4 : Coordinate) ^ degree from
          RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) degree)
    _ = (1 / 4 : Coordinate) ^ degree :=
      RFAP.ConstructiveFraction.mul_one_direct _

private theorem geometric_scale_shift (scale : Coordinate) (index : Nat) :
    scale * (1 / 4 : Coordinate) ^ (index + 1) =
      (scale / 4) * (1 / 4 : Coordinate) ^ index := by
  rw [pow_succ]
  have scaleQuarter :
      scale * (1 / 4 : Coordinate) = scale / 4 := by
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
  calc
    scale * ((1 / 4 : Coordinate) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Coordinate)) * (1 / 4 : Coordinate) ^ index := by
      ring1
    _ = (scale / 4) * (1 / 4 : Coordinate) ^ index := by
      rw [scaleQuarter]

private theorem four_mul_quarter_scale (scale : Coordinate) :
    4 * (scale / 4) = scale := by
  calc
    4 * (scale / 4) = scale / 4 * 4 :=
      RFAP.ConstructiveFraction.mul_comm _ _
    _ = scale :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne scale 4 (by decide)

private theorem two_double_scale (scale : Coordinate) :
    2 * (scale + scale) = 4 * scale := by ring1

/-- A finite geometric sum of Gaussian rationals has a uniform quadrance
bound.  This deliberately sums by bounded natural recursion: it neither forms
an infinite series nor uses a finite-set cardinality theorem. -/
theorem finiteSum_geometric_normSq_le (term : Nat → Gaussian) :
    ∀ (count : Nat) (scale : Coordinate), 0 ≤ scale →
      (∀ index, normSq (term index) ≤
        scale * (1 / 4 : Coordinate) ^ index) →
      normSq (finiteSum term count) ≤ 4 * scale := by
  intro count
  induction count generalizing term with
  | zero =>
    intro scale scaleNonnegative termBound
    rw [finiteSum_zero, normSq_zero]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      scaleNonnegative
  | succ count inductionHypothesis =>
    intro scale scaleNonnegative termBound
    rw [finiteSum_succ_front]
    have headBound : normSq (term 0) ≤ scale := by
      simpa only [pow_zero, RFAP.ConstructiveFraction.mul_one_direct] using
        termBound 0
    have quarterScaleNonnegative : 0 ≤ scale / 4 :=
      RFAP.ConstructiveFraction.div_nonneg_direct scaleNonnegative (by decide)
    have shiftedBound : ∀ index,
        normSq (term (index + 1)) ≤
          (scale / 4) * (1 / 4 : Coordinate) ^ index := by
      intro index
      calc
        normSq (term (index + 1)) ≤
            scale * (1 / 4 : Coordinate) ^ (index + 1) := termBound _
        _ = (scale / 4) * (1 / 4 : Coordinate) ^ index :=
          geometric_scale_shift scale index
    have tailBound := inductionHypothesis
      (fun index => term (index + 1)) (scale / 4)
        quarterScaleNonnegative shiftedBound
    have tailBound' :
        normSq (finiteSum (fun index => term (index + 1)) count) ≤ scale := by
      calc
        normSq (finiteSum (fun index => term (index + 1)) count) ≤
            4 * (scale / 4) := tailBound
        _ = scale := four_mul_quarter_scale scale
    calc
      normSq
          (term 0 + finiteSum (fun index => term (index + 1)) count) ≤
        2 * (normSq (term 0) +
          normSq (finiteSum (fun index => term (index + 1)) count)) :=
            normSq_add_le_two _ _
      _ ≤ 2 * (scale + scale) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add headBound tailBound') (by decide)
      _ = 4 * scale := two_double_scale scale

/-- The exact natural weight generated by repeated use of the squared-norm
two-term inequality. -/
def finiteSumWeight : Nat → Nat
  | 0 => 0
  | count + 1 => 2 * (finiteSumWeight count + 1)

@[simp] theorem finiteSumWeight_zero : finiteSumWeight 0 = 0 := rfl

@[simp] theorem finiteSumWeight_succ (count : Nat) :
    finiteSumWeight (count + 1) = 2 * (finiteSumWeight count + 1) := rfl

theorem finiteSumWeight_add_two : ∀ count : Nat,
    finiteSumWeight count + 2 = 2 ^ (count + 1)
  | 0 => by decide
  | count + 1 => by
      calc
        finiteSumWeight (count + 1) + 2 =
            2 * (finiteSumWeight count + 1) + 2 := rfl
        _ = 2 * (finiteSumWeight count + 2) := by ring1
        _ = 2 * 2 ^ (count + 1) := by rw [finiteSumWeight_add_two count]
        _ = 2 ^ (count + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (count + 1 + 1) := (pow_succ 2 (count + 1)).symm

theorem finiteSumWeight_le_two_pow (count : Nat) :
    finiteSumWeight count ≤ 2 ^ (count + 1) := by
  rw [← finiteSumWeight_add_two count]
  exact Nat.le_add_right _ _

private theorem add_one_add (left right : Nat) :
    left + 1 + right = left + right + 1 := by
  calc
    left + 1 + right = left + (1 + right) := Nat.add_assoc _ _ _
    _ = left + (right + 1) := by rw [Nat.add_comm 1 right]
    _ = left + right + 1 := (Nat.add_assoc _ _ _).symm

/-- A finite sum of uniformly bounded terms, with the precise elementary
weight incurred by repeated squared-norm addition. -/
theorem finiteSum_uniform_normSq_le (term : Nat → Gaussian) :
    ∀ (count : Nat) (bound : Coordinate), 0 ≤ bound →
      (∀ index, index < count → normSq (term index) ≤ bound) →
      normSq (finiteSum term count) ≤
        (finiteSumWeight count : Coordinate) * bound
  | 0, bound, boundNonnegative, termBound => by
      rw [finiteSum_zero, normSq_zero, finiteSumWeight_zero, Nat.cast_zero,
        RFAP.ConstructiveFraction.zero_mul_direct]
  | count + 1, bound, boundNonnegative, termBound => by
      rw [finiteSum_succ]
      have prefixBound := finiteSum_uniform_normSq_le term count bound
        boundNonnegative (fun index order =>
          termBound index (order.trans (Nat.lt_succ_self count)))
      have finalBound := termBound count (Nat.lt_succ_self count)
      calc
        normSq (finiteSum term count + term count) ≤
            2 * (normSq (finiteSum term count) + normSq (term count)) :=
          normSq_add_le_two _ _
        _ ≤ 2 * ((finiteSumWeight count : Coordinate) * bound + bound) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add prefixBound finalBound) (by decide)
        _ = (finiteSumWeight (count + 1) : Coordinate) * bound := by
          rw [finiteSumWeight_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
            Nat.cast_one]
          ring1

theorem cauchyUpperTail_term_normSq_le {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    {degree leftDegree : Nat} (degreePositive : 1 ≤ degree)
    (leftOrder : leftDegree ≤ degree) (offset : Nat) :
    normSq
        (taylorTerm x leftDegree *
          taylorTerm y (degree - leftDegree + 1 + offset)) ≤
      (1 / 4 : Coordinate) ^ (degree - 1) *
        (1 / 4 : Coordinate) ^ offset := by
  rw [normSq_mul]
  cases leftDegree with
  | zero =>
      rw [taylorTerm_zero, normSq_one, RFAP.ConstructiveFraction.one_mul]
      have rightBound := taylorTerm_succ_normSq_le yUnit (degree + offset)
      have rightIndex : degree - 0 + 1 + offset = degree + offset + 1 := by
        simp only [Nat.sub_zero]
        exact add_one_add degree offset
      rw [rightIndex]
      calc
        normSq (taylorTerm y (degree + offset + 1)) ≤
            (1 / 4 : Coordinate) ^ (degree + offset) := rightBound
        _ ≤ (1 / 4 : Coordinate) ^ (degree - 1 + offset) := by
          have exponentIdentity : degree + offset =
              (degree - 1 + offset) + 1 := by
            calc
              degree + offset = (degree - 1 + 1) + offset :=
                congrArg (fun value => value + offset)
                  (Nat.sub_add_cancel degreePositive).symm
              _ = (degree - 1 + offset) + 1 :=
                add_one_add (degree - 1) offset
          rw [exponentIdentity]
          exact quarter_pow_succ_le _
        _ = (1 / 4 : Coordinate) ^ (degree - 1) *
              (1 / 4 : Coordinate) ^ offset := by
          rw [← pow_add]
  | succ leftPred =>
      have leftBound := taylorTerm_succ_normSq_le xUnit leftPred
      have rightIndex :
          degree - (leftPred + 1) + 1 + offset =
            (degree - (leftPred + 1) + offset) + 1 := by
        exact add_one_add (degree - (leftPred + 1)) offset
      rw [rightIndex]
      have rightBound := taylorTerm_succ_normSq_le yUnit
        (degree - (leftPred + 1) + offset)
      have productBound := RFAP.ConstructiveFraction.mul_le_mul_direct
        leftBound rightBound (normSq_nonneg _) (by
          exact RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
      calc
        normSq (taylorTerm x (leftPred + 1)) *
            normSq
              (taylorTerm y (degree - (leftPred + 1) + offset + 1)) ≤
          (1 / 4 : Coordinate) ^ leftPred *
            (1 / 4 : Coordinate) ^
              (degree - (leftPred + 1) + offset) := productBound
        _ = (1 / 4 : Coordinate) ^ (degree - 1) *
              (1 / 4 : Coordinate) ^ offset := by
          rw [← pow_add, ← pow_add]
          congr 1
          have decomposition : degree =
              (leftPred + (degree - (leftPred + 1))) + 1 := by
            calc
              degree = (leftPred + 1) +
                  (degree - (leftPred + 1)) :=
                (Nat.add_sub_of_le leftOrder).symm
              _ = (leftPred + (degree - (leftPred + 1))) + 1 := by
                exact add_one_add leftPred (degree - (leftPred + 1))
          have core : degree - 1 =
              leftPred + (degree - (leftPred + 1)) :=
            Nat.sub_eq_of_eq_add decomposition
          rw [← Nat.add_assoc, ← core]

theorem cauchyUpperTail_row_normSq_le {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    {degree leftDegree : Nat} (degreePositive : 1 ≤ degree)
    (leftOrder : leftDegree ≤ degree) :
    normSq
        (finiteSum
          (fun offset =>
            taylorTerm x leftDegree *
              taylorTerm y (degree - leftDegree + 1 + offset))
          leftDegree) ≤
      4 * (1 / 4 : Coordinate) ^ (degree - 1) := by
  exact finiteSum_geometric_normSq_le _ leftDegree
    ((1 / 4 : Coordinate) ^ (degree - 1))
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
    (cauchyUpperTail_term_normSq_le xUnit yUnit degreePositive leftOrder)

/-- Explicit bound for the finite high-degree corner in the exponential
Cauchy product. -/
theorem cauchyUpperTail_normSq_le {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    {degree : Nat} (degreePositive : 1 ≤ degree) :
    normSq (cauchyUpperTail x y degree) ≤
      (2 : Coordinate) ^ (degree + 2) *
        (4 * (1 / 4 : Coordinate) ^ (degree - 1)) := by
  let bound : Coordinate := 4 * (1 / 4 : Coordinate) ^ (degree - 1)
  let row : Nat → Gaussian := fun leftDegree =>
    finiteSum
      (fun offset =>
        taylorTerm x leftDegree *
          taylorTerm y (degree - leftDegree + 1 + offset))
      leftDegree
  have boundNonnegative : 0 ≤ bound :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
  have weighted := finiteSum_uniform_normSq_le row (degree + 1) bound
    boundNonnegative
    (fun leftDegree order => cauchyUpperTail_row_normSq_le xUnit yUnit
      degreePositive (Nat.le_of_lt_succ order))
  have weightOrderNat := finiteSumWeight_le_two_pow (degree + 1)
  have weightOrder : (finiteSumWeight (degree + 1) : Coordinate) ≤
      (2 : Coordinate) ^ (degree + 2) := by
    have castOrder := RFAP.ConstructiveFraction.natCast_le_direct weightOrderNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castOrder
  have result := weighted.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        weightOrder boundNonnegative)
  simpa only [cauchyUpperTail, row, bound] using result

private theorem even_cauchy_bound_identity (index : Nat) :
    (2 : Coordinate) ^ (2 * index + 2 + 2) *
        (4 * (1 / 4 : Coordinate) ^ (2 * index + 2 - 1)) =
      CCL.FiniteGeometric.quarterRadius 16 index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  rw [show 2 * index + 2 + 2 = 4 + 2 * index by
      calc
        2 * index + 2 + 2 = 2 * index + 4 := by rw [Nat.add_assoc]
        _ = 4 + 2 * index := Nat.add_comm _ _,
    show 2 * index + 2 - 1 = 2 * index + 1 by
      exact Nat.add_sub_cancel (2 * index + 1) 1,
    pow_add, pow_add, pow_mul, pow_mul]
  rw [show (2 : Coordinate) ^ 4 = 16 by decide,
    show (2 : Coordinate) ^ 2 = 4 by decide,
    show (1 / 4 : Coordinate) ^ 2 = 1 / 16 by decide,
    show (1 / 4 : Coordinate) ^ 1 = 1 / 4 by decide]
  calc
    (16 * (4 : Coordinate) ^ index) *
        (4 * ((1 / 16 : Coordinate) ^ index * (1 / 4))) =
      (16 * ((4 : Coordinate) ^ index *
        (1 / 16 : Coordinate) ^ index)) * (4 * (1 / 4)) := by ring1
    _ = 16 * ((4 : Coordinate) ^ index *
        (1 / 16 : Coordinate) ^ index) := by
      rw [show (4 : Coordinate) * (1 / 4) = 1 by decide,
        RFAP.ConstructiveFraction.mul_one_direct]
    _ = 16 * ((4 : Coordinate) * (1 / 16 : Coordinate)) ^ index := by
      rw [mul_pow]
    _ = 16 * (1 / 4 : Coordinate) ^ index := by
      rw [show (4 : Coordinate) * (1 / 16) = 1 / 4 by decide]

/-- At the synchronized even truncation degree `2 * index + 2`, the finite
exponential addition-law error has the explicit quarter-power allowance
`16 / 4^index`. -/
theorem truncatedExp_addition_error_even {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) (index : Nat) :
    normSq
        (truncatedExp x (2 * index + 2) *
            truncatedExp y (2 * index + 2) -
          truncatedExp (x + y) (2 * index + 2)) ≤
      CCL.FiniteGeometric.quarterRadius 16 index := by
  rw [truncatedExp_mul_sub_truncatedExp_eq_upper]
  calc
    normSq (cauchyUpperTail x y (2 * index + 2)) ≤
        (2 : Coordinate) ^ (2 * index + 2 + 2) *
          (4 * (1 / 4 : Coordinate) ^ (2 * index + 2 - 1)) :=
      cauchyUpperTail_normSq_le xUnit yUnit
        (Nat.succ_le_succ (Nat.zero_le (2 * index + 1)))
    _ = CCL.FiniteGeometric.quarterRadius 16 index :=
      even_cauchy_bound_identity index

/-! ## The operational exponential addition law -/

def expProductSample (x y : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.sample x index *
    CCL.FiniteExp.sample y index

/-- Kept as a small finite arithmetic expression so kernel reduction does not
have to elaborate a large unary numeral. -/
def expProductErrorScale : Coordinate := 40 * 10

theorem expProductErrorScale_nonneg : 0 ≤ expProductErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 40) (by decide)).le
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 10) (by decide)).le

def expProductCenterBound : Coordinate := 10 * 10

theorem expProductCenterBound_nonneg : 0 ≤ expProductCenterBound :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 10) (by decide)).le
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 10) (by decide)).le

theorem expProductSample_bounded {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) (index : Nat) :
    normSq (expProductSample x y index) ≤ expProductCenterBound := by
  rw [expProductSample, normSq_mul]
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
    (CCL.FiniteExp.sample_bounded x xUnit index)
    (CCL.FiniteExp.sample_bounded y yUnit index)
    (normSq_nonneg _) (by decide : (0 : Coordinate) ≤ 10)
  calc
    normSq (CCL.FiniteExp.sample x index) *
        normSq (CCL.FiniteExp.sample y index) ≤ 10 * 10 :=
      multiplied
    _ = expProductCenterBound := rfl

private theorem product_difference_identity
    (xLater xEarlier yLater yEarlier : Gaussian) :
    xLater * yLater - xEarlier * yEarlier =
      (xLater - xEarlier) * yLater +
        xEarlier * (yLater - yEarlier) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

theorem expProductSample_later_close {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq (expProductSample x y later - expProductSample x y earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        expProductErrorScale earlier := by
  rw [expProductSample, expProductSample, product_difference_identity]
  let radius :=
    CCL.FiniteGeometric.quarterRadius 10 earlier
  have xClose := CCL.FiniteExp.sample_later_close x xUnit order
  have yClose := CCL.FiniteExp.sample_later_close y yUnit order
  have yLaterBound := CCL.FiniteExp.sample_bounded y yUnit later
  have xEarlierBound := CCL.FiniteExp.sample_bounded x xUnit earlier
  have firstBound :
      normSq
          ((CCL.FiniteExp.sample x later -
              CCL.FiniteExp.sample x earlier) *
            CCL.FiniteExp.sample y later) ≤ radius * 10 := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct xClose yLaterBound
      (normSq_nonneg _) (CCL.FiniteGeometric.quarterRadius_nonneg
        (by decide) _)
  have secondBound :
      normSq
          (CCL.FiniteExp.sample x earlier *
            (CCL.FiniteExp.sample y later -
              CCL.FiniteExp.sample y earlier)) ≤ 10 * radius := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct xEarlierBound yClose
      (normSq_nonneg _)
      (by decide : (0 : Coordinate) ≤ 10)
  calc
    normSq
        ((CCL.FiniteExp.sample x later -
              CCL.FiniteExp.sample x earlier) *
            CCL.FiniteExp.sample y later +
          CCL.FiniteExp.sample x earlier *
            (CCL.FiniteExp.sample y later -
              CCL.FiniteExp.sample y earlier)) ≤
      2 * (radius * 10 + 10 * radius) := by
        exact (normSq_add_le_two _ _).trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstBound secondBound) (by decide))
    _ = CCL.FiniteGeometric.quarterRadius
        expProductErrorScale earlier := by
      dsimp only [radius]
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      dsimp only [expProductErrorScale]
      ring1

/-- The pointwise product of the two finite exponential programs, equipped
with an explicit finite tail sidecar. -/
def expProductApproximation (x y : Gaussian)
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) : Approximation where
  sample := expProductSample x y
  radiusSq := CCL.FiniteGeometric.quarterRadius
    expProductErrorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      expProductErrorScale_nonneg
  later_close := expProductSample_later_close xUnit yUnit
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      expProductErrorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      expProductErrorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      expProductErrorScale expProductErrorScale_nonneg
  centerBound := expProductCenterBound
  centerBound_nonneg := expProductCenterBound_nonneg
  sample_bounded := expProductSample_bounded xUnit yUnit

theorem expProductSample_addition_error_odd {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) (index : Nat) :
    normSq
        (expProductSample x y (2 * index + 1) -
          CCL.FiniteExp.sample (x + y) (2 * index + 1)) ≤
      CCL.FiniteGeometric.quarterRadius 16 index := by
  rw [expProductSample,
    sample_eq_truncatedExp, sample_eq_truncatedExp,
    sample_eq_truncatedExp]
  simpa only [show 2 * index + 1 + 1 = 2 * index + 2 by rfl] using
    truncatedExp_addition_error_even xUnit yUnit index

private theorem quarterRadius_scale_mono {small large : Coordinate}
    (scaleOrder : small ≤ large) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius small index ≤
      CCL.FiniteGeometric.quarterRadius large index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scaleOrder
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have powerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have inner := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    extraPowerLe powerNonnegative
  have outerNonnegative :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      powerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe outerNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_one_direct _

private theorem ten_sixteenths_lt {target : Coordinate}
    (positive : 0 < target) : 10 * (target / 16) < target := by
  have scalarOrder : (10 / 16 : Coordinate) < 1 := by decide
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    scalarOrder positive
  calc
    10 * (target / 16) = (10 / 16 : Coordinate) * target := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    _ < 1 * target := scaled
    _ = target := RFAP.ConstructiveFraction.one_mul _

/-- Constructive, finite-request exponential addition law on the rational
unit disk.  Given any two current indices and any positive rational squared
tolerance, this program computes synchronized later indices after which every
pair of displayed samples satisfies that tolerance. -/
def exp_add_equivalent {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    (sumUnit : normSq (x + y) ≤ 1) :
    Equivalent
      (expProductApproximation x y xUnit yUnit)
      (CCL.FiniteExp.approximation (x + y) sumUnit) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := CCL.FiniteGeometric.firstQuarterBelow
      expProductErrorScale start smallTarget
    let synchronized := 2 * index + 1
    have indexGe : start ≤ index :=
      CCL.FiniteGeometric.firstQuarterBelow_ge
        expProductErrorScale start smallTarget
    have synchronizedGeIndex : index ≤ synchronized := by
      dsimp only [synchronized]
      omega
    have masterSmall :
        CCL.FiniteGeometric.quarterRadius
          expProductErrorScale index <
          smallTarget :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate
        expProductErrorScale expProductErrorScale_nonneg
          start smallTarget smallPositive
    exact
      { leftIndex := synchronized
        rightIndex := synchronized
        left_ge := (Nat.le_max_left _ _).trans
          (indexGe.trans synchronizedGeIndex)
        right_ge := (Nat.le_max_right _ _).trans
          (indexGe.trans synchronizedGeIndex)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have productTailLe :=
            (expProductApproximation x y xUnit yUnit).later_close leftOrder
          have productRadiusLe :
              CCL.FiniteGeometric.quarterRadius
                  expProductErrorScale synchronized ≤
                CCL.FiniteGeometric.quarterRadius
                  expProductErrorScale index :=
            quarterRadius_index_antitone expProductErrorScale_nonneg
              synchronizedGeIndex
          have productTail :
              normSq
                  (expProductSample x y leftLater -
                    expProductSample x y synchronized) < smallTarget :=
            productTailLe.trans_lt (productRadiusLe.trans_lt masterSmall)
          have directLe := expProductSample_addition_error_odd
            xUnit yUnit index
          have directScaleLe :
              CCL.FiniteGeometric.quarterRadius 16 index ≤
                CCL.FiniteGeometric.quarterRadius
                  expProductErrorScale index :=
            quarterRadius_scale_mono (by
              dsimp only [expProductErrorScale]
              calc
                (16 : Coordinate) ≤ 400 :=
                  RFAP.ConstructiveFraction.natCast_le_direct (by decide)
                _ = 40 * 10 := by ring1) index
          have direct :
              normSq
                  (expProductSample x y synchronized -
                    CCL.FiniteExp.sample (x + y) synchronized) <
                smallTarget :=
            directLe.trans_lt (directScaleLe.trans_lt masterSmall)
          have sumTailForward :=
            (CCL.FiniteExp.approximation (x + y) sumUnit).later_close
              rightOrder
          have sumRadiusLe :
              CCL.FiniteGeometric.quarterRadius 10 synchronized ≤
                CCL.FiniteGeometric.quarterRadius
                  expProductErrorScale index :=
            (quarterRadius_scale_mono (by
              dsimp only [expProductErrorScale]
              calc
                (10 : Coordinate) ≤ 400 :=
                  RFAP.ConstructiveFraction.natCast_le_direct (by decide)
                _ = 40 * 10 := by ring1) synchronized).trans
              productRadiusLe
          have sumTailReverse :
              normSq
                  (CCL.FiniteExp.sample (x + y) synchronized -
                    CCL.FiniteExp.sample (x + y) rightLater) <
                smallTarget := by
            have reverseIdentity :
                CCL.FiniteExp.sample (x + y) synchronized -
                    CCL.FiniteExp.sample (x + y) rightLater =
                  -(CCL.FiniteExp.sample (x + y) rightLater -
                    CCL.FiniteExp.sample (x + y) synchronized) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [reverseIdentity, normSq_neg]
            exact sumTailForward.trans_lt (sumRadiusLe.trans_lt masterSmall)
          have middle :
              normSq
                  (expProductSample x y synchronized -
                    CCL.FiniteExp.sample (x + y) rightLater) <
                2 * (smallTarget + smallTarget) := by
            exact (normSq_sub_le_via _ _ _).trans_lt
              (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  direct sumTailReverse))
          calc
            normSq
                (expProductSample x y leftLater -
                  CCL.FiniteExp.sample (x + y) rightLater) ≤
              2 * (normSq
                    (expProductSample x y leftLater -
                      expProductSample x y synchronized) +
                normSq
                    (expProductSample x y synchronized -
                      CCL.FiniteExp.sample (x + y) rightLater)) :=
                normSq_sub_le_via _ _ _
            _ < 2 * (smallTarget + 2 * (smallTarget + smallTarget)) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  productTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact ten_sixteenths_lt positive
      }

/-- The pointwise product side of the local exponential addition law exposed
through the ordinary productive CCL controller. -/
def expProductNamed (x y : Gaussian)
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) :
    CCL.ProgressiveTransducer.Named :=
  (expProductApproximation x y xUnit yUnit).toNamed

/-- The direct `exp(x+y)` side of the local addition law exposed through the
ordinary productive CCL controller. -/
def expSumNamed (x y : Gaussian) (sumUnit : normSq (x + y) ≤ 1) :
    CCL.ProgressiveTransducer.Named :=
  (CCL.FiniteExp.approximation (x + y) sumUnit).toNamed

theorem expProductNamed_productive (x y : Gaussian)
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1) (count : Nat) :
    (expProductNamed x y xUnit yUnit).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expProductNamed x y xUnit yUnit).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expProductNamed x y xUnit yUnit).machine count).emitted.length =
        count :=
  (expProductApproximation x y xUnit yUnit).output_productive count

theorem expSumNamed_productive (x y : Gaussian)
    (sumUnit : normSq (x + y) ≤ 1) (count : Nat) :
    (expSumNamed x y sumUnit).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expSumNamed x y sumUnit).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expSumNamed x y sumUnit).machine count).emitted.length = count :=
  (CCL.FiniteExp.approximation
    (x + y) sumUnit).output_productive count

/-- CCL-name form of the constructive local exponential addition law.  Both
sides emit arbitrary finite ordinary CCL prefixes, and their canonical finite
sampling paths are operationally equivalent at every positive rational
squared tolerance. -/
def exp_add_named_equivalent {x y : Gaussian}
    (xUnit : normSq x ≤ 1) (yUnit : normSq y ≤ 1)
    (sumUnit : normSq (x + y) ≤ 1) :
    CCL.OperationalEquivalence.NamedEquivalent
      (expProductNamed x y xUnit yUnit)
      (expSumNamed x y sumUnit) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
      (expProductApproximation x y xUnit yUnit))
    (CCL.OperationalEquivalence.Equivalent.trans
      (exp_add_equivalent xUnit yUnit sumUnit)
      (CCL.OperationalEquivalence.Equivalent.symm
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          (CCL.FiniteExp.approximation (x + y) sumUnit))))

/-! ## The finite complex-log program as an odd polynomial -/

/-- The positive odd natural immediately before the logarithm Horner index. -/
def priorOdd (index : Nat) : Nat := 2 * index - 1

theorem priorOdd_pos {index : Nat} (positive : 1 ≤ index) :
    0 < priorOdd index := by
  unfold priorOdd
  omega

theorem logCoefficient_eq_priorOdd_ratio {index : Nat}
    (positive : 1 ≤ index) :
    CCL.FiniteComplexLog.coefficient index =
      (priorOdd index : Coordinate) / (priorOdd (index + 1) : Coordinate) := by
  rw [CCL.FiniteComplexLog.coefficient,
    CCL.FiniteLog.coefficient]
  unfold priorOdd
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * index),
    Nat.cast_sub (by omega : 1 ≤ 2 * (index + 1)), Nat.cast_mul,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  ring1

private theorem div_mul_div_telescope
    (numerator middle denominator : Coordinate)
    (middleNonzero : middle ≠ 0) (denominatorNonzero : denominator ≠ 0) :
    (numerator / middle) * (middle / denominator) =
      numerator / denominator := by
  calc
    (numerator / middle) * (middle / denominator) =
        (numerator * middle) / (middle * denominator) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = numerator / denominator := by
      apply coordinate_div_eq_div_of_cross _ _ _ _
        (RFAP.ConstructiveFraction.mul_ne_zero_direct middleNonzero
          denominatorNonzero)
        denominatorNonzero
      ring1

theorem logCoefficient_telescope {index : Nat} (positive : 1 ≤ index)
    (degree : Nat) :
    CCL.FiniteComplexLog.coefficient index *
        ((priorOdd (index + 1) : Coordinate) /
          (priorOdd (index + 1 + degree) : Coordinate)) =
      (priorOdd index : Coordinate) /
        (priorOdd (index + (degree + 1)) : Coordinate) := by
  rw [logCoefficient_eq_priorOdd_ratio positive]
  have middleNonzero : (priorOdd (index + 1) : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (priorOdd_pos (positive.trans (Nat.le_add_right index 1)))).ne'
  have denominatorNonzero :
      (priorOdd (index + 1 + degree) : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (priorOdd_pos
        ((positive.trans (Nat.le_add_right index 1)).trans
          (Nat.le_add_right (index + 1) degree)))).ne'
  rw [div_mul_div_telescope _ _ _ middleNonzero denominatorNonzero]
  congr 2
  congr 1
  ring1

/-- The final monomial contributed by a finite complex-log Horner tail. -/
def logHornerTerm (w : Gaussian) : Nat → Nat → Gaussian
  | _, 0 => 1
  | index, degree + 1 =>
      CCL.FiniteComplexLog.scalar
          (CCL.FiniteComplexLog.coefficient index) *
        w * logHornerTerm w (index + 1) degree

@[simp] theorem logHornerTerm_zero (w : Gaussian) (index : Nat) :
    logHornerTerm w index 0 = 1 := rfl

@[simp] theorem logHornerTerm_succ (w : Gaussian) (index degree : Nat) :
    logHornerTerm w index (degree + 1) =
      CCL.FiniteComplexLog.scalar
          (CCL.FiniteComplexLog.coefficient index) *
        w * logHornerTerm w (index + 1) degree := rfl

private theorem scalar_mul_eq_scale (factor : Coordinate) (value : Gaussian) :
    CCL.FiniteComplexLog.scalar factor * value =
      CCL.FiniteExp.scale factor value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteComplexLog.scalar,
      CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem logHornerTerm_eq_scaled_power (w : Gaussian) :
    ∀ (degree index : Nat), 1 ≤ index →
      logHornerTerm w index degree =
        CCL.FiniteExp.scale
          ((priorOdd index : Coordinate) /
            (priorOdd (index + degree) : Coordinate))
          (w ^ degree)
  | 0, index, positive => by
      rw [logHornerTerm_zero, pow_zero]
      have same : priorOdd (index + 0) = priorOdd index := by
        rw [Nat.add_zero]
      rw [same]
      have denominatorNonzero : (priorOdd index : Coordinate) ≠ 0 :=
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (priorOdd_pos positive)).ne'
      have quotientOne :
          (priorOdd index : Coordinate) / (priorOdd index : Coordinate) = 1 :=
        (coordinate_div_eq_div_of_cross
          (priorOdd index : Coordinate) (priorOdd index : Coordinate) 1 1
          denominatorNonzero (by decide) (by
            rw [RFAP.ConstructiveFraction.one_mul,
              RFAP.ConstructiveFraction.mul_one_direct])).trans (by decide)
      rw [quotientOne]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, one_re, one_im] <;> ring1
  | degree + 1, index, positive => by
      rw [logHornerTerm_succ,
        logHornerTerm_eq_scaled_power w degree (index + 1) (by omega),
        scalar_mul_eq_scale, scale_mul_scale, pow_succ]
      have coefficientIdentity := logCoefficient_telescope positive degree
      rw [coefficientIdentity]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

/-- Increasing the finite local-log Horner depth appends exactly one bounded
odd monomial. -/
theorem complexLog_horner_succ_eq_add_term (w : Gaussian) :
    ∀ (degree index : Nat),
      CCL.FiniteComplexLog.horner w index (degree + 1) =
        CCL.FiniteComplexLog.horner w index degree +
          logHornerTerm w index (degree + 1)
  | 0, index => by
      rw [CCL.FiniteComplexLog.horner_succ,
        CCL.FiniteComplexLog.horner_zero,
        CCL.FiniteComplexLog.horner_zero,
        CCL.FiniteComplexLog.step_eq,
        logHornerTerm_succ, logHornerTerm_zero]
  | degree + 1, index => by
      calc
        CCL.FiniteComplexLog.horner w index (degree + 1 + 1) =
            CCL.FiniteComplexLog.step w index
              (CCL.FiniteComplexLog.horner w (index + 1)
                (degree + 1)) := rfl
        _ = CCL.FiniteComplexLog.step w index
              (CCL.FiniteComplexLog.horner w (index + 1) degree +
                logHornerTerm w (index + 1) (degree + 1)) := by
          rw [complexLog_horner_succ_eq_add_term w degree (index + 1)]
        _ = CCL.FiniteComplexLog.step w index
              (CCL.FiniteComplexLog.horner w (index + 1) degree) +
            logHornerTerm w index (degree + 1 + 1) := by
          have termStep :
              CCL.FiniteComplexLog.scalar
                    (CCL.FiniteComplexLog.coefficient index) *
                  w * logHornerTerm w (index + 1) (degree + 1) =
                logHornerTerm w index (degree + 1 + 1) := rfl
          rw [CCL.FiniteComplexLog.step_eq,
            CCL.FiniteComplexLog.step_eq, ← termStep]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im,
              CCL.FiniteComplexLog.scalar, one_re, one_im] <;> ring1
        _ = CCL.FiniteComplexLog.horner w index (degree + 1) +
            logHornerTerm w index (degree + 1 + 1) := rfl

theorem complexLog_horner_eq_finiteSum (w : Gaussian) :
    ∀ (depth index : Nat),
      CCL.FiniteComplexLog.horner w index depth =
        finiteSum (logHornerTerm w index) (depth + 1)
  | 0, index => by
      rw [CCL.FiniteComplexLog.horner_zero, finiteSum_succ,
        finiteSum_zero, logHornerTerm_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
  | depth + 1, index => by
      calc
        CCL.FiniteComplexLog.horner w index (depth + 1) =
            CCL.FiniteComplexLog.horner w index depth +
              logHornerTerm w index (depth + 1) :=
          complexLog_horner_succ_eq_add_term w depth index
        _ = finiteSum (logHornerTerm w index) (depth + 1) +
              logHornerTerm w index (depth + 1) := by
          rw [complexLog_horner_eq_finiteSum w depth index]
        _ = finiteSum (logHornerTerm w index) (depth + 1 + 1) := rfl

/-- One displayed odd logarithm monomial `2 z^(2j+1)/(2j+1)`. -/
def localLogTerm (z : Gaussian) (degree : Nat) : Gaussian :=
  CCL.FiniteExp.scale
    (2 / (2 * (degree : Coordinate) + 1)) (z ^ (2 * degree + 1))

theorem outputFactor_mul_logHornerTerm (z : Gaussian) (degree : Nat) :
    CCL.FiniteComplexLog.outputFactor z *
        logHornerTerm (CCL.FiniteComplexLog.squaredArgument z)
          1 degree =
      localLogTerm z degree := by
  rw [CCL.FiniteComplexLog.outputFactor_eq,
    CCL.FiniteComplexLog.squaredArgument_eq,
    logHornerTerm_eq_scaled_power _ degree 1 (by decide),
    scalar_mul_eq_scale, scale_mul_scale]
  have priorOne : priorOdd 1 = 1 := by decide
  have priorDegree : priorOdd (1 + degree) = 2 * degree + 1 := by
    unfold priorOdd
    omega
  rw [priorOne, priorDegree]
  have denominatorCast :
      ((2 * degree + 1 : Nat) : Coordinate) =
        2 * (degree : Coordinate) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rfl
  rw [denominatorCast]
  rw [show ((1 : Nat) : Coordinate) = 1 by rfl]
  change CCL.FiniteExp.scale
      ((2 : Coordinate) * (1 / (2 * (degree : Coordinate) + 1)))
      (z * (z * z) ^ degree) = localLogTerm z degree
  have coefficientIdentity :
      (2 : Coordinate) * (1 / (2 * (degree : Coordinate) + 1)) =
        2 / (2 * (degree : Coordinate) + 1) := by
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
  rw [coefficientIdentity, localLogTerm]
  congr 1
  calc
    z * (z * z) ^ degree = z * (z ^ 2) ^ degree := by rw [pow_two]
    _ = z * z ^ (2 * degree) := by rw [← pow_mul]
    _ = z ^ (2 * degree) * z :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
    _ = z ^ (2 * degree + 1) := (pow_succ z (2 * degree)).symm

/-- Exact bounded-polynomial identification of every complex-log sample. -/
theorem complexLog_sample_eq_finiteSum (z : Gaussian) (depth : Nat) :
    CCL.FiniteComplexLog.sample z depth =
      finiteSum (localLogTerm z) (depth + 1) := by
  rw [CCL.FiniteComplexLog.sample_eq,
    complexLog_horner_eq_finiteSum,
    mul_finiteSum_left]
  exact finiteSum_congr
    (fun degree => outputFactor_mul_logHornerTerm z degree) (depth + 1)

/-- The exact constant approximation.  It answers every refinement request
without changing its displayed rational sample. -/
def constantApproximation (value : Gaussian) : Approximation where
  sample := fun _ => value
  radiusSq := fun _ => 0
  radiusSq_nonneg := fun _ => by decide
  later_close := by
    intro earlier later order
    simp only [sub_self, normSq_zero]
    exact le_rfl
  refineIndex := fun current _ _ => current
  refineIndex_ge := by
    intro current target positive
    exact Nat.le_refl current
  refineIndex_accurate := by
    intro current target positive
    exact positive
  centerBound := normSq value
  centerBound_nonneg := normSq_nonneg value
  sample_bounded := by
    intro index
    exact le_rfl

def expZeroApproximation : Approximation :=
  CCL.FiniteExp.approximation 0 (by decide)

def oneApproximation : Approximation := constantApproximation 1

theorem expZero_sample (index : Nat) :
    expZeroApproximation.sample index = 1 :=
  CCL.FiniteExp.sample_zero index

theorem one_sample (index : Nat) : oneApproximation.sample index = 1 := rfl

/-- Constructive finite-request meaning of `exp(0) = 1`.  In fact both sides
display the same rational value at every index, so no refinement is required.
-/
def exp_zero_equivalent_one : Equivalent expZeroApproximation oneApproximation :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples
    expZeroApproximation oneApproximation 1 expZero_sample one_sample

end CCL.TranscendentalLaws
