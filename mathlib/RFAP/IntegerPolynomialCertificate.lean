import mathlib.Tactic.QuotientFreeRing
import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ExplicitField

/-!
# Finite integer-polynomial certificates

Integer coefficient lists are stored in ascending degree order.  The
primitive-recursive operations below let a literal finite Bezout identity be
checked by kernel reduction over `Int`, then evaluated in any constructive
explicit field.  This is useful for prime-field exclusions without listing
or searching an ambient carrier.
-/

namespace RFAP.IntegerPolynomialCertificate

/-- Evaluate an ascending finite integer coefficient list by Horner's rule. -/
def eval {K : Type*} [RFAP.ExplicitField K] : List Int → K → K
  | [], _ => 0
  | coefficient :: remaining, value =>
      (coefficient : K) + value * eval remaining value

@[simp] theorem eval_nil {K : Type*} [RFAP.ExplicitField K] (value : K) :
    eval [] value = 0 := rfl

@[simp] theorem eval_cons {K : Type*} [RFAP.ExplicitField K]
    (coefficient : Int) (remaining : List Int) (value : K) :
    eval (coefficient :: remaining) value =
      (coefficient : K) + value * eval remaining value := rfl

/-- Coefficientwise addition, padding the shorter high-degree tail by zero. -/
def add : List Int → List Int → List Int
  | [], right => right
  | left, [] => left
  | left :: lefts, right :: rights => (left + right) :: add lefts rights

/-- Multiply every coefficient by one displayed integer. -/
def scale (factor : Int) : List Int → List Int
  | [] => []
  | coefficient :: remaining =>
      factor * coefficient :: scale factor remaining

/-- Finite convolution in ascending-degree representation. -/
def mul : List Int → List Int → List Int
  | [], _ => []
  | coefficient :: remaining, right =>
      add (scale coefficient right) (0 :: mul remaining right)

theorem eval_add {K : Type*} [RFAP.ExplicitField K]
    (left right : List Int) (value : K) :
    eval (add left right) value = eval left value + eval right value := by
  induction left generalizing right with
  | nil => simp [add]
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil => simp [add]
      | cons other others =>
          simp only [add, eval_cons, Int.cast_add,
            inductionHypothesis others]
          ring1

theorem eval_scale {K : Type*} [RFAP.ExplicitField K]
    (factor : Int) (coefficients : List Int) (value : K) :
    eval (scale factor coefficients) value =
      (factor : K) * eval coefficients value := by
  induction coefficients with
  | nil => simp [scale]
  | cons coefficient remaining inductionHypothesis =>
      simp only [scale, eval_cons, QuotientFreeRing.intCast_mul,
        inductionHypothesis]
      ring1

theorem eval_mul {K : Type*} [RFAP.ExplicitField K]
    (left right : List Int) (value : K) :
    eval (mul left right) value = eval left value * eval right value := by
  induction left with
  | nil => simp [mul]
  | cons coefficient remaining inductionHypothesis =>
      simp only [mul, eval_add, eval_scale, eval_cons,
        inductionHypothesis]
      ring1

/-- Coefficientwise negation. -/
def neg (coefficients : List Int) : List Int :=
  scale (-1) coefficients

/-- Coefficientwise subtraction, padding the shorter high-degree tail. -/
def sub (left right : List Int) : List Int :=
  add left (neg right)

theorem eval_neg {K : Type*} [RFAP.ExplicitField K]
    (coefficients : List Int) (value : K) :
    eval (neg coefficients) value = -eval coefficients value := by
  rw [neg, eval_scale]
  simp only [Int.cast_neg, Int.cast_one]
  ring1

theorem eval_sub {K : Type*} [RFAP.ExplicitField K]
    (left right : List Int) (value : K) :
    eval (sub left right) value = eval left value - eval right value := by
  rw [sub, eval_add, eval_neg]
  ring1

/-- Multiply by the indeterminate by shifting every coefficient up one
degree. -/
def shift (coefficients : List Int) : List Int := 0 :: coefficients

theorem eval_shift {K : Type*} [RFAP.ExplicitField K]
    (coefficients : List Int) (value : K) :
    eval (shift coefficients) value = value * eval coefficients value := by
  unfold shift
  simp only [eval_cons, Int.cast_zero, zero_add]

theorem getLast?_shift_of_ne_nil (coefficients : List Int)
    (nonempty : coefficients ≠ []) :
    (shift coefficients).getLast? = coefficients.getLast? := by
  cases coefficients with
  | nil => exact (nonempty rfl).elim
  | cons coefficient remaining =>
      unfold shift
      rfl

theorem length_scale (factor : Int) (coefficients : List Int) :
    (scale factor coefficients).length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [scale, List.length_cons, inductionHypothesis]

theorem length_add (left right : List Int) :
    (add left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp only [add, List.length_nil, Nat.zero_max]
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil => simp only [add, List.length_cons, List.length_nil,
          Nat.max_zero]
      | cons other others =>
          simp only [add, List.length_cons, inductionHypothesis,
            Nat.succ_max_succ]

theorem length_neg (coefficients : List Int) :
    (neg coefficients).length = coefficients.length := by
  exact length_scale (-1) coefficients

theorem length_sub (left right : List Int) :
    (sub left right).length = max left.length right.length := by
  rw [sub, length_add, length_neg]

/-- Adding a strictly shorter coefficient list cannot change the leading
coefficient of the longer list. -/
theorem getLast?_add_of_length_lt : ∀ left right : List Int,
    right.length < left.length →
      (add left right).getLast? = left.getLast?
  | [], right, shorter => by
      simp only [List.length_nil] at shorter
      omega0
  | coefficient :: remaining, [], shorter => rfl
  | coefficient :: remaining, other :: others, shorter => by
      have tailsShorter : others.length < remaining.length := by
        simpa only [List.length_cons, Nat.add_lt_add_iff_right] using shorter
      cases remaining with
      | nil =>
          simp only [List.length_nil, Nat.not_lt_zero] at tailsShorter
      | cons next rest =>
          cases others with
          | nil => rfl
          | cons otherNext otherRest =>
              simp only [add, List.getLast?_cons_cons]
              exact getLast?_add_of_length_lt (next :: rest)
                (otherNext :: otherRest) tailsShorter

theorem getLast?_neg (coefficients : List Int) :
    (neg coefficients).getLast? = coefficients.getLast?.map (fun value => -value) := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      cases remaining with
      | nil => simp [neg, scale]
      | cons next rest =>
          simp only [neg, scale, List.getLast?_cons_cons] at inductionHypothesis ⊢
          exact inductionHypothesis

theorem getLast?_sub_of_length_lt (left right : List Int)
    (shorter : right.length < left.length) :
    (sub left right).getLast? = left.getLast? := by
  unfold sub
  apply getLast?_add_of_length_lt
  rw [length_neg]
  exact shorter

/-- A finite natural power in the coefficient-list ring. -/
def power (coefficients : List Int) : Nat → List Int
  | 0 => [1]
  | exponent + 1 => mul (power coefficients exponent) coefficients

@[simp] theorem power_zero (coefficients : List Int) :
    power coefficients 0 = [1] := rfl

@[simp] theorem power_succ (coefficients : List Int) (exponent : Nat) :
    power coefficients (exponent + 1) =
      mul (power coefficients exponent) coefficients := rfl

theorem eval_power {K : Type*} [RFAP.ExplicitField K]
    (coefficients : List Int) (exponent : Nat) (value : K) :
    eval (power coefficients exponent) value =
      eval coefficients value ^ exponent := by
  induction exponent with
  | zero =>
      simp only [power_zero, eval_cons, eval_nil, Int.cast_one, mul_zero,
        add_zero, pow_zero]
  | succ exponent inductionHypothesis =>
      rw [power_succ, eval_mul, inductionHypothesis, pow_succ]

/-- Substitute one finite integer polynomial into another by Horner
recursion. -/
def compose : List Int → List Int → List Int
  | [], _ => []
  | coefficient :: remaining, inner =>
      add [coefficient] (mul inner (compose remaining inner))

@[simp] theorem compose_nil (inner : List Int) : compose [] inner = [] := rfl

@[simp] theorem compose_cons (coefficient : Int) (remaining inner : List Int) :
    compose (coefficient :: remaining) inner =
      add [coefficient] (mul inner (compose remaining inner)) := rfl

theorem eval_compose {K : Type*} [RFAP.ExplicitField K]
    (outer inner : List Int) (value : K) :
    eval (compose outer inner) value =
      eval outer (eval inner value) := by
  induction outer with
  | nil => simp only [compose_nil, eval_nil]
  | cons coefficient remaining inductionHypothesis =>
      rw [compose_cons, eval_add, eval_mul, inductionHypothesis]
      simp only [eval_cons, eval_nil, mul_zero, add_zero]

/-- Add a displayed prefix of integer polynomials. -/
def finiteSum : Nat → (Nat → List Int) → List Int
  | 0, _ => []
  | count + 1, term => add (finiteSum count term) (term count)

@[simp] theorem finiteSum_zero (term : Nat → List Int) :
    finiteSum 0 term = [] := rfl

@[simp] theorem finiteSum_succ (count : Nat) (term : Nat → List Int) :
    finiteSum (count + 1) term =
      add (finiteSum count term) (term count) := rfl

/-- Evaluate a primitive-recursive sum directly in the target field. -/
def finiteValueSum {K : Type*} [RFAP.ExplicitField K] :
    Nat → (Nat → K) → K
  | 0, _ => 0
  | count + 1, term => finiteValueSum count term + term count

theorem eval_finiteSum {K : Type*} [RFAP.ExplicitField K]
    (count : Nat) (term : Nat → List Int) (value : K) :
    eval (finiteSum count term) value =
      finiteValueSum count (fun index => eval (term index) value) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteSum_succ, eval_add, inductionHypothesis,
        finiteValueSum]

/-- Multiply a displayed prefix of integer polynomials. -/
def finiteProduct : Nat → (Nat → List Int) → List Int
  | 0, _ => [1]
  | count + 1, term => mul (finiteProduct count term) (term count)

@[simp] theorem finiteProduct_zero (term : Nat → List Int) :
    finiteProduct 0 term = [1] := rfl

@[simp] theorem finiteProduct_succ (count : Nat)
    (term : Nat → List Int) :
    finiteProduct (count + 1) term =
      mul (finiteProduct count term) (term count) := rfl

/-- Evaluate the same primitive-recursive product directly in the target
field. -/
def finiteValueProduct {K : Type*} [RFAP.ExplicitField K] :
    Nat → (Nat → K) → K
  | 0, _ => 1
  | count + 1, term => finiteValueProduct count term * term count

theorem eval_finiteProduct {K : Type*} [RFAP.ExplicitField K]
    (count : Nat) (term : Nat → List Int) (value : K) :
    eval (finiteProduct count term) value =
      finiteValueProduct count (fun index => eval (term index) value) := by
  induction count with
  | zero =>
      simp only [finiteProduct_zero, eval_cons, eval_nil, Int.cast_one,
        mul_zero, add_zero, finiteValueProduct]
  | succ count inductionHypothesis =>
      rw [finiteProduct_succ, eval_mul, inductionHypothesis]
      rfl

/-- The finite list with one coefficient in the requested degree. -/
def monomial (degree : Nat) (coefficient : Int) : List Int :=
  List.replicate degree 0 ++ [coefficient]

theorem eval_monomial {K : Type*} [RFAP.ExplicitField K]
    (degree : Nat) (coefficient : Int) (value : K) :
    eval (monomial degree coefficient) value =
      (coefficient : K) * value ^ degree := by
  induction degree with
  | zero => simp [monomial, eval]
  | succ degree inductionHypothesis =>
      rw [monomial, List.replicate_succ, List.cons_append, eval_cons]
      rw [show List.replicate degree 0 ++ [coefficient] =
          monomial degree coefficient by rfl]
      rw [inductionHypothesis, pow_succ]
      simp only [Int.cast_zero, zero_add]
      ring1

/-- Coefficients of `X^modulus-X`. -/
def frobenius (modulus : Nat) : List Int :=
  add (monomial modulus 1) (monomial 1 (-1))

theorem eval_frobenius {K : Type*} [RFAP.ExplicitField K]
    (modulus : Nat) (value : K) :
    eval (frobenius modulus) value = value ^ modulus - value := by
  rw [frobenius, eval_add, eval_monomial, eval_monomial]
  simp only [Int.cast_one, one_mul]
  ring1

/-- A kernel-checkable finite Bezout identity
`left*cubic + right*(X^p-X) = 1 + p*correction`. -/
structure BezoutCertificate (modulus : Nat) (polynomial : List Int) where
  left : List Int
  right : List Int
  correction : List Int
  identity :
    add (mul left polynomial) (mul right (frobenius modulus)) =
      add [1] (scale (Int.ofNat modulus) correction)

/-- A checked certificate rules out a common root of the displayed integer
polynomial and the pointwise Frobenius equation in characteristic `p`. -/
theorem no_common_root {K : Type*} [RFAP.ExplicitField K] [Nontrivial K]
    {modulus : Nat} {polynomial : List Int}
    (certificate : BezoutCertificate modulus polynomial)
    (modulusZero : (modulus : K) = 0)
    (value : K) (polynomialZero : eval polynomial value = 0)
    (frobeniusValue : value ^ modulus = value) : False := by
  have evaluated := congrArg (fun coefficients => eval coefficients value)
    certificate.identity
  rw [eval_add, eval_mul, eval_mul, eval_frobenius,
    eval_add, eval_scale] at evaluated
  have frobeniusZero : value ^ modulus - value = 0 := by
    rw [frobeniusValue]
    ring1
  have modulusCast : ((Int.ofNat modulus : Int) : K) = (modulus : K) := by
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [polynomialZero, frobeniusZero, modulusCast, modulusZero] at evaluated
  have zeroOne : (0 : K) = 1 := by
    calc
      (0 : K) =
          eval certificate.left value * 0 +
            eval certificate.right value * 0 := by ring1
      _ = eval [1] value + 0 * eval certificate.correction value := evaluated
      _ = 1 := by
        simp only [eval_cons, eval_nil, Int.cast_one]
        ring1
  exact (one_ne_zero : (1 : K) ≠ 0) zeroOne.symm

end RFAP.IntegerPolynomialCertificate
