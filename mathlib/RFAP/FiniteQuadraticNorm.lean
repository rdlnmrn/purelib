import mathlib.RFAP.FiniteIntegerPolynomial
import mathlib.Tactic.QuotientFreeOmega

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace RFAP.FiniteQuadraticNorm

open RFAP.IntegerPolynomialCertificate

/-- Two coordinates in the basis `1,a`, where `a²=t*a-1`. -/
structure TracePair (K : Type*) where
  scalar : K
  generator : K

namespace TracePair

variable {K : Type*} [RFAP.ExplicitField K]

def zero : TracePair K := ⟨0, 0⟩

def one : TracePair K := ⟨1, 0⟩

def add (left right : TracePair K) : TracePair K :=
  ⟨left.scalar + right.scalar, left.generator + right.generator⟩

def scale (factor : K) (pair : TracePair K) : TracePair K :=
  ⟨factor * pair.scalar, factor * pair.generator⟩

def neg (pair : TracePair K) : TracePair K :=
  ⟨-pair.scalar, -pair.generator⟩

def sub (left right : TracePair K) : TracePair K :=
  ⟨left.scalar - right.scalar, left.generator - right.generator⟩

def mul (trace : K) (left right : TracePair K) : TracePair K :=
  ⟨left.scalar * right.scalar - left.generator * right.generator,
    left.scalar * right.generator + left.generator * right.scalar +
      trace * left.generator * right.generator⟩

def alpha : TracePair K := ⟨0, 1⟩

omit [RFAP.ExplicitField K] in
@[ext] theorem ext {left right : TracePair K}
    (scalar : left.scalar = right.scalar)
    (generator : left.generator = right.generator) : left = right := by
  cases left
  cases right
  simp_all

theorem mul_zero_left (trace : K) (pair : TracePair K) :
    mul trace zero pair = zero := by
  apply ext <;> simp [mul, zero]

theorem mul_one_left (trace : K) (pair : TracePair K) :
    mul trace one pair = pair := by
  apply ext <;> simp [mul, one]

theorem mul_add_left (trace : K) (first second right : TracePair K) :
    mul trace (add first second) right =
      add (mul trace first right) (mul trace second right) := by
  apply ext <;> simp only [mul, add] <;> ring0

theorem mul_scale_left (trace factor : K) (left right : TracePair K) :
    mul trace (scale factor left) right =
      scale factor (mul trace left right) := by
  apply ext <;> simp only [mul, scale] <;> ring0

theorem alpha_mul (trace : K) (pair : TracePair K) :
    mul trace alpha pair =
      ⟨-pair.generator, pair.scalar + trace * pair.generator⟩ := by
  apply ext <;> simp only [mul, alpha] <;> ring0

/-- Evaluate an ascending integer polynomial at the formal quadratic
generator, retaining its two trace coordinates. -/
def eval : List Int → K → TracePair K
  | [], _ => zero
  | coefficient :: remaining, trace =>
      let recursive := eval remaining trace
      ⟨(coefficient : K) - recursive.generator,
        recursive.scalar + trace * recursive.generator⟩

@[simp] theorem eval_nil (trace : K) : eval [] trace = zero := rfl

@[simp] theorem eval_cons (coefficient : Int) (remaining : List Int)
    (trace : K) :
    eval (coefficient :: remaining) trace =
      ⟨(coefficient : K) - (eval remaining trace).generator,
        (eval remaining trace).scalar +
          trace * (eval remaining trace).generator⟩ := rfl

theorem eval_add (left right : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.add left right) trace =
      add (eval left trace) (eval right trace) := by
  induction left generalizing right with
  | nil =>
      apply ext <;> simp [RFAP.IntegerPolynomialCertificate.add, eval, zero, add]
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil =>
          apply ext <;> simp [RFAP.IntegerPolynomialCertificate.add, eval,
            zero, add]
      | cons other others =>
          rw [RFAP.IntegerPolynomialCertificate.add, eval_cons,
            eval_cons, eval_cons, inductionHypothesis others]
          apply ext <;> simp only [add, Int.cast_add] <;> ring0

theorem eval_scale (factor : Int) (coefficients : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.scale factor coefficients) trace =
      scale (factor : K) (eval coefficients trace) := by
  induction coefficients with
  | nil =>
      apply ext <;> simp [RFAP.IntegerPolynomialCertificate.scale,
        eval, zero, scale]
  | cons coefficient remaining inductionHypothesis =>
      rw [RFAP.IntegerPolynomialCertificate.scale, eval_cons, eval_cons,
        inductionHypothesis]
      apply ext <;>
        simp only [scale, QuotientFreeRing.intCast_mul] <;> ring0

theorem eval_neg (coefficients : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.neg coefficients) trace =
      neg (eval coefficients trace) := by
  rw [RFAP.IntegerPolynomialCertificate.neg, eval_scale]
  apply ext <;> simp only [scale, neg, Int.cast_neg, Int.cast_one] <;> ring0

theorem eval_sub (left right : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.sub left right) trace =
      sub (eval left trace) (eval right trace) := by
  rw [RFAP.IntegerPolynomialCertificate.sub, eval_add, eval_neg]
  apply ext <;> simp only [add, neg, sub] <;> ring0

theorem eval_shift (coefficients : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.shift coefficients) trace =
      mul trace alpha (eval coefficients trace) := by
  rw [RFAP.IntegerPolynomialCertificate.shift, eval_cons,
    alpha_mul]
  apply ext <;> simp only [Int.cast_zero, zero_sub]

theorem eval_mul (left right : List Int) (trace : K) :
    eval (RFAP.IntegerPolynomialCertificate.mul left right) trace =
      mul trace (eval left trace) (eval right trace) := by
  induction left with
  | nil =>
      rw [RFAP.IntegerPolynomialCertificate.mul, eval_nil, mul_zero_left]
  | cons coefficient remaining inductionHypothesis =>
      rw [RFAP.IntegerPolynomialCertificate.mul, eval_add, eval_scale]
      change add
          (scale (coefficient : K) (eval right trace))
          (eval (RFAP.IntegerPolynomialCertificate.shift
            (RFAP.IntegerPolynomialCertificate.mul remaining right)) trace) = _
      rw [eval_shift, inductionHypothesis, eval_cons]
      apply ext <;> simp only [add, scale, mul, alpha] <;> ring0

/-- Appending a zero in a new highest-degree slot does not change evaluation
at the formal quadratic generator. -/
theorem eval_append_zero : ∀ coefficients : List Int, ∀ trace : K,
    eval (coefficients ++ [0]) trace = eval coefficients trace
  | [], trace => by
      apply ext <;> simp [eval, zero]
  | coefficient :: remaining, trace => by
      rw [List.cons_append, eval_cons, eval_cons,
        eval_append_zero remaining trace]

/-- Removing leading zeroes from a descending coefficient list does not
change evaluation after it is returned to ascending order. -/
theorem eval_reverse_dropWhile_zero : ∀ values : List Int, ∀ trace : K,
    eval ((values.dropWhile fun value => value = 0).reverse) trace =
      eval values.reverse trace
  | [], trace => rfl
  | value :: remaining, trace => by
      by_cases valueZero : value = 0
      · subst value
        rw [List.dropWhile_cons_of_pos (by decide), List.reverse_cons,
          eval_append_zero, eval_reverse_dropWhile_zero remaining trace]
      · rw [List.dropWhile_cons_of_neg (by simpa using valueZero)]

/-- A coefficient identity proved in the canonical rational embedding can
be evaluated at the formal quadratic generator over every explicit field.
Only finite list normalization is involved. -/
theorem eval_eq_of_ofAscending_eq
    {left right : List Int}
    (equal :
      RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending left =
        RFAP.FiniteIntegerPolynomial.IntegerPolynomial.ofAscending right)
    (trace : K) :
    eval left trace = eval right trace := by
  have normalized :=
    RFAP.FiniteIntegerPolynomial.normalized_reverse_eq_of_ofAscending_eq equal
  calc
    eval left trace =
        eval ((left.reverse.dropWhile fun value => value = 0).reverse)
          trace := by
      rw [eval_reverse_dropWhile_zero left.reverse trace,
        List.reverse_reverse]
    _ = eval ((right.reverse.dropWhile fun value => value = 0).reverse)
          trace := by rw [normalized]
    _ = eval right trace := by
      rw [eval_reverse_dropWhile_zero right.reverse trace,
        List.reverse_reverse]

/-- Conjugate norm of one reduced pair. -/
def norm (trace : K) (pair : TracePair K) : K :=
  pair.scalar * pair.scalar +
    trace * pair.scalar * pair.generator +
    pair.generator * pair.generator

theorem norm_mul (trace : K) (left right : TracePair K) :
    norm trace (mul trace left right) =
      norm trace left * norm trace right := by
  simp only [norm, mul]
  ring0

/-- Trace of a reduced quadratic value, namely the sum with its conjugate. -/
def traceValue (trace : K) (pair : TracePair K) : K :=
  2 * pair.scalar + trace * pair.generator

/-- The Lucas recurrence intrinsic to the trace relation. -/
def lucas : Nat → K → K
  | 0, _ => 2
  | 1, trace => trace
  | index + 2, trace =>
      trace * lucas (index + 1) trace - lucas index trace

/-- Finite powers of the formal quadratic generator. -/
def alphaPower : Nat → K → TracePair K
  | 0, _ => one
  | exponent + 1, trace => mul trace alpha (alphaPower exponent trace)

@[simp] theorem alphaPower_zero (trace : K) :
    alphaPower 0 trace = one := rfl

@[simp] theorem alphaPower_succ (exponent : Nat) (trace : K) :
    alphaPower (exponent + 1) trace =
      mul trace alpha (alphaPower exponent trace) := rfl

theorem alpha_square_action (trace : K) (pair : TracePair K) :
    mul trace alpha (mul trace alpha pair) =
      sub (scale trace (mul trace alpha pair)) pair := by
  apply ext <;> simp only [mul, alpha, sub, scale] <;> ring0

theorem alphaPower_succ_succ (index : Nat) (trace : K) :
    alphaPower (index + 2) trace =
      sub (scale trace (alphaPower (index + 1) trace))
        (alphaPower index trace) := by
  rw [show index + 2 = (index + 1) + 1 by omega0,
    alphaPower_succ, alphaPower_succ, alpha_square_action]

theorem traceValue_sub (trace : K) (left right : TracePair K) :
    traceValue trace (sub left right) =
      traceValue trace left - traceValue trace right := by
  simp only [traceValue, sub]
  ring0

theorem traceValue_scale (trace factor : K) (pair : TracePair K) :
    traceValue trace (scale factor pair) =
      factor * traceValue trace pair := by
  simp only [traceValue, scale]
  ring0

theorem traceValue_alphaPower : ∀ index : Nat, ∀ trace : K,
    traceValue trace (alphaPower index trace) = lucas index trace
  | 0, trace => by simp [traceValue, alphaPower, one, lucas]
  | 1, trace => by simp [traceValue, alphaPower, one, alpha, mul, lucas]
  | index + 2, trace => by
      rw [alphaPower_succ_succ, traceValue_sub, traceValue_scale,
        traceValue_alphaPower (index + 1) trace,
        traceValue_alphaPower index trace, lucas]

theorem norm_alpha (trace : K) : norm trace alpha = 1 := by
  simp [norm, alpha]

theorem norm_alphaPower : ∀ exponent : Nat, ∀ trace : K,
    norm trace (alphaPower exponent trace) = 1
  | 0, trace => by simp [alphaPower, one, norm]
  | exponent + 1, trace => by
      rw [alphaPower_succ, norm_mul, norm_alpha,
        norm_alphaPower exponent trace, one_mul]

theorem norm_sub_one (trace : K) (pair : TracePair K) :
    norm trace (sub pair one) =
      norm trace pair + 1 - traceValue trace pair := by
  simp only [norm, sub, one, traceValue]
  ring0

theorem norm_alphaPower_sub_one (exponent : Nat) (trace : K) :
    norm trace (sub (alphaPower exponent trace) one) =
      2 - lucas exponent trace := by
  rw [norm_sub_one, norm_alphaPower, traceValue_alphaPower]
  ring0

end TracePair

namespace IntegerPolynomial

/-- Ascending coefficients of `X^degree`. -/
def monomialCoefficients : Nat → List Int
  | 0 => [1]
  | degree + 1 => shift (monomialCoefficients degree)

/-- Ascending coefficients of `X^degree-1`. -/
def powerMinusOneCoefficients (degree : Nat) : List Int :=
  sub (monomialCoefficients degree) [1]

@[simp] theorem eval_monomialCoefficients
    {K : Type*} [RFAP.ExplicitField K] : ∀ degree : Nat, ∀ point : K,
    eval (monomialCoefficients degree) point = point ^ degree
  | 0, point => by
      simp [monomialCoefficients]
  | degree + 1, point => by
      rw [monomialCoefficients, eval_shift,
        eval_monomialCoefficients degree point, pow_succ]
      ring0

@[simp] theorem eval_powerMinusOneCoefficients
    {K : Type*} [RFAP.ExplicitField K] (degree : Nat) (point : K) :
    eval (powerMinusOneCoefficients degree) point = point ^ degree - 1 := by
  rw [powerMinusOneCoefficients, eval_sub, eval_monomialCoefficients]
  simp only [eval_cons, eval_nil, Int.cast_one, mul_zero, add_zero]

theorem eval_monomialCoefficients_pair {K : Type*} [RFAP.ExplicitField K] :
    ∀ degree : Nat, ∀ trace : K,
    TracePair.eval (monomialCoefficients degree) trace =
      TracePair.alphaPower degree trace
  | 0, trace => by
      apply TracePair.ext <;>
        simp [monomialCoefficients, TracePair.eval, TracePair.alphaPower,
          TracePair.one, TracePair.zero]
  | degree + 1, trace => by
      rw [monomialCoefficients, TracePair.eval_shift,
        eval_monomialCoefficients_pair degree trace,
        TracePair.alphaPower_succ]

theorem eval_powerMinusOneCoefficients_pair
    {K : Type*} [RFAP.ExplicitField K] (degree : Nat) (trace : K) :
    TracePair.eval (powerMinusOneCoefficients degree) trace =
      TracePair.sub (TracePair.alphaPower degree trace) TracePair.one := by
  rw [powerMinusOneCoefficients, TracePair.eval_sub,
    eval_monomialCoefficients_pair]
  apply TracePair.ext <;>
    simp [TracePair.eval, TracePair.one, TracePair.zero, TracePair.sub]

/-- Coefficient-level reduction to `A(t)+B(t)*a`. -/
def reduce : List Int → List Int × List Int
  | [] => ([], [])
  | coefficient :: remaining =>
      let recursive := reduce remaining
      (sub [coefficient] recursive.2,
        add recursive.1 (mul [0, 1] recursive.2))

@[simp] theorem reduce_nil : reduce [] = ([], []) := rfl

@[simp] theorem reduce_cons (coefficient : Int) (remaining : List Int) :
    reduce (coefficient :: remaining) =
      (sub [coefficient] (reduce remaining).2,
        add (reduce remaining).1 (mul [0, 1] (reduce remaining).2)) := rfl

theorem eval_reduce {K : Type*} [RFAP.ExplicitField K] :
    ∀ coefficients : List Int, ∀ trace : K,
    eval (reduce coefficients).1 trace =
        (TracePair.eval coefficients trace).scalar ∧
      eval (reduce coefficients).2 trace =
        (TracePair.eval coefficients trace).generator
  | [], trace => by simp [reduce, TracePair.eval, TracePair.zero]
  | coefficient :: remaining, trace => by
      have recursive := eval_reduce remaining trace
      rw [reduce_cons, eval_sub, eval_add, eval_mul,
        recursive.1, recursive.2, TracePair.eval_cons]
      simp only [eval_cons, eval_nil, Int.cast_zero, Int.cast_one, mul_zero,
        add_zero, zero_add, mul_one]
      constructor <;> dsimp only

/-- Integer trace-norm coefficients `A²+tAB+B²`. -/
def normCoefficients (coefficients : List Int) : List Int :=
  let reduced := reduce coefficients
  add (add (mul reduced.1 reduced.1)
      (mul [0, 1] (mul reduced.1 reduced.2)))
    (mul reduced.2 reduced.2)

theorem eval_normCoefficients {K : Type*} [RFAP.ExplicitField K]
    (coefficients : List Int) (trace : K) :
    eval (normCoefficients coefficients) trace =
      TracePair.norm trace (TracePair.eval coefficients trace) := by
  unfold normCoefficients
  rw [eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_mul,
    (eval_reduce coefficients trace).1,
    (eval_reduce coefficients trace).2]
  simp only [eval_cons, eval_nil, Int.cast_zero, Int.cast_one, mul_zero,
    add_zero, zero_add, mul_one, TracePair.norm]
  ring0

/-- The finite trace norm is multiplicative. -/
theorem eval_normCoefficients_mul {K : Type*} [RFAP.ExplicitField K]
    (left right : List Int) (trace : K) :
    eval (normCoefficients (mul left right)) trace =
      eval (normCoefficients left) trace *
        eval (normCoefficients right) trace := by
  rw [eval_normCoefficients, TracePair.eval_mul, TracePair.norm_mul,
    ← eval_normCoefficients, ← eval_normCoefficients]

theorem eval_norm_powerMinusOneCoefficients
    {K : Type*} [RFAP.ExplicitField K] (degree : Nat) (trace : K) :
    eval (normCoefficients (powerMinusOneCoefficients degree)) trace =
      2 - TracePair.lucas degree trace := by
  rw [eval_normCoefficients, eval_powerMinusOneCoefficients_pair,
    TracePair.norm_alphaPower_sub_one]

end IntegerPolynomial

end RFAP.FiniteQuadraticNorm
