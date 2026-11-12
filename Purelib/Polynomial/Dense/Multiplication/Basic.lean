module

public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Original dense multiplication over a commutative ring

The same coefficient Horner fold constructs the product, including over rings
with zero divisors. Its evaluation law does not assume a nonzero-product rule.
-/

public section

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial.Dense

variable {K : Type*} [CommRing K] [DecidableEq K]

/-- Polynomial multiplication as a finite Horner fold over the left factor.

Each original coefficient shifts the retained accumulator once and adds its
scaled right factor. The fold scans the unchanged left coefficient list from
the original empty polynomial accumulator. -/
@[expose] def mulPolynomial (p q : Basic.DensePolynomial K) : Basic.DensePolynomial K :=
  p.coeffs.foldl (fun acc a => Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale a q) 0

/-- The multiplication instance uses the finite polynomial Horner fold. -/
instance : Mul (Basic.DensePolynomial K) := ⟨Basic.DensePolynomial.mulPolynomial⟩

/-- Dense Horner multiplication returns an already normalized polynomial.

Every nonempty fold step ends with the original normalized addition. The
empty fold retains its normalized original accumulator. This holds over rings
with zero divisors and does not require nonzero products of leading entries.
-/
theorem normalize_mul (p q : Basic.DensePolynomial K) :
    (p * q).normalize = p * q := by
  have foldNormalized : ∀ (coefficients : List K) (accumulator : Basic.DensePolynomial K),
      accumulator.normalize = accumulator →
      (coefficients.foldl
        (fun value coefficient => Basic.DensePolynomial.shift 1 value +
          Basic.DensePolynomial.scale coefficient q) accumulator).normalize =
        coefficients.foldl
          (fun value coefficient => Basic.DensePolynomial.shift 1 value +
            Basic.DensePolynomial.scale coefficient q) accumulator := by
    intro coefficients
    induction coefficients with
    | nil => intro accumulator same; exact same
    | cons coefficient remaining previous =>
        intro accumulator _
        exact previous _ (Basic.DensePolynomial.normalize_add _ _)
  exact foldNormalized p.coeffs 0 rfl

/-- Evaluating a polynomial multiplication fold yields its scalar Horner recurrence.

Each coefficient contribution is multiplied by the fixed right factor's value, and the initial scalar state is the
accumulator polynomial's value. -/
private theorem eval_foldl_mulPolynomial (x : K) (q : Basic.DensePolynomial K)
    (cs : List K) (acc : Basic.DensePolynomial K) :
    (cs.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) acc).eval x =
      cs.foldl (fun value a => value * x + a * q.eval x) (acc.eval x) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_shift, Basic.DensePolynomial.eval_scale]
      rewrite [pow_one]
      exact Eq.refl _

omit [DecidableEq K] in
/-- Scaling each Horner contribution and the initial accumulator scales the final value. -/
private theorem foldl_scaled_horner (x c : K) (cs : List K) (acc : K) :
    cs.foldl (fun value a => value * x + a * c) (acc * c) =
      cs.foldl (fun value a => value * x + a) acc * c := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [show acc * c * x + a * c = (acc * x + a) * c by ring1, ih]

/-- Evaluation of dense multiplication is multiplication of the two values. -/
@[simp] theorem eval_mul (p q : Basic.DensePolynomial K) (x : K) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial,
    Basic.DensePolynomial.eval_foldl_mulPolynomial]
  rw [Basic.DensePolynomial.eval_zero]
  simpa only [zero_mul, Basic.DensePolynomial.eval, Basic.DensePolynomial.evalCoeffs] using
    Basic.DensePolynomial.foldl_scaled_horner x (q.eval x) p.coeffs 0
end Purelib.Polynomial.Dense.Basic.DensePolynomial
