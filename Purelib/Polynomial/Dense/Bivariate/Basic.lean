module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.List.Replicate
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Fold
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (CoefficientPolynomial DensePolynomial)

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Polynomial

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic

set_option genInjectivity false in
/-- Outer coefficients are dense polynomials in the inner variable. -/
structure DenseBivariate (K : Type*) where
  /-- Outer coefficients in descending degree order, each retaining its dense inner-variable table. -/ coeffs : List
    (CoefficientPolynomial K)
deriving DecidableEq

constructive_injectivity DenseBivariate

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

section
@[expose] public section

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
/-- Dense bivariate polynomials over canonical Gaussian rational coefficients. -/
abbrev GaussianBivariate :=
  DenseBivariate Gaussian.Basic.Canonical

end Purelib.Polynomial.Dense.Bivariate.Basic
end

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The bivariate zero polynomial represented by an empty outer table. -/
def zero : DenseBivariate K := ⟨[]⟩

/-- A scalar constant represented by a singleton outer table of dense constants. -/
def constant (a : K) : DenseBivariate K :=
  ⟨[DensePolynomial.constant a]⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Evaluate the inner variable first and the outer variable second. -/
def eval (p : DenseBivariate K) (outer inner : K)
  : K :=
  p.coeffs.foldl
    (fun accumulator coefficient =>
      accumulator * outer + coefficient.eval inner) 0

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- A bivariate constant evaluates to its scalar coefficient. -/
@[simp] theorem eval_constant (a outer inner : K) :
    eval (constant a) outer inner = a := by
  simp [eval, constant, -eq_self, -iff_self] ; rfl

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- Appending a zero outer coefficient multiplies the accumulated evaluation by the outer argument. -/
private theorem eval_foldl_append_zero (outer inner : K)
    (coefficients : List (CoefficientPolynomial K)) (accumulator : K) :
    (coefficients ++ [0]).foldl
        (fun value (coefficient : CoefficientPolynomial K) =>
          value * outer + coefficient.eval inner)
        accumulator =
      coefficients.foldl
        (fun value (coefficient : CoefficientPolynomial K) =>
          value * outer + coefficient.eval inner)
        accumulator * outer := open Purelib in by
  rw [Data.List.Fold.foldl_append]
  let result := coefficients.foldl
    (fun value (coefficient : CoefficientPolynomial K) =>
      value * outer + coefficient.eval inner) accumulator
  change result * outer + 0 = result * outer
  exact _root_.add_zero _

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Removing leading zero outer polynomials preserves evaluation from zero. -/
private theorem eval_foldl_dropWhile_zero
    (coefficients : List (CoefficientPolynomial K)) (outer inner : K) :
    (coefficients.dropWhile (fun coefficient => coefficient.isZero)).foldl
        (fun value coefficient => value * outer + coefficient.eval inner) 0 =
      coefficients.foldl
        (fun value coefficient => value * outer + coefficient.eval inner) 0 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      by_cases zeroCoefficient : coefficient.isZero = true
      · rw [Data.List.DropWhile.cons_of_true _ _ _ zeroCoefficient, List.foldl_cons,
          DensePolynomial.eval_eq_zero_of_isZero
            zeroCoefficient]
        rw [show (0 : K) * outer + 0 = 0 by ring1]
        exact inductionHypothesis
      · have retained : coefficient.isZero = false := by
          cases observed : coefficient.isZero with
          | false => rfl
          | true => exact False.elim (zeroCoefficient observed)
        rw [Data.List.DropWhile.cons_of_false _ _ _ retained]
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Negating every coefficient and the initial accumulator negates the outer Horner value. -/
private theorem eval_foldl_map_neg (outer inner : K) :
    ∀ (coefficients : List (CoefficientPolynomial K)) (accumulator : K),
      (coefficients.map (-·)).foldl
          (fun value a => value * outer + a.eval inner) (-accumulator) =
        -coefficients.foldl
          (fun value a => value * outer + a.eval inner) accumulator
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.map_cons, List.foldl_cons, DensePolynomial.eval_neg]
      rw [show -accumulator * outer + -a.eval inner =
          -(accumulator * outer + a.eval inner) by ring1]
      exact eval_foldl_map_neg outer inner remaining
        (accumulator * outer + a.eval inner)
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Scaling all outer coefficients by one inner polynomial scales the evaluated Horner fold. -/
private theorem eval_foldl_map_scaleInner
    (coefficient : CoefficientPolynomial K) (outer inner : K) :
    ∀ (coefficients : List (CoefficientPolynomial K)) (accumulator : K),
      (coefficients.map (coefficient * ·)).foldl
          (fun value a => value * outer + a.eval inner)
          (coefficient.eval inner * accumulator) =
        coefficient.eval inner *
          coefficients.foldl
            (fun value a => value * outer + a.eval inner) accumulator
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.map_cons, List.foldl_cons, DensePolynomial.eval_mul]
      rw [show coefficient.eval inner * accumulator * outer +
          coefficient.eval inner * a.eval inner =
        coefficient.eval inner * (accumulator * outer + a.eval inner) by
          ring1]
      exact eval_foldl_map_scaleInner coefficient outer inner remaining
        (accumulator * outer + a.eval inner)
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- Leading zero padding preserves an outer Horner fold initialized at zero. -/
private theorem eval_foldl_replicate_zero (outer inner : K)
    (n : Nat) (coefficients : List (CoefficientPolynomial K)) :
    (List.replicate n 0 ++ coefficients).foldl
        (fun value (a : CoefficientPolynomial K) => value * outer + a.eval inner) 0 =
      coefficients.foldl
        (fun value (a : CoefficientPolynomial K) => value * outer + a.eval inner) 0 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [List.replicate_succ, List.cons_append, List.foldl_cons]
      have zeroStep : (0 : K) * outer + (0 : CoefficientPolynomial K).eval inner = 0 :=
        calc
          (0 : K) * outer + (0 : CoefficientPolynomial K).eval inner =
              0 + (0 : CoefficientPolynomial K).eval inner :=
            congrArg (fun value => value + (0 : CoefficientPolynomial K).eval inner)
              (MulZeroClass.zero_mul outer)
          _ = 0 + 0 := congrArg (fun value => 0 + value)
            (DensePolynomial.eval_zero inner)
          _ = 0 := _root_.zero_add 0
      rw [zeroStep]
      exact inductionHypothesis
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Equally sized outer coefficient tables add pointwise under Horner evaluation. -/
private theorem eval_foldl_zipWith_add (outer inner : K) :
    ∀ (as bs : List (CoefficientPolynomial K)) (first second : K),
      as.length = bs.length →
      (List.zipWith (fun a b => a + b) as bs).foldl
          (fun value a => value * outer + a.eval inner) (first + second) =
        as.foldl (fun value a => value * outer + a.eval inner) first +
          bs.foldl (fun value a => value * outer + a.eval inner) second
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      exact Nat.noConfusion equal
  | _ :: _, [], _, _, equal => by
      exact Nat.noConfusion equal
  | a :: as, b :: bs, first, second, equal => by
      have tailsEqual : as.length = bs.length := Nat.succ.inj equal
      simp only [List.zipWith_cons_cons, List.foldl_cons, DensePolynomial.eval_add]
      rw [show (first + second) * outer + (a.eval inner + b.eval inner) =
          (first * outer + a.eval inner) +
            (second * outer + b.eval inner) by ring1]
      exact eval_foldl_zipWith_add outer inner as bs
        (first * outer + a.eval inner) (second * outer + b.eval inner) tailsEqual
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- The empty outer table evaluates to zero. -/
@[simp] theorem eval_zero (outer inner : K) :
    eval Dense.Bivariate.Basic.zero outer inner = 0 := rfl

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The bivariate inner coordinate represented as one dense linear coefficient. -/
def innerX : DenseBivariate K := ⟨[⟨[1, 0]⟩]⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- The inner coordinate polynomial evaluates to the inner argument. -/
@[simp] theorem eval_innerX (outer inner : K) :
    eval innerX outer inner = inner := by
  rw [eval, innerX]
  change [(⟨[1, 0]⟩ : CoefficientPolynomial K)].foldl
      (fun accumulator coefficient => accumulator * outer +
        coefficient.eval inner) 0 = inner
  simp [DensePolynomial.eval, DensePolynomial.evalCoeffs, -eq_self, -iff_self] ; rfl

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Negate every retained inner polynomial in the outer coefficient table. -/
def neg (p : DenseBivariate K) :
  DenseBivariate K := ⟨p.coeffs.map (-·)⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Coefficientwise negation negates bivariate evaluation. -/
@[simp] theorem eval_neg (p : DenseBivariate K)
  (outer inner : K) :
    eval (neg p) outer inner = -eval p outer inner :=
      by
  change (p.coeffs.map (-·)).foldl
      (fun value a => value * outer + a.eval inner) 0 =
    -p.coeffs.foldl (fun value a => value * outer + a.eval inner) 0
  simpa only [neg_zero] using
    eval_foldl_map_neg outer inner p.coeffs 0
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Remove representation-only zero outer coefficients. -/
def normalizeOuter (p : DenseBivariate K) :
  DenseBivariate K :=
  ⟨p.coeffs.dropWhile (fun coefficient => coefficient.isZero)⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Removing leading zero outer coefficients preserves bivariate evaluation. -/
@[simp] theorem eval_normalizeOuter (p :
  DenseBivariate K)
    (outer inner : K) :
    eval (normalizeOuter p) outer inner = eval p outer
      inner :=
  eval_foldl_dropWhile_zero p.coeffs outer inner
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The outer degree of the normalized finite coefficient list. -/
def outerNatDegree (p : DenseBivariate K) : Nat :=
  (normalizeOuter p).coeffs.length - 1
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The bivariate outer coordinate with coefficient table [1, 0]. -/
def outerX : DenseBivariate K :=
  ⟨[DensePolynomial.constant 1,
    (0 : CoefficientPolynomial K)]⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- The outer coordinate polynomial evaluates to the outer argument. -/
@[simp] theorem eval_outerX (outer inner : K) :
    eval outerX outer inner = outer := by
  simp [eval, outerX, -eq_self, -iff_self] ; rfl

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Prefix an outer coefficient table with the specified number of zero polynomials. -/
def padLeft (n : Nat) (coefficients : List
  (CoefficientPolynomial K)) :
    List (CoefficientPolynomial K) :=
  List.replicate n 0 ++ coefficients
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Add bivariate coefficient tables after aligning their descending outer degrees.

Both tables are padded to the larger length, then their inner polynomials are added pointwise. -/
def add (p q : DenseBivariate K) :
  DenseBivariate K :=
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  ⟨List.zipWith (fun a b => a + b) ps qs⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Aligned coefficientwise addition evaluates to the sum of bivariate values. -/
@[simp] theorem eval_add (p q : DenseBivariate K)
  (outer inner : K) :
    eval (add p q) outer inner = eval p outer inner +
      eval q outer inner := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have pLe : p.coeffs.length ≤ n := Data.Nat.Order.le_max_left _ _
  have qLe : q.coeffs.length ≤ n := Data.Nat.Order.le_max_right _ _
  have pLength : ps.length = n := by
    simp only [ps, padLeft, Data.List.Append.length_append, Data.List.Replicate.length_replicate,
      Data.Nat.Subtraction.sub_add_cancel pLe, -eq_self, -iff_self]; rfl
  have qLength : qs.length = n := by
    simp only [qs, padLeft, Data.List.Append.length_append, Data.List.Replicate.length_replicate,
      Data.Nat.Subtraction.sub_add_cancel qLe, -eq_self, -iff_self]; rfl
  change (List.zipWith (fun a b => a + b) ps qs).foldl
      (fun value a => value * outer + a.eval inner) 0 = _
  rw [show (0 : K) = 0 + 0 by ring1,
    eval_foldl_zipWith_add outer inner ps qs 0 0 (pLength.trans qLength.symm)]
  dsimp only [ps, qs, padLeft]
  rw [eval_foldl_replicate_zero, eval_foldl_replicate_zero]
  rfl
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Multiply every outer coefficient by a retained inner-variable polynomial. -/
def scaleInner (coefficient :
  CoefficientPolynomial K) (p :
  DenseBivariate K) : DenseBivariate K :=
  ⟨p.coeffs.map (coefficient * ·)⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Inner-polynomial scaling multiplies evaluation by that polynomial's inner value. -/
@[simp] theorem eval_scaleInner (coefficient :
  CoefficientPolynomial K) (p :
  DenseBivariate K)
    (outer inner : K) :
    eval (scaleInner coefficient p) outer inner =
      coefficient.eval inner * eval p outer inner := by
  change (p.coeffs.map (coefficient * ·)).foldl
      (fun value a => value * outer + a.eval inner) 0 =
    coefficient.eval inner * p.coeffs.foldl
      (fun value a => value * outer + a.eval inner) 0
  simpa only [show coefficient.eval inner * (0 : K) = 0 by ring1] using
    eval_foldl_map_scaleInner coefficient outer inner p.coeffs 0

end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Multiply the outer representation by its coordinate, retaining the empty zero table. -/
def shiftOuter (p : DenseBivariate K) :
  DenseBivariate K :=
  if p.coeffs.isEmpty then Dense.Bivariate.Basic.zero else ⟨p.coeffs ++ [0]⟩
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [DecidableEq K] in
/-- Shifting the outer table multiplies evaluation by the outer argument. -/
@[simp] theorem eval_shiftOuter (p :
  DenseBivariate K) (outer inner : K) :
    eval (shiftOuter p) outer inner = eval p outer
      inner * outer := by
  rw [shiftOuter]
  split
  · rename_i empty
    have coefficientsEmpty : p.coeffs = [] := by
      cases observed : p.coeffs with
      | nil => rfl
      | cons head tail =>
          rw [observed] at empty
          cases empty
    simp [eval, Dense.Bivariate.Basic.zero, coefficientsEmpty, -eq_self, -iff_self]; rfl
  · exact eval_foldl_append_zero outer inner p.coeffs 0
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Evaluation transports the bivariate multiplication fold to scalar Horner evaluation. -/
private theorem eval_foldl_mul (q : DenseBivariate
  K) (outer inner : K) :
    ∀ (coefficients : List (CoefficientPolynomial K)) (accumulator :
      DenseBivariate K),
      eval (coefficients.foldl
          (fun value a => add (shiftOuter value)
            (scaleInner a q))
          accumulator) outer inner =
        coefficients.foldl
          (fun value a => value * outer + a.eval inner * eval q outer inner)
          (eval accumulator outer inner)
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.foldl_cons]
      rw [eval_foldl_mul q outer inner remaining,
        eval_add,
        eval_shiftOuter, eval_scaleInner]
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Multiply bivariate polynomials by a finite outer Horner fold.

Each step shifts the accumulated product and adds the second polynomial scaled by the next inner coefficient. -/
def mul (p q : DenseBivariate K) :
  DenseBivariate K :=
  p.coeffs.foldl
    (fun accumulator coefficient =>
      add (shiftOuter accumulator) (scaleInner
        coefficient q)) Dense.Bivariate.Basic.zero
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Finite bivariate multiplication evaluates to the product of both input values. -/
@[simp] theorem eval_mul (p q : DenseBivariate K)
  (outer inner : K) :
    eval (mul p q) outer inner = eval p outer inner *
      eval q outer inner := by
  rw [mul, eval_foldl_mul]
  have scaled : ∀ (coefficients : List (CoefficientPolynomial K))
      (accumulator : K),
      coefficients.foldl
          (fun value a => value * outer + a.eval inner * eval q outer inner)
          (accumulator * eval q outer inner) =
        coefficients.foldl
          (fun value a => value * outer + a.eval inner) accumulator *
          eval q outer inner := by
    intro coefficients accumulator
    induction coefficients generalizing accumulator with
    | nil => rfl
    | cons a remaining inductionHypothesis =>
        simp only [List.foldl_cons]
        rw [show accumulator * eval q outer inner * outer +
            a.eval inner * eval q outer inner =
          (accumulator * outer + a.eval inner) * eval q outer inner by ring1,
          inductionHypothesis]
  change p.coeffs.foldl
      (fun value a => value * outer + a.eval inner * eval q outer inner) 0 =
    p.coeffs.foldl (fun value a => value * outer + a.eval inner) 0 *
      eval q outer inner
  have zeroMul : (0 : K) * eval q outer inner = 0 := MulZeroClass.zero_mul _
  simpa only [zeroMul] using scaled p.coeffs 0
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]
/-- Subtract bivariate polynomials by adding the coefficientwise negation. -/
def sub (p q : DenseBivariate K) :
  DenseBivariate K := add p (neg q)
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Bivariate subtraction evaluates to the difference of both values. -/
@[simp] theorem eval_sub (p q : DenseBivariate K)
  (outer inner : K) :
    eval (sub p q) outer inner = eval p outer inner -
      eval q outer inner := by
  rw [sub, eval_add, eval_neg]
  ring1
end Purelib.Polynomial.Dense.Bivariate.Basic

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Algebra.Polynomial.Bivariate
variable {K : Type*} [ExplicitField K] [DecidableEq K]

end Purelib.Algebra.Polynomial.Bivariate

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Basic
/-- Dense bivariate polynomials over the original normalized Gaussian working scalar. -/
abbrev GaussianNumberBivariate :=
  DenseBivariate Gaussian.Basic.Number
end Purelib.Polynomial.Dense.Bivariate.Basic
end
