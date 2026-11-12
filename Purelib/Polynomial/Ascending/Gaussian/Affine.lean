module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring

/-!
# Finite affine Gaussian polynomial substitution

Exact coefficient arithmetic multiplies by affine factors and compiles Horner
substitution on the original finite table. Evaluation and coefficientwise
linearity follow from those retained scalar and list operations.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Affine

open Purelib.Data
open Purelib.Polynomial

public section
open Purelib.Data.Gaussian.Basic.Canonical

/-- Multiply a retained Gaussian polynomial by its affine factor.

The offset scales the original coefficient table. The slope scales that same
table before its degree is shifted once, and exact coefficient addition combines them. -/
@[expose] def affineMul (offset slope : Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) :
  CoefficientPolynomial :=
  Arithmetic.add (Arithmetic.scale offset polynomial)
    (Arithmetic.shift (Arithmetic.scale slope polynomial))

/-- Read the affine product's constant entry as its offset contribution.

The shifted slope contribution has zero constant entry. Thus the same original
constant coefficient is multiplied by the retained offset alone. -/
@[simp] theorem coefficient_affineMul_zero (offset slope : Gaussian.Basic.Canonical) (polynomial :
  CoefficientPolynomial) :
    Coefficient.coefficient (affineMul offset slope polynomial) 0 = offset *
      Coefficient.coefficient polynomial 0 := by
  unfold affineMul
  rw [Arithmetic.coefficient_add, Arithmetic.coefficient_scale,
    Arithmetic.coefficient_shift_zero, Gaussian.Basic.add_zero]

/-- Read an affine product entry as its offset and shifted slope contributions.

At a positive degree, the offset multiplies the same original coordinate and
the slope multiplies its preceding coordinate. Both readbacks use the retained table. -/
@[simp] theorem coefficient_affineMul_succ (offset slope : Gaussian.Basic.Canonical) (polynomial :
  CoefficientPolynomial)
    (degree : Nat) :
    Coefficient.coefficient (affineMul offset slope polynomial) (degree + 1) =
      offset * Coefficient.coefficient polynomial (degree + 1) + slope *
        Coefficient.coefficient polynomial degree := by
  unfold affineMul
  rw [Arithmetic.coefficient_add, Arithmetic.coefficient_scale,
    Arithmetic.coefficient_shift_succ, Arithmetic.coefficient_scale]

/-- Multiplication by the same affine factor preserves coefficientwise equality. -/
theorem coefficientwise_affineMul (offset slope : Gaussian.Basic.Canonical) {left right :
  CoefficientPolynomial}
    (equal : Coefficient.CoefficientwiseEqual left right) :
    Coefficient.CoefficientwiseEqual (affineMul offset slope left) (affineMul offset slope right) :=
  Arithmetic.coefficientwise_add (Arithmetic.coefficientwise_scale offset equal)
    (Arithmetic.coefficientwise_shift (Arithmetic.coefficientwise_scale slope
      equal))

/-- Multiplication by an affine factor distributes over polynomial addition coefficientwise. -/
theorem affineMul_add (offset slope : Gaussian.Basic.Canonical) (left right : CoefficientPolynomial) :
    Coefficient.CoefficientwiseEqual (affineMul offset slope (Arithmetic.add left
      right))
      (Arithmetic.add (affineMul offset slope left) (affineMul offset slope right)) := by
  intro degree
  cases degree <;>
    simp only [coefficient_affineMul_zero, coefficient_affineMul_succ, Arithmetic.coefficient_add]
      <;> ring1

/-- Multiplication by an affine factor commutes with Gaussian scaling coefficientwise. -/
theorem affineMul_scale (offset slope factor : Gaussian.Basic.Canonical) (polynomial :
  CoefficientPolynomial) :
    Coefficient.CoefficientwiseEqual (affineMul offset slope (Arithmetic.scale
      factor polynomial))
      (Arithmetic.scale factor (affineMul offset slope polynomial)) := by
  intro degree
  cases degree <;>
    simp only [coefficient_affineMul_zero, coefficient_affineMul_succ, Arithmetic.coefficient_scale]
      <;> ring1

/-- Evaluation of affine multiplication multiplies the polynomial value by `offset + slope * input`. -/
@[simp] theorem eval_affineMul (offset slope : Gaussian.Basic.Canonical) (polynomial :
  CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    Evaluation.eval (affineMul offset slope polynomial) input =
      (offset + slope * input) * Evaluation.eval polynomial input := by
  simp only [affineMul, Evaluation.eval_add, Evaluation.eval_scale,
    Evaluation.eval_shift]
  ring1

/-- Compile the retained coefficient list by finite affine Horner substitution.

Each original constant entry is added to the affine factor times the compiled
original tail. Empty tables return the empty zero polynomial without sampling. -/
@[expose] def affineCoefficients (offset slope : Gaussian.Basic.Canonical) : List Gaussian.Basic.Canonical →
  CoefficientPolynomial
  | [] => Basic.zero
  | head :: tail => Arithmetic.add (Basic.constant head) (affineMul offset slope
    (Affine.affineCoefficients offset slope tail))

/-- Substitute `offset + slope * X` into the retained Gaussian polynomial.

Finite Horner coefficient arithmetic constructs the complete output table, including when the slope is zero. -/
@[expose] def affine (polynomial : CoefficientPolynomial) (offset slope : Gaussian.Basic.Canonical) :
  CoefficientPolynomial :=
  affineCoefficients offset slope polynomial.coefficients

/-- Affine substitution preserves the empty zero polynomial. -/
@[simp] theorem affine_zero (offset slope : Gaussian.Basic.Canonical) : affine Basic.zero offset
  slope = Basic.zero := rfl

/-- Evaluating an affine-substituted table equals evaluating the original table at the affine input. -/
theorem eval_affineCoefficients (offset slope input : Gaussian.Basic.Canonical) : ∀ coefficients,
    Evaluation.eval (affineCoefficients offset slope coefficients) input =
      Evaluation.evalCoeffs coefficients (offset + slope * input)
  | [] => rfl
  | head :: tail => by
      rw [affineCoefficients, Evaluation.eval_add, Evaluation.eval_constant,
        eval_affineMul,
        Affine.eval_affineCoefficients,
          Evaluation.evalCoeffs_cons]

/-- Affine polynomial substitution evaluates at `offset + slope * input`. -/
@[simp] theorem eval_affine (polynomial : CoefficientPolynomial) (offset slope input :
  Gaussian.Basic.Canonical) :
    Evaluation.eval (affine polynomial offset slope) input = Evaluation.eval
      polynomial (offset + slope * input) :=
  eval_affineCoefficients offset slope input polynomial.coefficients

/-- Affine substitution preserves padded finite coefficient-list addition.

Horner construction distributes each affine factor over the two retained tails.
Constant entries combine directly at degree zero and vanish at positive degrees. -/
theorem affineCoefficients_add (offset slope : Gaussian.Basic.Canonical) : ∀ left right,
    Coefficient.CoefficientwiseEqual (affineCoefficients offset slope
      (Data.List.Gaussian.Arithmetic.addCoefficients left right))
      (Arithmetic.add (affineCoefficients offset slope left) (affineCoefficients offset slope right))
  | [], right => by
      intro degree
      change Coefficient.coefficient (affineCoefficients offset slope right) degree =
        Coefficient.coefficient (Arithmetic.add Basic.zero
          (affineCoefficients offset slope right)) degree
      rw [Arithmetic.coefficient_add, Coefficient.coefficient_zero,
        Gaussian.Basic.zero_add]
  | head :: tail, [] => by
      intro degree
      change Coefficient.coefficient (affineCoefficients offset slope (head :: tail)) degree =
        Coefficient.coefficient (Arithmetic.add (affineCoefficients offset slope
          (head :: tail)) Basic.zero) degree
      rw [Arithmetic.coefficient_add, Coefficient.coefficient_zero,
        Gaussian.Basic.add_zero]
  | left :: leftTail, right :: rightTail => by
      let leftPolynomial := affineCoefficients offset slope leftTail
      let rightPolynomial := affineCoefficients offset slope rightTail
      have tailEqual := coefficientwise_affineMul offset slope
        (Affine.affineCoefficients_add offset slope leftTail rightTail)
      have distributed := affineMul_add offset slope leftPolynomial rightPolynomial
      intro degree
      change Coefficient.coefficient (Arithmetic.add
        (Basic.constant (left + right))
          (affineMul offset slope (affineCoefficients offset slope
            (Data.List.Gaussian.Arithmetic.addCoefficients leftTail rightTail)))) degree =
        Coefficient.coefficient (Arithmetic.add (Arithmetic.add
          (Basic.constant left) (affineMul offset slope leftPolynomial))
          (Arithmetic.add (Basic.constant right) (affineMul offset slope
            rightPolynomial))) degree
      rw [Arithmetic.coefficient_add, tailEqual degree, distributed degree]
      cases degree with
      | zero =>
          simp only [Arithmetic.coefficient_add]
          rw [show Coefficient.coefficient (Basic.constant (left + right)) 0 =
            left + right from rfl,
            show Coefficient.coefficient (Basic.constant left) 0 = left from rfl,
            show Coefficient.coefficient (Basic.constant right) 0 = right from
              rfl]
          ring1
      | succ degree =>
          simp only [Arithmetic.coefficient_add]
          rw [show Coefficient.coefficient (Basic.constant (left + right)) (degree
            + 1) = 0 from rfl,
            show Coefficient.coefficient (Basic.constant left) (degree + 1) = 0
              from rfl,
            show Coefficient.coefficient (Basic.constant right) (degree + 1) = 0
              from rfl]
          ring1

/-- Affine substitution preserves polynomial addition coefficientwise. -/
theorem affine_add (left right : CoefficientPolynomial) (offset slope : Gaussian.Basic.Canonical) :
    Coefficient.CoefficientwiseEqual (affine (Arithmetic.add left right) offset
      slope)
      (Arithmetic.add (affine left offset slope) (affine right offset slope)) :=
  affineCoefficients_add offset slope left.coefficients right.coefficients

end

end Purelib.Polynomial.Ascending.Gaussian.Affine
