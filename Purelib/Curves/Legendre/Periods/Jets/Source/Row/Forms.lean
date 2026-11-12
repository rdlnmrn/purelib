module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Operational
public import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.Operational
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Data.Fin.Two

/-! # Original numerical primitive forms for the three retained source rows

Selection returns the existing original connection or scalar primitive
owner. Its coefficient cache is normalized to the original Row expression
by a finite cleared polynomial equality; no evaluator is replaced.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Row

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- Select the unchanged original operational connection/scalar primitive form for this exact source row. -/
@[expose] def form (parameter : Canonical) : Row → OddPowerDifferential (Paths.polynomial parameter)
  | .inl coordinate => Connection.Operational.primitiveForm parameter coordinate
  | .inr _ => PicardFuchs.Operational.primitiveForm parameter

/-- The original selected primitive retains the same exact numerator table as its source row. -/
theorem form_numerator (parameter : Canonical) (row : Row) :
    (row.form parameter).numerator = row.numerator parameter := by
  cases row with
  | inl coordinate =>
    rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
    · subst coordinate
      change (Connection.connectionReduction parameter 0).primitiveNumerator = _
      rewrite [Connection.connectionReduction_zero]
      rfl
    · subst coordinate
      change (Connection.connectionReduction parameter 1).primitiveNumerator = _
      rewrite [Connection.connectionReduction_one]
      rfl
  | inr _ => rfl

/-- The original connection forms use one sheet factor; the scalar form uses the original cube. -/
theorem form_pairs (parameter : Canonical) (row : Row) :
    (row.form parameter).denominatorPairs = row.pairs.val := by
  cases row <;> rfl

/-- Each original selected primitive carries its unchanged exact unit coefficient scale. -/
theorem form_scale (parameter : Canonical) (row : Row) : (row.form parameter).scale = 1 := by
  cases row <;> rfl

/-- Finite cleared coefficient equality normalizes the original numerical primitive to its SAME source row expression.

The original form's cached coefficient specification remains its owner.
Only polynomial evaluation of the exact unit scale is used; no selected
root, primitive constant or numerical witness occurs in this certificate.
-/
theorem form_equal (parameter : Canonical) (row : Row) :
    (row.expression parameter).Equal (row.form parameter).coefficient := by
  have original := (row.form parameter).coefficient_eq
  rewrite [form_numerator, form_pairs, form_scale] at original
  rewrite [original]
  apply Expression.equal_of_cross_eval
  · intro point
    change (0 : Coefficients).eval point * _ = (0 : Coefficients).eval point * _
    rfl
  · intro point
    change (row.numerator parameter).eval point * _ = ((row.numerator parameter).scale 1).eval point * _
    rewrite [DensePolynomial.eval_scale, Basic.one_mul]
    rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Row

end
