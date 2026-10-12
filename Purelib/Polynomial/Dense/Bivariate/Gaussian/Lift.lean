module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Fold
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Basic
public import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Leading

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Polynomial

public section

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

namespace Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift

/-! ## Separated bivariate pair -/

/-- The low-to-high outer coefficients of `p(U)` are constants in the parameter.

The normalized original descending table is reversed once and mapped through
the same normalized scalar-constant constructor, preserving its coefficient order. -/
@[expose] def SeparatedVariables.liftedCoefficients (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    List (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  p.normalize.coeffs.reverse.map Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant

/-- Retain the bivariate lift `p(U)` of the original Gaussian polynomial.

The original ascending scalar-constant table is reversed into the descending
outer coefficient representation without changing its normalized inner entries. -/
@[expose] def SeparatedVariables.lifted (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Dense.Bivariate.Basic.DenseBivariate Gaussian.Basic.Canonical) :=
  ⟨(SeparatedVariables.liftedCoefficients p).reverse⟩

/-- Evaluate the bivariate lift as its original polynomial in the outer variable.

Structural map and reversal certificates retain the original coefficient fold.
Each inner constant evaluates to the same scalar independently of the parameter. -/
@[simp] theorem eval_lifted (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (outer parameter : Gaussian.Basic.Canonical) :
    Dense.Bivariate.Basic.eval (SeparatedVariables.lifted p) outer parameter =
      p.eval outer := open Purelib in by
  rw [← Dense.Basic.DensePolynomial.eval_normalize p outer]
  simp only [Dense.Bivariate.Basic.eval, SeparatedVariables.lifted, SeparatedVariables.liftedCoefficients,
    Data.List.Reverse.map_reverse, Data.List.Reverse.reverse_reverse]
  rw [Data.List.Fold.foldl_map]
  unfold Dense.Basic.DensePolynomial.eval
  unfold Dense.Basic.DensePolynomial.evalCoeffs
  change p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * outer + (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant coefficient).eval
          parameter) 0 =
    p.normalize.coeffs.foldl
      (fun value coefficient => value * outer + coefficient) 0
  exact Data.List.Fold.foldl_congr _ _ (fun value coefficient => by
    rw [Dense.Gaussian.Coefficients.Constants.eval_parameterConstant]) _ _

/-- Read the lifted outer coefficient from its retained ascending constant table.

The original descending-to-ascending reversals cancel on the same list. Its
natural index and zero fallback remain those of the bivariate coefficient reader. -/
@[simp] theorem outerCoeff_lifted (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (index : Nat) :
    Dense.Bivariate.Resultant.outerCoeff (SeparatedVariables.lifted p) index =
      Data.List.getD (SeparatedVariables.liftedCoefficients p) index 0 := by
  unfold Dense.Bivariate.Resultant.outerCoeff SeparatedVariables.lifted
  rewrite [Data.List.Reverse.reverse_reverse]
  exact Eq.refl _

set_option backward.match.sparseCases false in
/-- Every retained indexed scalar-constant polynomial has degree at most zero.

The original list and natural coordinate choose the corresponding normalized
constant; the zero polynomial supplies the same degree bound beyond the table. -/
private theorem getD_map_parameterConstant_atMost :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (index : Nat),
      Dense.Leading.DegreeAtMost
        (Data.List.getD (coefficients.map Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant)
          index 0) 0
  | [], _ => Dense.Leading.DegreeAtMost.zero 0
  | coefficient :: _, 0 => Dense.Gaussian.Coefficients.Constants.parameterConstant_atMost coefficient
  | _ :: remaining, index + 1 =>
      getD_map_parameterConstant_atMost remaining index

set_option backward.match.sparseCases false in
/-- Read a mapped scalar-constant table by constructing its retained indexed scalar.

Structural recursion retains the original list coordinate. The mapped zero
fallback agrees with the same normalized scalar-constant constructor. -/
private theorem getD_map_parameterConstant :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (index : Nat),
      Data.List.getD (coefficients.map Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant) index
        0 =
        Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (Data.List.getD coefficients index 0)
  | [], _ => Dense.Gaussian.Coefficients.Constants.parameterConstant_zero.symm
  | _ :: _, 0 => rfl
  | _ :: remaining, index + 1 =>
      getD_map_parameterConstant remaining index

/-- Every lifted outer coefficient is constant in its inner parameter.

The original outer reader returns its retained normalized scalar constant,
including the zero fallback beyond the same finite coefficient table. -/
theorem liftedCoeff_atMost (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (index : Nat) :
    Dense.Leading.DegreeAtMost
      (Dense.Bivariate.Resultant.outerCoeff (SeparatedVariables.lifted p) index) 0 := by
  apply Dense.Leading.DegreeAtMost.of_equal (outerCoeff_lifted p index) rfl
  exact getD_map_parameterConstant_atMost p.normalize.coeffs.reverse index

/-- A nonzero normalized source table has exactly degree plus one coefficients.

The original nonzero certificate identifies the normalized coefficient count
with the natural degree plus its leading entry. -/
private theorem normalizedCoefficients_length (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    p.normalize.coeffs.length = p.natDegree + 1 := by
  have degreeCount := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  change p.natDegree + 1 = p.normalize.coeffs.length at degreeCount
  exact degreeCount.symm

/-- A nonzero ascending lifted table has exactly degree plus one entries.

Reversing and mapping the normalized original coefficients retain their count.
The supplied nonzero source certificate gives the same natural degree. -/
theorem liftedCoefficients_length (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (SeparatedVariables.liftedCoefficients p).length = p.natDegree + 1 := by
  unfold SeparatedVariables.liftedCoefficients
  rewrite [Data.List.Map.length_map, Data.List.Reverse.length_reverse]
  exact normalizedCoefficients_length p nonzero

/-- The highest outer coefficient is the constant polynomial of the original leading scalar.

The nonzero normalized table retains its actual first scalar. Reversal places
that same occurrence at the original natural-degree coordinate of the lift. -/
theorem liftedCoeff_degree_leading (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    Dense.Leading.LeadingTerm
      (Dense.Bivariate.Resultant.outerCoeff (SeparatedVariables.lifted p) p.natDegree) 0
      p.leadingCoeff := open Purelib in by
  apply Dense.Leading.LeadingTerm.of_equal (outerCoeff_lifted p p.natDegree) rfl rfl
  have coefficientIdentity :
      Data.List.getD (SeparatedVariables.liftedCoefficients p) p.natDegree 0 =
        Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant p.leadingCoeff := by
    unfold SeparatedVariables.liftedCoefficients
    have lengthEq := normalizedCoefficients_length p nonzero
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at lengthEq
        change 0 = Nat.succ p.natDegree at lengthEq
        exact Nat.noConfusion lengthEq
    | cons leading remaining =>
        have degreeEq : p.natDegree = remaining.length := by
          rw [coefficients] at lengthEq
          simp only [List.length_cons] at lengthEq
          exact (Nat.succ.inj lengthEq).symm
        rw [getD_map_parameterConstant, degreeEq,
          Data.List.reverse_getD_last]
        rewrite [Dense.Basic.DensePolynomial.leadingCoeff, coefficients]
        exact Eq.refl _
  exact Dense.Leading.LeadingTerm.of_equal coefficientIdentity rfl rfl
    (Dense.Gaussian.Coefficients.Constants.parameterConstant_leading (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero
      nonzero))

/-- Lifted outer coefficients beyond the original nonzero source degree are zero.

The retained table has exactly degree plus one entries. Its out-of-range natural
coordinate therefore returns the same zero polynomial supplied by the reader. -/
theorem liftedCoeff_eq_zero_of_degree_lt (p : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) {index : Nat}
    (beyond : p.natDegree < index) :
    Dense.Bivariate.Resultant.outerCoeff (SeparatedVariables.lifted p) index = 0 := open Purelib in by
  rw [outerCoeff_lifted]
  apply Data.List.getD_eq_default_of_length_le
  rw [liftedCoefficients_length p nonzero]
  exact Nat.succ_le_of_lt beyond
end Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
