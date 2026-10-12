module
import Purelib.Algebra.NatCast
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.List.Reverse
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Polynomial.Dense.Derivative
import Purelib.Data.List.Fold
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

/-!+# Finite reciprocal coefficient and derivative identities

Reverse the normalized dense coefficient list. Both the value and derivative
transport laws follow from the two finite Horner folds. In particular no
polynomial extensionality on an infinite carrier or analytic chain rule is
used to differentiate inversion.
-/

@[expose] public section

-- Retain exact public scalar/carrier shorthand names after subject placement.

namespace Purelib.Polynomial.Dense.Gaussian.Reciprocal

open Purelib.Algebra
open Purelib.Data.List

/-- Canonical Gaussian rational scalars for reciprocal polynomials. -/
abbrev Scalar := Gaussian.Basic.Canonical
/-- Dense polynomials over canonical Gaussian rationals. -/
abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative
open _root_.Purelib.Polynomial.Dense.Derivative renaming CoefficientPolynomial -> Dense
open Purelib.Data.Gaussian.Basic.Canonical

/-- Reverse the normalized coefficient table.

The resulting polynomial is the denominator-cleared reciprocal with exponent equal to the original natural degree. -/
def reversed (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨polynomial.normalize.coeffs.reverse⟩

/-- Evaluate a coefficient table in ascending order together with its derivative. -/
def lowJet (point : Scalar) (coefficients : List Scalar) :
  Scalar × Scalar :=
  coefficients.foldr (fun coefficient state =>
    (coefficient + point * state.1, state.1 + point * state.2)) (0, 0)

/-- The empty ascending table has zero value and derivative. -/
private theorem lowJet_nil (point : Scalar) : lowJet point [] = (0,
  0) := rfl

/-- Prepending a coefficient performs the ascending Horner jet step. -/
private theorem lowJet_cons (point coefficient : Scalar) (tail : List
  Scalar) :
    lowJet point (coefficient :: tail) =
      (coefficient + point * (lowJet point tail).1,
        (lowJet point tail).1 + point * (lowJet point tail).2) :=
          rfl

/-- The descending jet of the reversed table equals its ascending jet. -/
private theorem reverse_jet (point : Scalar) (coefficients : List
  Scalar) :
    Dense.Derivative.evalDerivativeCoeffs point coefficients.reverse = lowJet point
      coefficients := open Purelib in by
  unfold Dense.Derivative.evalDerivativeCoeffs
  rw [Data.List.Fold.foldl_reverse]
  induction coefficients with
  | nil => rfl
  | cons coefficient tail ih =>
      rw [List.foldr_cons, lowJet_cons, ih]
      dsimp only [Dense.Derivative.evalDerivativeStep]
      apply Prod.ext <;> dsimp only <;> ring1

/-- Reciprocal evaluation is the value component of the normalized ascending jet. -/
theorem reversed_eval (polynomial : CoefficientPolynomial) (point : Scalar) :
    (reversed polynomial).eval point = (lowJet point
      polynomial.normalize.coeffs).1 := by
  rw [← Dense.Derivative.eval_original, reversed, reverse_jet]

/-- The reciprocal derivative is the derivative component of the normalized ascending jet. -/
theorem reversed_derivative_eval (polynomial : CoefficientPolynomial) (point :
  Scalar) :
    (Dense.Derivative.derivative (reversed polynomial)).eval point =
      (lowJet point polynomial.normalize.coeffs).2 := by
  rw [Dense.Derivative.eval_derivative, reversed, reverse_jet]

/-- The ascending jet at zero reads the first coefficient, defaulting to zero.

The empty list supplies zero; otherwise the argument annihilates the retained
tail value and leaves the original head coefficient. -/
private theorem lowJet_origin : (coefficients : List Scalar) →
    (lowJet 0 coefficients).1 = coefficients.headD 0
  | [] => rfl
  | coefficient :: tail => by
      change coefficient + 0 * (lowJet 0 tail).1 = coefficient
      rw [Gaussian.Basic.zero_mul, Gaussian.Basic.add_zero]

/-- The reciprocal value at zero equals the original leading coefficient. -/
theorem reversed_origin (polynomial : CoefficientPolynomial) :
    (reversed polynomial).eval 0 = polynomial.leadingCoeff := by
  rw [reversed_eval, lowJet_origin]
  rfl

/-- Reversing a nonzero polynomial preserves nonzeroness.

Evaluation of the reciprocal at zero recovers the original nonzero leading
coefficient, which rules out the zero branch of its retained Boolean check. -/
theorem reversed_nonzero {polynomial : CoefficientPolynomial} (nonzero : polynomial.isZero = false) :
    (reversed polynomial).isZero = false := by
  by_cases zero : (reversed polynomial).isZero = true
  · have vanished := DensePolynomial.eval_eq_zero_of_isZero zero 0
    rw [reversed_origin] at vanished
    exact (DensePolynomial.leadingCoeff_ne_zero nonzero vanished).elim
  · cases selected : (reversed polynomial).isZero with
    | false => rfl
    | true => exact (zero selected).elim

/-- Relate descending evaluation and the ascending jet at inverse chart coordinates.

The coefficient-count power clears the denominator using only the displayed chart-times-affine identity. -/
private theorem homogenized (affine chart : Scalar) (cancel : chart * affine = 1) :
    (coefficients : List Scalar) →
    chart ^ coefficients.length * DensePolynomial.evalCoeffs affine coefficients = chart *
      (lowJet chart coefficients).1
  | [] => by
      change chart ^ 0 * 0 = chart * 0
      rw [Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero]
  | coefficient :: tail => by
      have powers : chart ^ tail.length * affine ^ tail.length = 1 := by
        rw [← Semiring.Normalization.product_pow, cancel, one_pow]
      rw [List.length_cons, DensePolynomial.evalCoeffs_cons_expansion,
        lowJet_cons, pow_succ]
      calc
        _ = chart * coefficient * (chart ^ tail.length * affine ^ tail.length) +
            chart * (chart ^ tail.length * DensePolynomial.evalCoeffs affine tail) := by ring1
        _ = _ := by
          rw [powers, homogenized affine chart cancel tail]; ring1

/-- At a nonzero point, reciprocal evaluation is the degree power times evaluation at its inverse.

The normalized coefficient count supplies the original degree exponent.
Multiplying the two finite Horner evaluations by the retained inverse identity
clears the same denominator, including the separate zero-polynomial case. -/
theorem reversed_identity (polynomial : CoefficientPolynomial) (point : Scalar)
  (pointNonzero : point ≠ 0) :
    (reversed polynomial).eval point = point ^ polynomial.natDegree * polynomial.eval point⁻¹
      := open Purelib.Algebra.Field in by
  by_cases zero : polynomial.isZero = true
  · have normalized := DensePolynomial.normalize_eq_zero_of_isZero zero
    rw [reversed, normalized]
    change (0 : Scalar) = _
    rw [DensePolynomial.eval_eq_zero_of_isZero zero, Gaussian.Basic.mul_zero]
  · have nonzero : polynomial.isZero = false := by
      cases selected : polynomial.isZero with
      | false => rfl
      | true => exact (zero selected).elim
    have count := (DensePolynomial.natDegree_add_one_eq_degreeCount nonzero).symm
    change polynomial.normalize.coeffs.length = polynomial.natDegree + 1 at count
    have identity := homogenized point⁻¹ point (ExplicitField.mul_inv_cancel point
      pointNonzero)
      polynomial.normalize.coeffs
    have evaluated : DensePolynomial.evalCoeffs point⁻¹ polynomial.normalize.coeffs = polynomial.eval
      point⁻¹ :=
      DensePolynomial.eval_normalize polynomial point⁻¹
    rw [count, evaluated, ← reversed_eval, pow_succ] at identity
    apply Gaussian.Field.mul_right_cancel_of_ne pointNonzero
    calc
      _ = point * (reversed polynomial).eval point := by ring1
      _ = _ := identity.symm.trans (by ring1)

/-- A bounded-degree reciprocal, retaining enough powers to clear a
displayed finite coefficient witness. -/
def padded (polynomial : CoefficientPolynomial) (degree : Nat) : CoefficientPolynomial :=
  DensePolynomial.shift (degree - polynomial.natDegree) (reversed polynomial)

/-- A reciprocal padded to an upper degree bound has the corresponding denominator-cleared evaluation.

The original bounded natural degree difference selects the shift. Adding it
back to the polynomial's retained degree recovers the same clearing exponent. -/
theorem padded_identity (polynomial : CoefficientPolynomial) (degree : Nat) (bound : polynomial.natDegree ≤
  degree)
    (point : Scalar) (pointNonzero : point ≠ 0) :
    (padded polynomial degree).eval point = point ^ degree * polynomial.eval point⁻¹ := by
  rw [padded, DensePolynomial.eval_shift,
    reversed_identity polynomial point pointNonzero]
  calc
    _ = point ^ (polynomial.natDegree + (degree - polynomial.natDegree)) * polynomial.eval point⁻¹ := by
      rw [pow_add]; ring1
    _ = _ := by rw [Nat.Subtraction.add_sub_of_le bound]

/-- Padding above the original degree makes the reciprocal vanish at zero.

The strict degree bound makes the original natural padding difference nonzero.
The retained shift contributes that positive coordinate power at the origin. -/
theorem padded_origin (polynomial : CoefficientPolynomial) (degree : Nat) (bound : polynomial.natDegree <
  degree) :
    (padded polynomial degree).eval 0 = 0 := by
  have positivePower : degree - polynomial.natDegree ≠ 0 := by
    intro zero
    have reconstruction := Nat.Subtraction.add_sub_of_le (Nat.le_of_lt bound)
    rw [zero, Nat.add_zero] at reconstruction
    exact (Nat.ne_of_lt bound) reconstruction
  rw [padded, DensePolynomial.eval_shift,
    zero_pow positivePower, Gaussian.Basic.mul_zero]

/-- Remove the constant coefficient without assuming it is nonzero. -/
def originTail (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  ⟨polynomial.coeffs.reverse.tail.reverse⟩

/-- Appending a trailing coefficient multiplies the previous evaluation by the point and adds that coefficient. -/
private theorem evalCoeffs_snoc (point coefficient : Scalar) (tail : List
  Scalar) :
    DensePolynomial.evalCoeffs point (tail ++ [coefficient]) = DensePolynomial.evalCoeffs point
      tail * point + coefficient := open Purelib in by
  unfold DensePolynomial.evalCoeffs
  rw [Data.List.Fold.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Split evaluation into the constant term and the argument times the retained origin tail.

The original reversed coefficient table either is empty or exposes its final
constant coefficient. Removing that same coefficient yields the displayed
origin tail without a nonzero-constant assumption. -/
theorem origin_decomposition (polynomial : CoefficientPolynomial) (point : Scalar) :
    polynomial.eval point = point * (originTail polynomial).eval point + polynomial.eval 0 :=
      by
  cases coefficients : polynomial.coeffs.reverse with
  | nil =>
      have original : polynomial.coeffs = [] := by
        have reflected := congrArg List.reverse coefficients
        rw [Reverse.reverse_reverse, List.reverse_nil]
          at reflected
        exact reflected
      change DensePolynomial.evalCoeffs point polynomial.coeffs =
        point * DensePolynomial.evalCoeffs point polynomial.coeffs.reverse.tail.reverse +
          DensePolynomial.evalCoeffs 0 polynomial.coeffs
      rw [original]
      change (0 : Scalar) = point * 0 + 0
      rw [Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
  | cons coefficient tail =>
      have original : polynomial.coeffs = tail.reverse ++ [coefficient] := by
        have reflected := congrArg List.reverse coefficients
        rw [Reverse.reverse_reverse, Reverse.reverse_cons]
          at reflected
        exact reflected
      change DensePolynomial.evalCoeffs point polynomial.coeffs =
        point * DensePolynomial.evalCoeffs point polynomial.coeffs.reverse.tail.reverse +
          DensePolynomial.evalCoeffs 0 polynomial.coeffs
      rw [coefficients]
      simp only [List.tail_cons, original, evalCoeffs_snoc, Gaussian.Basic.mul_zero,
        Gaussian.Basic.zero_add]
      ring1

/-- Evaluation at zero reads the last normalized coefficient, defaulting to zero.

Reversing the original normalized table exposes its constant coefficient.
The ascending jet at zero reads that same head with the original zero default. -/
private theorem origin_value (polynomial : CoefficientPolynomial) :
    polynomial.eval 0 = polynomial.normalize.coeffs.reverse.headD 0 := by
  have identity := congrArg Prod.fst (reverse_jet 0 polynomial.normalize.coeffs.reverse)
  rw [Reverse.reverse_reverse, Dense.Derivative.eval_original, DensePolynomial.eval_normalize,
    lowJet_origin]
      at identity
  exact identity

/-- Reversal retains the degree when the affine constant term is nonzero.

The same normalized coefficient list reverses to a nonzero head. Its Boolean
leading-zero scan therefore retains the complete list and its original length. -/
theorem reversed_degree_regular (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (originNonzero : polynomial.eval 0 ≠ 0) : (reversed polynomial).natDegree =
      polynomial.natDegree := by
  have headNonzero : polynomial.normalize.coeffs.reverse.headD 0 ≠ 0 := by
    rw [← origin_value]; exact originNonzero
  have count : (reversed polynomial).degreeCount = polynomial.degreeCount := by
    cases coefficients : polynomial.normalize.coeffs.reverse with
    | nil => exact (headNonzero (by rw [coefficients]; rfl)).elim
    | cons coefficient tail =>
        have coefficientNonzero : coefficient ≠ 0 := by
          rw [coefficients, List.headD_cons]
            at headNonzero
          exact headNonzero
        change ((polynomial.normalize.coeffs.reverse).dropWhile (· = 0)).length = _
        have retained : decide (coefficient = 0) = false := by
          cases selected : decide (coefficient = 0) with
          | false => rfl
          | true => exact (coefficientNonzero (of_decide_eq_true selected)).elim
        rw [coefficients, DropWhile.cons_of_false (fun value : Scalar => decide (value = 0)) coefficient tail retained]
        rw [← coefficients, Reverse.length_reverse]
        rfl
  rw [← DensePolynomial.natDegree_add_one_eq_degreeCount (reversed_nonzero
    nonzero),
    ← DensePolynomial.natDegree_add_one_eq_degreeCount nonzero]
      at count
  omega

/-- A simple affine zero removes exactly one leading zero after reversal.

The original value at zero supplies a zero head and the nonzero derivative
supplies the next nonzero coefficient. The retained Boolean normalization scan
therefore drops exactly the first entry of the reversed list. -/
theorem reversed_degree_simple (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (originZero : polynomial.eval 0 = 0) (derivativeNonzero : (Dense.Derivative.derivative polynomial).eval 0 ≠ 0) :
    (reversed polynomial).natDegree + 1 = polynomial.natDegree := by
  have value := origin_value polynomial
  have jet := congrArg Prod.snd (reverse_jet 0 polynomial.normalize.coeffs.reverse)
  rw [Reverse.reverse_reverse, ← Dense.Derivative.eval_derivative, Dense.Derivative.derivative_normalize] at jet
  have count : (reversed polynomial).degreeCount + 1 = polynomial.degreeCount := by
    cases coefficients : polynomial.normalize.coeffs.reverse with
    | nil =>
        rw [coefficients, lowJet_nil] at jet
        exact (derivativeNonzero jet).elim
    | cons coefficient tail =>
        have coefficientZero : coefficient = 0 := by
          rw [coefficients, List.headD_cons, originZero] at value
          exact value.symm
        subst coefficient
        cases tail with
        | nil =>
            rw [coefficients, lowJet_cons, lowJet_nil] at jet
            exact (derivativeNonzero (jet.trans (by ring1))).elim
        | cons next remaining =>
            have nextNonzero : next ≠ 0 := by
              rw [coefficients, lowJet_cons, lowJet_cons]
                at jet
              dsimp only at jet
              rw [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_mul,
                Gaussian.Basic.add_zero, Gaussian.Basic.add_zero]
                  at jet
              intro equal
              exact derivativeNonzero (jet.trans equal)
            change ((polynomial.normalize.coeffs.reverse).dropWhile (· = 0)).length + 1 = _
            have retained : decide (next = 0) = false := by
              cases selected : decide (next = 0) with
              | false => rfl
              | true => exact (nextNonzero (of_decide_eq_true selected)).elim
            rw [coefficients,
              DropWhile.cons_of_true (fun value : Scalar => decide (value = 0)) 0 (next :: remaining) (by decide),
              DropWhile.cons_of_false (fun value : Scalar => decide (value = 0)) next remaining retained]
            calc
              _ = (polynomial.normalize.coeffs.reverse).length := by
                rw [coefficients]; rfl
              _ = _ := Reverse.length_reverse _
  rw [← DensePolynomial.natDegree_add_one_eq_degreeCount (reversed_nonzero
    nonzero),
    ← DensePolynomial.natDegree_add_one_eq_degreeCount nonzero]
      at count
  omega

/-- Shifting a nonzero polynomial by a coordinate power preserves nonzeroness.

The nonzero Boolean branch appends the original number of zero coefficients
to the same normalized nonempty table, retaining its nonzero head. -/
theorem shifted_nonzero (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) (degree :
  Nat) :
    (DensePolynomial.shift degree polynomial).isZero = false := by
  obtain ⟨tail, coefficients, _⟩ := DensePolynomial.normalized_coeffs_shape nonzero
  unfold DensePolynomial.isZero
  rw [DensePolynomial.normalize_shift, DensePolynomial.shift, if_neg (by
      intro same
      have impossible : (false : Bool) = true := nonzero.symm.trans same
      cases impossible), coefficients]
  rfl

/-- Shifting a nonzero polynomial adds the shift to its natural degree.

Appending the original replicated zero table increases the coefficient count
by the selected shift; the retained nonzero head relates both counts to degree. -/
theorem shifted_degree (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) (degree :
  Nat) :
    (DensePolynomial.shift degree polynomial).natDegree = polynomial.natDegree + degree := by
  have count := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  unfold DensePolynomial.natDegree DensePolynomial.degreeCount
  rw [DensePolynomial.normalize_shift, DensePolynomial.shift, if_neg (by
      intro same
      have impossible : (false : Bool) = true := nonzero.symm.trans same
      cases impossible), Append.length_append, Replicate.length_replicate]
  change polynomial.natDegree + 1 = polynomial.normalize.coeffs.length at count
  rw [← count]
  omega

/-- Separate the initial value and tangent contributions in a finite derivative fold.

The identity retains the coefficient-count powers and the zero-initialized polynomial derivative. -/
private theorem fold_derivative (point : Scalar) :
    (coefficients : List Scalar) → (value derivativeValue : Scalar)
      →
    point * (coefficients.foldl (Dense.Derivative.evalDerivativeStep point) (value, derivativeValue)).2 =
      derivativeValue * point ^ (coefficients.length + 1) +
        value * (coefficients.length : Scalar) * point ^ coefficients.length +
          point * (Dense.Derivative.evalDerivativeCoeffs point coefficients).2
  | [], value, derivativeValue => by
      simp only [List.foldl_nil, List.length_nil, Nat.cast_zero, Nat.zero_add,
        pow_one, pow_zero, Dense.Derivative.evalDerivativeCoeffs, Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
      ring1
  | coefficient :: tail, value, derivativeValue => by
      simp only [List.foldl_cons, Dense.Derivative.evalDerivativeStep, List.length_cons]
      rw [fold_derivative point tail (value * point + coefficient)
        (derivativeValue * point + value)]
      simp only [Dense.Derivative.evalDerivativeCoeffs, List.foldl_cons, Dense.Derivative.evalDerivativeStep,
        Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add]
      rw [fold_derivative point tail coefficient 0]
      simp only [Dense.Derivative.evalDerivativeCoeffs, NatCast.add, Nat.cast_one, pow_succ]
      ring1

/-- Separate the leading monomial contribution from a descending coefficient jet derivative. -/
private theorem highJet_cons_derivative (point coefficient : Scalar) (tail : List
  Scalar) :
    point * (Dense.Derivative.evalDerivativeCoeffs point (coefficient :: tail)).2 =
      coefficient * (tail.length : Scalar) * point ^ tail.length +
        point * (Dense.Derivative.evalDerivativeCoeffs point tail).2 := by
  simpa only [Dense.Derivative.evalDerivativeCoeffs, List.foldl_cons, Dense.Derivative.evalDerivativeStep,
    Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add] using fold_derivative point tail
      coefficient 0

/-- Two extra chart powers clear the reciprocal derivative denominator.

The finite coefficient-count identity includes empty tables and constants.
Each recursive step retains the original chart-times-affine inverse witness
and the same value and derivative jet components. -/
private theorem reciprocal_jet (affine chart : Scalar) (cancel : chart * affine = 1) :
    (coefficients : List Scalar) →
    chart ^ coefficients.length * (Dense.Derivative.evalDerivativeCoeffs affine coefficients).2 +
      chart ^ 3 * (lowJet chart coefficients).2 + chart ^ 2 *
        (lowJet chart coefficients).1 =
        (coefficients.length : Scalar) * chart ^ 2 * (lowJet chart
          coefficients).1
  | [] => by
      change chart ^ 0 * 0 + chart ^ 3 * 0 + chart ^ 2 * 0 = (0 : Scalar) * chart ^ 2 * 0
      rw [Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero,
        Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero, Gaussian.Basic.add_zero]
  | coefficient :: tail => by
      have powers : chart ^ tail.length * affine ^ tail.length = 1 := by
        rw [← Semiring.Normalization.product_pow, cancel, one_pow]
      have contribution :
          chart ^ (tail.length + 1) * (Dense.Derivative.evalDerivativeCoeffs affine (coefficient :: tail)).2 =
            coefficient * (tail.length : Scalar) * chart ^ 2 +
              chart ^ (tail.length + 1) * (Dense.Derivative.evalDerivativeCoeffs affine tail).2 := by
        calc
          _ = chart ^ (tail.length + 1) * (chart * affine) *
              (Dense.Derivative.evalDerivativeCoeffs affine (coefficient :: tail)).2 := by rw [cancel,
                Gaussian.Basic.mul_one]
          _ = chart ^ tail.length * chart ^ 2 *
              (affine * (Dense.Derivative.evalDerivativeCoeffs affine (coefficient :: tail)).2) := by
                rw [pow_succ]; ring1
          _ = chart ^ tail.length * chart ^ 2 *
              (coefficient * (tail.length : Scalar) * affine ^ tail.length +
                affine * (Dense.Derivative.evalDerivativeCoeffs affine tail).2) := by rw
                  [highJet_cons_derivative]
          _ = coefficient * (tail.length : Scalar) * chart ^ 2 *
                (chart ^ tail.length * affine ^ tail.length) +
              chart ^ (tail.length + 1) * (chart * affine) * (Dense.Derivative.evalDerivativeCoeffs affine tail).2 := by
                rw [pow_succ]; ring1
          _ = _ := by rw [powers, cancel, Gaussian.Basic.mul_one, Gaussian.Basic.mul_one]
      have tailIdentity := reciprocal_jet affine chart cancel tail
      rw [List.length_cons, contribution, lowJet_cons, NatCast.add, Nat.cast_one]
      calc
        _ = chart * (chart ^ tail.length * (Dense.Derivative.evalDerivativeCoeffs affine tail).2 +
              chart ^ 3 * (lowJet chart tail).2 + chart ^ 2 *
                (lowJet chart tail).1) +
            (tail.length : Scalar) * chart ^ 2 * coefficient +
              chart ^ 2 * coefficient + chart ^ 3 * (lowJet chart tail).1 := by
                rw [pow_succ]; ring1
        _ = _ := by rw [tailIdentity]; ring1

/-- The reciprocal derivative identity holds with its denominator cleared.

The retained nonzero polynomial supplies its coefficient-count degree and the
nonzero chart supplies its inverse. The same two Horner jets establish the
law even when the original affine value at zero vanishes. -/
theorem reversed_derivative_identity (polynomial : CoefficientPolynomial)
    (nonzero : polynomial.isZero = false) (point : Scalar) (pointNonzero : point ≠ 0) :
    point ^ polynomial.natDegree * (Dense.Derivative.derivative polynomial).eval point⁻¹ +
      point ^ 2 * (Dense.Derivative.derivative (reversed polynomial)).eval point =
        (polynomial.natDegree : Scalar) * point * (reversed
          polynomial).eval point := open Purelib.Algebra.Field in by
  have identity := reciprocal_jet point⁻¹ point
    (ExplicitField.mul_inv_cancel point pointNonzero) polynomial.normalize.coeffs
  have count := (DensePolynomial.natDegree_add_one_eq_degreeCount nonzero).symm
  change polynomial.normalize.coeffs.length = polynomial.natDegree + 1 at count
  rw [← reversed_eval, ← reversed_derivative_eval,
    Dense.Derivative.evalDerivativeCoeffs_normalize,
    ← Dense.Derivative.eval_derivative, count, NatCast.add, Nat.cast_one, pow_succ] at identity
  apply Gaussian.Field.mul_right_cancel_of_ne pointNonzero
  have reduced :
      (point ^ polynomial.natDegree * (Dense.Derivative.derivative polynomial).eval point⁻¹ +
          point ^ 2 * (Dense.Derivative.derivative (reversed polynomial)).eval point) * point
            +
          point ^ 2 * (reversed polynomial).eval point =
        ((polynomial.natDegree : Scalar) * point * (reversed
          polynomial).eval point) * point +
          point ^ 2 * (reversed polynomial).eval point := by
    calc
      _ = point ^ polynomial.natDegree * point * (Dense.Derivative.derivative polynomial).eval point⁻¹ +
            point ^ 3 * (Dense.Derivative.derivative (reversed polynomial)).eval point +
              point ^ 2 * (reversed polynomial).eval point := by ring1
      _ = ((polynomial.natDegree : Scalar) + 1) * point ^ 2 *
            (reversed polynomial).eval point := identity
      _ = _ := by ring1
  exact add_right_cancel reduced

end Purelib.Polynomial.Dense.Gaussian.Reciprocal
