module

public import Purelib.Polynomial.Laurent.Polynomialization
public import Purelib.Polynomial.Dense.ZeroMultiplicity
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached support normalization of Gaussian-rational Laurent expressions

A sufficient raw shift first combines every displayed coefficient in the
original dense polynomial owner. Its exact zero suffix then determines the
minimal pole order, both signed support endpoints and the polynomialization.
The source expression retains its original negative-power domain guards.
-/

namespace Purelib.Polynomial.Laurent.Normalization

open Purelib
open Purelib.Data
open Purelib.Polynomial
open Purelib.Polynomial.Laurent.Basic
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Leading

set_option genInjectivity false in
/-- A nonzero normalized Laurent expression with its retained original coefficient computation.

The shifted table and zero core refer to the same original finite source.
The polynomial uses the smallest pole-clearing shift and keeps any actual
zero-root multiplicity caused by positive lowest support. -/
public structure Normalized (source : LaurentPolynomial) where
  /-- The cached sufficient shift before coefficient cancellation. -/ rawShift : Nat
  /-- The raw shift is computed from the original displayed exponents. -/ rawShift_spec : rawShift = source.rawShift
  /-- The cached original normalized shifted dense coefficient table. -/
  shifted : DensePolynomial Gaussian.Basic.Canonical
  /-- The shifted table is the original finite polynomialization. -/
  shifted_spec : shifted = (source.polynomialize rawShift).normalize
  /-- The actual shifted coefficient table is nonzero. -/ shifted_nonzero : shifted.isZero = false
  /-- The cached original shifted table after removing trailing zeroes. -/
  core : DensePolynomial Gaussian.Basic.Canonical
  /-- The core is computed by the original trailing-zero scan. -/ core_spec : core = shifted.zeroCore
  /-- The cached length of the removed trailing zero block. -/ trailing : Nat
  /-- The trailing count is the original shifted polynomial's zero multiplicity. -/
  trailing_spec : trailing = shifted.zeroMultiplicity
  /-- The lowest exponent after combining all repeated terms and cancellations. -/ lower : Int
  /-- The lower endpoint includes the exact removed-zero compensation. -/
  lower_spec : lower = (trailing : Int) - (rawShift : Int)
  /-- The highest exponent after combining all repeated terms and cancellations. -/ upper : Int
  /-- The upper endpoint retains the original nonzero core degree. -/
  upper_spec : upper = lower + (core.natDegree : Int)
  /-- The actual minimal natural pole-clearing shift. -/ poleOrder : Nat
  /-- The minimal shift removes only the uncancelled negative support. -/
  poleOrder_spec : poleOrder = rawShift - trailing
  /-- The cached ordinary dense polynomial at the minimal shift. -/
  polynomial : DensePolynomial Gaussian.Basic.Canonical
  /-- Polynomialization retains every positive lowest-support zero root. -/
  polynomial_spec : polynomial = DensePolynomial.shift (trailing - rawShift) core
  /-- The cached actual zero-root multiplicity of the ordinary polynomial. -/ zeroMultiplicity : Nat
  /-- The zero multiplicity counts the positive lowest support exactly. -/
  zeroMultiplicity_spec : zeroMultiplicity = trailing - rawShift

constructive_injectivity Normalized

namespace Normalized

/-- The cached shifted table retains its original leading normalization. -/
public theorem shifted_normalized {source : LaurentPolynomial} (result : Normalized source) :
    result.shifted.normalize = result.shifted := by
  rewrite [result.shifted_spec]
  exact DensePolynomial.normalize_normalize _

/-- The exact cached core and trailing block reconstruct the retained shifted polynomial. -/
public theorem shifted_factorization {source : LaurentPolynomial} (result : Normalized source) :
    DensePolynomial.shift result.trailing result.core = result.shifted := by
  rewrite [result.core_spec, result.trailing_spec]
  exact (DensePolynomial.shift_zeroCore result.shifted_nonzero).trans result.shifted_normalized

/-- The retained zero core is normalized. -/
public theorem core_normalized {source : LaurentPolynomial} (result : Normalized source) :
    result.core.normalize = result.core := by
  rewrite [result.core_spec]
  exact DensePolynomial.zeroCore_normalized result.shifted_nonzero

/-- The retained zero core is nonzero. -/
public theorem core_nonzero {source : LaurentPolynomial} (result : Normalized source) :
    result.core.isZero = false := by
  rewrite [result.core_spec]
  exact DensePolynomial.zeroCore_nonzero result.shifted_nonzero

/-- The original retained constant coefficient of the zero core is nonzero. -/
public theorem core_constant_nonzero {source : LaurentPolynomial} (result : Normalized source) :
    Dense.Coefficients.constantCoefficient result.core.coeffs ≠ 0 := by
  rewrite [result.core_spec]
  exact DensePolynomial.zeroCore_constant_nonzero result.shifted_nonzero

/-- The retained polynomialization is normalized by the original dense operation. -/
public theorem polynomial_normalized {source : LaurentPolynomial} (result : Normalized source) :
    result.polynomial.normalize = result.polynomial := by
  rewrite [result.polynomial_spec]
  exact DensePolynomial.normalize_shift _ _

/-- The retained polynomialization is nonzero. -/
public theorem polynomial_nonzero {source : LaurentPolynomial} (result : Normalized source) :
    result.polynomial.isZero = false := by
  rewrite [result.polynomial_spec]
  exact (LeadingTerm.shift _ (LeadingTerm.ofNormalized result.core_nonzero result.core_normalized)).nonzero

/-- The normalized signed support interval has its endpoints in increasing order. -/
public theorem lower_le_upper {source : LaurentPolynomial} (result : Normalized source) :
    result.lower ≤ result.upper := by
  rewrite [result.upper_spec]
  omega0

/-- The highest support exponent is the shifted polynomial degree minus the original raw shift. -/
public theorem upper_degree {source : LaurentPolynomial} (result : Normalized source) :
    result.upper = (result.shifted.natDegree : Int) - (result.rawShift : Int) := by
  have shiftedDegree := (LeadingTerm.shift result.trailing
    (LeadingTerm.ofNormalized result.core_nonzero result.core_normalized)).degree_eq
  rewrite [result.shifted_factorization] at shiftedDegree
  rewrite [result.upper_spec, result.lower_spec, shiftedDegree]
  omega0

/-- The original polynomial degree is the highest Laurent exponent plus its actual pole order. -/
public theorem polynomial_degree {source : LaurentPolynomial} (result : Normalized source) :
    (result.polynomial.natDegree : Int) = result.upper + (result.poleOrder : Int) := by
  have degree := (LeadingTerm.shift (result.trailing - result.rawShift)
    (LeadingTerm.ofNormalized result.core_nonzero result.core_normalized)).degree_eq
  rewrite [← result.polynomial_spec] at degree
  rewrite [degree, result.upper_spec, result.lower_spec, result.poleOrder_spec]
  omega0

/-- Minimal polynomialization has either zero pole order or zero original zero-root multiplicity. -/
public theorem poleOrder_zero_or_zeroMultiplicity_zero {source : LaurentPolynomial}
    (result : Normalized source) : result.poleOrder = 0 ∨ result.zeroMultiplicity = 0 := by
  by_cases ordered : result.rawShift ≤ result.trailing
  · left
    rewrite [result.poleOrder_spec]
    omega0
  · right
    rewrite [result.zeroMultiplicity_spec]
    omega0

/-- The exact retained nonzero core does not have zero as a root. -/
public theorem core_eval_zero_nonzero {source : LaurentPolynomial} (result : Normalized source) :
    result.core.eval 0 ≠ 0 := by
  rewrite [result.core_spec]
  exact DensePolynomial.zeroCore_eval_zero_nonzero result.shifted_nonzero

/-- Positive minimal pole order leaves a nonzero constant coefficient in the original polynomialization.

The minimal shift removes exactly the negative support. Positive lowest
support can still produce zero roots when the pole order is zero; this
claim supplies the constant unit only for actual positive startup shifts.
-/
public theorem polynomial_eval_zero_nonzero {source : LaurentPolynomial} (result : Normalized source)
    (polePositive : 0 < result.poleOrder) : result.polynomial.eval 0 ≠ 0 := by
  have exponentZero : result.trailing - result.rawShift = 0 := by
    have shift := result.poleOrder_spec
    omega0
  have same : result.polynomial.eval 0 = result.core.eval 0 := by
    rewrite [result.polynomial_spec, DensePolynomial.eval_shift, exponentZero]
    exact Gaussian.Basic.mul_one _
  intro zero
  exact result.core_eval_zero_nonzero (same.symm.trans zero)

/-- The retained pole order is the nonnegative part of the negative lowest exponent. -/
public theorem poleOrder_eq {source : LaurentPolynomial} (result : Normalized source) :
    result.poleOrder = (-result.lower).toNat := by
  rewrite [result.poleOrder_spec, result.lower_spec]
  have reversed : -((result.trailing : Int) - (result.rawShift : Int)) =
      (result.rawShift : Int) - (result.trailing : Int) := by omega0
  rewrite [reversed]
  exact (Int.toNat_sub result.rawShift result.trailing).symm

/-- The retained zero-root count is exactly the original polynomial's executable readback. -/
public theorem polynomial_zeroMultiplicity {source : LaurentPolynomial} (result : Normalized source) :
    result.polynomial.zeroMultiplicity = result.zeroMultiplicity := by
  rewrite [result.polynomial_spec, DensePolynomial.zeroMultiplicity_shift _ result.core_nonzero]
  have coreZero : result.core.zeroMultiplicity = 0 := by
    rewrite [result.core_spec]
    exact DensePolynomial.zeroMultiplicity_zeroCore result.shifted_nonzero
  rewrite [coreZero, result.zeroMultiplicity_spec]
  exact Nat.zero_add _

/-- The original polynomial's zero-root multiplicity is the lowest Laurent exponent plus the actual pole order. -/
public theorem zeroMultiplicity_eq {source : LaurentPolynomial} (result : Normalized source) :
    (result.zeroMultiplicity : Int) = result.lower + (result.poleOrder : Int) := by
  rewrite [result.zeroMultiplicity_spec, result.lower_spec, result.poleOrder_spec]
  omega0

/-- The retained shifted dense table evaluates as the original guarded expression times the raw power. -/
public theorem shifted_eval {source : LaurentPolynomial} (result : Normalized source)
    (point : Gaussian.Basic.Canonical) (defined : source.DefinedAt point) :
    result.shifted.eval point = point ^ result.rawShift * source.eval point := by
  rewrite [result.shifted_spec, DensePolynomial.eval_normalize]
  exact source.eval_polynomialize result.rawShift
    (by rewrite [result.rawShift_spec]; exact Nat.le_refl _) point defined

/-- The retained zero core factors the same shifted dense polynomial. -/
public theorem shifted_core_eval {source : LaurentPolynomial} (result : Normalized source)
    (point : Gaussian.Basic.Canonical) :
    result.shifted.eval point = result.core.eval point * point ^ result.trailing := by
  rewrite [result.core_spec, result.trailing_spec]
  exact DensePolynomial.eval_zeroCore_mul_power _ _

/-- Minimal polynomialization preserves the original expression on its retained source domain.

Positive lowest support remains as actual zero roots of the polynomial. The
zero-input branch uses the original domain to prove the raw shift is zero. -/
public theorem polynomial_eval {source : LaurentPolynomial} (result : Normalized source)
    (point : Gaussian.Basic.Canonical) (defined : source.DefinedAt point) :
    result.polynomial.eval point = point ^ result.poleOrder * source.eval point := by
  by_cases pointZero : point = 0
  · subst point
    have shiftZero : result.rawShift = 0 := result.rawShift_spec.trans
      (source.rawShift_eq_zero_of_definedAt_zero defined)
    have poleZero : result.poleOrder = 0 := by rewrite [result.poleOrder_spec, shiftZero]; exact Nat.zero_sub _
    have remaining : result.trailing - result.rawShift = result.trailing := by rewrite [shiftZero]; exact Nat.sub_zero _
    rewrite [result.polynomial_spec, DensePolynomial.eval_shift, remaining]
    rewrite [← result.shifted_core_eval, result.shifted_eval 0 defined, shiftZero, poleZero]
    exact Eq.refl _
  · have powerNonzero := Gaussian.Power.pow_ne_zero_direct point pointZero result.rawShift
    apply Gaussian.Field.mul_right_cancel_of_ne powerNonzero
    have degreeBalance : result.trailing - result.rawShift + result.rawShift =
        result.trailing + result.poleOrder := by
      rewrite [result.poleOrder_spec]
      omega0
    calc
      result.polynomial.eval point * point ^ result.rawShift =
          result.core.eval point * point ^ (result.trailing - result.rawShift + result.rawShift) := by
        rewrite [result.polynomial_spec, DensePolynomial.eval_shift, pow_add]
        ring1
      _ = result.core.eval point * point ^ (result.trailing + result.poleOrder) :=
        congrArg (fun degree : Nat => result.core.eval point * point ^ degree) degreeBalance
      _ = (result.core.eval point * point ^ result.trailing) * point ^ result.poleOrder := by
        rewrite [pow_add]
        exact (Gaussian.Basic.mul_assoc _ _ _).symm
      _ = (point ^ result.rawShift * source.eval point) * point ^ result.poleOrder := by
        rewrite [← result.shifted_core_eval, result.shifted_eval point defined]
        exact Eq.refl _
      _ = (point ^ result.poleOrder * source.eval point) * point ^ result.rawShift := by ring1

/-- Minimal polynomialization preserves the original symbol quadrance on the rational unit circle. -/
public theorem polynomial_normSq {source : LaurentPolynomial} (result : Normalized source)
    (point : Gaussian.Basic.Canonical) (unit : point.normSq = 1) :
    Gaussian.Norm.Basic.normSq (result.polynomial.eval point) =
      Gaussian.Norm.Basic.normSq (source.eval point) := by
  have nonzero : point ≠ 0 := by
    intro zero
    rewrite [zero, Gaussian.Basic.Canonical.normSq_zero] at unit
    exact (by decide : (0 : Rat.Fraction.Rational) ≠ 1) unit
  rewrite [result.polynomial_eval point (source.definedAt_of_nonzero nonzero),
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow,
    Gaussian.Norm.Basic.normSq_eq_canonical point, unit, one_pow, Rat.Fraction.Field.one_mul]
  rfl

/-- A larger polynomializing shift adds exactly the displayed zero-root count. -/
public theorem nonminimal_zeroMultiplicity {source : LaurentPolynomial} (result : Normalized source)
    (extra : Nat) :
    (DensePolynomial.shift extra result.polynomial).zeroMultiplicity = result.zeroMultiplicity + extra := by
  rewrite [DensePolynomial.zeroMultiplicity_shift _ result.polynomial_nonzero,
    result.polynomial_zeroMultiplicity]
  exact Eq.refl _

/-- A larger original dense shift polynomializes the same guarded Laurent expression. -/
public theorem nonminimal_eval {source : LaurentPolynomial} (result : Normalized source)
    (extra : Nat) (point : Gaussian.Basic.Canonical) (defined : source.DefinedAt point) :
    (DensePolynomial.shift extra result.polynomial).eval point =
      point ^ (result.poleOrder + extra) * source.eval point := by
  rewrite [DensePolynomial.eval_shift, result.polynomial_eval point defined, pow_add]
  ring1

/-- Every sufficient original polynomializing shift adds exactly its excess pole-clearing zeros.

Both sides retain the original source expression and normalized coefficient
owners. The finite positive probe bank compares values away from zero, so
cancelled negative powers never erase the original source-domain guards.
-/
public theorem polynomialize_eq_shift {source : LaurentPolynomial} (result : Normalized source)
    (shift : Nat) (sufficient : source.rawShift ≤ shift) :
    (source.polynomialize shift).normalize =
      DensePolynomial.shift (shift - result.poleOrder) result.polynomial := by
  have poleBound : result.poleOrder ≤ shift := by
    rewrite [result.poleOrder_spec, result.rawShift_spec]
    exact (Nat.sub_le _ _).trans sufficient
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_normalize _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have defined := source.definedAt_of_nonzero nonzero
  have powers : point ^ result.poleOrder * point ^ (shift - result.poleOrder) = point ^ shift := by
    rewrite [← pow_add, Nat.add_sub_of_le poleBound]
    rfl
  rewrite [DensePolynomial.eval_normalize, source.eval_polynomialize shift sufficient point defined,
    DensePolynomial.eval_shift, result.polynomial_eval point defined]
  calc
    point ^ shift * source.eval point =
        (point ^ result.poleOrder * point ^ (shift - result.poleOrder)) * source.eval point := by rewrite [powers]; rfl
    _ = _ := by ring1

/-- Equal added pole and zero-root counts cancel in the signed index balance. -/
public theorem nonminimal_balance {source : LaurentPolynomial} (result : Normalized source)
    (inside extra : Nat) :
    ((result.poleOrder + extra : Nat) : Int) - ((inside + extra : Nat) : Int) =
      (result.poleOrder : Int) - (inside : Int) := by omega0

end Normalized

set_option genInjectivity false in
/-- A computed zero coefficient table certifies a zero original Laurent symbol.

The original raw shift and table are retained, so cancellation does not erase
the source expression's negative-power guards. -/
public structure ZeroSymbol (source : LaurentPolynomial) where
  /-- The actual cached raw polynomializing shift. -/ rawShift : Nat
  /-- The shift belongs to the same original expression. -/ rawShift_spec : rawShift = source.rawShift
  /-- The actual cached shifted coefficient table. -/ shifted : DensePolynomial Gaussian.Basic.Canonical
  /-- The coefficient table is the original polynomialization. -/
  shifted_spec : shifted = (source.polynomialize rawShift).normalize
  /-- The original exact dense zero test rejected this symbol. -/ zero : shifted.isZero = true

constructive_injectivity ZeroSymbol

namespace ZeroSymbol

/-- A computed zero symbol evaluates to zero at every point in its original domain. -/
public theorem eval_zero {source : LaurentPolynomial} (result : ZeroSymbol source)
    (point : Gaussian.Basic.Canonical) (defined : source.DefinedAt point) : source.eval point = 0 := by
  have zeroValue := DensePolynomial.eval_eq_zero_of_isZero result.zero point
  have shiftedValue : result.shifted.eval point = point ^ result.rawShift * source.eval point := by
    rewrite [result.shifted_spec, DensePolynomial.eval_normalize]
    exact source.eval_polynomialize result.rawShift
      (by rewrite [result.rawShift_spec]; exact Nat.le_refl _) point defined
  by_cases pointZero : point = 0
  · subst point
    have shiftZero : result.rawShift = 0 := result.rawShift_spec.trans
      (source.rawShift_eq_zero_of_definedAt_zero defined)
    rewrite [shiftedValue, shiftZero, pow_zero, Gaussian.Basic.one_mul] at zeroValue
    exact zeroValue
  · have powerNonzero := Gaussian.Power.pow_ne_zero_direct point pointZero result.rawShift
    apply Gaussian.Field.mul_right_cancel_of_ne powerNonzero
    calc
      source.eval point * point ^ result.rawShift =
          point ^ result.rawShift * source.eval point := Gaussian.Basic.mul_comm _ _
      _ = 0 := shiftedValue.symm.trans zeroValue
      _ = 0 * point ^ result.rawShift := (Gaussian.Basic.zero_mul _).symm

/-- The unit-boundary point one witnesses the computed zero symbol's boundary contact. -/
public theorem boundary_contact {source : LaurentPolynomial} (result : ZeroSymbol source) :
    source.eval 1 = 0 :=
  result.eval_zero 1 (source.definedAt_of_nonzero (by decide))

end ZeroSymbol

set_option genInjectivity false in
/-- Exact preparation either retains a computed zero obstruction or a normalized nonzero symbol. -/
public inductive Preparation (source : LaurentPolynomial) where
  /-- The actual coefficient computation vanishes, proving unit-boundary contact. -/
  | zero (obstruction : ZeroSymbol source)
  /-- The actual coefficient computation supplies its minimal polynomialization. -/
  | normalized (result : Normalized source)

constructive_injectivity Preparation

end Purelib.Polynomial.Laurent.Normalization

namespace Purelib.Polynomial.Laurent.Basic.LaurentPolynomial

open Purelib.Data
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Laurent.Normalization

/-- Prepare the original Laurent expression by one cached shifted coefficient computation.

The exact zero decision returns a certified obstruction. Otherwise the same
retained table and its trailing-zero scan determine the normalized support,
minimal pole order, polynomial and original zero-root multiplicity. -/
@[expose] public def prepare (source : LaurentPolynomial) : Preparation source :=
  let rawShift := source.rawShift
  let shifted := (source.polynomialize rawShift).normalize
  if zero : shifted.isZero = true then
    .zero ⟨rawShift, rfl, shifted, rfl, zero⟩
  else
    let core := shifted.zeroCore
    let trailing := shifted.zeroMultiplicity
    let lower := (trailing : Int) - (rawShift : Int)
    .normalized
      { rawShift := rawShift
        rawShift_spec := rfl
        shifted := shifted
        shifted_spec := rfl
        shifted_nonzero := by cases actual : shifted.isZero with
          | false => rfl
          | true => exact (zero actual).elim
        core := core
        core_spec := rfl
        trailing := trailing
        trailing_spec := rfl
        lower := lower
        lower_spec := rfl
        upper := lower + (core.natDegree : Int)
        upper_spec := rfl
        poleOrder := rawShift - trailing
        poleOrder_spec := rfl
        polynomial := DensePolynomial.shift (trailing - rawShift) core
        polynomial_spec := rfl
        zeroMultiplicity := trailing - rawShift
        zeroMultiplicity_spec := rfl }

end Purelib.Polynomial.Laurent.Basic.LaurentPolynomial
