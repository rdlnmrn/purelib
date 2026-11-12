module

public import Purelib.Polynomial.Laurent.Normalization
public import Purelib.Polynomial.Dense.Gaussian.Conjugate
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Multiplicity
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.List.Map
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Reversal, coefficient conjugation and adjoints of original Laurent terms

Each operation maps the same ordered original term spine, retaining repeated
and zero-coefficient occurrences. Inversion identities explicitly retain a
nonzero input; algebraic cancellation never removes an original source guard.
-/

public section

namespace Purelib.Polynomial.Laurent.Basic.LaurentTerm

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Algebra.Power.Gaussian.Signed.Secant

/-- Reverse the exponent of this same original term while retaining its actual coefficient. -/
@[expose] def reverse (term : LaurentTerm) : LaurentTerm := ⟨term.coefficient, term.exponent.neg⟩

/-- Conjugate the coefficient of this same original term while retaining its actual exponent. -/
@[expose] def conjugate (term : LaurentTerm) : LaurentTerm := ⟨Canonical.conj term.coefficient, term.exponent⟩

/-- Conjugate the coefficient and reverse the exponent in one original term. -/
@[expose] def adjoint (term : LaurentTerm) : LaurentTerm := ⟨Canonical.conj term.coefficient, term.exponent.neg⟩

/-- Exponent reversal evaluates at the reciprocal on the original nonzero domain. -/
theorem eval_reverse (term : LaurentTerm) (point : Canonical) (nonzero : point ≠ 0) :
    term.reverse.eval point = term.eval point⁻¹ := by
  change term.coefficient * signedPower point term.exponent.neg = _
  rewrite [signedPower_neg point nonzero]
  rfl

/-- Coefficient conjugation evaluates as the conjugate of the original value at the conjugated input. -/
theorem eval_conjugate (term : LaurentTerm) (point : Canonical) :
    term.conjugate.eval point = Canonical.conj (term.eval (Canonical.conj point)) := by
  change Canonical.conj term.coefficient * signedPower point term.exponent =
    Canonical.conj (term.coefficient * signedPower (Canonical.conj point) term.exponent)
  rewrite [Canonical.conj_mul, signedPower_conj, Canonical.conj_conj]
  rfl

/-- The combined adjoint is the same term's conjugate followed by exponent reversal. -/
theorem adjoint_eq (term : LaurentTerm) : term.adjoint = term.conjugate.reverse := rfl

/-- Reversing an original term twice retains its same coefficient and exponent. -/
theorem reverse_reverse (term : LaurentTerm) : term.reverse.reverse = term := by
  change ⟨term.coefficient, term.exponent.neg.neg⟩ = term
  rewrite [Purelib.Data.Int.Exponent.neg_neg]
  cases term
  rfl

/-- Conjugating an original term twice retains its same coefficient and exponent. -/
theorem conjugate_conjugate (term : LaurentTerm) : term.conjugate.conjugate = term := by
  change ⟨Canonical.conj (Canonical.conj term.coefficient), term.exponent⟩ = term
  rewrite [Canonical.conj_conj]
  cases term
  rfl

/-- Taking the original term's combined adjoint twice retains the complete term. -/
theorem adjoint_adjoint (term : LaurentTerm) : term.adjoint.adjoint = term := by
  change ⟨Canonical.conj (Canonical.conj term.coefficient), term.exponent.neg.neg⟩ = term
  rewrite [Canonical.conj_conj, Purelib.Data.Int.Exponent.neg_neg]
  cases term
  rfl

/-- Conjugation followed by the combined adjoint is the same original exponent reversal. -/
theorem conjugate_adjoint (term : LaurentTerm) : term.conjugate.adjoint = term.reverse := by
  change ⟨Canonical.conj (Canonical.conj term.coefficient), term.exponent.neg⟩ = term.reverse
  exact congrArg (fun coefficient => LaurentTerm.mk coefficient term.exponent.neg)
    (Canonical.conj_conj term.coefficient)

end Purelib.Polynomial.Laurent.Basic.LaurentTerm

namespace Purelib.Polynomial.Laurent.Basic.LaurentPolynomial

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic.DividedDifference
open Purelib.Data.List

/-- Reverse every retained original exponent in its same ordered Laurent term list. -/
@[expose] def reverse (source : LaurentPolynomial) : LaurentPolynomial := ⟨source.terms.map LaurentTerm.reverse⟩

/-- Conjugate every retained original coefficient in its same ordered Laurent term list. -/
@[expose] def conjugate (source : LaurentPolynomial) : LaurentPolynomial := ⟨source.terms.map LaurentTerm.conjugate⟩

/-- Construct the combined adjoint in one traversal of the original ordered Laurent term list. -/
@[expose] def adjoint (source : LaurentPolynomial) : LaurentPolynomial := ⟨source.terms.map LaurentTerm.adjoint⟩

/-- The original reversed term sum evaluates at the reciprocal input. -/
private theorem eval_reverse_terms (point : Canonical) (nonzero : point ≠ 0) :
    ∀ terms : List LaurentTerm,
      sumGaussian ((terms.map LaurentTerm.reverse).map fun term => term.eval point) =
        sumGaussian (terms.map fun term => term.eval point⁻¹)
  | [] => rfl
  | term :: remaining => by
      change term.reverse.eval point + _ = term.eval point⁻¹ + _
      rewrite [term.eval_reverse point nonzero, eval_reverse_terms point nonzero remaining]
      rfl

/-- Original exponent reversal evaluates at the reciprocal without dropping any retained source term. -/
theorem eval_reverse (source : LaurentPolynomial) (point : Canonical) (nonzero : point ≠ 0) :
    source.reverse.eval point = source.eval point⁻¹ := eval_reverse_terms point nonzero source.terms

/-- The original coefficient-conjugated term sum is the conjugate of the original conjugated-input sum. -/
private theorem eval_conjugate_terms (point : Canonical) :
    ∀ terms : List LaurentTerm,
      sumGaussian ((terms.map LaurentTerm.conjugate).map fun term => term.eval point) =
        Canonical.conj (sumGaussian (terms.map fun term => term.eval (Canonical.conj point)))
  | [] => rfl
  | term :: remaining => by
      change term.conjugate.eval point + _ = Canonical.conj (term.eval (Canonical.conj point) + _)
      rewrite [term.eval_conjugate point, eval_conjugate_terms point remaining, Canonical.conj_add]
      rfl

/-- Original coefficient conjugation evaluates at the conjugated input and conjugates the complete source sum. -/
theorem eval_conjugate (source : LaurentPolynomial) (point : Canonical) :
    source.conjugate.eval point = Canonical.conj (source.eval (Canonical.conj point)) :=
  eval_conjugate_terms point source.terms

/-- The combined adjoint retains the same ordered term list as conjugation followed by reversal. -/
theorem adjoint_eq (source : LaurentPolynomial) : source.adjoint = source.conjugate.reverse := by
  apply congrArg LaurentPolynomial.mk
  have same := Map.map_map LaurentTerm.reverse LaurentTerm.conjugate source.terms
  exact same.symm

/-- Original adjoints evaluate as the conjugate source value at the reciprocal conjugated input. -/
theorem eval_adjoint (source : LaurentPolynomial) (point : Canonical) (nonzero : point ≠ 0) :
    source.adjoint.eval point = Canonical.conj (source.eval (Canonical.conj point⁻¹)) := by
  rewrite [source.adjoint_eq, eval_reverse _ point nonzero, eval_conjugate]
  rfl

/-- Coefficient conjugation preserves exactly the corresponding original guarded domain. -/
theorem definedAt_conjugate (source : LaurentPolynomial) (point : Canonical) :
    source.conjugate.DefinedAt point ↔ source.DefinedAt (Canonical.conj point) := by
  constructor
  · intro defined term member negative
    have mapped : term.conjugate ∈ source.conjugate.terms := Map.mem_map.mpr ⟨term, member, rfl⟩
    exact Canonical.conj_ne_zero (defined term.conjugate mapped negative)
  · intro defined term member
    obtain ⟨original, originalMember, equal⟩ := Map.mem_map.mp member
    cases equal
    intro negative zero
    exact defined original originalMember negative (congrArg Canonical.conj zero)

/-- On the original nonzero unit-circle domain the adjoint is the conjugate of the same source value. -/
theorem eval_adjoint_unit (source : LaurentPolynomial) (point : Canonical) (nonzero : point ≠ 0)
    (unit : point.normSq = 1) : source.adjoint.eval point = Canonical.conj (source.eval point) := by
  rewrite [source.eval_adjoint point nonzero, Canonical.inv_eq_conj_of_normSq_one point unit, Canonical.conj_conj]
  rfl

/-- Original exponent reversal is an involution of the complete ordered term representation. -/
theorem reverse_reverse (source : LaurentPolynomial) : source.reverse.reverse = source := by
  apply congrArg LaurentPolynomial.mk
  exact (Map.map_map LaurentTerm.reverse LaurentTerm.reverse source.terms).trans
    ((Map.map_congr_left (fun term _ => term.reverse_reverse)).trans (Map.map_id source.terms))

/-- Original coefficient conjugation is an involution of the complete ordered term representation. -/
theorem conjugate_conjugate (source : LaurentPolynomial) : source.conjugate.conjugate = source := by
  apply congrArg LaurentPolynomial.mk
  exact (Map.map_map LaurentTerm.conjugate LaurentTerm.conjugate source.terms).trans
    ((Map.map_congr_left (fun term _ => term.conjugate_conjugate)).trans (Map.map_id source.terms))

/-- The original combined adjoint is an involution of the complete ordered term representation. -/
theorem adjoint_adjoint (source : LaurentPolynomial) : source.adjoint.adjoint = source := by
  apply congrArg LaurentPolynomial.mk
  exact (Map.map_map LaurentTerm.adjoint LaurentTerm.adjoint source.terms).trans
    ((Map.map_congr_left (fun term _ => term.adjoint_adjoint)).trans (Map.map_id source.terms))

/-- Coefficient conjugation followed by the combined adjoint retains the same original reversed term list. -/
theorem conjugate_adjoint (source : LaurentPolynomial) : source.conjugate.adjoint = source.reverse := by
  apply congrArg LaurentPolynomial.mk
  exact (Map.map_map LaurentTerm.adjoint LaurentTerm.conjugate source.terms).trans
    (Map.map_congr_left (fun term _ => term.conjugate_adjoint))

end Purelib.Polynomial.Laurent.Basic.LaurentPolynomial

namespace Purelib.Polynomial.Laurent.Normalization.Normalized

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra
open Purelib.Polynomial.Laurent.Basic (LaurentPolynomial)

/-- A retained nonzero normalization excludes a zero certificate of the same original source.

Both certificates identify their cached shifted table with the same original
polynomialization at the same raw shift. Their original exact Boolean zero
tests therefore cannot disagree.
-/
theorem zero_impossible {source : LaurentPolynomial} (result : Normalized source)
    (obstruction : ZeroSymbol source) : False := by
  have same : result.shifted = obstruction.shifted := by
    rewrite [result.shifted_spec, obstruction.shifted_spec, result.rawShift_spec, obstruction.rawShift_spec]
    rfl
  have falseZero := (congrArg DensePolynomial.isZero same).trans obstruction.zero
  exact Bool.noConfusion (result.shifted_nonzero.symm.trans falseZero)

/-- A nonzero original normalization excludes a computed zero obstruction after exponent reversal. -/
private theorem reverse_zero_impossible {source : LaurentPolynomial} (result : Normalized source)
    (obstruction : ZeroSymbol source.reverse) : False := by
  have zero := Extensionality.isZero_of_positive_grid_zero result.polynomial (fun point member => by
    have nonzero := Extensionality.positiveProbePoints_nonzero _ point member
    have inverseNonzero := Canonical.inv_ne_zero nonzero
    have vanished := obstruction.eval_zero point⁻¹ (source.reverse.definedAt_of_nonzero inverseNonzero)
    have reading := source.eval_reverse point⁻¹ inverseNonzero
    rewrite [Canonical.inv_inv_nonzero point nonzero] at reading
    have sourceZero := reading.symm.trans vanished
    exact (result.polynomial_eval point (source.definedAt_of_nonzero nonzero)).trans
      ((congrArg (fun value => point ^ result.poleOrder * value) sourceZero).trans
        (Purelib.Data.Gaussian.Basic.mul_zero _)))
  exact Bool.noConfusion (result.polynomial_nonzero.symm.trans zero)

/-- A nonzero original normalization excludes a computed zero obstruction after coefficient conjugation. -/
private theorem conjugate_zero_impossible {source : LaurentPolynomial} (result : Normalized source)
    (obstruction : ZeroSymbol source.conjugate) : False := by
  have zero := Extensionality.isZero_of_positive_grid_zero result.polynomial (fun point member => by
    have nonzero := Extensionality.positiveProbePoints_nonzero _ point member
    have conjugateNonzero := Canonical.conj_ne_zero nonzero
    have vanished := obstruction.eval_zero (Canonical.conj point)
      (source.conjugate.definedAt_of_nonzero conjugateNonzero)
    have reading := source.eval_conjugate (Canonical.conj point)
    rewrite [Canonical.conj_conj] at reading
    have sourceZero := congrArg Canonical.conj (reading.symm.trans vanished)
    rewrite [Canonical.conj_conj] at sourceZero
    exact (result.polynomial_eval point (source.definedAt_of_nonzero nonzero)).trans
      ((congrArg (fun value => point ^ result.poleOrder * value) sourceZero).trans
        (Purelib.Data.Gaussian.Basic.mul_zero _)))
  exact Bool.noConfusion (result.polynomial_nonzero.symm.trans zero)

/-- Normalize the actual ordered exponent reversal with the original total coefficient preparation. -/
@[expose] def reverse {source : LaurentPolynomial} (result : Normalized source) : Normalized source.reverse :=
  match source.reverse.prepare with
  | .zero obstruction => False.elim (by exact reverse_zero_impossible result obstruction)
  | .normalized retained => retained

/-- Normalize the actual ordered coefficient conjugate with the original total coefficient preparation. -/
@[expose] def conjugate {source : LaurentPolynomial} (result : Normalized source) : Normalized source.conjugate :=
  match source.conjugate.prepare with
  | .zero obstruction => False.elim (by exact conjugate_zero_impossible result obstruction)
  | .normalized retained => retained

/-- Normalize the actual ordered adjoint once with the original total coefficient preparation. -/
@[expose] def adjoint {source : LaurentPolynomial} (result : Normalized source) : Normalized source.adjoint :=
  match source.adjoint.prepare with
  | .zero obstruction =>
      False.elim (by exact reverse_zero_impossible result.conjugate (source.adjoint_eq ▸ obstruction))
  | .normalized retained => retained

/-- The two actual conjugate polynomializations agree after the same original common pole shifts. -/
theorem conjugate_commonShift {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) :
    DensePolynomial.shift result.poleOrder retained.polynomial =
      DensePolynomial.shift retained.poleOrder (Conjugate.polynomial result.polynomial) := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_shift _ _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have sourceValue : source.conjugate.eval point = Canonical.conj (source.eval (Canonical.conj point)) :=
    source.eval_conjugate point
  have original := result.polynomial_eval (Canonical.conj point)
    (source.definedAt_of_nonzero (Canonical.conj_ne_zero nonzero))
  have power := Power.conj_pow (Canonical.conj point) result.poleOrder
  change Canonical.conj ((Canonical.conj point) ^ result.poleOrder) =
    (Canonical.conj (Canonical.conj point)) ^ result.poleOrder at power
  rewrite [Canonical.conj_conj] at power
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_shift,
    retained.polynomial_eval point (source.conjugate.definedAt_of_nonzero nonzero), sourceValue,
    Conjugate.eval, original, Canonical.conj_mul, power]
  ring1

/-- Original zero-root compensation is retained between the two actual coefficient-conjugate normalizations. -/
theorem conjugate_zero_balance {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) :
    retained.zeroMultiplicity + result.poleOrder = result.zeroMultiplicity + retained.poleOrder := by
  have balance := congrArg DensePolynomial.zeroMultiplicity (result.conjugate_commonShift retained)
  rewrite [DensePolynomial.zeroMultiplicity_shift _ retained.polynomial_nonzero,
    DensePolynomial.zeroMultiplicity_shift _ (Conjugate.nonzero result.polynomial result.polynomial_nonzero),
    Conjugate.zeroMultiplicity result.polynomial result.polynomial_normalized result.polynomial_nonzero,
    result.polynomial_zeroMultiplicity, retained.polynomial_zeroMultiplicity] at balance
  exact balance

/-- Coefficient conjugation preserves the actual minimal pole order. -/
theorem conjugate_poleOrder {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) : retained.poleOrder = result.poleOrder := by
  have balance := result.conjugate_zero_balance retained
  have sourceAxes := result.poleOrder_zero_or_zeroMultiplicity_zero
  have targetAxes := retained.poleOrder_zero_or_zeroMultiplicity_zero
  omega0

/-- Coefficient conjugation preserves the actual zero-root multiplicity. -/
theorem conjugate_zeroMultiplicity {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) : retained.zeroMultiplicity = result.zeroMultiplicity := by
  have balance := result.conjugate_zero_balance retained
  have poles := result.conjugate_poleOrder retained
  omega0

/-- The actual normalized conjugate polynomial is the original coefficient-conjugated polynomial table. -/
theorem conjugate_polynomial {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) : retained.polynomial = Conjugate.polynomial result.polynomial := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero retained.polynomial_normalized
    (Conjugate.normalized result.polynomial result.polynomial_normalized)
  intro point nonzero
  have same := congrArg (fun polynomial : DensePolynomial Canonical => polynomial.eval point)
    (result.conjugate_commonShift retained)
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_shift, result.conjugate_poleOrder retained] at same
  exact Field.mul_right_cancel_of_ne (Power.pow_ne_zero_direct point nonzero result.poleOrder) same

/-- Coefficient conjugation preserves the actual lowest signed support endpoint. -/
theorem conjugate_lower {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) : retained.lower = result.lower := by
  have poles := result.conjugate_poleOrder retained
  have zeroes := result.conjugate_zeroMultiplicity retained
  have sourcePole := result.poleOrder_spec
  have sourceZero := result.zeroMultiplicity_spec
  have sourceLower := result.lower_spec
  have targetPole := retained.poleOrder_spec
  have targetZero := retained.zeroMultiplicity_spec
  have targetLower := retained.lower_spec
  omega0

/-- Coefficient conjugation preserves the actual highest signed support endpoint. -/
theorem conjugate_upper {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.conjugate) : retained.upper = result.upper := by
  have poles := result.conjugate_poleOrder retained
  have sourceDegree := result.polynomial_degree
  have targetDegree := retained.polynomial_degree
  have degrees := congrArg DensePolynomial.natDegree (result.conjugate_polynomial retained)
  rewrite [Conjugate.natDegree] at degrees
  omega0

/-- The actual reversed polynomialization agrees with the original reciprocal under explicit common shifts.

The original polynomial degree and both actual minimal poles determine the
clearing powers. No nonzero-constant or nonnegative-upper-endpoint premise
removes original zero roots or transient coordinates.
-/
theorem reverse_commonShift {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) :
    DensePolynomial.shift result.polynomial.natDegree retained.polynomial =
      DensePolynomial.shift (result.poleOrder + retained.poleOrder) (Reciprocal.reversed result.polynomial) := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_shift _ _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have original := result.polynomial_eval point⁻¹ (source.definedAt_of_nonzero (Canonical.inv_ne_zero nonzero))
  have powers : point⁻¹ ^ result.poleOrder * point ^ result.poleOrder = 1 := by
    rewrite [← Semiring.Normalization.product_pow, Canonical.inv_mul_cancel point nonzero, one_pow]
    rfl
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_shift,
    retained.polynomial_eval point (source.reverse.definedAt_of_nonzero nonzero), source.eval_reverse point nonzero,
    Reciprocal.reversed_identity result.polynomial point nonzero, original, pow_add]
  calc
    _ = 1 * (point ^ retained.poleOrder * source.eval point⁻¹ * point ^ result.polynomial.natDegree) :=
      (Purelib.Data.Gaussian.Basic.one_mul _).symm
    _ = (point⁻¹ ^ result.poleOrder * point ^ result.poleOrder) *
        (point ^ retained.poleOrder * source.eval point⁻¹ * point ^ result.polynomial.natDegree) :=
      congrArg (fun value => value *
        (point ^ retained.poleOrder * source.eval point⁻¹ * point ^ result.polynomial.natDegree)) powers.symm
    _ = _ := by ring1

/-- The actual adjoint polynomialization agrees with the original reversed conjugate under explicit common shifts.

The original degree and the two minimal poles retain every zero-root
compensation. The proof reads the same original guarded source at the
reciprocal conjugated input; it constructs no intermediate normalization.
-/
theorem adjoint_commonShift {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.adjoint) :
    DensePolynomial.shift result.polynomial.natDegree retained.polynomial =
      DensePolynomial.shift (result.poleOrder + retained.poleOrder)
        (Reciprocal.reversed (Conjugate.polynomial result.polynomial)) := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq_nonzero
    (DensePolynomial.normalize_shift _ _) (DensePolynomial.normalize_shift _ _)
  intro point nonzero
  have original := result.polynomial_eval (Canonical.conj point⁻¹)
    (source.definedAt_of_nonzero (Canonical.conj_ne_zero (Canonical.inv_ne_zero nonzero)))
  have power := Power.conj_pow (Canonical.conj point⁻¹) result.poleOrder
  change Canonical.conj ((Canonical.conj point⁻¹) ^ result.poleOrder) =
    (Canonical.conj (Canonical.conj point⁻¹)) ^ result.poleOrder at power
  rewrite [Canonical.conj_conj] at power
  have powers : point⁻¹ ^ result.poleOrder * point ^ result.poleOrder = 1 := by
    rewrite [← Semiring.Normalization.product_pow, Canonical.inv_mul_cancel point nonzero, one_pow]
    rfl
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_shift,
    retained.polynomial_eval point (source.adjoint.definedAt_of_nonzero nonzero), source.eval_adjoint point nonzero,
    Reciprocal.reversed_identity (Conjugate.polynomial result.polynomial) point nonzero,
    Conjugate.natDegree, Conjugate.eval, original, Canonical.conj_mul, power, pow_add]
  calc
    _ = 1 * (point ^ retained.poleOrder * Canonical.conj (source.eval (Canonical.conj point⁻¹)) *
        point ^ result.polynomial.natDegree) := (Purelib.Data.Gaussian.Basic.one_mul _).symm
    _ = (point⁻¹ ^ result.poleOrder * point ^ result.poleOrder) *
        (point ^ retained.poleOrder * Canonical.conj (source.eval (Canonical.conj point⁻¹)) *
          point ^ result.polynomial.natDegree) :=
      congrArg (fun value => value *
        (point ^ retained.poleOrder * Canonical.conj (source.eval (Canonical.conj point⁻¹)) *
          point ^ result.polynomial.natDegree)) powers.symm
    _ = _ := by ring1

/-- Reversing support retains the exact original zero-root and pole compensation. -/
theorem reverse_zero_balance {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) :
    retained.zeroMultiplicity + result.polynomial.natDegree = result.poleOrder + retained.poleOrder := by
  have balance := congrArg DensePolynomial.zeroMultiplicity (result.reverse_commonShift retained)
  rewrite [DensePolynomial.zeroMultiplicity_shift _ retained.polynomial_nonzero,
    DensePolynomial.zeroMultiplicity_shift _ (Reciprocal.reversed_nonzero result.polynomial_nonzero),
    Reciprocal.reversed_zeroMultiplicity result.polynomial result.polynomial_nonzero,
    retained.polynomial_zeroMultiplicity] at balance
  exact balance.trans (Nat.zero_add _)

/-- Exponent reversal negates the actual highest endpoint to obtain the actual lowest endpoint. -/
theorem reverse_lower {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) : retained.lower = -result.upper := by
  have balance := result.reverse_zero_balance retained
  have degree := result.polynomial_degree
  have targetPole := retained.poleOrder_spec
  have targetZero := retained.zeroMultiplicity_spec
  have targetLower := retained.lower_spec
  omega0

/-- Exponent reversal negates the actual lowest endpoint to obtain the actual highest endpoint. -/
theorem reverse_upper {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) : retained.upper = -result.lower := by
  have degrees := congrArg DensePolynomial.natDegree (result.reverse_commonShift retained)
  rewrite [Reciprocal.shifted_degree _ retained.polynomial_nonzero,
    Reciprocal.shifted_degree _ (Reciprocal.reversed_nonzero result.polynomial_nonzero)] at degrees
  have reciprocalDegree := Reciprocal.reversed_degree_zeroMultiplicity result.polynomial result.polynomial_nonzero
  have sourceZero := result.polynomial_zeroMultiplicity
  have targetDegree := retained.polynomial_degree
  have sourcePole := result.poleOrder_spec
  have sourceZeroSpec := result.zeroMultiplicity_spec
  have sourceLower := result.lower_spec
  omega0

/-- Equality of the original source owners transports a normalization's same lowest scalar endpoint. -/
private theorem lower_transport {source target : LaurentPolynomial} (equal : source = target)
    (result : Normalized source) : (equal ▸ result).lower = result.lower := by
  cases equal
  rfl

/-- Equality of the original source owners transports a normalization's same highest scalar endpoint. -/
private theorem upper_transport {source target : LaurentPolynomial} (equal : source = target)
    (result : Normalized source) : (equal ▸ result).upper = result.upper := by
  cases equal
  rfl

/-- The actual combined adjoint negates the original highest endpoint to give its lowest endpoint. -/
theorem adjoint_lower {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.adjoint) : retained.lower = -result.upper := by
  let reversed : Normalized source.conjugate.reverse := source.adjoint_eq ▸ retained
  have lower := result.conjugate.reverse_lower reversed
  exact (lower_transport source.adjoint_eq retained).symm.trans
    (lower.trans (congrArg Neg.neg (result.conjugate_upper result.conjugate)))

/-- The actual combined adjoint negates the original lowest endpoint to give its highest endpoint. -/
theorem adjoint_upper {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.adjoint) : retained.upper = -result.lower := by
  let reversed : Normalized source.conjugate.reverse := source.adjoint_eq ▸ retained
  have upper := result.conjugate.reverse_upper reversed
  exact (upper_transport source.adjoint_eq retained).symm.trans
    (upper.trans (congrArg Neg.neg (result.conjugate_lower result.conjugate)))

/-- Reversal's actual minimal pole is the positive part of the original highest endpoint. -/
theorem reverse_poleOrder {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) : retained.poleOrder = result.upper.toNat := by
  rewrite [retained.poleOrder_eq, result.reverse_lower retained]
  exact congrArg Int.toNat (show -(-result.upper) = result.upper by omega0)

/-- Reversal's actual zero-root count is the negative part of the original highest endpoint. -/
theorem reverse_zeroMultiplicity {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.reverse) : retained.zeroMultiplicity = (-result.upper).toNat := by
  have lower : (retained.trailing : Int) - (retained.rawShift : Int) = -result.upper :=
    retained.lower_spec.symm.trans (result.reverse_lower retained)
  exact retained.zeroMultiplicity_spec.trans
    ((Int.toNat_sub retained.trailing retained.rawShift).symm.trans (congrArg Int.toNat lower))

/-- The combined adjoint's actual minimal pole is the positive part of the original highest endpoint. -/
theorem adjoint_poleOrder {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.adjoint) : retained.poleOrder = result.upper.toNat := by
  rewrite [retained.poleOrder_eq, result.adjoint_lower retained]
  exact congrArg Int.toNat (show -(-result.upper) = result.upper by omega0)

/-- The combined adjoint's actual zero-root count is the negative part of the original highest endpoint. -/
theorem adjoint_zeroMultiplicity {source : LaurentPolynomial} (result : Normalized source)
    (retained : Normalized source.adjoint) : retained.zeroMultiplicity = (-result.upper).toNat := by
  have lower : (retained.trailing : Int) - (retained.rawShift : Int) = -result.upper :=
    retained.lower_spec.symm.trans (result.adjoint_lower retained)
  exact retained.zeroMultiplicity_spec.trans
    ((Int.toNat_sub retained.trailing retained.rawShift).symm.trans (congrArg Int.toNat lower))

end Purelib.Polynomial.Laurent.Normalization.Normalized

end
