module
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Mul

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Power
public import Purelib.Approximation.Gaussian.Provenance.Power.Nonzero
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Polynomial.Dense.Gaussian.Basic

section
@[expose] public section

/-!
# Odd-power differentials on an original radicand

A differential retains its numerator, scale and odd denominator exponent,
with the exact coefficient expression `scale * R(x) * Y / P(x)^(k+1)` cached
on its original radicand. The productive numerical evaluator uses the
original apart sheet; its square provenance compares that same evaluator
with the retained coefficient interpretation.

Changing the radicand constructs a new coefficient cache while preserving
the original scalar data. This construction does not choose a root or identify
distinct sheets.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- The canonical finite coefficient reduction of one displayed odd-power differential. -/
def coefficientSpec (radicand numerator : Coefficients) (pairs : Nat)
    (scale : Data.Gaussian.Basic.Canonical) : Expression radicand :=
  Expression.oddReciprocal radicand pairs (numerator.scale scale)

/-! ## Odd-power algebraic integrands -/

set_option genInjectivity false in
/-- A displayed differential `scale * numerator(x) * dx / y^(2*denominatorPairs+1)`. -/
structure OddPowerDifferential (radicand : Coefficients) where
  /-- The explicit Gaussian polynomial numerator of the differential. -/
  numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The number of additional pairs of sheet-value factors in the odd denominator power. -/ denominatorPairs : Nat
  /-- The exact Gaussian scalar multiplying the polynomial numerator. -/ scale : Data.Gaussian.Basic.Canonical
  /-- The cached reduced coefficients at this same original radicand. -/
  coefficient : Expression radicand
  /-- The cached expression belongs to these original numerator, exponent and scale. -/
  coefficient_eq : coefficient = coefficientSpec radicand numerator denominatorPairs scale

constructive_injectivity Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

namespace OddPowerDifferential

variable {radicand : Coefficients}

/-- Compute the exact reduced coefficients once and retain their original specification. -/
def ofCoefficients (radicand numerator : Coefficients) (pairs : Nat)
    (scale : Data.Gaussian.Basic.Canonical) : OddPowerDifferential radicand :=
  ⟨numerator, pairs, scale, coefficientSpec radicand numerator pairs scale, rfl⟩

/-- Retain the original scalar data while constructing its coefficient expression on a new radicand.

The target coefficient cache is computed once from the target polynomial.
This operation asserts no equality between the two coefficient expressions,
root channels or fibres.
-/
def atRadicand (original : OddPowerDifferential radicand) (target : Coefficients) :
    OddPowerDifferential target :=
  ofCoefficients target original.numerator original.denominatorPairs original.scale

/-- A changed radicand retains the original numerator table literally. -/
theorem atRadicand_numerator (original : OddPowerDifferential radicand) (target : Coefficients) :
    (original.atRadicand target).numerator = original.numerator := rfl

/-- A changed radicand retains the original odd denominator pair count. -/
theorem atRadicand_denominatorPairs (original : OddPowerDifferential radicand) (target : Coefficients) :
    (original.atRadicand target).denominatorPairs = original.denominatorPairs := rfl

/-- A changed radicand retains the original scalar coefficient. -/
theorem atRadicand_scale (original : OddPowerDifferential radicand) (target : Coefficients) :
    (original.atRadicand target).scale = original.scale := rfl

/-- A changed radicand computes its coefficient cache from the target polynomial
and the retained original scalar data. -/
theorem atRadicand_coefficient (original : OddPowerDifferential radicand) (target : Coefficients) :
    (original.atRadicand target).coefficient =
      coefficientSpec target original.numerator original.denominatorPairs original.scale := rfl

/-- The odd sheet-value exponent, twice the retained pair count plus one. -/
def denominatorExponent
  (differential : OddPowerDifferential radicand) : Nat :=
  2 * differential.denominatorPairs + 1

/-- The actual productive coefficient name at one displayed point and sheet.

Only division by the already apart sheet value is used; higher reciprocal
powers are total finite multiplications on that original numerical channel.
-/
def value (differential : OddPowerDifferential radicand) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed) (apart : Named.Apart sheetValue.name)
    (reading : { value : Data.Gaussian.Basic.Canonical //
      value = differential.scale * differential.numerator.eval point } :=
        ⟨differential.scale * differential.numerator.eval point, rfl⟩) : Coherent.CoherentNamed :=
  let numerator := Coherence.exact reading.val
  let reciprocal := CoherentNamed.div
    (Coherence.exact 1) sheetValue apart
  CoherentNamed.mul numerator
    (Power.namedPower reciprocal differential.denominatorExponent)

/-- Changing only the coefficient radicand retains the complete original numerical evaluator at each point and sheet. -/
theorem value_atRadicand (original : OddPowerDifferential radicand) (target : Coefficients)
    (point : Data.Gaussian.Basic.Canonical) (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    (original.atRadicand target).value point sheetValue apart = original.value point sheetValue apart := rfl

/-- The original root evidence establishes the cached coefficient denominator guard. -/
theorem defined (differential : OddPowerDifferential radicand) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed) (identity : PowerIdentity sheetValue 2 (radicand.eval point))
    (apart : Named.Apart sheetValue.name) : differential.coefficient.Defined point := by
  rw [differential.coefficient_eq]
  change (Polynomial.Dense.Power.power radicand (differential.denominatorPairs + 1)).eval point ≠ 0
  rw [Polynomial.Dense.Power.eval_power]
  exact Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero (identity.square_coefficient_nonzero apart) _

/-- Cache one original-sheet readback, deriving its domain guard from the retained root evidence. -/
def interpret (differential : OddPowerDifferential radicand) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed) (identity : PowerIdentity sheetValue 2 (radicand.eval point))
    (apart : Named.Apart sheetValue.name) : Expression.Denotation differential.coefficient point sheetValue :=
  Expression.retain differential.coefficient point sheetValue (differential.defined point sheetValue identity apart)
    identity

/-- The existing original reciprocal-power arithmetic agrees with the same cached exact coefficient readback.

The proof retains the selected root and its actual apartness presentation;
no different root or approximate square equation is substituted. -/
def reciprocal_power_equivalent (differential : OddPowerDifferential radicand)
    (point : Data.Gaussian.Basic.Canonical) (sheetValue : Coherent.CoherentNamed)
    (identity : PowerIdentity sheetValue 2 (radicand.eval point)) (apart : Named.Apart sheetValue.name) :
    Approximation.Gaussian.Equivalence.NamedEquivalent
      (differential.value point sheetValue apart).name
      (differential.interpret point sheetValue identity apart).channel.name := by
  have equation : PowerIdentity sheetValue 2 (-(-radicand.eval point)) := by
    rw [neg_neg]
    exact identity
  have nonzero : -(-radicand.eval point) ≠ 0 := by
    rw [neg_neg]
    exact identity.square_coefficient_nonzero apart
  have comparison := Algebra.Quadratic.Pair.Gaussian.reciprocal_odd_power
    (differential.scale * differential.numerator.eval point) sheetValue equation nonzero apart
    differential.denominatorPairs
  have readback : differential.coefficient.evaluate point =
      ⟨0, differential.scale * differential.numerator.eval point /
        (radicand.eval point ^ (differential.denominatorPairs + 1))⟩ := by
    rw [differential.coefficient_eq]
    apply Algebra.Quadratic.Pair.ext
    · change (0 : Coefficients).eval point / _ = 0
      rw [Polynomial.Dense.Basic.DensePolynomial.eval_zero, Algebra.Field.ExplicitField.zero_div]
    · change (differential.numerator.scale differential.scale).eval point /
        (Polynomial.Dense.Power.power radicand (differential.denominatorPairs + 1)).eval point = _
      rw [Polynomial.Dense.Basic.DensePolynomial.eval_scale, Polynomial.Dense.Power.eval_power]
  rw [(differential.interpret point sheetValue identity apart).channel_readback, Expression.denote, readback]
  simpa only [value, denominatorExponent, neg_neg] using comparison

end OddPowerDifferential

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

end

end

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {radicand : Coefficients}

/-- Exact coefficient addition agrees operationally on the same original apart sheet.

All three original differential owners retain their coefficient caches.
Their three admitted readbacks and the same square identity are consumed
once before transporting the original numerical addition. -/
def agrees_add (input first second : OddPowerDifferential radicand)
    (equal : input.coefficient.Equal (first.coefficient.add second.coefficient))
    (point : Data.Gaussian.Basic.Canonical) (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (radicand.eval point)).name) :
    NamedEquivalent (input.value point sheet apart).name
      (CoherentNamed.add (first.value point sheet apart) (second.value point sheet apart)).name := by
  let identity := PowerIdentity.ofSquare square
  let source := input.interpret point sheet identity apart
  let lower := first.interpret point sheet identity apart
  let derivative := second.interpret point sheet identity apart
  have addedDefined := Expression.defined_add first.coefficient second.coefficient
    point lower.defined derivative.defined
  have coefficients := equal.denote_equivalent point sheet source.defined addedDefined
  have addition := Expression.denote_add first.coefficient second.coefficient
    point sheet lower.defined derivative.defined
  have interpreted : NamedEquivalent source.channel.name (CoherentNamed.add lower.channel derivative.channel).name := by
    rewrite [source.channel_readback, lower.channel_readback, derivative.channel_readback]
    exact coefficients.trans addition.symm
  have arithmetic := Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (first.value point sheet apart) lower.channel (second.value point sheet apart) derivative.channel
    (first.reciprocal_power_equivalent point sheet identity apart)
    (second.reciprocal_power_equivalent point sheet identity apart)
  exact (input.reciprocal_power_equivalent point sheet identity apart).trans (interpreted.trans arithmetic.symm)

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

end

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)

variable {radicand : Coefficients}

/-- A zero-pair original differential evaluator agrees with its same original guarded single quotient.

The actual numerator includes the original scale and polynomial reading.
Only the one-power readback and the original guarded quotient/product laws
are used; the coefficient cache, root channel and denominator guard are
unchanged. This operation does not choose a sheet or change the radicand.
-/
def value_zero_pairs (differential : OddPowerDifferential radicand)
    (pairs : differential.denominatorPairs = 0) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed) (apart : Named.Apart sheetValue.name)
    (reading : { value : Data.Gaussian.Basic.Canonical //
      value = differential.scale * differential.numerator.eval point } :=
        ⟨differential.scale * differential.numerator.eval point, rfl⟩) :
    Equivalence.NamedEquivalent (differential.value point sheetValue apart).name
      (CoherentNamed.div (Coherence.exact reading.val)
        sheetValue apart).name := by
  let numerator := Coherence.exact reading.val
  let one := Coherence.exact 1
  let reciprocal := CoherentNamed.div one sheetValue apart
  have exponent : differential.denominatorExponent = 1 := by
    rewrite [denominatorExponent, pairs]
    rfl
  have original := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects numerator numerator
    (Power.namedPower reciprocal 1) reciprocal
    (Equivalence.NamedEquivalent.refl _) (Power.namedPower_one reciprocal)
  have normalized := Cancellation.coherentDiv_mul_left
    numerator one sheetValue apart
  have numeratorOne := Mul.coherentMul_one_right numerator
  have quotient := Name.Coherent.Division.Equivalence.coherentDiv_respects
    (numerator.mul one) numerator sheetValue sheetValue apart apart numeratorOne
    (Equivalence.NamedEquivalent.refl _)
  have sourceEq : (numerator.mul (Power.namedPower reciprocal 1)) =
      differential.value point sheetValue apart := by
    unfold value
    rewrite [exponent]
    dsimp only [numerator]
    rewrite [reading.property]
    rfl
  exact Equivalence.NamedEquivalent.transport (congrArg CoherentNamed.name sourceEq) rfl
    (original.trans (normalized.symm.trans quotient))

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

end

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)

/-- A retained exact scalar numerator produces the complete original differential channel. -/
theorem value_reading {radicand : Coefficients} (differential : OddPowerDifferential radicand)
    (point : Data.Gaussian.Basic.Canonical) (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (reading : { value : Data.Gaussian.Basic.Canonical //
      value = differential.scale * differential.numerator.eval point }) :
    differential.value point sheet apart reading = differential.value point sheet apart := by
  rcases reading with ⟨value, equal⟩
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

end
