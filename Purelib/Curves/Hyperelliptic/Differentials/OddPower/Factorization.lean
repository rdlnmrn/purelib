module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Approximation.Gaussian.Division.Prepared.ExactFactor
import Purelib.Approximation.Gaussian.Name.Coherent.Power.Composition
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Odd-power pullbacks through an exact sheet factor

An original sheet channel factored as a retained apart source times an exact
nonzero factor has a corresponding odd-power pullback. One exact sheet factor
in the tangent cancels one reciprocal factor. The remaining finite powers use
the same source reciprocal and exact scalar factor; the comparison preserves
the original sheet, its actual denominator preparation and both process trees.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

/-- Construct the factored pullback from the original numerator, source reciprocal and remaining exact factor powers. -/
@[expose] def factorizedValue (differential : OddPowerDifferential radicand) (point : Canonical)
    (source : CoherentNamed) (apart : Named.Apart source.name) (factor velocity : Canonical) : CoherentNamed :=
  let reciprocal := (Coherence.exact 1).div source apart
  let coefficient := differential.scale * differential.numerator.eval point * velocity *
    factor⁻¹ ^ (2 * differential.denominatorPairs)
  (Coherence.exact coefficient).mul (Power.namedPower reciprocal differential.denominatorExponent)

/-- One nonzero exact factor cancels one factor of the original odd reciprocal power. -/
theorem scalar_factor_cancellation (numerator factor velocity : Canonical) (pairs : Nat)
    (nonzero : factor ≠ 0) :
    (numerator * factor⁻¹ ^ (2 * pairs + 1)) * (factor * velocity) =
      numerator * velocity * factor⁻¹ ^ (2 * pairs) := by
  have unit : factor * factor⁻¹ = 1 := by
    rewrite [Field.inv_eq]
    exact Field.mul_inv factor nonzero
  have cancel : factor * factor⁻¹ ^ (2 * pairs + 1) = factor⁻¹ ^ (2 * pairs) := by
    rewrite [pow_succ]
    calc
      _ = (factor * factor⁻¹) * factor⁻¹ ^ (2 * pairs) := by ring1
      _ = _ := by rewrite [unit, Basic.one_mul]; rfl
  calc
    _ = (numerator * velocity) * (factor * factor⁻¹ ^ (2 * pairs + 1)) := by ring1
    _ = _ := by rewrite [cancel]; rfl

/-- The ordinary differential on the prepared sheet, times its factored tangent, agrees with the constructed pullback.

The original sheet's complete product identity and its supplied denominator
preparation remain inputs. General reciprocal, power and product comparisons
derive the agreement; no original arithmetic reading is replaced by a scalar
reciprocal-power reading.
-/
def value_factorized (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet source : CoherentNamed) (prepared : Division.Prepared sheet)
    (factor velocity : Canonical) (retained : sheet = source.mul (Coherence.exact factor))
    (nonzero : factor ≠ 0) (apart : Named.Apart source.name) :
    NamedEquivalent ((differential.value point prepared.denominator prepared.apart).mul
      (Coherence.exact (factor * velocity))).name
      (differential.factorizedValue point source apart factor velocity).name := by
  let numerator := differential.scale * differential.numerator.eval point
  let top := Coherence.exact numerator
  let reciprocal := (Coherence.exact 1).div source apart
  let actualReciprocal := prepared.quotient (Coherence.exact 1)
  let inverseFactor := Coherence.exact factor⁻¹
  let rootPower := Power.namedPower reciprocal differential.denominatorExponent
  let factorPower := Coherence.exact (factor⁻¹ ^ differential.denominatorExponent)
  let tangent := Coherence.exact (factor * velocity)
  have reciprocalAgreement : NamedEquivalent actualReciprocal.name (reciprocal.mul inverseFactor).name :=
    prepared.reciprocal_exactRight source factor retained nonzero apart
  have powerAgreement : NamedEquivalent (Power.namedPower actualReciprocal differential.denominatorExponent).name
      (factorPower.mul rootPower).name :=
    (Power.namedPower_respects actualReciprocal (reciprocal.mul inverseFactor)
      reciprocalAgreement differential.denominatorExponent).trans
      ((Power.namedPower_product reciprocal inverseFactor differential.denominatorExponent).trans
        ((Product.Congruence.coherentMul_respects rootPower rootPower
          (Power.namedPower inverseFactor differential.denominatorExponent) factorPower
          (NamedEquivalent.refl _) (Power.namedPower_exact factor⁻¹ differential.denominatorExponent)).trans
            (Product.Laws.coherentMul_comm rootPower factorPower)))
  have replacePower : NamedEquivalent
      ((differential.value point prepared.denominator prepared.apart).mul tangent).name
      ((top.mul (factorPower.mul rootPower)).mul tangent).name :=
    Product.Congruence.coherentMul_respects
      (top.mul (Power.namedPower actualReciprocal differential.denominatorExponent))
      (top.mul (factorPower.mul rootPower)) tangent tangent
      (Product.Congruence.coherentMul_respects top top
        (Power.namedPower actualReciprocal differential.denominatorExponent) (factorPower.mul rootPower)
        (NamedEquivalent.refl _) powerAgreement) (NamedEquivalent.refl _)
  have regroup : NamedEquivalent ((top.mul (factorPower.mul rootPower)).mul tangent).name
      (((top.mul factorPower).mul tangent).mul rootPower).name :=
    (Product.Congruence.coherentMul_respects (top.mul (factorPower.mul rootPower))
      ((top.mul factorPower).mul rootPower) tangent tangent
      (Product.Laws.coherentMul_assoc top factorPower rootPower).symm (NamedEquivalent.refl _)).trans
      ((Product.Laws.coherentMul_assoc (top.mul factorPower) rootPower tangent).trans
        ((Product.Congruence.coherentMul_respects (top.mul factorPower) (top.mul factorPower)
          (rootPower.mul tangent) (tangent.mul rootPower) (NamedEquivalent.refl _)
          (Product.Laws.coherentMul_comm rootPower tangent)).trans
            (Product.Laws.coherentMul_assoc (top.mul factorPower) tangent rootPower).symm))
  have exactCoefficient : NamedEquivalent ((top.mul factorPower).mul tangent).name
      (Coherence.exact ((numerator * factor⁻¹ ^ differential.denominatorExponent) * (factor * velocity))).name :=
    (Product.Congruence.coherentMul_respects (top.mul factorPower)
      (Coherence.exact (numerator * factor⁻¹ ^ differential.denominatorExponent)) tangent tangent
      (Name.Coherent.Exact.Arithmetic.exact_mul numerator (factor⁻¹ ^ differential.denominatorExponent))
      (NamedEquivalent.refl _)).trans
        (Name.Coherent.Exact.Arithmetic.exact_mul _ _)
  have cancelled : NamedEquivalent ((top.mul factorPower).mul tangent).name
      (Coherence.exact (numerator * velocity * factor⁻¹ ^ (2 * differential.denominatorPairs))).name :=
    NamedEquivalent.transport rfl
      (congrArg (fun value : Canonical => (Coherence.exact value).name)
        (scalar_factor_cancellation numerator factor velocity differential.denominatorPairs nonzero))
      exactCoefficient
  exact replacePower.trans (regroup.trans
    (Product.Congruence.coherentMul_respects ((top.mul factorPower).mul tangent)
      (Coherence.exact (numerator * velocity * factor⁻¹ ^ (2 * differential.denominatorPairs)))
      rootPower rootPower cancelled (NamedEquivalent.refl _)))

/-- The original factored coefficient at scalar factor⁻¹ retains the complete odd reciprocal factor exponent.

This scalar specialization concerns the original numerator, scale and odd
power. Its reciprocal factor is coefficient arithmetic; it asserts no chart
velocity or derivative identity.
-/
theorem factorized_inverse_coefficient (differential : OddPowerDifferential radicand) (point factor : Canonical) :
    differential.scale * differential.numerator.eval point * factor⁻¹ * factor⁻¹ ^
        (2 * differential.denominatorPairs) =
      differential.scale * differential.numerator.eval point * factor⁻¹ ^ differential.denominatorExponent := by
  unfold denominatorExponent
  rewrite [pow_succ]
  ring1

/-- The actual original primitive evaluator agrees with its uncancelled exact-factor coefficient specialization.

The original prepared full-sheet evaluator and original cofactor reciprocal
remain distinct retained process trees. The existing factorization comparison
uses factor·factor⁻¹=1; the original multiplication-by-one comparison removes
that exact unit without changing either actual arithmetic owner.
-/
def value_factorized_inverse (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet source : CoherentNamed) (prepared : Division.Prepared sheet) (factor : Canonical)
    (retained : sheet = source.mul (Coherence.exact factor)) (nonzero : factor ≠ 0)
    (apart : Named.Apart source.name) :
    NamedEquivalent (differential.value point prepared.denominator prepared.apart).name
      (differential.factorizedValue point source apart factor factor⁻¹).name := by
  have unit : factor * factor⁻¹ = 1 := by
    rewrite [Field.inv_eq]
    exact Field.mul_inv factor nonzero
  have compared := differential.value_factorized point sheet source prepared factor factor⁻¹ retained nonzero apart
  have exactUnit := congrArg
    (fun scalar : Canonical =>
      ((differential.value point prepared.denominator prepared.apart).mul (Coherence.exact scalar)).name) unit
  exact (Arithmetic.Mul.coherentMul_one_right
    (differential.value point prepared.denominator prepared.apart)).symm.trans
      (NamedEquivalent.transport exactUnit rfl compared)

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential
