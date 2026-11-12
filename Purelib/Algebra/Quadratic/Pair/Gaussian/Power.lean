module

public import Purelib.Algebra.Quadratic.Pair.Gaussian
public import Purelib.Algebra.Quadratic.Pair.Norm
import Purelib.Algebra.Quadratic.Pair.Gaussian.Norm
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Tactic.Ring

/-!
# Finite powers at the original quadratic generator

Interpret finite powers in the existing pair ring at the retained generator.
The comparison uses its original square equation and the same coefficient
map at every multiplication; no injectivity or nonsquareness is required.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

variable {K : Type} {parameter : K}

open Purelib.Algebra.Field (ExplicitField)

/-- The existing norm inverse of the generator has zero scalar coordinate
and reciprocal radicand as its generator coefficient. -/
theorem generator_inverse_coordinates [ExplicitField K] :
    (Pair.generator : Pair K parameter).inverse = ⟨0, (-parameter)⁻¹⟩ := by
  apply Pair.ext
  · change (0 * 0 + parameter * 1 * 1)⁻¹ * 0 = 0
    exact mul_zero _
  · change (0 * 0 + parameter * 1 * 1)⁻¹ * -1 = (-parameter)⁻¹
    rw [zero_mul, mul_one, mul_one, zero_add, ExplicitField.inv_neg]
    ring1

/-- The square of the retained generator inverse reduces to the reciprocal
radicand using its original nonzero-domain guard. -/
theorem generator_inverse_square [ExplicitField K] (nonzero : -parameter ≠ 0) :
    (Pair.generator : Pair K parameter).inverse ^ 2 = Pair.scalar (-parameter)⁻¹ := by
  rw [generator_inverse_coordinates, pow_two]
  apply Pair.ext
  · change 0 * 0 - parameter * (-parameter)⁻¹ * (-parameter)⁻¹ = (-parameter)⁻¹
    calc
      _ = ((-parameter) * (-parameter)⁻¹) * (-parameter)⁻¹ := by ring1
      _ = (-parameter)⁻¹ := by rw [ExplicitField.mul_inv_cancel (-parameter) nonzero, one_mul]
  · change 0 * (-parameter)⁻¹ + (-parameter)⁻¹ * 0 = 0
    ring1

/-- Every original odd inverse-generator power reduces to one generator
coefficient and the retained power of the radicand denominator. -/
theorem generator_inverse_odd_power [ExplicitField K] (nonzero : -parameter ≠ 0) (pairs : Nat) :
    (Pair.generator : Pair K parameter).inverse ^ (2 * pairs + 1) =
      ⟨0, ((-parameter) ^ (pairs + 1))⁻¹⟩ := by
  rw [pow_add, pow_mul, pow_one, generator_inverse_square nonzero, ← Pair.scalar_pow,
    generator_inverse_coordinates]
  apply Pair.ext
  · change ((-parameter)⁻¹ ^ pairs) * 0 - parameter * 0 * (-parameter)⁻¹ = 0
    ring1
  · change ((-parameter)⁻¹ ^ pairs) * (-parameter)⁻¹ + 0 * 0 = ((-parameter) ^ (pairs + 1))⁻¹
    rw [zero_mul, add_zero, ← pow_succ, ExplicitField.inverse_pow_nonzero nonzero]

/-- Actual division by the original apart generator agrees with its existing
pair inverse. Only its radicand guard is used, including for split radicands. -/
def generator_reciprocal {parameter : Canonical} (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (-parameter)) (nonzero : -parameter ≠ 0)
    (apart : Purelib.Approximation.Gaussian.Name.Basic.Named.Apart generator.name) :
    NamedEquivalent (CoherentNamed.div (Coherence.exact 1) generator apart).name
      (denote id generator (Pair.generator : Pair Canonical parameter).inverse).name := by
  let value : Pair Canonical parameter := Pair.generator
  let inverse := denote id generator value.inverse
  have normNonzero : value.norm ≠ 0 := by
    change 0 * 0 + parameter * 1 * 1 ≠ 0
    rw [zero_mul, mul_one, mul_one, zero_add]
    intro vanishes
    apply nonzero
    rw [vanishes, neg_zero]
  have pairUnit := denote_inverse id rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) generator identity value normNonzero
  have originalUnit : NamedEquivalent (CoherentNamed.mul generator inverse).name (Coherence.exact 1).name :=
    NamedEquivalent.trans
      (Arithmetic.Product.Congruence.coherentMul_respects generator (denote id generator value)
        inverse inverse
        (NamedEquivalent.symm (denote_generator id rfl rfl generator)) (NamedEquivalent.refl _)) pairUnit
  let prepared : Purelib.Approximation.Gaussian.Division.Prepared generator :=
    ⟨generator, apart, NamedEquivalent.refl _⟩
  exact prepared.reciprocal_equivalent_of_product inverse originalUnit

/-- A finite power of the original interpreted pair compares to the
interpretation of the same finite pair power. -/
def denote_power [CommRing K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (one_eq : coefficient 1 = 1)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (value : Pair K parameter) : (exponent : Nat) →
    NamedEquivalent (Power.namedPower (denote coefficient generator value) exponent).name
      (denote coefficient generator (value ^ exponent)).name
  | 0 => by
      rw [pow_zero]
      have unit := denote_scalar (parameter := parameter) coefficient zero_eq generator (1 : K)
      rw [one_eq] at unit
      exact NamedEquivalent.symm unit
  | exponent + 1 => by
      rw [pow_succ]
      exact NamedEquivalent.trans
        (Arithmetic.Product.Congruence.coherentMul_respects
          (Power.namedPower (denote coefficient generator value) exponent)
          (denote coefficient generator (value ^ exponent))
          (denote coefficient generator value) (denote coefficient generator value)
          (denote_power coefficient zero_eq one_eq add_eq mul_eq sub_eq generator identity value exponent)
          (NamedEquivalent.refl _))
        (denote_mul coefficient add_eq mul_eq sub_eq generator identity (value ^ exponent) value)

/-- The actual original odd reciprocal-power channel realizes its single
reduced generator coefficient with the same retained radicand denominator. -/
def reciprocal_odd_power {parameter : Canonical} (coefficient : Canonical) (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (-parameter)) (nonzero : -parameter ≠ 0)
    (apart : Purelib.Approximation.Gaussian.Name.Basic.Named.Apart generator.name) (pairs : Nat) :
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact coefficient)
        (Power.namedPower (CoherentNamed.div (Coherence.exact 1) generator apart) (2 * pairs + 1))).name
      (denote id generator (⟨0, coefficient / ((-parameter) ^ (pairs + 1))⟩ : Pair Canonical parameter)).name := by
  let value : Pair Canonical parameter := Pair.generator
  let reciprocal := CoherentNamed.div (Coherence.exact 1) generator apart
  have originalReciprocal := generator_reciprocal generator identity nonzero apart
  have powers := NamedEquivalent.trans
    (Power.namedPower_respects reciprocal (denote id generator value.inverse) originalReciprocal (2 * pairs + 1))
    (denote_power id rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      generator identity value.inverse (2 * pairs + 1))
  have combine := NamedEquivalent.trans
    (Arithmetic.Product.Congruence.coherentMul_respects
      (Coherence.exact coefficient) (denote id generator (Pair.scalar coefficient : Pair Canonical parameter))
      (Power.namedPower reciprocal (2 * pairs + 1)) (denote id generator (value.inverse ^ (2 * pairs + 1)))
      (NamedEquivalent.symm (denote_scalar id rfl generator coefficient)) powers)
    (denote_mul id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) generator identity
      (Pair.scalar coefficient) (value.inverse ^ (2 * pairs + 1)))
  have reduced : (Pair.scalar coefficient : Pair Canonical parameter) * value.inverse ^ (2 * pairs + 1) =
      ⟨0, coefficient / ((-parameter) ^ (pairs + 1))⟩ := by
    rw [generator_inverse_odd_power nonzero pairs]
    apply Pair.ext
    · change coefficient * 0 - parameter * 0 * ((-parameter) ^ (pairs + 1))⁻¹ = 0
      ring1
    · change coefficient * ((-parameter) ^ (pairs + 1))⁻¹ + 0 * 0 =
        coefficient / ((-parameter) ^ (pairs + 1))
      rw [ExplicitField.div_eq_mul_inv]
      ring1
  rw [reduced] at combine
  exact combine

end Purelib.Algebra.Quadratic.Pair.Gaussian
