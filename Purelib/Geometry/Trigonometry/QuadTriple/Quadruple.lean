module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
-- The deliberate QuadTriple.Basic API already re-exports the numeral owner.
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Quadratic.CommonRoot.Centered
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Trigonometry
open scoped Purelib.Data.Nat

open Purelib.Polynomial.Quadratic.CommonRoot

/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.QuadTriple.Quadruple

variable {K : Type*} [ExplicitField K]

/-- The symmetric polynomial in the Quadruple quad formula. -/
def quadrupleQuadFunction (a b c d : K) : K :=
  ((a + b + c + d) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 -
    64 * a * b * c * d

/-- Theorem 30 (Two quad triples), polynomial clause. -/
theorem two_quad_triples
    (a b c d x : K) (first : Trigonometry.QuadTriple a b x)
    (second : Trigonometry.QuadTriple c d x) :
    quadrupleQuadFunction a b c d = 0 := by
  have compatible : Centered.QuadraticsCompatible (a + b) (4 * a * b)
      (c + d) (4 * c * d) :=
    ⟨x, (QuadTriple.Basic.quadTriple_iff_centered_square a b x).1 first,
      (QuadTriple.Basic.quadTriple_iff_centered_square c d x).1 second⟩
  have compatibilityIdentity :=
    Centered.quadraticCompatibilityIdentity_of_compatible compatible
  unfold Centered.quadraticCompatibilityIdentity at compatibilityIdentity
  unfold quadrupleQuadFunction
  calc
    ((a + b + c + d) ^ 2 -
          2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 -
        64 * a * b * c * d =
      (((a + b - (c + d)) ^ 2 -
          (4 * a * b + 4 * c * d)) ^ 2) -
        4 * (4 * a * b) * (4 * c * d) := by ring1
    _ = 0 := by rw [compatibilityIdentity]; ring1

/-- Theorem 30, common-value clause. Its sole denominator is displayed as a nonzero hypothesis. -/
theorem two_quad_triples_common_value
    (a b c d x : K) (twoNonzero : (2 : K) ≠ 0)
    (centresDistinct : a + b ≠ c + d)
    (first : Trigonometry.QuadTriple a b x) (second : Trigonometry.QuadTriple c d x) :
    x = ((a - b) ^ 2 - (c - d) ^ 2) /
      (2 * (a + b - c - d)) := by
  have differenceNonzero : a + b - c - d ≠ 0 := by
    have centreDifference : a + b - (c + d) ≠ 0 :=
      sub_ne_zero_of_ne centresDistinct
    intro differenceZero
    apply centreDifference
    calc
      a + b - (c + d) = a + b - c - d := by ring1
      _ = 0 := differenceZero
  have denominatorNonzero : (2 : K) * (a + b - c - d) ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero differenceNonzero
  have denominatorCancel :
      (2 * (a + b - c - d)) * (2 * (a + b - c - d))⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  have firstEquation := (QuadTriple.Basic.quadTriple_iff_centered_square a b x).1 first
  have secondEquation := (QuadTriple.Basic.quadTriple_iff_centered_square c d x).1 second
  have cleared :
      2 * (a + b - c - d) * x =
        (a - b) ^ 2 - (c - d) ^ 2 := by
    calc
      2 * (a + b - c - d) * x =
          (a + b) ^ 2 - (c + d) ^ 2 -
            (x - (a + b)) ^ 2 + (x - (c + d)) ^ 2 := by ring1
      _ = (a + b) ^ 2 - (c + d) ^ 2 -
          4 * a * b + 4 * c * d := by rw [firstEquation, secondEquation]
      _ = (a - b) ^ 2 - (c - d) ^ 2 := by ring1
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    x = x * ((2 * (a + b - c - d)) *
        (2 * (a + b - c - d))⁻¹) := by
          rw [denominatorCancel, mul_one]
    _ = (2 * (a + b - c - d) * x) *
        (2 * (a + b - c - d))⁻¹ := by ring1
    _ = ((a - b) ^ 2 - (c - d) ^ 2) *
        (2 * (a + b - c - d))⁻¹ := by rw [cleared]

/-- Theorem 32 (Brahmagupta's identity), as the exact eight-factor polynomial identity in the source. -/
theorem brahmagupta_identity (d₁₂ d₂₃ d₃₄ d₁₄ : K) :
    quadrupleQuadFunction
        (d₁₂ ^ 2) (d₂₃ ^ 2) (d₃₄ ^ 2) (d₁₄ ^ 2) =
      (d₁₂ - d₁₄ + d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ + d₂₃ - d₃₄) *
      (d₁₄ - d₁₂ + d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ - d₂₃ + d₃₄) *
      (d₁₂ + d₁₄ + d₂₃ + d₃₄) *
      (d₁₂ - d₁₄ - d₂₃ + d₃₄) *
      (d₁₂ - d₁₄ + d₂₃ - d₃₄) *
      (d₂₃ - d₁₄ - d₁₂ + d₃₄) := by
  unfold quadrupleQuadFunction
  ring1

end Purelib.Geometry.Trigonometry.QuadTriple.Quadruple

end
