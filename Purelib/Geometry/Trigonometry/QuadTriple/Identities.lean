module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Polynomial.Quadratic.CommonRoot.Centered
import Mathlib.Algebra.Group.Basic
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

open Purelib.LinearAlgebra

open Purelib.Polynomial.Quadratic.CommonRoot

/-!
# Divine Proportions, Chapter 5 quad-triple exercises

The exercises below are direct finite polynomial consequences of
Archimedes' function.  Exercise 5.11 exposes the same distinct-centre premise
missing from the source's earlier quadratic-compatibility claim; no root is
selected in the degenerate case.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.QuadTriple.Identities

variable {K : Type*} [ExplicitField K]

/-- The two-by-two determinant displayed in Exercise 5.7. -/
def archimedesDeterminantTwo (a b c : K) : K :=
  2 * a * (2 * b) - (a + b - c) * (a + b - c)

/-- The determinant of the exact symmetric four-by-four matrix printed in Exercise 5.7, expanded along its first row. -/
def archimedesDeterminantFour (a b c : K) : K :=
  -a * Coordinates3.Matrix.scalarDeterminantThree a c 1 b 0 1 1 1 0 +
    b * Coordinates3.Matrix.scalarDeterminantThree a 0 1 b c 1 1 1 0 -
    Coordinates3.Matrix.scalarDeterminantThree a 0 c b c 0 1 1 1

/-- Exercise 5.7: all five displayed forms of Archimedes' function, including both literal finite determinants. -/
theorem exercise_5_7 (a b c : K) :
    QuadTriple.Basic.archimedesFunction a b c = 4 * a * b - (a + b - c) ^ 2 ∧
      QuadTriple.Basic.archimedesFunction a b c =
        2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2) ∧
      QuadTriple.Basic.archimedesFunction a b c =
        4 * (a * b + b * c + c * a) - (a + b + c) ^ 2 ∧
      QuadTriple.Basic.archimedesFunction a b c = archimedesDeterminantTwo a b c ∧
      QuadTriple.Basic.archimedesFunction a b c = -archimedesDeterminantFour
        a b c := by
  unfold QuadTriple.Basic.archimedesFunction archimedesDeterminantTwo
    archimedesDeterminantFour Coordinates3.Matrix.scalarDeterminantThree
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Exercise 5.8: every one of the four relations `a ± b = ±c` makes the three squares a quad triple. -/
theorem exercise_5_8 (a b c : K)
    (signedRelation :
      a + b = c ∨ a - b = c ∨ a + b = -c ∨ a - b = -c) :
    Trigonometry.QuadTriple (a ^ 2) (b ^ 2) (c ^ 2) := by
  unfold Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction
  rcases signedRelation with sumEquals | differenceEquals |
      sumEqualsNegative | differenceEqualsNegative
  · rw [← sumEquals]
    ring1
  · rw [← differenceEquals]
    ring1
  · have cValue : c = -(a + b) := by
      calc
        c = -(-c) := by ring1
        _ = -(a + b) := by rw [sumEqualsNegative]
    rw [cValue]
    ring1
  · have cValue : c = -(a - b) := by
      calc
        c = -(-c) := by ring1
        _ = -(a - b) := by rw [differenceEqualsNegative]
    rw [cValue]
    ring1

/-- Exercise 5.10: Archimedes' relation written as the displayed quadratic equation in its third entry. -/
theorem exercise_5_10 (q₁ q₂ q₃ : K) :
    Trigonometry.QuadTriple q₁ q₂ q₃ ↔
      q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2 = 0 := by
  unfold Trigonometry.QuadTriple
  constructor
  · intro triple
    calc
      q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2 =
          -QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  · intro quadratic
    calc
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ =
          -(q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2) := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
      _ = 0 := by rw [quadratic]; ring1

/-- Exercise 5.11, with the necessary distinct-centre premise made explicit: the two displayed quadratic equations have
a common solution exactly when their two right sides and squared centre separation form a quad triple. -/
theorem exercise_5_11
    (p₁ q₁ p₂ q₂ : K)
    (twoNonzero : (2 : K) ≠ 0) (centresDistinct : p₁ ≠ p₂) :
    Centered.QuadraticsCompatible p₁ q₁ p₂ q₂ ↔
      Trigonometry.QuadTriple q₁ q₂ ((p₁ - p₂) ^ 2) := by
  apply Iff.trans (Centered.quadraticCompatibility_of_distinct_centres
    twoNonzero centresDistinct)
  unfold Centered.quadraticCompatibilityIdentity
  exact (QuadTriple.Basic.quadTriple_iff_centered_square q₁ q₂ ((p₁ - p₂) ^ 2)).symm

/-- Exercise 5.14: the cyclic linear-factor expansion of the quadrea. -/
theorem exercise_5_14 (q₁ q₂ q₃ : K) :
    QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ =
      q₁ * (q₂ + q₃ - q₁) +
        q₂ * (q₃ + q₁ - q₂) +
        q₃ * (q₁ + q₂ - q₃) := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Exercise 5.15: the three-product expansion of the quadrea. -/
theorem exercise_5_15 (q₁ q₂ q₃ : K) :
    QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ =
      (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) +
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) +
        (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Exercise 5.18: two quad triples `{a,b,x}` and `{b,c,x}` with distinct outer entries determine their common value as
`(a+c-2b)/2`. -/
theorem exercise_5_18 [DecidableEq K]
    (a b c x : K) (twoNonzero : (2 : K) ≠ 0)
    (outerDistinct : a ≠ c)
    (firstTriple : Trigonometry.QuadTriple a b x)
    (secondTriple : Trigonometry.QuadTriple b c x) :
    x = (a + c - 2 * b) / 2 := by
  have differenceNonzero : a - c ≠ 0 := by
    intro differenceZero
    apply outerDistinct
    calc
      a = (a - c) + c := by ring1
      _ = c := by rw [differenceZero]; ring1
  have productZero :
      (a - c) * (2 * x - (a + c - 2 * b)) = 0 := by
    unfold Trigonometry.QuadTriple at firstTriple secondTriple
    calc
      (a - c) * (2 * x - (a + c - 2 * b)) =
          QuadTriple.Basic.archimedesFunction a b x -
            QuadTriple.Basic.archimedesFunction b c x := by
              unfold QuadTriple.Basic.archimedesFunction
              ring1
      _ = 0 := by rw [firstTriple, secondTriple]; ring1
  have cleared : 2 * x = a + c - 2 * b := by
    have secondFactorZero : 2 * x - (a + c - 2 * b) = 0 := by
      by_cases factorZero : 2 * x - (a + c - 2 * b) = 0
      · exact factorZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero differenceNonzero factorZero)
            productZero)
    calc
      2 * x = (2 * x - (a + c - 2 * b)) + (a + c - 2 * b) := by ring1
      _ = a + c - 2 * b := by rw [secondFactorZero]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    x = x * (2 * (2 : K)⁻¹) := by rw [twoCancel, mul_one]
    _ = (2 * x) * (2 : K)⁻¹ := by ring1
    _ = (a + c - 2 * b) * (2 : K)⁻¹ := by rw [cleared]

end Purelib.Geometry.Trigonometry.QuadTriple.Identities

end
