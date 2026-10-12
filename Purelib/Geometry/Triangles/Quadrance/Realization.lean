module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Incidence

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Quadrance.Realization

variable {K : Type*} [ExplicitField K]

/-- A displayed noncollinear triangle with the three prescribed quadrances, using the book's convention `q₁ = Q(A₂,A₃)`,
and cyclically. -/
def HasTriangleQuadrances (q₁ q₂ q₃ : K) : Prop :=
  ∃ first second third : Plane.Point K,
    ¬ Incidence.Collinear first second third ∧
      Quadrance.quadrance second third = q₁ ∧
      Quadrance.quadrance first third = q₂ ∧
      Quadrance.quadrance first second = q₃

section
open _root_.Purelib.Geometry
/-- Construct a noncollinear triangle with prescribed quadrances from a nonzero second quadrance and a nonzero square
root of the quadrea.

The supplied sum-of-two-squares representation determines one side; explicit coordinate quotients determine the
remaining vertex when two is nonzero. -/
private theorem
  construct_triangle_when_q₂_nonzero
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ a b root : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₂Nonzero : q₂ ≠ 0)
    (q₂Squares : a ^ 2 + b ^ 2 = q₂)
    (rootNonzero : root ≠ 0)
    (rootEquation : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = root ^ 2) :
    HasTriangleQuadrances q₁ q₂ q₃ := by
  let r : K := q₁ + q₂ - q₃
  let denominator : K := 2 * q₂
  let xNumerator : K := a * r - b * root
  let yNumerator : K := b * r + a * root
  let first : Plane.Point K := ⟨a, b⟩
  let second : Plane.Point K :=
    ⟨xNumerator / denominator, yNumerator / denominator⟩
  let third : Plane.Point K := ⟨0, 0⟩
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    exact ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have rootSquared : root ^ 2 = 4 * q₁ * q₂ - r ^ 2 := by
    calc
      root ^ 2 = QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := rootEquation.symm
      _ = 4 * q₁ * q₂ - r ^ 2 := by
        unfold QuadTriple.Basic.archimedesFunction r
        ring1
  have numeratorNorm : xNumerator ^ 2 + yNumerator ^ 2 =
      4 * q₁ * q₂ ^ 2 := by
    calc
      xNumerator ^ 2 + yNumerator ^ 2 =
          (a ^ 2 + b ^ 2) * (r ^ 2 + root ^ 2) := by
            unfold xNumerator yNumerator
            ring1
      _ = q₂ * (r ^ 2 + root ^ 2) := by rw [q₂Squares]
      _ = 4 * q₁ * q₂ ^ 2 := by rw [rootSquared]; ring1
  have secondThirdQuadrance : Quadrance.quadrance second third = q₁ := by
    unfold Quadrance.quadrance second third
    simp only [zero_sub]
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (-(xNumerator * denominator⁻¹)) ^ 2 +
          (-(yNumerator * denominator⁻¹)) ^ 2 =
        (xNumerator ^ 2 + yNumerator ^ 2) * denominator⁻¹ ^ 2 := by ring1
      _ = 4 * q₁ * q₂ ^ 2 * denominator⁻¹ ^ 2 := by
        rw [numeratorNorm]
      _ = q₁ * (denominator * denominator⁻¹) ^ 2 := by
        unfold denominator
        ring1
      _ = q₁ := by rw [denominatorCancel]; ring1
  have firstThirdQuadrance : Quadrance.quadrance first third = q₂ := by
    unfold Quadrance.quadrance first third
    simp only [zero_sub]
    calc
      (-a) ^ 2 + (-b) ^ 2 = a ^ 2 + b ^ 2 := by ring1
      _ = q₂ := q₂Squares
  have xDifference :
      xNumerator / denominator - a =
        (xNumerator - a * denominator) * denominator⁻¹ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      xNumerator * denominator⁻¹ - a =
          xNumerator * denominator⁻¹ -
            a * (denominator * denominator⁻¹) := by
              rw [denominatorCancel]
              ring1
      _ = (xNumerator - a * denominator) * denominator⁻¹ := by ring1
  have yDifference :
      yNumerator / denominator - b =
        (yNumerator - b * denominator) * denominator⁻¹ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      yNumerator * denominator⁻¹ - b =
          yNumerator * denominator⁻¹ -
            b * (denominator * denominator⁻¹) := by
              rw [denominatorCancel]
              ring1
      _ = (yNumerator - b * denominator) * denominator⁻¹ := by ring1
  have differenceNumeratorNorm :
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        q₃ * denominator ^ 2 := by
    calc
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        (a ^ 2 + b ^ 2) * ((r - 2 * q₂) ^ 2 + root ^ 2) := by
          unfold xNumerator yNumerator denominator
          ring1
      _ = q₂ * ((r - 2 * q₂) ^ 2 + root ^ 2) := by rw [q₂Squares]
      _ = q₃ * denominator ^ 2 := by
        rw [rootSquared]
        unfold r denominator
        ring1
  have firstSecondQuadrance : Quadrance.quadrance first second = q₃ := by
    unfold Quadrance.quadrance first second
    change
      (xNumerator / denominator - a) ^ 2 +
          (yNumerator / denominator - b) ^ 2 = q₃
    rw [xDifference, yDifference]
    calc
      ((xNumerator - a * denominator) * denominator⁻¹) ^ 2 +
          ((yNumerator - b * denominator) * denominator⁻¹) ^ 2 =
        ((xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2) * denominator⁻¹ ^ 2 := by
            ring1
      _ = q₃ * denominator ^ 2 * denominator⁻¹ ^ 2 := by
        rw [differenceNumeratorNorm]
      _ = q₃ * (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = q₃ := by rw [denominatorCancel]; ring1
  have constructedQuadrea : Quadrea.Basic.quadrea first second third = root ^ 2 := by
    unfold Quadrea.Basic.quadrea
    rw [secondThirdQuadrance, firstThirdQuadrance, firstSecondQuadrance]
    exact rootEquation
  have rootSquareNonzero : root ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero rootNonzero rootNonzero
  have notCollinear : ¬ Incidence.Collinear first second third :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).1
      (by rw [constructedQuadrea]; exact rootSquareNonzero)
  exact ⟨first, second, third, notCollinear,
    secondThirdQuadrance, firstThirdQuadrance, firstSecondQuadrance⟩
end

/-- Theorem 28 (Triangle quadrea), with all constructive witnesses exposed. The disjunction is the finite content of
“not all zero”; each sum-of-squares and square assertion carries its actual witness. -/
theorem triangle_quadrea [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ : K) (twoNonzero : (2 : K) ≠ 0) :
    HasTriangleQuadrances q₁ q₂ q₃ ↔
      (q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0) ∧
      Squares.IsSumOfTwoSquares q₁ ∧ Squares.IsSumOfTwoSquares q₂ ∧
      Squares.IsSumOfTwoSquares q₃ ∧
      Squares.IsNonzeroSquare (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := by
  constructor
  · rintro ⟨first, second, third, notCollinear,
      firstQuadrance, secondQuadrance, thirdQuadrance⟩
    have someNonzero : q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0 := by
      by_cases q₁Nonzero : q₁ ≠ 0
      · exact Or.inl q₁Nonzero
      · by_cases q₂Nonzero : q₂ ≠ 0
        · exact Or.inr (Or.inl q₂Nonzero)
        · right
          right
          intro q₃Zero
          apply notCollinear
          apply (Quadrea.Basic.triple_quad_formula first second third twoNonzero).1
          rw [firstQuadrance, secondQuadrance, thirdQuadrance]
          have q₁Zero : q₁ = 0 := by
            by_cases equality : q₁ = 0
            · exact equality
            · exact False.elim (q₁Nonzero equality)
          have q₂Zero : q₂ = 0 := by
            by_cases equality : q₂ = 0
            · exact equality
            · exact False.elim (q₂Nonzero equality)
          rw [q₁Zero, q₂Zero, q₃Zero]
          unfold QuadTriple.Basic.archimedesFunction
          ring1
    have q₁Squares : Squares.IsSumOfTwoSquares q₁ := by
      refine ⟨third.x - second.x, third.y - second.y, ?_⟩
      exact firstQuadrance
    have q₂Squares : Squares.IsSumOfTwoSquares q₂ := by
      refine ⟨third.x - first.x, third.y - first.y, ?_⟩
      exact secondQuadrance
    have q₃Squares : Squares.IsSumOfTwoSquares q₃ := by
      refine ⟨second.x - first.x, second.y - first.y, ?_⟩
      exact thirdQuadrance
    have determinantNonzero : Incidence.pointDeterminant first second third ≠ 0 := by
      intro determinantZero
      exact notCollinear
        ((Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
          determinantZero)
    have twiceDeterminantNonzero :
        (2 : K) * Incidence.pointDeterminant first second third ≠ 0 :=
      ExplicitField.mul_ne_zero twoNonzero determinantNonzero
    have quadreaSquare : Squares.IsNonzeroSquare
        (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := by
      refine ⟨2 * Incidence.pointDeterminant first second third,
        twiceDeterminantNonzero, ?_⟩
      calc
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ =
            Quadrea.Basic.quadrea first second third := by
              unfold Quadrea.Basic.quadrea
              rw [firstQuadrance, secondQuadrance, thirdQuadrance]
        _ = 4 * Incidence.pointDeterminant first second third ^ 2 :=
          Quadrea.Basic.quadrea_coordinate_formula first second third
        _ = (2 * Incidence.pointDeterminant first second third) ^ 2 := by ring1
    exact ⟨someNonzero, q₁Squares, q₂Squares, q₃Squares,
      quadreaSquare⟩
  · rintro ⟨someNonzero, q₁Squares, q₂Squares, q₃Squares,
      root, rootNonzero, rootEquation⟩
    rcases q₁Squares with ⟨a₁, b₁, q₁Equation⟩
    rcases q₂Squares with ⟨a₂, b₂, q₂Equation⟩
    rcases q₃Squares with ⟨a₃, b₃, q₃Equation⟩
    rcases someNonzero with q₁Nonzero | q₂Nonzero | q₃Nonzero
    · have permutedRoot :
          QuadTriple.Basic.archimedesFunction q₂ q₁ q₃ = root ^ 2 := by
        calc
          QuadTriple.Basic.archimedesFunction q₂ q₁ q₃ =
              QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
                unfold QuadTriple.Basic.archimedesFunction
                ring1
          _ = root ^ 2 := rootEquation
      rcases construct_triangle_when_q₂_nonzero
        q₂ q₁ q₃ a₁ b₁ root twoNonzero q₁Nonzero
        q₁Equation rootNonzero permutedRoot with
        ⟨first, second, third, notCollinear,
          firstQuadrance, secondQuadrance, thirdQuadrance⟩
      exact ⟨second, first, third,
        Purelib.Geometry.Plane.Line.Incidence.not_collinear_swap_first_second notCollinear,
        secondQuadrance, firstQuadrance,
        (Quadrance.quadrance_symm second first).trans thirdQuadrance⟩
    · exact construct_triangle_when_q₂_nonzero
        q₁ q₂ q₃ a₂ b₂ root twoNonzero q₂Nonzero
        q₂Equation rootNonzero rootEquation
    · have permutedRoot :
          QuadTriple.Basic.archimedesFunction q₁ q₃ q₂ = root ^ 2 := by
        calc
          QuadTriple.Basic.archimedesFunction q₁ q₃ q₂ =
              QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
                unfold QuadTriple.Basic.archimedesFunction
                ring1
          _ = root ^ 2 := rootEquation
      rcases construct_triangle_when_q₂_nonzero
        q₁ q₃ q₂ a₃ b₃ root twoNonzero q₃Nonzero
        q₃Equation rootNonzero permutedRoot with
        ⟨first, second, third, notCollinear,
          firstQuadrance, secondQuadrance, thirdQuadrance⟩
      exact ⟨first, third, second,
        Purelib.Geometry.Plane.Line.Incidence.not_collinear_swap_second_third notCollinear,
        (Quadrance.quadrance_symm third second).trans firstQuadrance,
        thirdQuadrance, secondQuadrance⟩
end Purelib.Geometry.Triangles.Quadrance.Realization

end
