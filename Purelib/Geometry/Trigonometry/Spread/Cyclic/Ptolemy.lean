module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.Geometry.Trigonometry.Spread.Cyclic.Basic
import Purelib.Geometry.Trigonometry.Spread.Cyclic.Diagonals
public import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 114: Ptolemy's theorem

The source proves its rational-trigonometric Ptolemy theorem by substituting
the two diagonal-spread quotients from Theorem 110 and factoring the resulting
Archimedes polynomial.  Here the same calculation is kept finite and
constructive: `ptolemy_cleared_factorization` is the denominator-cleared
polynomial identity, and `ptolemy` cancels only the two explicitly certified
nonzero denominators.
-/

section

variable {K : Type*} [ExplicitField K]

section

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

/-- Numerator of the first diagonal-spread quotient in Theorem 110. -/
def ptolemyFirstDiagonalNumerator (a b c d : K) : K :=
  (a - b) ^ 2 - (d - c) ^ 2

/-- Denominator of the first diagonal-spread quotient in Theorem 110. -/
def ptolemyFirstDiagonalDenominator (a b c d : K) : K :=
  2 * (a + b - d - c - 2 * a * b + 2 * d * c)

/-- Numerator of the second diagonal-spread quotient in Theorem 110. -/
def ptolemySecondDiagonalNumerator (a b c d : K) : K :=
  (a - d) ^ 2 - (b - c) ^ 2

/-- Denominator of the second diagonal-spread quotient in Theorem 110. -/
def ptolemySecondDiagonalDenominator (a b c d : K) : K :=
  2 * (a + d - b - c - 2 * a * d + 2 * b * c)

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

namespace Purelib.Geometry.Trigonometry.Spread.Cyclic.Basic.Quadrilateral.CyclicSubtendedSpreads

/-- The two denominators whose nonvanishing is the book's definition of a solvable cyclic quadrilateral. -/
def IsSolvable
    (spreads : Quadrilateral.CyclicSubtendedSpreads K) : Prop :=
  Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral.ptolemyFirstDiagonalDenominator spreads.r₁₂ spreads.r₂₃
      spreads.r₃₄ spreads.r₁₄ ≠ 0 ∧
    Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral.ptolemySecondDiagonalDenominator spreads.r₁₂ spreads.r₂₃
      spreads.r₃₄ spreads.r₁₄ ≠ 0

end Purelib.Geometry.Trigonometry.Spread.Cyclic.Basic.Quadrilateral.CyclicSubtendedSpreads

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

/-- The auxiliary polynomial `B` displayed in the source's computer-assisted factorization proof. -/
def ptolemyAuxiliaryFunction (a b c d : K) : K :=
  4 * (a + c - b - d) *
      ((a - c) ^ 2 * (b + d) * (b + d - 1) -
        (b - d) ^ 2 * (a + c) * (a + c - 1)) -
    Quadruple.quadrupleSpreadFunction a b c d

/-- Archimedes' polynomial after both diagonal-spread quotients have been cleared. Its third input is represented by the
product of their numerators, and the first two inputs are scaled by the product of their denominators. -/
def ptolemyClearedArchimedes (a b c d : K) : K :=
  let denominator :=
    ptolemyFirstDiagonalDenominator a b c d *
      ptolemySecondDiagonalDenominator a b c d
  let diagonalProductNumerator :=
    ptolemyFirstDiagonalNumerator a b c d *
      ptolemySecondDiagonalNumerator a b c d
  (a * c * denominator + d * b * denominator +
      diagonalProductNumerator) ^ 2 -
    2 * ((a * c * denominator) ^ 2 + (d * b * denominator) ^ 2 +
      diagonalProductNumerator ^ 2)

/-- The Ptolemy factorization in opposite-side sums and products.

The four retained scalars keep the final elimination at degree eight instead of expanding all side variables.
-/
private theorem ptolemy_factorization_symmetric
    (s t x y : K) :
    let denominator := 4 * ((s - t) * (s + t - 2 * s * t) -
      4 * x * (1 - t) ^ 2 + 4 * y * (1 - s) ^ 2)
    let numerator := (s - t) ^ 2 * (s ^ 2 - t ^ 2 - 4 * x + 4 * y)
    let core := -(s - t) ^ 2 + 4 * x * (1 - t) + 4 * y * (1 - s) + 8 * x * y
    let quadruple := core ^ 2 - 64 * x * y * (1 - s + x) * (1 - t + y)
    (x * denominator + y * denominator + numerator) ^ 2 -
      2 * ((x * denominator) ^ 2 + (y * denominator) ^ 2 + numerator ^ 2) =
      quadruple * (4 * (s - t) *
        (s * t * (t - s) - 4 * x * t * (t - 1) + 4 * y * s * (s - 1)) - quadruple) := by
  dsimp only
  ring1

/-- The denominator-cleared factorization used in the proof of Theorem 114. It is a universal polynomial identity, so it
has no solvability hypothesis. -/
theorem ptolemy_cleared_factorization (a b c d : K) :
    ptolemyClearedArchimedes a b c d =
      Quadruple.quadrupleSpreadFunction a b c d *
        ptolemyAuxiliaryFunction a b c d := by
  let s := a + c
  let t := b + d
  let x := a * c
  let y := b * d
  let denominator := 4 * ((s - t) * (s + t - 2 * s * t) -
    4 * x * (1 - t) ^ 2 + 4 * y * (1 - s) ^ 2)
  let numerator := (s - t) ^ 2 * (s ^ 2 - t ^ 2 - 4 * x + 4 * y)
  let core := -(s - t) ^ 2 + 4 * x * (1 - t) + 4 * y * (1 - s) + 8 * x * y
  let quadruple := core ^ 2 - 64 * x * y * (1 - s + x) * (1 - t + y)
  have denominatorEq :
      Quadrilateral.ptolemyFirstDiagonalDenominator a b c d *
        Quadrilateral.ptolemySecondDiagonalDenominator a b c d = denominator := by
    dsimp only [Quadrilateral.ptolemyFirstDiagonalDenominator,
      Quadrilateral.ptolemySecondDiagonalDenominator, denominator, s, t, x, y]
    ring1
  have numeratorEq :
      Quadrilateral.ptolemyFirstDiagonalNumerator a b c d *
        Quadrilateral.ptolemySecondDiagonalNumerator a b c d = numerator := by
    dsimp only [Quadrilateral.ptolemyFirstDiagonalNumerator,
      Quadrilateral.ptolemySecondDiagonalNumerator, numerator, s, t, x, y]
    ring1
  have coreEq : Quadruple.quadrupleSpreadCore a b c d = core := by
    dsimp only [Quadruple.quadrupleSpreadCore, core, s, t, x, y]
    ring1
  have complementsEq : 64 * a * b * c * d * (1 - a) * (1 - b) * (1 - c) * (1 - d) =
      64 * x * y * (1 - s + x) * (1 - t + y) := by
    dsimp only [s, t, x, y]
    ring1
  have quadrupleEq : Quadruple.quadrupleSpreadFunction a b c d = quadruple := by
    unfold Quadruple.quadrupleSpreadFunction
    rw [coreEq, complementsEq]
  have auxiliaryEq : Quadrilateral.ptolemyAuxiliaryFunction a b c d =
      4 * (s - t) *
        (s * t * (t - s) - 4 * x * t * (t - 1) + 4 * y * s * (s - 1)) - quadruple := by
    unfold Quadrilateral.ptolemyAuxiliaryFunction
    rw [quadrupleEq]
    congr 1
    dsimp only [s, t, x, y]
    ring1
  unfold ptolemyClearedArchimedes
  dsimp only
  rw [denominatorEq, numeratorEq, quadrupleEq, auxiliaryEq]
  have db : d * b = y := by dsimp only [y]; ring1
  rw [db]
  change (x * denominator + y * denominator + numerator) ^ 2 -
    2 * ((x * denominator) ^ 2 + (y * denominator) ^ 2 + numerator ^ 2) = _
  exact ptolemy_factorization_symmetric s t x y

/-- Theorem 114 (Ptolemy): for a solvable cyclic quadrilateral, the products of opposite side spreads and the product of
the diagonal spreads form a quad triple. -/
theorem ptolemy
    (spreads : Quadrilateral.CyclicSubtendedSpreads K)
    (twoNonzero : (2 : K) ≠ 0)
    (solvable : Cyclic.Basic.Quadrilateral.CyclicSubtendedSpreads.IsSolvable spreads) :
    Trigonometry.QuadTriple
      (spreads.r₁₂ * spreads.r₃₄)
      (spreads.r₁₄ * spreads.r₂₃)
      (spreads.r₁₃ * spreads.r₂₄) := by
  let a := spreads.r₁₂
  let b := spreads.r₂₃
  let c := spreads.r₃₄
  let d := spreads.r₁₄
  let firstNumerator := ptolemyFirstDiagonalNumerator a b c d
  let firstDenominator := ptolemyFirstDiagonalDenominator a b c d
  let secondNumerator := ptolemySecondDiagonalNumerator a b c d
  let secondDenominator := ptolemySecondDiagonalDenominator a b c d
  let denominator := firstDenominator * secondDenominator
  have theorem110 := Quadrilateral.cyclic_quadrilateral_spreads spreads twoNonzero
  have quadrupleRelation : Quadruple.quadrupleSpreadFunction a b c d = 0 := by
    exact theorem110.1
  have firstDenominatorNonzero : firstDenominator ≠ 0 := by
    exact solvable.1
  have secondDenominatorNonzero : secondDenominator ≠ 0 := by
    exact solvable.2
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero firstDenominatorNonzero
      secondDenominatorNonzero
  have firstFormula : spreads.r₁₃ = firstNumerator / firstDenominator := by
    exact theorem110.2.1 firstDenominatorNonzero
  have secondFormula : spreads.r₂₄ = secondNumerator / secondDenominator := by
    exact theorem110.2.2 secondDenominatorNonzero
  have firstCleared : spreads.r₁₃ * firstDenominator = firstNumerator := by
    rw [firstFormula]
    exact ExplicitField.div_mul_cancel firstNumerator
      firstDenominatorNonzero
  have secondCleared : spreads.r₂₄ * secondDenominator = secondNumerator := by
    rw [secondFormula]
    exact ExplicitField.div_mul_cancel secondNumerator
      secondDenominatorNonzero
  have diagonalProductCleared :
      (spreads.r₁₃ * spreads.r₂₄) * denominator =
        firstNumerator * secondNumerator := by
    unfold denominator
    calc
      (spreads.r₁₃ * spreads.r₂₄) *
          (firstDenominator * secondDenominator) =
        (spreads.r₁₃ * firstDenominator) *
          (spreads.r₂₄ * secondDenominator) := by ring1
      _ = firstNumerator * secondNumerator := by
        rw [firstCleared, secondCleared]
  unfold Trigonometry.QuadTriple
  apply ExplicitField.eq_zero_of_mul_eq_zero_left
    (ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero)
  calc
    denominator * denominator *
        QuadTriple.Basic.archimedesFunction (spreads.r₁₂ * spreads.r₃₄)
          (spreads.r₁₄ * spreads.r₂₃)
          (spreads.r₁₃ * spreads.r₂₄) =
      ((spreads.r₁₂ * spreads.r₃₄) * denominator +
          (spreads.r₁₄ * spreads.r₂₃) * denominator +
          firstNumerator * secondNumerator) ^ 2 -
        2 * (((spreads.r₁₂ * spreads.r₃₄) * denominator) ^ 2 +
          ((spreads.r₁₄ * spreads.r₂₃) * denominator) ^ 2 +
          (firstNumerator * secondNumerator) ^ 2) := by
            unfold QuadTriple.Basic.archimedesFunction
            rw [← diagonalProductCleared]
            ring1
    _ = ptolemyClearedArchimedes a b c d := by
      unfold ptolemyClearedArchimedes denominator firstNumerator
        firstDenominator secondNumerator secondDenominator a b c d
      rfl
    _ = Quadruple.quadrupleSpreadFunction a b c d *
        ptolemyAuxiliaryFunction a b c d :=
      ptolemy_cleared_factorization a b c d
    _ = 0 := by rw [quadrupleRelation]; ring1

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

end

end
