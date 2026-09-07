import DivineProportions.Quadrilaterals.CyclicSpreads
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Theorem 114: Ptolemy's theorem

The source proves its rational-trigonometric Ptolemy theorem by substituting
the two diagonal-spread quotients from Theorem 110 and factoring the resulting
Archimedes polynomial.  Here the same calculation is kept finite and
constructive: `ptolemy_cleared_factorization` is the denominator-cleared
polynomial identity, and `ptolemy` cancels only the two explicitly certified
nonzero denominators.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

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

/-- The two denominators whose nonvanishing is the book's definition of a
solvable cyclic quadrilateral. -/
def CyclicSubtendedSpreads.IsSolvable
    (spreads : CyclicSubtendedSpreads K) : Prop :=
  ptolemyFirstDiagonalDenominator spreads.r₁₂ spreads.r₂₃
      spreads.r₃₄ spreads.r₁₄ ≠ 0 ∧
    ptolemySecondDiagonalDenominator spreads.r₁₂ spreads.r₂₃
      spreads.r₃₄ spreads.r₁₄ ≠ 0

/-- The auxiliary polynomial `B` displayed in the source's computer-assisted
factorization proof. -/
def ptolemyAuxiliaryFunction (a b c d : K) : K :=
  4 * (a + c - b - d) *
      ((a - c) ^ 2 * (b + d) * (b + d - 1) -
        (b - d) ^ 2 * (a + c) * (a + c - 1)) -
    quadrupleSpreadFunction a b c d

/-- Archimedes' polynomial after both diagonal-spread quotients have been
cleared.  Its third input is represented by the product of their numerators,
and the first two inputs are scaled by the product of their denominators. -/
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

/-- The denominator-cleared factorization used in the proof of Theorem 114.
It is a universal polynomial identity, so it has no solvability hypothesis. -/
theorem ptolemy_cleared_factorization (a b c d : K) :
    ptolemyClearedArchimedes a b c d =
      quadrupleSpreadFunction a b c d *
        ptolemyAuxiliaryFunction a b c d := by
  unfold ptolemyClearedArchimedes ptolemyFirstDiagonalNumerator
    ptolemyFirstDiagonalDenominator ptolemySecondDiagonalNumerator
    ptolemySecondDiagonalDenominator ptolemyAuxiliaryFunction
    quadrupleSpreadFunction quadrupleSpreadCore
  ring1

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-- Theorem 114 (Ptolemy): for a solvable cyclic quadrilateral, the products
of opposite side spreads and the product of the diagonal spreads form a quad
triple. -/
theorem ptolemy
    (spreads : CyclicSubtendedSpreads K)
    (twoNonzero : (2 : K) ≠ 0)
    (solvable : spreads.IsSolvable) :
    QuadTriple
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
  have theorem110 := cyclic_quadrilateral_spreads spreads twoNonzero
  have quadrupleRelation : quadrupleSpreadFunction a b c d = 0 := by
    exact theorem110.1
  have firstDenominatorNonzero : firstDenominator ≠ 0 := by
    exact solvable.1
  have secondDenominatorNonzero : secondDenominator ≠ 0 := by
    exact solvable.2
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstDenominatorNonzero
      secondDenominatorNonzero
  have firstFormula : spreads.r₁₃ = firstNumerator / firstDenominator := by
    exact theorem110.2.1 firstDenominatorNonzero
  have secondFormula : spreads.r₂₄ = secondNumerator / secondDenominator := by
    exact theorem110.2.2 secondDenominatorNonzero
  have firstCleared : spreads.r₁₃ * firstDenominator = firstNumerator := by
    rw [firstFormula]
    exact RFAP.ExplicitField.div_mul_cancel firstNumerator
      firstDenominatorNonzero
  have secondCleared : spreads.r₂₄ * secondDenominator = secondNumerator := by
    rw [secondFormula]
    exact RFAP.ExplicitField.div_mul_cancel secondNumerator
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
  unfold QuadTriple
  apply eq_zero_of_mul_eq_zero_left
    (RFAP.ExplicitField.mul_ne_zero denominatorNonzero denominatorNonzero)
  calc
    denominator * denominator *
        archimedesFunction (spreads.r₁₂ * spreads.r₃₄)
          (spreads.r₁₄ * spreads.r₂₃)
          (spreads.r₁₃ * spreads.r₂₄) =
      ((spreads.r₁₂ * spreads.r₃₄) * denominator +
          (spreads.r₁₄ * spreads.r₂₃) * denominator +
          firstNumerator * secondNumerator) ^ 2 -
        2 * (((spreads.r₁₂ * spreads.r₃₄) * denominator) ^ 2 +
          ((spreads.r₁₄ * spreads.r₂₃) * denominator) ^ 2 +
          (firstNumerator * secondNumerator) ^ 2) := by
            unfold archimedesFunction
            rw [← diagonalProductCleared]
            ring1
    _ = ptolemyClearedArchimedes a b c d := by
      unfold ptolemyClearedArchimedes denominator firstNumerator
        firstDenominator secondNumerator secondDenominator a b c d
      rfl
    _ = quadrupleSpreadFunction a b c d *
        ptolemyAuxiliaryFunction a b c d :=
      ptolemy_cleared_factorization a b c d
    _ = 0 := by rw [quadrupleRelation]; ring1

end Quadrilateral

end DivineProportions
