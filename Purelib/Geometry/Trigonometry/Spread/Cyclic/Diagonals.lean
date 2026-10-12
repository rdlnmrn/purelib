module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Cyclic.Basic
public import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Theorem 110 (Cyclic quadrilateral spreads): the four side spreads obey the Quadruple spread formula, and each
diagonal spread has the printed quotient whenever its displayed denominator is nonzero. -/
theorem cyclic_quadrilateral_spreads
    (spreads : Quadrilateral.CyclicSubtendedSpreads K) (twoNonzero : (2 : K) ≠ 0) :
    Quadruple.quadrupleSpreadFunction spreads.r₁₂ spreads.r₂₃ spreads.r₃₄
        spreads.r₁₄ = 0 ∧
      (let denominator :=
          2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄);
        denominator ≠ 0 →
          spreads.r₁₃ =
            ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
              (spreads.r₁₄ - spreads.r₃₄) ^ 2) / denominator) ∧
      (let denominator :=
          2 * (spreads.r₁₂ + spreads.r₁₄ - spreads.r₂₃ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₁₄ +
            2 * spreads.r₂₃ * spreads.r₃₄);
        denominator ≠ 0 →
          spreads.r₂₄ =
            ((spreads.r₁₂ - spreads.r₁₄) ^ 2 -
              (spreads.r₂₃ - spreads.r₃₄) ^ 2) / denominator) := by
  dsimp only
  have firstResult := Quadruple.two_spread_triples spreads.r₁₂ spreads.r₂₃
    spreads.r₃₄ spreads.r₁₄ spreads.r₁₃ twoNonzero
    spreads.firstDiagonalAtFourth spreads.firstDiagonalAtSecond
  have secondResult := Quadruple.two_spread_triples spreads.r₁₂ spreads.r₁₄
    spreads.r₂₃ spreads.r₃₄ spreads.r₂₄ twoNonzero
    spreads.secondDiagonalAtThird spreads.secondDiagonalAtFirst
  refine ⟨firstResult.1, ?_, ?_⟩
  · intro denominatorNonzero
    have centersDistinct :
        spreads.r₁₂ + spreads.r₂₃ - 2 * spreads.r₁₂ * spreads.r₂₃ ≠
          spreads.r₃₄ + spreads.r₁₄ - 2 * spreads.r₃₄ * spreads.r₁₄ := by
      intro centersEqual
      apply denominatorNonzero
      calc
        2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄) =
          2 * ((spreads.r₁₂ + spreads.r₂₃ -
              2 * spreads.r₁₂ * spreads.r₂₃) -
            (spreads.r₃₄ + spreads.r₁₄ -
              2 * spreads.r₃₄ * spreads.r₁₄)) := by ring1
        _ = 0 := by rw [centersEqual]; ring1
    have formula := (firstResult.2 centersDistinct).2
    have numeratorEqual :
        (spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₃₄ - spreads.r₁₄) ^ 2 =
          (spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₁₄ - spreads.r₃₄) ^ 2 := by ring1
    have denominatorEqual :
        2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₃₄ - spreads.r₁₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₃₄ * spreads.r₁₄) =
          2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄) := by ring1
    calc
      spreads.r₁₃ =
          ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₃₄ - spreads.r₁₄) ^ 2) /
            (2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₃₄ -
              spreads.r₁₄ - 2 * spreads.r₁₂ * spreads.r₂₃ +
              2 * spreads.r₃₄ * spreads.r₁₄)) := formula
      _ = ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₁₄ - spreads.r₃₄) ^ 2) /
          (2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ -
            spreads.r₃₄ - 2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄)) := by
        rw [numeratorEqual, denominatorEqual]
  · intro denominatorNonzero
    have centersDistinct :
        spreads.r₁₂ + spreads.r₁₄ - 2 * spreads.r₁₂ * spreads.r₁₄ ≠
          spreads.r₂₃ + spreads.r₃₄ - 2 * spreads.r₂₃ * spreads.r₃₄ := by
      intro centersEqual
      apply denominatorNonzero
      calc
        2 * (spreads.r₁₂ + spreads.r₁₄ - spreads.r₂₃ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₁₄ +
            2 * spreads.r₂₃ * spreads.r₃₄) =
          2 * ((spreads.r₁₂ + spreads.r₁₄ -
              2 * spreads.r₁₂ * spreads.r₁₄) -
            (spreads.r₂₃ + spreads.r₃₄ -
              2 * spreads.r₂₃ * spreads.r₃₄)) := by ring1
        _ = 0 := by rw [centersEqual]; ring1
    exact (secondResult.2 centersDistinct).2

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
