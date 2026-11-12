module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid.Adjacent
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Algebra.NatCast

/-! # Exact endpoint and interior positions of the original finite parameter grid

The initial edge uses the first positive node. Every other edge uses the
literal retained positive-positive position, with both endpoint indices
proved from their original finite bounds. A one-interval grid has only the
initial edge and never asks for an element of Fin 0.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Select the first retained positive node of an original positive grid. -/
@[expose] def gridFirstIndex (count : Nat) (positive : 0 < count) : Fin count := ⟨0, positive⟩

/-- The first original positive offset is exactly the original reciprocal-width Gaussian increment. -/
theorem gridOffset_first (count : Nat) (positive : 0 < count) (direction : Canonical) :
    gridOffset count (gridFirstIndex count positive).succ direction = gridIncrement count direction := by
  apply congrArg (fun width : Rational => Purelib.Data.Gaussian.Scale.scale width direction)
  change Arithmetic.normalizedDiv ((1 : Nat) : Rational) (count : Rational) = 1 / (count : Rational)
  rewrite [Nat.cast_one]
  exact Arithmetic.normalizedDiv_eq 1 (count : Rational)

/-- Select the retained positive-positive position of an original edge after the initial edge. -/
@[expose] def gridInnerEdge (count : Nat) (index : Fin count) (nonzero : index.val ≠ 0) : Fin (count - 1) :=
  ⟨index.val - 1, by
    have bound := index.isLt
    omega0⟩

/-- The first positive endpoint of an interior edge is the literal preceding grid sample position. -/
theorem gridInnerEdge_first (count : Nat) (index : Fin count) (nonzero : index.val ≠ 0) :
    (gridPairIndex count (gridInnerEdge count index nonzero)).succ = index.castSucc := by
  apply Fin.ext
  change index.val - 1 + 1 = index.val
  omega0

/-- The second positive endpoint of an interior edge is the literal same retained positive node. -/
theorem gridInnerEdge_last (count : Nat) (index : Fin count) (nonzero : index.val ≠ 0) :
    gridNextIndex count (gridPairIndex count (gridInnerEdge count index nonzero))
      (gridPairFollowing count (gridInnerEdge count index nonzero)) = index := by
  apply Fin.ext
  change index.val - 1 + 1 = index.val
  omega0

/-- A zero-valued original edge is exactly the first retained positive-node index. -/
theorem gridIndex_first (count : Nat) (positive : 0 < count) (index : Fin count) (zero : index.val = 0) :
    index = gridFirstIndex count positive := Fin.ext zero

/-- The source position of the initial edge is the original node zero. -/
theorem gridIndex_zero (count : Nat) (index : Fin count) (zero : index.val = 0) :
    index.castSucc = (0 : Fin (count + 1)) := Fin.ext zero

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

end
