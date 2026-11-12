module

import Purelib.Polynomial.Dense.Roots.Units
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Cached original root units over a ring with nilpotents

The repeated root has two generalized occurrences but one original block.
Its actual synthetic quotient and constant inverse produce the same retained
root inverse at both occurrences.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Units

open Purelib.Algebra.Quadratic
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix

/-- The original square-zero pair algebra over exact Gaussian rationals. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original algebra's nonzero nilpotent generator. -/
private def epsilon : Dual := ⟨0, 1⟩

/-- The exact displayed repeated-root quadratic. -/
private def polynomial : DensePolynomial Dual := ⟨[1, -2 - 2 * epsilon, 1 + 2 * epsilon]⟩

/-- One original block retains the repeated perturbed-unit root. -/
private def blocks : List (Block Dual) := [⟨1 + epsilon, 2, by decide⟩]

/-- The original singleton difference table has no distinct-root obligations. -/
private def differences : SquareMatrix Dual blocks.length := .cons (.cons 0 .nil) .nil

/-- The original quadratic has the literal retained repeated-root factorization. -/
private def bank : Bank polynomial :=
  { blocks := blocks
    count_eq := by decide +kernel
    monicProduct := product blocks
    product_eq := rfl
    factorization := by decide +kernel
    differenceInverses := differences
    difference_unit := by decide +kernel }

/-- The original constant reading times its displayed inverse equals one. -/
private theorem constant_unit : polynomial.normalize.eval 0 * (1 - 2 * epsilon) = 1 := by
  decide +kernel

/-- The producer retains the original block's actual division and quotient-derived inverse once. -/
private def retained : bank.Units := Bank.Units.prepare bank (1 - 2 * epsilon) constant_unit

/-- The same original synthetic quotient is the independently displayed monic linear table. -/
private theorem quotient : (retained.get ⟨0, by decide⟩).division.quotient.coeffs = [1, -1 - epsilon] := by
  decide +kernel

/-- The cached inverse is the independently computed exact perturbed-unit inverse. -/
private theorem inverse : retained.inverseAt ⟨0, by decide⟩ = 1 - epsilon := by
  decide +kernel

/-- The retained inverse multiplies its same original root to one. -/
private theorem original_unit : (bank.block ⟨0, by decide⟩).point * retained.inverseAt ⟨0, by decide⟩ = 1 :=
  retained.unitAt ⟨0, by decide⟩

/-- Two generalized occurrences select the same single retained original block. -/
private def word : List (Fin bank.blocks.length) := [⟨0, by decide⟩, ⟨0, by decide⟩]

/-- Repeated occurrences read the same retained scalar rather than repeat synthetic division. -/
private theorem repeated : retained.wordInverses word =
    (.cons (1 - epsilon) (.cons (1 - epsilon) .nil) : Vec Dual 2) := by
  apply vector_ext
  intro column
  have readings : ∀ position : Fin 2,
      retained.wordInverses word position =
        (.cons (1 - epsilon) (.cons (1 - epsilon) .nil) : Vec Dual 2) position := by decide +kernel
  exact readings column

/-- Every repeated word coordinate retains the same original block-root unit equation. -/
private theorem repeated_units (column : Fin word.length) :
    (bank.block (word[column.val]'column.isLt)).point * retained.wordInverses word column = 1 :=
  retained.word_units word column

end TestPurelib.Polynomial.Dense.Roots.Units
