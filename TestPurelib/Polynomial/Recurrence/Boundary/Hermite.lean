module

import Purelib.Polynomial.Recurrence.Boundary.Hermite.Selected
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Quadratic.Pair.Basic

/-!
# Original boundary rows through automatic retained Hermite coordinates

The exact coupled row uses a complete original root bank with an unselected
outside root. A repeated perturbed-unit root tests generalized modes over a
ring with a nonzero nilpotent element. Zero shifts retain true zero-root
transients without any root or constant inverse premise.
-/

namespace TestPurelib.Polynomial.Recurrence.Boundary.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- The original cubic has the demanded coupled startup coefficients at its first two roots. -/
private def polynomial : DensePolynomial Rational := ⟨[1, -11 / 4, 13 / 8, -1 / 4]⟩

/-- The complete original root bank includes the unselected outside root two. -/
private def blocks : List (Block Rational) :=
  [⟨1 / 4, 1, by decide⟩, ⟨1 / 2, 1, by decide⟩, ⟨2, 1, by decide⟩]

/-- Every original distinct-root difference uses its independent exact inverse. -/
private def differences : SquareMatrix Rational blocks.length :=
  .cons (.cons 0 (.cons (-4) (.cons (-4 / 7) .nil)))
    (.cons (.cons 4 (.cons 0 (.cons (-2 / 3) .nil)))
      (.cons (.cons (4 / 7) (.cons (2 / 3) (.cons 0 .nil))) .nil))

/-- The complete original factorization is kernel-checked independently of the boundary construction. -/
private def bank : Bank polynomial :=
  { blocks := blocks
    count_eq := by decide +kernel
    monicProduct := product blocks
    product_eq := rfl
    factorization := by decide +kernel
    differenceInverses := differences
    difference_unit := by decide +kernel }

/-- Original retained labels select the first two simple roots and reject the third original block. -/
private def labels : Vec Bool bank.blocks.length := .cons true (.cons true (.cons false .nil))

/-- The actual selected original word is computed from those same retained labels. -/
private def word := (Word.Selection.prepare bank labels).word

/-- The selected producer derives the original word, bounds, equations, units and actual boundary coordinates. -/
private def selected := Boundary.Hermite.Selected.preparePositive bank (by decide +kernel) labels 0 5
  (by decide) (-4) (by decide +kernel)

/-- The actual original boundary consumes the same computed selected word. -/
private def retained : Boundary.Hermite bank word 1 5 := selected.result

/-- The computed selected word preserves the original first and second block indices. -/
private theorem selected_word : word = [⟨0, by decide⟩, ⟨1, by decide⟩] := by decide +kernel

/-- The original label fold produces two actual source coordinates. -/
private theorem selected_count : selected.selection.count = 2 := by decide +kernel

/-- The actual cached boundary retains its required first coefficient one. -/
private theorem coupled_first : retained.boundary 0 ⟨0, by decide⟩ = 1 := by decide +kernel

/-- Its second coefficient remains one half, with the same original selected root. -/
private theorem coupled_second : retained.boundary 0 ⟨1, by decide⟩ = 1 / 2 := by decide +kernel

/-- The actual automatically constructed identity block has one coordinate. -/
private theorem coupled_rank : retained.normal.rank = 1 := by decide +kernel

/-- The same original coupled boundary has one free source coordinate. -/
private theorem coupled_kernel_dimension : retained.normal.kernelDimension = 1 := by decide +kernel

/-- The actual target-minus-source coordinate count gives defect minus one. -/
private theorem coupled_defect : retained.normal.defect = -1 := by decide +kernel

/-- Half of the actual retained kernel coordinate reconstructs the demanded normalized witness. -/
private def half : Vec Rational 2 := retained.normal.kernelVector (.cons (1 / 2) .nil)

/-- The normalized witness has its exact first original mode coefficient minus one half. -/
private theorem half_first : half 0 = -1 / 2 := by decide +kernel

/-- The same witness has its exact second original mode coefficient one. -/
private theorem half_second : half 1 = 1 := by decide +kernel

/-- The actual computed boundary annihilates that same reconstructed coordinate vector. -/
private theorem half_kernel : Rectangular.apply retained.boundary half = .cons 0 .nil :=
  retained.normal.matrix_kernelVector _

/-- Reading the same original kernel coordinates recovers the retained half coefficient. -/
private theorem half_readback : retained.normal.kernelCoordinates half = .cons (1 / 2) .nil :=
  retained.normal.kernelCoordinates_kernelVector _

/-- An empty original label table dispatches the positive constructor to its unit-free empty branch. -/
private def rejected := Boundary.Hermite.Selected.preparePositive bank (by decide +kernel)
  (.cons false (.cons false (.cons false .nil))) 0 5 (by decide) (-4) (by decide +kernel)

/-- The actual positive empty-selection transport retains no block-unit or shift cache. -/
private theorem rejected_transport :
    (match rejected.result.transport with | .empty _ => true | _ => false) = true := by decide +kernel

/-- The sole actual target coordinate of that rejected selection remains complementary. -/
private theorem rejected_complement : rejected.result.normal.cokernelDimension = 1 := by decide +kernel

/-- The original exact algebra with one nonzero nilpotent generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- Its original nonzero square-zero element. -/
private def epsilon : Dual := ⟨0, 1⟩

/-- The actual repeated perturbed-unit quadratic. -/
private def repeatedPolynomial : DensePolynomial Dual := ⟨[1, -2 - 2 * epsilon, 1 + 2 * epsilon]⟩

/-- The original block retains both generalized orders at that same root. -/
private def repeatedBlocks : List (Block Dual) := [⟨1 + epsilon, 2, by decide⟩]

/-- The exact original repeated-root factorization. -/
private def repeatedBank : Bank repeatedPolynomial :=
  { blocks := repeatedBlocks
    count_eq := by decide +kernel
    monicProduct := product repeatedBlocks
    product_eq := rfl
    factorization := by decide +kernel
    differenceInverses := .cons (.cons 0 .nil) .nil
    difference_unit := by decide +kernel }

/-- The original selected word computes both actual generalized coordinates from one retained true label. -/
private def repeatedWord := (Word.Selection.prepare repeatedBank (.cons true .nil)).word

/-- The selected construction handles repeated roots without caller-supplied occurrence bounds. -/
private def repeated : Boundary.Hermite repeatedBank repeatedWord 1 4 :=
  (Boundary.Hermite.Selected.preparePositive repeatedBank (by decide +kernel) (.cons true .nil) 0 4
    (by decide) (1 - 2 * epsilon) (by decide +kernel)).result

/-- Its first original boundary coefficient is minus the repeated original root. -/
private theorem repeated_first : repeated.boundary 0 ⟨0, by decide⟩ = -1 - epsilon := by decide +kernel

/-- The actual generalized-order column retains boundary coefficient one. -/
private theorem repeated_second : repeated.boundary 0 ⟨1, by decide⟩ = 1 := by decide +kernel

/-- The original repeated-root kernel reconstructs first coefficient one. -/
private theorem repeated_kernel_first : repeated.normal.kernelVector (.cons 1 .nil) ⟨0, by decide⟩ = 1 := by
  decide +kernel

/-- Its second original coefficient is the same repeated root, satisfying the actual row. -/
private theorem repeated_kernel_second :
    repeated.normal.kernelVector (.cons 1 .nil) ⟨1, by decide⟩ = 1 + epsilon := by decide +kernel

/-- More startup rows use only finite auxiliary coordinate completion, with no extra polynomial mode claim. -/
private def tall : Boundary.Hermite repeatedBank repeatedWord 3 6 :=
  (Boundary.Hermite.Selected.preparePositive repeatedBank (by decide +kernel) (.cons true .nil) 2 6
    (by decide) (1 - 2 * epsilon) (by decide +kernel)).result

/-- Three actual rows on two original modes leave one target complement coordinate. -/
private theorem tall_complement : tall.normal.cokernelDimension = 1 := by decide +kernel

/-- The same tall actual boundary has no free source coordinate. -/
private theorem tall_kernel : tall.normal.kernelDimension = 0 := by decide +kernel

/-- The exact zero-root quadratic retains its original zero coefficient slots. -/
private def zeroPolynomial : DensePolynomial Rational := ⟨[1, 0, 0]⟩

/-- Its one original root block retains both true zero-root transients. -/
private def zeroBank : Bank zeroPolynomial :=
  { blocks := [⟨0, 2, by decide⟩]
    count_eq := by decide +kernel
    monicProduct := product [⟨0, 2, by decide⟩]
    product_eq := rfl
    factorization := by decide +kernel
    differenceInverses := .cons (.cons 0 .nil) .nil
    difference_unit := by decide +kernel }

/-- An empty original selection needs no constant or root inverse at positive shift. -/
private def empty := Boundary.Hermite.prepareEmpty zeroBank 3 3 (by decide)

/-- The empty actual boundary has all three original target coordinates as complement. -/
private theorem empty_complement : empty.normal.cokernelDimension = 3 := by decide +kernel

/-- A zero shift constructs both actual transients without a constant or root inverse. -/
private def transients := Boundary.Hermite.prepareZero zeroBank (Word.expand zeroBank.blocks) 3

/-- Both actual zero-root transients are free original source coordinates. -/
private theorem transient_kernel : transients.normal.kernelDimension = 2 := by decide +kernel

/-- The original first zero-root transient reads one at the original initial index. -/
private theorem transient_first : transients.readings.values ⟨0, by decide⟩ 0 = 1 := by decide +kernel

/-- The original generalized zero-root transient reads one at its distinct next index. -/
private theorem transient_second : transients.readings.values ⟨1, by decide⟩ 1 = 1 := by decide +kernel

end TestPurelib.Polynomial.Recurrence.Boundary.Hermite
