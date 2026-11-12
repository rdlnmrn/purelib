module

import Purelib.Polynomial.Dense.Roots.Word.Selection
import Purelib.Polynomial.Recurrence.Boundary.Hermite.Selected
import Purelib.Data.Rat.Fraction.Field

/-!
# Selected original block multiplicities and actual zero-shift coordinates

The original zero root occurs twice, the rejected root once, and another
selected original root once. The computed selected word keeps indices zero,
zero and two, so its count is three rather than the two chosen block labels.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Word.Selection

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix

/-- The exact original fourth-degree polynomial has a repeated zero root. -/
private def polynomial : DensePolynomial Rational := ⟨[1, -3, 2, 0, 0]⟩

/-- Original block multiplicities are two, one and one in their retained order. -/
private def blocks : List (Block Rational) := [⟨0, 2, by decide⟩, ⟨1, 1, by decide⟩, ⟨2, 1, by decide⟩]

/-- The original difference table uses those same bounded root indices. -/
private def differences : SquareMatrix Rational blocks.length :=
  .cons (.cons 0 (.cons (-1) (.cons (-1 / 2) .nil)))
    (.cons (.cons 1 (.cons 0 (.cons (-1) .nil))) (.cons (.cons (1 / 2) (.cons 1 (.cons 0 .nil))) .nil))

/-- The retained original factorization is independent of every label and selected word. -/
private def bank : Bank polynomial :=
  { blocks := blocks
    count_eq := by decide +kernel
    monicProduct := product blocks
    product_eq := rfl
    factorization := by decide +kernel
    differenceInverses := differences
    difference_unit := by decide +kernel }

/-- The first and third original blocks are labelled selected. -/
private def labels : Vec Bool bank.blocks.length := .cons true (.cons false (.cons true .nil))

/-- The original selector retains those actual labels and their certified finite caches. -/
private def retained := Word.Selection.prepare bank labels

/-- The complete cached original word includes the rejected original index between the selected blocks. -/
private theorem full_word : retained.fullWord =
    [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide +kernel

/-- The selected word preserves both zero-root occurrences and the original final index two. -/
private theorem selected_word : retained.word = [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩] := by
  decide +kernel

/-- The selected count includes the original repeated multiplicity. -/
private theorem weighted_count : retained.count = 3 := by decide +kernel

/-- The original zero-root block retains both of its actual occurrences. -/
private theorem repeated_count : countBefore ⟨0, by decide⟩ retained.word retained.word.length = 2 := by
  decide +kernel

/-- The rejected original block has no selected occurrence. -/
private theorem rejected_count : countBefore ⟨1, by decide⟩ retained.word retained.word.length = 0 := by
  decide +kernel

/-- Every selected occurrence retains its actual original multiplicity bound. -/
private theorem original_bounds (column : Fin retained.word.length) :
    countBefore (retained.word[column.val]'column.isLt) retained.word column.val <
      (bank.block (retained.word[column.val]'column.isLt)).multiplicity := retained.admissible column

/-- The selected final occurrence retains the true label at its original third block. -/
private theorem original_label : retained.labels (retained.word[2]'(by decide)) = true :=
  retained.accepted ⟨2, by decide⟩

/-- Zero-shift boundary preparation consumes the same original labels without any root-unit input. -/
private def boundary := Boundary.Hermite.Selected.prepareZero bank labels 4

/-- The actual zero-shift kernel has three original source coordinates, including both transients. -/
private theorem kernel_dimension : boundary.result.normal.kernelDimension = 3 := by decide +kernel

/-- Its actual independent kernel and complement coordinates give defect minus three. -/
private theorem defect : boundary.result.normal.defect = -3 := by decide +kernel

/-- The generic original count readback derives this same defect from actual coordinate dimensions. -/
private theorem defect_readback : boundary.result.normal.defect = -(boundary.selection.count : Int) :=
  boundary.defect_count

/-- Rejecting all original labels produces the exact empty original word. -/
private def none := Word.Selection.prepare bank (.cons false (.cons false (.cons false .nil)))

/-- No rejected original block contributes a selected coordinate. -/
private theorem empty_word : none.word = [] := by decide +kernel

/-- The same original selection directly supplies an empty positive-shift boundary without a root unit. -/
private def emptyBoundary := Boundary.Hermite.Selected.ofEmpty none empty_word 2 2 (by decide)

/-- Both actual target coordinates of that empty selection remain complementary. -/
private theorem empty_complement : emptyBoundary.result.normal.cokernelDimension = 2 := by decide +kernel

/-- Selecting every original block retains all four original multiplicity coordinates. -/
private def all := Word.Selection.prepare bank (.cons true (.cons true (.cons true .nil)))

/-- The complete selected count is the original degree-sized coordinate count. -/
private theorem all_count : all.count = 4 := by decide +kernel

end TestPurelib.Polynomial.Dense.Roots.Word.Selection
