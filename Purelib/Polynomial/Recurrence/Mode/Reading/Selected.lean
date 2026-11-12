module

public import Purelib.Polynomial.Recurrence.Mode.Reading
public import Purelib.Polynomial.Dense.Roots.Word.Selection
public import Purelib.Data.List.DependentProduct
public import Purelib.Data.Rat.List.Minimum
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Pre-observation schedules on original selected generalized modes

The original selected word and its retained occurrence orders determine every
root and generalized order. Fixed scalar weights, gains and original-block
ceilings produce the same finite mode requests before a reading is observed.
One positive minimum pays all retained requests, including an empty word.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.Data.Rat.List

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}

namespace Selected

/-- Read the same original bounded block at an occurrence of the already selected word. -/
abbrev original (selection : Word.Selection bank) (column : Fin selection.word.length) :=
  selection.word[column.val]'column.isLt

set_option genInjectivity false in
/-- The retained threshold and finite discrepancy request of one original selected generalized occurrence.

The original root and cached occurrence order remain indices. Each expensive
constructor is retained with its complete defining equation; the discrepancy
horizon starts at zero and includes the computed threshold and requested tail.
-/
structure Entry (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (ceilings : Vec Rational bank.blocks.length)
    (epsilon : Rational) (count : Nat) (column : Fin selection.word.length) where
  /-- The same fixed original gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The fixed selected original-block ceiling is nonnegative. -/
  ceilingNonnegative : 0 ≤ ceilings (original selection column)
  /-- The same selected original-block ceiling lies strictly inside unit quadrance. -/
  ceilingInside : ceilings (original selection column) < 1
  /-- The original quarter-target is positive. -/
  quarterPositive : 0 < epsilon / 4
  /-- The original uniform inside threshold on the same ceiling and generalized order. -/
  inside : Inside (ceilings (original selection column)) (occurrences.orders column) (epsilon / 4)
  /-- The retained threshold is the complete original pre-observation constructor. -/
  inside_eq : inside = Inside.prepare (ceilings (original selection column)) ceilingNonnegative ceilingInside
    (occurrences.orders column) (epsilon / 4) quarterPositive
  /-- The same original root and fixed gain supply all required finite discrepancy coefficients. -/
  parameters : Parameters weight (bank.block (original selection column)).point gain
    (occurrences.orders column) (inside.index + count)
  /-- The parameters are the complete original constructor on that same retained threshold. -/
  parameters_eq : parameters = Parameters.prepare weight (bank.block (original selection column)).point gain
    gainNonnegative (occurrences.orders column) (inside.index + count)
  /-- The retained original mode request pays the same quarter-target. -/
  request : Request parameters (epsilon / 4)
  /-- The request is the complete original constructor on the same stored coefficient cache. -/
  request_eq : request = Request.prepare parameters (epsilon / 4) quarterPositive

constructive_injectivity Entry

namespace Entry

/-- Prepare one original selected mode schedule without selecting or observing any Gaussian reading. -/
@[expose] def prepare (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (ceilings : Vec Rational bank.blocks.length)
    (epsilon : Rational) (count : Nat) (column : Fin selection.word.length)
    (gainNonnegative : 0 ≤ gain) (ceilingNonnegative : 0 ≤ ceilings (original selection column))
    (ceilingInside : ceilings (original selection column) < 1) (quarterPositive : 0 < epsilon / 4) :
    Entry selection occurrences weight gain ceilings epsilon count column :=
  let inside := Inside.prepare (ceilings (original selection column)) ceilingNonnegative ceilingInside
    (occurrences.orders column) (epsilon / 4) quarterPositive
  let parameters := Parameters.prepare weight (bank.block (original selection column)).point gain
    gainNonnegative (occurrences.orders column) (inside.index + count)
  let request := Request.prepare parameters (epsilon / 4) quarterPositive
  { gainNonnegative, ceilingNonnegative, ceilingInside, quarterPositive, inside, inside_eq := rfl
    parameters, parameters_eq := rfl, request, request_eq := rfl }

variable {selection : Word.Selection bank} {occurrences : Occurrences selection.word}
variable {weight : Weight K} {gain : Rational} {ceilings : Vec Rational bank.blocks.length}
variable {epsilon : Rational} {count : Nat} {column : Fin selection.word.length}

/-- A requested tail coordinate is the same original finite index after the stored inside threshold. -/
@[expose] def index (retained : Entry selection occurrences weight gain ceilings epsilon count column)
    (offset : Fin count) : Fin (retained.inside.index + count) :=
  ⟨retained.inside.index + offset.val, Nat.add_lt_add_left offset.isLt retained.inside.index⟩

/-- A paid reading bounds the actual original formal mode throughout its retained finite tail window. -/
theorem window_lt (retained : Entry selection occurrences weight gain ceilings epsilon count column)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ retained.request.tolerance)
    (pointBound : Norm.Basic.normSq (reading.read (bank.block (original selection column)).point) ≤
      ceilings (original selection column)) (offset : Fin count) :
    Norm.Basic.normSq (reading.read (window (bank.block (original selection column)).point
      (occurrences.orders column) (retained.inside.index + count) (retained.index offset))) < epsilon :=
  retained.request.inside_window_lt retained.inside reading gain_eq paid pointBound (retained.index offset)
    (Nat.le_add_right _ _)

end Entry
end Selected

set_option genInjectivity false in
/-- Cached pre-observation schedules for the same original selected word and occurrence orders.

Each retained dependent-product entry belongs to its original selected column.
The common tolerance is the positive minimum of those actual stored requests;
the initial bound one handles an empty selection without observing roots.
-/
structure Selected (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (ceilings : Vec Rational bank.blocks.length)
    (epsilon : Rational) (count : Nat) where
  /-- The actual stored original mode schedules in unchanged selected-word order. -/
  entries : DependentProduct selection.word (Selected.Entry selection occurrences weight gain ceilings epsilon count)
  /-- The materialized endpoint requests read the same already stored mode schedules. -/
  tolerances : List Rational
  /-- The displayed requests preserve original selected-column order without rerunning producers. -/
  tolerances_eq : tolerances = List.ofFn (fun column =>
    (DependentProduct.get selection.word entries column).request.tolerance)
  /-- The once-computed sufficient common endpoint tolerance. -/
  tolerance : Rational
  /-- The common tolerance is the original positive-default finite minimum of the stored requests. -/
  tolerance_eq : tolerance = Minimum.positiveMinimum tolerances

constructive_injectivity Selected

namespace Selected

/-- Prepare all original selected mode requests before any common Gaussian reading is observed.

The same retained occurrence cache supplies every generalized order. The
original dependent product materializes each mode schedule once; the finite
minimum then consumes only their actual stored endpoint tolerances.
-/
@[expose] def prepare (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (ceilings : Vec Rational bank.blocks.length)
    (ceilingsNonnegative : ∀ original, selection.labels original = true → 0 ≤ ceilings original)
    (ceilingsInside : ∀ original, selection.labels original = true → ceilings original < 1)
    (epsilon : Rational) (epsilonPositive : 0 < epsilon) (count : Nat) :
    Selected selection occurrences weight gain ceilings epsilon count :=
  let quarterPositive := Field.div_pos_direct epsilonPositive (by decide : (0 : Rational) < 4)
  let entries := DependentProduct.ofFn selection.word (fun column =>
    Entry.prepare selection occurrences weight gain ceilings epsilon count column gainNonnegative
      (ceilingsNonnegative (original selection column) (selection.accepted column))
      (ceilingsInside (original selection column) (selection.accepted column)) quarterPositive)
  let tolerances := List.ofFn (fun column =>
    (DependentProduct.get selection.word entries column).request.tolerance)
  let tolerance := Minimum.positiveMinimum tolerances
  { entries, tolerances, tolerances_eq := rfl, tolerance, tolerance_eq := rfl }

variable {selection : Word.Selection bank} {occurrences : Occurrences selection.word}
variable {weight : Weight K} {gain : Rational} {ceilings : Vec Rational bank.blocks.length}
variable {epsilon : Rational} {count : Nat}

/-- Read the same already stored mode schedule at its unchanged original selected-column coordinate. -/
@[expose] def entryAt (retained : Selected selection occurrences weight gain ceilings epsilon count)
    (column : Fin selection.word.length) := DependentProduct.get selection.word retained.entries column

/-- The common endpoint tolerance is positive even when the selected word is empty. -/
theorem tolerance_positive (retained : Selected selection occurrences weight gain ceilings epsilon count) :
    0 < retained.tolerance := by
  rewrite [retained.tolerance_eq]
  apply Minimum.positiveMinimum_pos
  intro tolerance member
  rewrite [retained.tolerances_eq] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨column, same⟩
  exact same ▸ (retained.entryAt column).request.tolerance_positive

/-- The same common endpoint tolerance pays every actual stored original mode request. -/
theorem tolerance_le (retained : Selected selection occurrences weight gain ceilings epsilon count)
    (column : Fin selection.word.length) : retained.tolerance ≤ (retained.entryAt column).request.tolerance := by
  rewrite [retained.tolerance_eq]
  apply Minimum.positiveMinimum_le_of_mem
  rewrite [retained.tolerances_eq]
  exact OfFn.Basic.mem_ofFn.mpr ⟨column, rfl⟩

/-- A common paid reading and its same original root ceiling bound every requested original finite mode value. -/
theorem window_lt (retained : Selected selection occurrences weight gain ceilings epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ retained.tolerance) (column : Fin selection.word.length)
    (pointBound : Norm.Basic.normSq (reading.read (bank.block (original selection column)).point) ≤
      ceilings (original selection column)) (offset : Fin count) :
    Norm.Basic.normSq (reading.read (window (bank.block (original selection column)).point
      (occurrences.orders column) ((retained.entryAt column).inside.index + count)
      ((retained.entryAt column).index offset))) < epsilon :=
  (retained.entryAt column).window_lt reading gain_eq (paid.trans (retained.tolerance_le column)) pointBound offset

end Selected
end Purelib.Polynomial.Recurrence.Mode.Reading

end
