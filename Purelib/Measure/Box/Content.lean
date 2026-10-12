module
import Purelib.Measure.Weighted.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content

public import Purelib.Measure.Content.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Normalized finite distributions on RFAP box partitions

A displayed positive-area box partition can be normalized to an exact
rational distribution over its finitely many child boxes.  This is a law on
the partition cells themselves, not a completed uniform point measure.
-/

namespace Purelib.Measure.Box.Content

open Purelib in
open Purelib.Geometry.Rational in
/-- Retain a rational box as a weighted atom with its exact nonnegative rectangular content. -/
def boxContentAtom (box : Box) :
    Measure.Weighted Box where
  item := box
  weight := Box.Content.boxContent box
  nonnegative := Box.Content.boxContent_nonneg box

open Purelib
open Purelib.Geometry.Rational
open Purelib.Measure
/-- Build finite content from the exact ordered box list, weighting each original occurrence by its rectangular content.
-/
def boxPartitionContent (boxes : List Box) :
    Measure.Content Box where
  atoms := boxes.map boxContentAtom

/-- Total content of the exact box list equals the sum of its original rectangular contents. -/
theorem boxPartitionContent_total (boxes : List Box) :
    (boxPartitionContent boxes).total =
      (boxes.map Box.Content.boxContent).sum := by
  induction boxes with
  | nil => rfl
  | cons box remaining inductionHypothesis =>
      simp only [boxPartitionContent,
        Content.total,
        Measure.totalWeight, List.map_cons,
        boxContentAtom, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]
end Purelib.Measure.Box.Content

end
