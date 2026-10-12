module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Distribution.Basic

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Box.Content
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Normalization.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Geometry.Rational.Box.Subdivision

section
@[expose] public section

/-!
# Normalized finite distributions on RFAP box partitions

A displayed positive-area box partition can be normalized to an exact
rational distribution over its finitely many child boxes.  This is a law on
the partition cells themselves, not a completed uniform point measure.
-/

namespace Purelib.Measure.Box.Distribution

open Purelib in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- Normalize the exact box-content list using its supplied positive-total certificate.

The distribution retains the original box occurrences and divides their rectangular contents by the same original total.
-/
def boxPartitionDistribution (boxes : List Box)
    (positive : 0 < (Box.Content.boxPartitionContent boxes).total) :
    Measure.Distribution Box :=
  (Box.Content.boxPartitionContent boxes).normalize positive

open Purelib.Geometry.Rational in
open Purelib.Measure in
open Purelib.Data in
/-- Normalizing the box-content list retains exactly the original number of box occurrences. -/
theorem boxPartitionDistribution_atoms_length (boxes : List Box)
    (positive : 0 < (Box.Content.boxPartitionContent boxes).total) :
    (boxPartitionDistribution boxes positive).atoms.length = boxes.length := by
  rw [boxPartitionDistribution,
    Content.normalize_atoms_length]
  simp only [-eq_self, -iff_self, Box.Content.boxPartitionContent, List.Map.length_map]
  rfl

open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- A box event's normalized probability equals its original content divided by the exact sum of box contents. -/
theorem boxPartitionDistribution_probability (boxes : List Box)
    (positive : 0 < (Box.Content.boxPartitionContent boxes).total)
    (event : Box → Bool) :
    (boxPartitionDistribution boxes positive).probability event =
      (Box.Content.boxPartitionContent boxes).measure event /
        (boxes.map Box.Content.boxContent).sum := by
  rw [boxPartitionDistribution,
    Content.normalize_probability,
    Box.Content.boxPartitionContent_total]

section
open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Measure
/-- Normalize the two exact vertical children of a positive-content box at the retained interior cut. -/
def verticalSplitDistribution (box : Box) (cut :
  Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < Box.Content.boxContent box) :
    Measure.Distribution Box :=
  boxPartitionDistribution
    [box.verticalLeft cut inside, box.verticalRight cut inside] (by
      rw [Box.Content.boxPartitionContent_total]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [Box.Content.vertical_content_add]
      exact positive)

/-- Normalize the two exact horizontal children of a positive-content box at the retained interior cut. -/
def horizontalSplitDistribution (box : Box) (cut :
  Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < Box.Content.boxContent box) :
    Measure.Distribution Box :=
  boxPartitionDistribution
    [box.horizontalLower cut inside, box.horizontalUpper cut inside] (by
      rw [Box.Content.boxPartitionContent_total]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [Box.Content.horizontal_content_add]
      exact positive)

end

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Measure
/-- The exact vertical-split distribution retains two atom occurrences. -/
theorem verticalSplitDistribution_atoms_length (box : Box)
    (cut : Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < Box.Content.boxContent box) :
    (verticalSplitDistribution box cut inside positive).atoms.length = 2 := by
  unfold verticalSplitDistribution
  rw [boxPartitionDistribution_atoms_length]
  rfl

/-- The exact horizontal-split distribution retains two atom occurrences. -/
theorem horizontalSplitDistribution_atoms_length (box : Box)
    (cut : Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < Box.Content.boxContent box) :
    (horizontalSplitDistribution box cut inside positive).atoms.length = 2 := by
  unfold horizontalSplitDistribution
  rw [boxPartitionDistribution_atoms_length]
  rfl
end Purelib.Measure.Box.Distribution

end
